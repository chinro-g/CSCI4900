#include <gtk/gtk.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>
#include <glib/gunicode.h> /* for utf8 strlen */
#include <sys/socket.h>
#include <netinet/in.h>
#include <netdb.h>
#include <openssl/sha.h>
#include <openssl/evp.h>
#include <openssl/hmac.h>
#include <getopt.h>
#include "dh.h"
#include "keys.h"
#include "util.h"

#ifndef PATH_MAX
#define PATH_MAX 1024
#endif

static GtkTextBuffer* tbuf; /* transcript buffer */
static GtkTextBuffer* mbuf; /* message buffer */
static GtkTextView*  tview; /* view for transcript */
static GtkTextMark*   mark; /* used for scrolling to end of transcript, etc */
int cylen; /*Length of the cipher text*/
char encKey[32];


static pthread_t trecv;     /* wait for incoming messages and post to queue */
void recvMsg();       /* for trecv */
char decryptMe(char);
char encryptMe(char);
char random_char(int);
//void initPk();
unsigned char hmac(unsigned char, char);
static dhKey client_ephemeral;
static dhKey server_ephemeral;
//unsigned char mainDH[128];
unsigned char clientDH[128];
unsigned char serverDH[128];

#define max(a, b)         \
	({ typeof(a) _a = a;    \
	 typeof(b) _b = b;    \
	 _a > _b ? _a : _b; })

/* network stuff... */

static int listensock, sockfd;
static int isclient = 1;

static void error(const char *msg)
{
	perror(msg);
	exit(EXIT_FAILURE);
}

int initServerNet(int port)
{
	int reuse = 1;
    initKey(&server_ephemeral);
    dhGenk(&server_ephemeral);
    

	struct sockaddr_in serv_addr;
	listensock = socket(AF_INET, SOCK_STREAM, 0);
	setsockopt(listensock, SOL_SOCKET, SO_REUSEADDR, &reuse, sizeof(reuse));
	/* NOTE: might not need the above if you make sure the client closes first */
	if (listensock < 0)
		error("ERROR opening socket");
	bzero((char *) &serv_addr, sizeof(serv_addr));
	serv_addr.sin_family = AF_INET;
	serv_addr.sin_addr.s_addr = INADDR_ANY;
	serv_addr.sin_port = htons(port);
	if (bind(listensock, (struct sockaddr *) &serv_addr, sizeof(serv_addr)) < 0)
		error("ERROR on binding");
	fprintf(stderr, "listening on port %i...\n",port);
	listen(listensock,1);
	socklen_t clilen;
	struct sockaddr_in  cli_addr;
	sockfd = accept(listensock, (struct sockaddr *) &cli_addr, &clilen);
	if (sockfd < 0)
		error("error on accept");
	close(listensock);

	fprintf(stderr, "connection made, starting session...\n");

	/* at this point, should be able to send/recv on sockfd */

	fprintf(stderr, "Grabbing client key from socket...\n");
    if(deserialize_mpz(client_ephemeral.PK,sockfd)!=0)
        error("ERROR receiving server's ephemeral key");

    dhFinal(server_ephemeral.SK,server_ephemeral.PK,client_ephemeral.PK,clientDH,128);

    return 0;
}

static int initClientNet(char* hostname, int port)
{
    unsigned char client[128];

    /* Client's key: */
    initKey(&client_ephemeral);
	dhGenk(&client_ephemeral);
	
	struct sockaddr_in serv_addr;
	sockfd = socket(AF_INET, SOCK_STREAM, 0);
	struct hostent *server;
	if (sockfd < 0)
		error("ERROR opening socket");
	server = gethostbyname(hostname);
	if (server == NULL) {
		fprintf(stderr,"ERROR, no such host\n");
		exit(0);
	}
	bzero((char *) &serv_addr, sizeof(serv_addr));
	serv_addr.sin_family = AF_INET;
	memcpy(&serv_addr.sin_addr.s_addr,server->h_addr,server->h_length);
	serv_addr.sin_port = htons(port);
	if (connect(sockfd,(struct sockaddr *) &serv_addr,sizeof(serv_addr)) < 0)
		error("ERROR connecting");

	/* at this point, should be able to send/recv on sockfd */
	sleep(2);
	
	fprintf(stderr, "Sending client key to the socket...\n");
    if (serialize_mpz(sockfd,client_ephemeral.PK)==0)
        error("ERROR sending server ephemeral key");
	return 0;
}

static int shutdownNetwork()
{
	shutdown(sockfd,2);
	unsigned char dummy[64];
	ssize_t r;
	do {
		r = recv(sockfd,dummy,64,0);
	} while (r != 0 && r != -1);
	close(sockfd);
	return 0;
}

/* end network stuff. */

static const char* usage =
"Usage: %s [OPTIONS]...\n"
"Secure chat (CCNY computer security project).\n\n"
"   -c, --connect HOST  Attempt a connection to HOST.\n"
"   -l, --listen        Listen for new connections.\n"
"   -p, --port    PORT  Listen or connect on PORT (defaults to 1337).\n"
"   -h, --help          show this message and exit.\n";

/* Append message to transcript with optional styling.  NOTE: tagnames, if not
 * NULL, must have it's last pointer be NULL to denote its end.  We also require
 * that messsage is a NULL terminated string.  If ensurenewline is non-zero, then
 * a newline may be added at the end of the string (possibly overwriting the \0
 * char!) and the view will be scrolled to ensure the added line is visible.  */
static void tsappend(char* message, char** tagnames, int ensurenewline)
{
	GtkTextIter t0;
	gtk_text_buffer_get_end_iter(tbuf,&t0);
	size_t len = g_utf8_strlen(message,-1);
	if (ensurenewline && message[len-1] != '\n')
		message[len++] = '\n';
	gtk_text_buffer_insert(tbuf,&t0,message,len);
	GtkTextIter t1;
	gtk_text_buffer_get_end_iter(tbuf,&t1);
	/* Insertion of text may have invalidated t0, so recompute: */
	t0 = t1;
	gtk_text_iter_backward_chars(&t0,len);
	if (tagnames) {
		char** tag = tagnames;
		while (*tag) {
			gtk_text_buffer_apply_tag_by_name(tbuf,*tag,&t0,&t1);
			tag++;
		}
	}
	if (!ensurenewline) return;
	gtk_text_buffer_add_mark(tbuf,mark,&t1);
	gtk_text_view_scroll_to_mark(tview,mark,0.0,0,0.0,0.0);
	gtk_text_buffer_delete_mark(tbuf,mark);
}

static void sendMessage(GtkWidget* w /* <-- msg entry widget */, gpointer /* data */)
{
	char* tags[2] = {"self",NULL};
	tsappend("me: ",tags,0);
	GtkTextIter mstart; /* start of message pointer */
	GtkTextIter mend;   /* end of message pointer */
	gtk_text_buffer_get_start_iter(mbuf,&mstart);
	gtk_text_buffer_get_end_iter(mbuf,&mend);
	char* message = gtk_text_buffer_get_text(mbuf,&mstart,&mend,1);
	size_t len = g_utf8_strlen(message,-1);
	/* XXX we should probably do the actual network stuff in a different
	 * thread and have it call this once the message is actually sent. */
	ssize_t nbytes;
	
	if ((nbytes = send(sockfd,message,len,0)) == -1)
		error("send failed");

	tsappend(message,NULL,1);
	free(message);
	/* clear message text and reset focus */
	gtk_text_buffer_delete(mbuf,&mstart,&mend);
	gtk_widget_grab_focus(w);
}

static gboolean shownewmessage(gpointer msg)
{
	char* tags[2] = {"friend",NULL};
	char* friendname = "mr. friend: ";
	tsappend(friendname,tags,0);
	char* message = (char*)msg;
	tsappend(message,NULL,1);
	free(message);
	return 0;
}

int main(int argc, char *argv[])
{

	if (init("params") != 0) {
		fprintf(stderr, "could not read DH params from file 'params'\n");
		return 1;
	}
	// define long options

	static struct option long_opts[] = {
		{"connect",  required_argument, 0, 'c'},
		{"listen",   no_argument,       0, 'l'},
		{"port",     required_argument, 0, 'p'},
		{"help",     no_argument,       0, 'h'},
		{0,0,0,0}
	};
	// process options:
	char c;
	int opt_index = 0;
	int port = 1337;
	char hostname[HOST_NAME_MAX+1] = "localhost";
	hostname[HOST_NAME_MAX] = 0;
	char xMessage = NULL;
	char mMsg = NULL;
	const size_t keylength = 128;
    unsigned char prvKeyS[keylength];
	unsigned char mainDH[keylength];

	while ((c = getopt_long(argc, argv, "c:lp:h", long_opts, &opt_index)) != -1) {
		switch (c) {
			case 'c':
				if (strnlen(optarg,HOST_NAME_MAX))
					strncpy(hostname,optarg,HOST_NAME_MAX);
				break;
			case 'l':
				isclient = 0;
				break;
			case 'p':
				port = atoi(optarg);
				break;
			case 'h':
				printf(usage,argv[0]);
				return 0;
			case '?':
				printf(usage,argv[0]);
				return 1;
		}
	}

	/* setup GTK... */
	GtkBuilder* builder;
	GObject* window;
	GObject* button;
	GObject* transcript;
	GObject* message;
	GError* error = NULL;
	gtk_init(&argc, &argv);

	if (isclient) {
        printf("\nClient init started\n~~~~~~~~~~~~~~~~~~~~~~~\n");
        initClientNet(hostname,port);

        if(deserialize_mpz(server_ephemeral.PK,sockfd)!=0)
                fprintf(stderr,"\nERROR receiving server's ephemeral key\n");

        dhFinal(client_ephemeral.SK,client_ephemeral.PK,server_ephemeral.PK,clientDH,128);  

        memcpy(prvKeyS,clientDH,128);

        xwrite(sockfd, clientDH, keylength);
        
                for (size_t i = 0; i < 128; i++) {
            printf("%02x ",clientDH[i]);
            }

    printf("\nClient init complete\n~~~~~~~~~~~~~~~~~~~~~~~\n");
     }
    else {
        printf("\nServer init started\n~~~~~~~~~~~~~~~~~~~~~~~\n");
        initServerNet(port);
        if (serialize_mpz(sockfd,server_ephemeral.PK)==0)
                fprintf(stderr,"\nERROR sending server ephemeral key\n");

        xread(sockfd, clientDH, keylength);

        memcpy(prvKeyS,serverDH,128);

                for (size_t i = 0; i < 128; i++) {
            printf("%02x ",serverDH[i]);
            }

        printf("\nServer init complete\n~~~~~~~~~~~~~~~~~~~~~~~\n");
    }


	builder = gtk_builder_new();
	if (gtk_builder_add_from_file(builder,"layout.ui",&error) == 0) {
		g_printerr("Error reading %s\n", error->message);
		g_clear_error(&error);
		return 1;
	}

	mark = gtk_text_mark_new(NULL,TRUE);
	window = gtk_builder_get_object(builder,"window");
	g_signal_connect(window, "destroy", G_CALLBACK(gtk_main_quit), NULL);
	transcript = gtk_builder_get_object(builder, "transcript");
	tview = GTK_TEXT_VIEW(transcript);
	message = gtk_builder_get_object(builder, "message");
	tbuf = gtk_text_view_get_buffer(tview);
	mbuf = gtk_text_view_get_buffer(GTK_TEXT_VIEW(message));
	memcpy(xMessage,encryptMe((char *)message),strlen(message));
	cylen = strlen(xMessage);
	memcpy(mMsg,hmac(prvKeyS,(char*)xMessage),strlen(hmac(prvKeyS,(char*)xMessage)));
	button = gtk_builder_get_object(builder, "send");
	g_signal_connect_swapped(button, "clicked", G_CALLBACK(sendMessage), GTK_WIDGET(mMsg));
	gtk_widget_grab_focus(GTK_WIDGET(message));
	GtkCssProvider* css = gtk_css_provider_new();
	gtk_css_provider_load_from_path(css,"colors.css",NULL);
	gtk_style_context_add_provider_for_screen(gdk_screen_get_default(),
			GTK_STYLE_PROVIDER(css),
			GTK_STYLE_PROVIDER_PRIORITY_USER);

	/* setup styling tags for transcript text buffer */
	gtk_text_buffer_create_tag(tbuf,"status","foreground","#657b83","font","italic",NULL);
	gtk_text_buffer_create_tag(tbuf,"friend","foreground","#6c71c4","font","bold",NULL);
	gtk_text_buffer_create_tag(tbuf,"self","foreground","#268bd2","font","bold",NULL);

	/* start receiver thread: */
	if (pthread_create(&trecv,0,recvMsg,0)) {
		fprintf(stderr, "Failed to create update thread.\n");
	}

	gtk_main();

	shutdownNetwork();
	return 0;
}

/* thread function to listen for new messages and post them to the gtk
 * main loop for processing: */
void recvMsg()
{
	size_t maxlen = 1024;
	char msg[maxlen+2]; /* might add \n and \0 */
	char plaintxt, msgWmac[cylen];
	int i;
	ssize_t nbytes;
	while (1) {

		if ((nbytes = recv(sockfd,msg,maxlen,0)) == -1)
			error("recv failed");
		if (nbytes == 0) {
			/* XXX maybe show in a status message that the other
			 * side has disconnected. */
			error("other side disconnected");
		}
		for(i=0; i < cylen; i++) msgWmac[i] = msg [i];

		plaintxt = decryptMe((char *) msgWmac);
		char* m = malloc(maxlen+2);
		memcpy(m,plaintxt,nbytes);
		if (m[nbytes-1] != '\n')
			m[nbytes++] = '\n';
		m[nbytes] = 0;
		g_main_context_invoke(NULL,shownewmessage,(gpointer)m);
	}
}

char decryptMe(char ct){
		//decrypt
		size_t i;
		EVP_CIPHER_CTX* ctx = EVP_CIPHER_CTX_new();
		unsigned char iv[16];
		int nWritten; 
		char pt[1024];
		for (i = 0; i < 16; i++) iv[i] = i;
		size_t len = strlen(ct);

		memset(pt,0,1024);
		ctx = EVP_CIPHER_CTX_new();
		if (1!=EVP_DecryptInit_ex(ctx,EVP_aes_256_ctr(),0,encKey,iv))
			ERR_print_errors_fp(stderr);

		for (size_t i = 0; i < len; i++) {
			if (1!=EVP_DecryptUpdate(ctx,pt+i,&nWritten,ct+i,1))
				ERR_print_errors_fp(stderr);
		}
		EVP_CIPHER_CTX_free(ctx);
		return pt;
}

char encryptMe(char msg){
	/*define random encryption key*/
	srand(time(NULL));
	int i, index;
	for (i = 0; i < 32; i++) {
	index = rand() % 62;
	encKey[i] = random_char(index);
	}
	encKey[i] = '\0';
	unsigned char iv[16];
	for (i = 0; i < 16; i++) iv[i] = i;
	/* NOTE: in general you need t compute the sizes of these
	 * buffers.  512 is an arbitrary value larger than what we
	 * will need for our short message. */
	unsigned char ct[1024];

	/* so you can see which bytes were written: */
	memset(ct,0,1024);
	
	size_t msglen = strlen(msg);
	/* encrypt: */
	EVP_CIPHER_CTX* ctx = EVP_CIPHER_CTX_new();
	if (1!=EVP_EncryptInit_ex(ctx,EVP_aes_256_ctr(),0,encKey,iv))
		ERR_print_errors_fp(stderr);
	int nWritten; /* stores number of written bytes (size of ciphertext) */
	if (1!=EVP_EncryptUpdate(ctx,ct,&nWritten,(unsigned char*)msg,msglen))
		ERR_print_errors_fp(stderr);
	EVP_CIPHER_CTX_free(ctx);
	//size_t ctlen = nWritten;
	return ct;
}

unsigned char hmac(unsigned char dhKey, char msg)
{
	unsigned char mac[64]; /* if using sha512 */
	memset(mac,0,64);
	HMAC(EVP_sha512(),dhKey,strlen(dhKey),(unsigned char*)msg,
			strlen(msg),mac,0);
	return mac;
}

char random_char(int index) {
	char charset[] = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";
	return charset[index];
}