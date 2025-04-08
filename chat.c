#include <gtk/gtk.h>
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

#include <openssl/rand.h> /* for generating random IVs */
#include <openssl/err.h>  /* for error handling */
#include <unistd.h> /* deleting mykey files */

#ifndef PATH_MAX
#define PATH_MAX 1024
#endif

static GtkTextBuffer* tbuf; /* transcript buffer */
static GtkTextBuffer* mbuf; /* message buffer */
static GtkTextView*  tview; /* view for transcript */
static GtkTextMark*   mark; /* used for scrolling to end of transcript, etc */

static pthread_t trecv;     /* wait for incoming messagess and post to queue */
void* recvMsg(void*);       /* for trecv */

#define max(a, b)         \
	({ typeof(a) _a = a;    \
	 typeof(b) _b = b;    \
	 _a > _b ? _a : _b; })

/* network stuff... */

static int listensock, sockfd;
static int isclient = 1;

static dhKey longTermKey;
static dhKey ephemeralKey;

// Shared session key -3dh 128 bytes
static unsigned char sessionKey[128];

static unsigned char encKey[32];
static unsigned char macKey[64];
static unsigned char counterKey[32];

// Ctr replay protection - need for both send and receive
static uint32_t sendCounter = 0;
static uint32_t recvCounter = 0;

// Track handshake status
static int handshakeComplete = 0;

static void deleteKeyFiles(void) {
	if (access("mykey", F_OK) == 0) unlink("mykey");
	if (access("mykey.pub", F_OK) == 0) unlink("mykey.pub");
}

static void error(const char *msg)
{
	perror(msg);
	exit(EXIT_FAILURE);
}

// OpenSSL error handling , just print and abort -- shows crypto errors
static void handleErrors(void)
{
    ERR_print_errors_fp(stderr);
    abort();
}

// From session key, derive encryption and mac keys
static void deriveKeys(void)
{
    // sessionKey has 128 bytes from 3DH
    // Divide it into separate keys for different purposes
    
    // First 32 bytes (256 bits) for AES-256 encryption
    memcpy(encKey, sessionKey, 32);
    
    // Next 64 bytes (512 bits) for HMAC-SHA512
    memcpy(macKey, sessionKey + 32, 64);
    
    // Last 32 bytes for generating IVs
    memcpy(counterKey, sessionKey + 96, 32);
    
    // debugging, printing first few byets each key
    fprintf(stderr, "Key derivation complete:\n");
    fprintf(stderr, "  Encryption key: %02x%02x%02x...%02x%02x%02x\n", 
            encKey[0], encKey[1], encKey[2], encKey[29], encKey[30], encKey[31]);
    fprintf(stderr, "  MAC key: %02x%02x%02x...%02x%02x%02x\n", 
            macKey[0], macKey[1], macKey[2], macKey[61], macKey[62], macKey[63]);
    fprintf(stderr, "  Counter key: %02x%02x%02x...%02x%02x%02x\n", 
            counterKey[0], counterKey[1], counterKey[2], counterKey[29], counterKey[30], counterKey[31]);
}

// Encrypt message using AES-256-CTR
// Format: [IV (16 bytes)][Encrypted Message]
// function to return total len formatted message
static int encryptMessage(unsigned char *plaintext, int plaintext_len, unsigned char *output)
{
    EVP_CIPHER_CTX *ctx;
    int len;
    int ciphertext_len;
    unsigned char iv[16];
    
    // Generate random IV
    if(1 != RAND_bytes(iv, 16)) 
        handleErrors();
    
    // Copy IV to output buffer
    memcpy(output, iv, 16);
    
    // Create and init context
    ctx = EVP_CIPHER_CTX_new();
    if (!ctx) 
        handleErrors();

    // 1. EVP_EncryptInit_ex: Initializes the encryption context with AES-256-CTR, the encryption key, and IV
    // 2. EVP_EncryptUpdate: Processes plaintext and produces ciphertext (called multiple times for large messages)
    // 3. EVP_EncryptFinal_ex: Finalizes the encryption process, handling any remaining data
    
    // Init encryption operation with AES-256-CTR
    // EVP_EncryptInit_ex(ctx,EVP_aes_256_ctr(),0,key,iv)
    if(1 != EVP_EncryptInit_ex(ctx, EVP_aes_256_ctr(), NULL, encKey, iv))
        handleErrors();
    
    // Encrypt the message
    // EVP_EncryptUpdate(ctx,ct,&nWritten,(unsigned char*)message,len)
    if(1 != EVP_EncryptUpdate(ctx, output + 16, &len, plaintext, plaintext_len))
        handleErrors();
    ciphertext_len = len;
    

    if(1 != EVP_EncryptFinal_ex(ctx, output + 16 + len, &len))
        handleErrors();
    ciphertext_len += len;
    
    // free context
    EVP_CIPHER_CTX_free(ctx);
    
	// IV (16 bytes) + ciphertext
    return ciphertext_len + 16;
}

// Function calculates an HMAC using SHA-512.
// The function takes the data, len, and buffer to store the HMAC.
// Returns the length of the HMAC (should be 64 bytes for SHA512)

static int calculateHMAC(unsigned char *data, int data_len, unsigned char *hmac)
{
    unsigned int hmac_len;
    
    // Initialize HMAC buffer
    memset(hmac, 0, 64); 
    
    // Calculate HMAC using SHA-512 and the MAC key
    HMAC(EVP_sha512(), macKey, 64, data, data_len, hmac, &hmac_len);
    
    // debug
    // fprintf(stderr, "Calculated HMAC of length %d for %d bytes of data\n", hmac_len, data_len);
    
	return hmac_len;
}


// 1. verifyHMAC: Takes received data and its HMAC, calculates the expected HMAC, and compares them.
// Returns 1 if match (message good), 0 if they don't (message bad).

// 2. decryptMessage: Decrypts a message using AES-256-CTR. Takes the encrypted data (including IV) and
// spits out decrypted plaintext. same as encryption process
// Verify HMAC for the given data
// Returns 1 if HMAC is valid, 0 otherwise

static int verifyHMAC(unsigned char *data, int data_len,
                     unsigned char *received_hmac, int hmac_len)
{
    unsigned char calculated_hmac[64]; // SHA-512 produces 64 byte output
    unsigned int calc_len;

    memset(calculated_hmac, 0, 64);
    
    // Calculate HMAC for the received data using the same key

    HMAC(EVP_sha512(), macKey, 64, data, data_len, calculated_hmac, &calc_len);
    
    // debug: Print first few bytes
    fprintf(stderr, "HMAC debug:\n");
    fprintf(stderr, "  First bytes of calculated: %02x %02x %02x %02x\n", 
            calculated_hmac[0], calculated_hmac[1], calculated_hmac[2], calculated_hmac[3]);
    fprintf(stderr, "  First bytes of received: %02x %02x %02x %02x\n", 
            received_hmac[0], received_hmac[1], received_hmac[2], received_hmac[3]);
    

    if(calc_len != hmac_len) {
        fprintf(stderr, "HMAC length mismatch: calculated=%d, received=%d\n", calc_len, hmac_len);
        return 0;
    }
    

    if(CRYPTO_memcmp(calculated_hmac, received_hmac, calc_len) != 0) {
        fprintf(stderr, "HMAC verification failed!\n");
        return 0;
    }
    
    fprintf(stderr, "HMAC verified successfully\n");
    return 1;
}

// Decrypt a message using AES-256-CTR
// given [IV (16 bytes)][Encrypted Message]
// returns the length of the decrypted plaintext
static int decryptMessage(unsigned char *input, int input_len,
                         unsigned char *output)
{
    EVP_CIPHER_CTX *ctx;
    int len;
    int plaintext_len;
    unsigned char *iv = input; // First 16 bytes are the IV
    
    // Ensure we have at least an IV
    if(input_len <= 16)
        return -1;
    
    // Create and initialize the context
    ctx = EVP_CIPHER_CTX_new();
    if (!ctx)
        handleErrors();
    
    // Initialize decryption operation with AES-256-CTR

    if(1 != EVP_DecryptInit_ex(ctx, EVP_aes_256_ctr(), NULL, encKey, iv))
        handleErrors();
    
    // decrypt ciphertext
    if(1 != EVP_DecryptUpdate(ctx, output, &len, input + 16, input_len - 16))
        handleErrors();
    plaintext_len = len;
    

    if(1 != EVP_DecryptFinal_ex(ctx, output + len, &len))
        handleErrors();
    plaintext_len += len;
    
    EVP_CIPHER_CTX_free(ctx);

    return plaintext_len;
}

static int performHandshake(int isClient) {
	// Init keys
	if (initKey(&longTermKey) != 0 || initKey(&ephemeralKey) != 0) {
		fprintf(stderr, "Failed to initialize keys\n");
		return -1;
	}

	// Generate long-term key pair if we don't have one
	if (access("mykey.pub", F_OK) != 0) {
		// Generate new long-term key
		dhGen(longTermKey.SK, longTermKey.PK);
		strncpy(longTermKey.name, "mychat", MAX_NAME);
		// write long term to file
		writeDH("mykey", &longTermKey);
		fprintf(stderr, "Generated new long-term key\n");
	} else {
		// have long-trem key just load existing
		readDH("mykey", &longTermKey);
		fprintf(stderr, "Loaded existing long-term key\n");
	}

	// Generate ephemeral key pair for this session (pfs)
	dhGen(ephemeralKey.SK, ephemeralKey.PK);
	strncpy(ephemeralKey.name, "ephemeral", MAX_NAME);
	fprintf(stderr, "Generated ephemeral key\n");

	// replay protection ctr
	sendCounter = 0;
	recvCounter = 0;


	// Exchange keys based on role
	if (isClient) {
		fprintf(stderr, "Client: Doing 3dh handshake...\n");
		
		// Client sends its keys first
		fprintf(stderr, "Client: Sending public keys\n");
		serialize_mpz(sockfd, longTermKey.PK);
		serialize_mpz(sockfd, ephemeralKey.PK);
		
		// Receive server's keys
		fprintf(stderr, "Client: Receiving server public keys\n");
		dhKey serverLongTermKey, serverEphemeralKey;
		initKey(&serverLongTermKey);
		initKey(&serverEphemeralKey);
		
		// Deserialize the server's public keys from the socket
		deserialize_mpz(serverLongTermKey.PK, sockfd);
		deserialize_mpz(serverEphemeralKey.PK, sockfd);
		
		// 32 bytes * 2 chars per byte + null terminator
		char hashBuffer[65]; 

		// hash the server's long-term public key and print the hash for verification.
		// basically client can check they connect to correct server by comparing hash
		// with prev known val

		hashPK(&serverLongTermKey, hashBuffer);
		fprintf(stderr, "Server long term key hash: %s\n", hashBuffer);

		// Generate session using 3dh
		fprintf(stderr, "Client: Doing 3dh key derivation...\n");
		
		// long term key(auth) , ephemeral key(pfs) , server long term key(auth) , server ephemeral key , session key , size of session key
		dh3Finalk(&longTermKey, &ephemeralKey, &serverLongTermKey, &serverEphemeralKey, sessionKey, sizeof(sessionKey));
		
		shredKey(&serverLongTermKey);
		shredKey(&serverEphemeralKey);
	} else {
		fprintf(stderr, "Server: Doing 3dh handshake...\n");
		
		// Server receives client's keys first
		fprintf(stderr, "Server: Receiving client public keys\n");
		dhKey clientLongTermKey, clientEphemeralKey;
		initKey(&clientLongTermKey);
		initKey(&clientEphemeralKey);
		
		deserialize_mpz(clientLongTermKey.PK, sockfd);
		deserialize_mpz(clientEphemeralKey.PK, sockfd);
		
		// same logic as client just do client long term key
		char hashBuffer[65]; 
		hashPK(&clientLongTermKey, hashBuffer);
		fprintf(stderr, "Client long term key hash: %s\n", hashBuffer);

		// Send server's keys
		fprintf(stderr, "Server: Sending server public keys\n");
		serialize_mpz(sockfd, longTermKey.PK);
		serialize_mpz(sockfd, ephemeralKey.PK);
		
		// Generate session using 3dh
		fprintf(stderr, "Server: Doing 3dh key derivation...\n");
		dh3Finalk(&longTermKey, &ephemeralKey, &clientLongTermKey, &clientEphemeralKey, sessionKey, sizeof(sessionKey));
		
		shredKey(&clientLongTermKey);
		shredKey(&clientEphemeralKey);
	}

	// handshake done so get encryption and mac keys
	deriveKeys();

	handshakeComplete = 1;
	
	// Checking if session key was generated

	int nonzero = 0;
	for (int i = 0; i < sizeof(sessionKey); i++) {
		if (sessionKey[i] != 0) {
			nonzero = 1;
			break;
		}
	}

	if (!nonzero) {
		fprintf(stderr, "Handshake failed: Session key not generated\n");
		return -1;
	}

	return 0;
}

int initServerNet(int port)
{
	int reuse = 1;
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
	if (performHandshake(0) != 0) {
		error("Handshake failed");
		return -1;
	}
	fprintf(stderr, "Handshake completed successfully\n");
	return 0;
}

static int initClientNet(char* hostname, int port)
{
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
	if (performHandshake(1) != 0) {
		error("Handshake failed");
		return -1;
	}
	fprintf(stderr, "Handshake completed successfully\n");
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
	if (!handshakeComplete) {
		tsappend("Error: Handshake not complete\n", NULL, 1);
		return;
	}

	char* tags[2] = {"self",NULL};
	tsappend("me: ",tags,0);

	GtkTextIter mstart; /* start of message pointer */
	GtkTextIter mend;   /* end of message pointer */
	gtk_text_buffer_get_start_iter(mbuf,&mstart);
	gtk_text_buffer_get_end_iter(mbuf,&mend);
	char* message = gtk_text_buffer_get_text(mbuf,&mstart,&mend,1);
	size_t len = g_utf8_strlen(message,-1);

	// prepare plaintext with msg cntr for replay protection
	// [Counter (4 bytes)][Original Message]
	unsigned char* plaintext = malloc(len + 4);
	if (!plaintext) {
		tsappend("Error: Memory allocation failed\n", NULL, 1);
		free(message);
		return;
	}

	// Add counter at start of plaintext
	uint32_t counter_n = htonl(sendCounter++);
	memcpy(plaintext, &counter_n, 4);
	memcpy(plaintext + 4, message, len);

	// Encrypt : [IV][Encrypted (Counter|Message)]
	// Buffer Size : 16 (IV) + plaintext (len + 4) + potential padding (16)
	// need +4 for 4 byte ctr we prepend to each message
	unsigned char* encrypted = malloc(16 + len + 4 + 16);

	if (!encrypted) {
		tsappend("Error: Memory allocation failed\n", NULL, 1);
		free(message);
		free(plaintext);
		return;
	}

	// Encrypt plaintext
	int encrypted_len = encryptMessage(plaintext, len + 4, encrypted);
	if (encrypted_len <= 0) {
		tsappend("Error: Encryption failed\n", NULL, 1);
		free(message);
		free(plaintext);
		free(encrypted);
		return;
	}

	// MAC for encrypted message
	unsigned char mac[64]; // SHA-512 output size
	int mac_len = calculateHMAC(encrypted, encrypted_len, mac);

	// Final message
	// [Length (4 bytes)][Encrypted Data][MAC]
	uint32_t total_len = encrypted_len + mac_len;
	uint32_t total_len_n = htonl(total_len);

	// Buffer for complete message
	// [Length (4 bytes)][Encrypted Data with IV][MAC (64 bytes)]
	unsigned char* full_message = malloc(4 + total_len);
	if (!full_message) {
		tsappend("Error: Memory allocation failed\n", NULL, 1);
		free(message);
		free(plaintext);
		free(encrypted);
		return;
	}

	// Put together final message (length + encrypted + mac)
	memcpy(full_message, &total_len_n, 4);
	memcpy(full_message + 4, encrypted, encrypted_len);
	memcpy(full_message + 4 + encrypted_len, mac, mac_len);

	// Send message
	ssize_t nbytes;
	if ((nbytes = send(sockfd, full_message, 4 + total_len, 0)) == -1) {
		free(message);
		free(plaintext);
		free(encrypted);
		free(full_message);
		error("send failed");
	}

	tsappend(message, NULL, 1);

	free(message);
	free(plaintext);
	free(encrypted);
	free(full_message);

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
	deleteKeyFiles();
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
	/* NOTE: might want to start this after gtk is initialized so you can
	 * show the messages in the main window instead of stderr/stdout.  If
	 * you decide to give that a try, this might be of use:
	 * https://docs.gtk.org/gtk4/func.is_initialized.html */
	if (isclient) {
		initClientNet(hostname,port);
	} else {
		initServerNet(port);
	}

	/* setup GTK... */
	GtkBuilder* builder;
	GObject* window;
	GObject* button;
	GObject* transcript;
	GObject* message;
	GError* error = NULL;
	gtk_init(&argc, &argv);
	builder = gtk_builder_new();
	if (gtk_builder_add_from_file(builder,"layout.ui",&error) == 0) {
		g_printerr("Error reading %s\n", error->message);
		g_clear_error(&error);
		return 1;
	}
	mark  = gtk_text_mark_new(NULL,TRUE);
	window = gtk_builder_get_object(builder,"window");
	g_signal_connect(window, "destroy", G_CALLBACK(gtk_main_quit), NULL);
	transcript = gtk_builder_get_object(builder, "transcript");
	tview = GTK_TEXT_VIEW(transcript);
	message = gtk_builder_get_object(builder, "message");
	tbuf = gtk_text_view_get_buffer(tview);
	mbuf = gtk_text_view_get_buffer(GTK_TEXT_VIEW(message));
	button = gtk_builder_get_object(builder, "send");
	g_signal_connect_swapped(button, "clicked", G_CALLBACK(sendMessage), GTK_WIDGET(message));
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

// Forward declaration for status message function bc showStatusMessage in recvMsg but defined later

static gboolean showStatusMessage(gpointer msg);

/* thread function to listen for new messages and post them to the gtk
 * main loop for processing: */
void* recvMsg(void*)
{
	// this works
	size_t maxlen = 4096;
	
	unsigned char buffer[maxlen]; 
	unsigned char length_buffer[4]; // For reading message length
	
	ssize_t nbytes;
	// while (1) {
	// 	if ((nbytes = recv(sockfd,msg,maxlen,0)) == -1)
	// 		error("recv failed");
	// 	if (nbytes == 0) {
	// 		/* XXX maybe show in a status message that the other
	// 		 * side has disconnected. */
	// 		tsappend("Other side disconnected\n", NULL, 1);
	// 		return 0;
	// 	}
	// 	char* m = malloc(maxlen+2);
	// 	memcpy(m,msg,nbytes);
	// 	if (m[nbytes-1] != '\n')
	// 		m[nbytes++] = '\n';
	// 	m[nbytes] = 0;
	// 	g_main_context_invoke(NULL,shownewmessage,(gpointer)m);
	// }
	// return 0;
	while (1) {
		// Step 1: Read the message length (4 bytes)
		if ((nbytes = recv(sockfd, length_buffer, 4, 0)) <= 0) {
			if (nbytes == 0) {
				// Connection closed
				char* disconnect_msg = strdup("The other user has disconnected.");
				g_main_context_invoke(NULL, showStatusMessage, (gpointer)disconnect_msg);
				return 0;
			} else {
				// Error
				error("recv failed on length");
			}
		}
		
		// Convert network byte order to host byte order
		uint32_t message_length = ntohl(*(uint32_t*)length_buffer);
		
		if (message_length > maxlen) {
			char buffer[100];
			snprintf(buffer, sizeof(buffer), "Error: Received implausible message length: %u", message_length);
			char* error_msg = strdup(buffer);
			g_main_context_invoke(NULL, showStatusMessage, (gpointer)error_msg);
			continue;
		}
		
		// Step 2: Read encyrpted message + MAC
		size_t bytes_read = 0;
		while (bytes_read < message_length) {
			nbytes = recv(sockfd, buffer + bytes_read, message_length - bytes_read, 0);
			if (nbytes <= 0) {
				if (nbytes == 0) {
					// Connection closed
					char* disconnect_msg = strdup("The other user disconnected unexpectedly.");
					g_main_context_invoke(NULL, showStatusMessage, (gpointer)disconnect_msg);
					return 0;
				} else {
					// Error
					error("recv failed on message body");
				}
			}
			bytes_read += nbytes;
		}
		
		// Split the received data into encrypted message and MAC
		// The last 64 bytes are the MAC (SHA-512 output size)
		if (message_length <= 64) {
			char* error_msg = strdup("Error: Received message too short to contain MAC");
			g_main_context_invoke(NULL, showStatusMessage, (gpointer)error_msg);
			continue;
		}
		
		unsigned char* encrypted_data = buffer;
		size_t encrypted_len = message_length - 64;
		unsigned char* received_mac = buffer + encrypted_len;
		
		// Step 3: Verify MAC before decryption
		if (!verifyHMAC(encrypted_data, encrypted_len, received_mac, 64)) {
			char* error_msg = strdup("Error: Message authentication failed (MAC invalid)");
			g_main_context_invoke(NULL, showStatusMessage, (gpointer)error_msg);
			continue;
		}
		
		// Step 4: Decrypt
		unsigned char plaintext[maxlen];
		int plaintext_len = decryptMessage(encrypted_data, encrypted_len, plaintext);
		
		if (plaintext_len <= 0) {
			char* error_msg = strdup("Error: Message decryption failed");
			g_main_context_invoke(NULL, showStatusMessage, (gpointer)error_msg);
			continue;
		}
		
		// Step 5: Check counter (first 4 bytes of plaintext)
		if (plaintext_len <= 4) {
			char* error_msg = strdup("Error: Decrypted message too short");
			g_main_context_invoke(NULL, showStatusMessage, (gpointer)error_msg);
			continue;
		}
		
		uint32_t received_counter = ntohl(*(uint32_t*)plaintext);
		
		// Out of order msg check / replay attack check
		if (received_counter < recvCounter) {
			char buffer[100];
			snprintf(buffer, sizeof(buffer), 
				"Warning: Possible replay attack detected (counter=%u, expected>=%u)", 
				received_counter, recvCounter);
			char* warning_msg = strdup(buffer);
			g_main_context_invoke(NULL, showStatusMessage, (gpointer)warning_msg);
			continue;
		}
		
		recvCounter = received_counter + 1;
		
		// Step 6: Get the ACTUAL MESSAGE (everything after the counter)
		unsigned char* actual_message = plaintext + 4;
		int actual_len = plaintext_len - 4;
		
		char* m = malloc(actual_len + 2); // +2 for newline and null terminator
		if (!m) {
			char* error_msg = strdup("Error: Memory allocation failed");
			g_main_context_invoke(NULL, showStatusMessage, (gpointer)error_msg);
			continue;
		}
		
		memcpy(m, actual_message, actual_len);
		
		// End with newline and null terminator check
		if (actual_len > 0 && m[actual_len-1] != '\n') {
			m[actual_len++] = '\n';
		}
		m[actual_len] = 0;
		
		g_main_context_invoke(NULL, shownewmessage, (gpointer)m);
	}
	return 0;
}

static gboolean showStatusMessage(gpointer msg)
{
	char* message = (char*)msg;
	char* tags[2] = {"status", NULL};
	tsappend(message, tags, 1);
	free(message);
	return 0;
}