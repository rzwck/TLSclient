import sys, struct, time, hmac, hashlib, math, random, binascii
from Crypto.Cipher import AES
from Crypto.Util.asn1 import DerSequence
from Crypto.PublicKey import RSA
from Crypto.Cipher import ARC4
from socket import *

TLS_VERSION = "\x03\x01"  
CIPHER_DHE_RSA_AES128_SHA = "\x00\x33"
CIPHER_AES128_SHA = "\x00\x2F"
CIPHER_RC4_SHA =  "\x00\x05"

""" ################################# BEGIN Classes Definition ################################# """
class RandomNonce(object):	
	def __init__(self):		
		self.server_random = None
		self.client_random = None

class SequenceNumber(object):	
	def __init__(self):		
		self.server = 0
		self.client = 0

class SessionKeys(object):
	def __init__(self):
		self.client_write_MAC_secret = None
		self.server_write_MAC_secret = None
		self.client_write_key = None
		self.server_write_key = None
		self.client_write_IV = None
		self.server_write_IV = None
		self.server_pubkey = None
		self.master = None
		self.client_rc4 = None
		self.server_rc4 = None

	def expand(self, premaster, nonce):
		# Calculate master secret
		self.master = PRF(premaster, "master secret", nonce.client_random+nonce.server_random, 48)

		# Calculate keys, MAC secret and IV
		outputLength = 20*2 + 16*2 + 16*2; # MAC size 20 + Key size 16 + IV size 16
		keyBlock = PRF(self.master,"key expansion",nonce.server_random + nonce.client_random, outputLength)

		self.client_write_MAC_secret = keyBlock[0:20]
		self.server_write_MAC_secret = keyBlock[20:40]
		self.client_write_key = keyBlock[40:56]
		self.server_write_key = keyBlock[56:72]
		self.client_write_IV = keyBlock[72:88]
		self.server_write_IV = keyBlock[88:104]
		return self

class DHParams(object):
	def __init__(self):
		self.p = None
		self.g = None
		self.Ys = None
		self.Yc = None
		self.Xc = None
		self.premaster = None

	def generate_premaster(self):
		self.premaster = numtostr(pow(self.Ys, self.Xc, self.p))
		return self.premaster

class HandshakeHash(object):
	def __init__(self):
		self.sha1 = hashlib.sha1()
		self.md5 = hashlib.md5()

""" ################################# END Classes Definition ################################# """

""" ################################# BEGIN Key Derivation Functions ################################# """
def P_SHA1(secret, seed, length):
	A = seed
	p = ""
	while len(p) <= length:
		A = hmac.HMAC(secret, A, hashlib.sha1).digest()
		p += hmac.HMAC(secret, A+seed, hashlib.sha1).digest()

	return p[0:length]

def P_MD5(secret, seed, length):
	A = seed
	p = ""
	while len(p) <= length:
		A = hmac.HMAC(secret, A, hashlib.md5).digest()
		p += hmac.HMAC(secret, A+seed, hashlib.md5).digest()

	return p[0:length]

def PRF(secret, label, seed, length):
	mid = int(math.ceil(len(secret)/2.0))	
	S1 = secret[ : mid ]
	S2 = secret[ mid : ]

	pmd5 = P_MD5(S1, label+seed, length)
	psha1 = P_SHA1(S2, label+seed, length)
	return ''.join(chr(ord(a) ^ ord(b)) for a,b in zip(pmd5,psha1))

""" ################################# END Key Derivation Functions ################################# """	


""" ################################# BEGIN Verification Functions ################################# """
def verifyServerDHParamsSignature(nonce, keys, tbs_dhparams, signature):
	tobeSigned = nonce.client_random + nonce.server_random + tbs_dhparams 
	tbsmd5 = hashlib.md5()
	tbsmd5.update(tobeSigned)
	tbssha1 = hashlib.sha1()
	tbssha1.update(tobeSigned)
	hashed = tbsmd5.digest() + tbssha1.digest()
	modulo_bits = int(math.ceil(math.log(keys.server_pubkey.n,2)))
	paddedHash = addPKCS1Padding(modulo_bits/8, hashed,1)
	return keys.server_pubkey.verify(paddedHash, (signature,""))

def verifyFinishedMessage(payload, keys, seq, hs, ciphersuite):
	if ciphersuite == CIPHER_AES128_SHA or ciphersuite == CIPHER_DHE_RSA_AES128_SHA:
		aescipher = AES.new(keys.server_write_key, AES.MODE_CBC, keys.server_write_IV)
		plaintext = aescipher.decrypt(payload)
		keys.server_write_IV = payload[-16:]		
	elif ciphersuite == CIPHER_RC4_SHA:
		keys.server_rc4 = ARC4.new(keys.server_write_key)
		plaintext = keys.server_rc4.decrypt(payload)
		
	serververify = plaintext[4:16]
	servermac = plaintext[16:36]
	verify = PRF(keys.master, "server finished", hs.md5.digest()+hs.sha1.digest(),12)
	validVerify = verify == serververify

	# Calculate MAC
	seqnumber = struct.pack('!Q', seq.server) # Seq Number from Server start with 0
	seq.server += 1
	recordfinished = "\x16" + TLS_VERSION + struct.pack(">h", 16) + plaintext[0:16]
	
	mac = hmac.HMAC(keys.server_write_MAC_secret, seqnumber+recordfinished, hashlib.sha1).digest()			

	# Handshake complete if both verify and mac were matched
	return (verify == serververify) and (mac == servermac)	
""" ################################# END Verification Functions ################################# """

""" ################################# BEGIN Packet Handling Functions ################################# """
def extractRecords(paket):
	pos = 0
	records = []
	while pos < len(paket):
		length = struct.unpack(">h",paket[pos+3:pos+5])[0]
		payload = paket[pos+5:(pos+5+length)]
		if len(payload) == length:
			records.append(paket[pos:pos+5+length])
		pos = pos + 5 + length
	return records

def parseCertificate(payload, keys):
	certlen = struct.unpack(">L","\x00"+payload[7:10])[0]
	servercert = payload[10:10+certlen]
	cert = DerSequence()
	cert.decode(servercert)
	tbsCertificate = DerSequence()
	tbsCertificate.decode(cert[0])
	keys.server_pubkey = RSA.importKey(tbsCertificate[6])

def decodeAppData(payload, seq, keys, ciphersuite):
	if ciphersuite == CIPHER_AES128_SHA or ciphersuite == CIPHER_DHE_RSA_AES128_SHA:
		aescipher = AES.new(keys.server_write_key, AES.MODE_CBC, keys.server_write_IV)
		keys.server_write_IV = payload[-16:]
		plaintext = aescipher.decrypt(payload)
		padLength = ord(plaintext[-1])+1
		plaintext = plaintext[:-padLength] # strip padding	
	elif ciphersuite == CIPHER_RC4_SHA:
		plaintext = keys.server_rc4.decrypt(payload)

	# get MAC
	servermac = plaintext[-20:]
	plaintext = plaintext[:-20] # strip MAC

	seqnumber = struct.pack('!Q', seq.server) 
	seq.server += 1
	record = craftSSLRecord("\x17", plaintext)
	recordmac = hmac.HMAC(keys.server_write_MAC_secret, seqnumber+record, hashlib.sha1).digest()

	if recordmac != servermac:
		print "HMAC INVALID!"

	return plaintext		

def handleAppData(record_content, seq, keys, ciphersuite):
	pos = 0
	rec_len = len(record_content)
	while pos < rec_len:
		length = struct.unpack(">L","\x00"+record_content[pos+1:pos+4]) [0]
		payload = record_content[pos:pos+length+4]
		pos = pos + 4 + length
		plaintext = decodeAppData(payload, seq, keys, ciphersuite)

		print "BEGIN Plaintext Application Data:"
		sys.stdout.write(plaintext)
		print "\nEND Plaintext Application Data."		


def handlePlainHandshake(payload, sock, ciphersuite):
	# Update hs.md5 dan hs.sha1
	hs.md5.update(payload)
	hs.sha1.update(payload)

	hstype = ord(payload[0])
	if hstype == 2: # ServerHello
		print "-"*5 + "ServerHello" + "-"*5
		nonce.server_random = payload[6:38]
		sessid = payload[39:39+ord(payload[38])]

	elif hstype == 11: # Certificate
		print "-"*5 + "Certificate" + "-"*5	
		parseCertificate(payload, keys)

	elif hstype == 12: # ServerKeyExchange
		print "-"*5 + "ServerKeyExchange" + "-"*5
		
		pLen = struct.unpack(">h",payload[4:6])[0]
		pos = 6		
		dh.p = strtonum(payload[pos:pos+pLen])
		pos += pLen

		gLen = struct.unpack(">h",payload[pos:pos+2])[0]
		pos += 2
		
		dh.g = strtonum(payload[pos:pos+gLen])
		pos += gLen

		YsLen = struct.unpack(">h",payload[pos:pos+2])[0] 
		pos += 2
		
		dh.Ys = strtonum(payload[pos:pos+YsLen])
		pos += YsLen

		tbs_dhparams = payload[4:pos]

		signLen = struct.unpack(">h",payload[pos:pos+2])[0] 
		pos += 2
		signature_str = payload[pos:pos+signLen]
		signature = strtonum(payload[pos:pos+signLen])

		is_verified = verifyServerDHParamsSignature(nonce, keys, tbs_dhparams, signature)
		print "Signature verified: " + str(is_verified)

		dh.Xc = strtonum(open("/dev/urandom","rb").read(32))
		dh.Yc = pow(dh.g, dh.Xc, dh.p) 

	elif hstype == 14: # ServerHelloDone
		print "-"*5 + "ServerHelloDone" + "-"*5
		# After ServerHelloDone, responds with ClientKeyExchange	
		if ciphersuite == CIPHER_DHE_RSA_AES128_SHA:
			premaster_secret = dh.generate_premaster()		
			keys.expand(premaster_secret, nonce)
			Yc_size = int(math.ceil((math.ceil(math.log(dh.Yc,2)))/8))
			clientkeyexchange = craftClientKeyExchange(numtostr(dh.Yc), Yc_size)
			
		elif ciphersuite == CIPHER_AES128_SHA or ciphersuite == CIPHER_RC4_SHA:
			premaster_secret = TLS_VERSION + open("/dev/urandom","rb").read(46)
			keys.expand(premaster_secret, nonce)
			modulo_bits = int(math.ceil(math.log(keys.server_pubkey.n,2)))
			paddedpremaster = addPKCS1Padding(modulo_bits/8, premaster_secret,2)
			cipherpremaster = keys.server_pubkey.encrypt(paddedpremaster,"")[0]
			clientkeyexchange = craftClientKeyExchange(cipherpremaster, len(cipherpremaster))
		
		record_cke = craftSSLRecord("\x16", clientkeyexchange)
		sock.send(record_cke)

		# Update handshake hashes
		hs.md5.update(clientkeyexchange)
		hs.sha1.update(clientkeyexchange)
		
		''' Send ChangeCipherSepec message '''
		record_ccs = craftSSLRecord("\x14", "\x01")
		sock.send(record_ccs)
		
		# Create Encrypted Finished message
		record_finished = craftFinishedRecord(keys,hs,seq, ciphersuite)
		sock.send(record_finished)

def handleSSLRecord(record,keys,hs,seq,hsdone,serverCCS,ciphersuite):
	keepalive = True

	protocoltype = ord(record[0])
	rec_len = struct.unpack(">h",record[3:5]) [0]
	record_content = record[5:5+rec_len]

	if protocoltype == 22: # Handshake protocol
		print "Handshake. "
		pos = 0
		while pos < rec_len:
			length = struct.unpack(">L","\x00"+record_content[pos+1:pos+4]) [0]
			payload = record_content[pos:pos+length+4]
			pos = pos + 4 + length
			if serverCCS == False:
				# Before server CCS arrived
				handlePlainHandshake(payload, sock, ciphersuite)
			else: 
				# Everything is encrypted after ChangeCipherSepec from server
				hsdone = verifyFinishedMessage(payload, keys, seq, hs, ciphersuite)

	elif protocoltype == 20: # Change Cipher Spec protocol
		print "ChangeCipherSpec. Everything after this will be encrypted."
		serverCCS = True

	elif protocoltype == 21: # Alert protocol
		print "Alert. Tear down SSL connection.\n"
		keepalive = False

	elif protocoltype == 23: # Application data
		print "\nApplication Data. "
		handleAppData(record_content, seq, keys, ciphersuite)

	return (keepalive,hsdone,serverCCS)
""" ################################# END Packet Handling Functions ################################# """	


""" ################################# BEGIN Packet Crafting Functions ################################# """
def craftSSLRecord(payloadtype, payload):
	# Wrap in record header
	record = payloadtype
	record += TLS_VERSION
	record += struct.pack(">h",len(payload))
	record += payload
	return record

def craftFinished(keys, hs):	
	clientfinished = "\x14" # Handshake type 0x14 = Finished
	clientfinished += "\x00\x00\x0C" # Length = 12 bytes
	hs_hash = hs.md5.digest()+hs.sha1.digest()
	verify = PRF(keys.master, "client finished", hs_hash, 12)

	clientfinished += verify
	return clientfinished

def craftClientKeyExchange(keymaterials, keysize):
	clientkeyexchange = "\x10" # Handshake type 0x10 = ClientKeyExchange
	clientkeyexchange += "\x00" + struct.pack(">h", keysize+2)
	clientkeyexchange += struct.pack(">h",keysize)
	clientkeyexchange += keymaterials
	return clientkeyexchange		

def craftHelloClient(hs, nonce, ciphersuite):
	currepoch = struct.pack(">L", int(time.mktime(time.gmtime())))
	nonce.client_random = currepoch + open("/dev/urandom","rb").read(28)

	hello = TLS_VERSION + nonce.client_random
	hello += "\x00" # Session ID length = 0
	hello += struct.pack(">h",2) # Length ciphersuite
	hello += ciphersuite
	hello += "\x01\x00" # Compression method NULL

	handshake_hello = "\x01" # type = ClientHello
	handshake_hello += "\x00"+struct.pack(">h",len(hello))
	handshake_hello += hello

	# update md5 and sha1 handshake hash
	hs.md5.update(handshake_hello)
	hs.sha1.update(handshake_hello)

	# Wrap in record header
	return craftSSLRecord("\x16", handshake_hello)

def craftAppDataRecord(data, seq, keys, ciphersuite):
	# Calculate HMAC
	seqnumber = struct.pack('!Q', seq.client)
	seq.client += 1

	record = craftSSLRecord("\x17", data)
	recordmac = hmac.HMAC(keys.client_write_MAC_secret, seqnumber+record, hashlib.sha1).digest()
	tobeencrypted = data + recordmac

	if ciphersuite == CIPHER_AES128_SHA or ciphersuite == CIPHER_DHE_RSA_AES128_SHA:
		# PKCS#7 padding prior to AES encryption		
		padLength = 15 - (len(tobeencrypted) % 16) 
		tobeencrypted += chr(padLength)*padLength + chr(padLength)
		
		# AES encrypt
		aescipher = AES.new(keys.client_write_key, AES.MODE_CBC, keys.client_write_IV)
		ciphertext = aescipher.encrypt(tobeencrypted)

		# Update IV for next record
		keys.client_write_IV = ciphertext[-16:]
	elif ciphersuite == CIPHER_RC4_SHA:
		# RC4 encrypt
		ciphertext = keys.client_rc4.encrypt(tobeencrypted)

	return craftSSLRecord("\x17", ciphertext)

def craftFinishedRecord(keys, hs, seq, ciphersuite):
	clientfinished = craftFinished(keys, hs)
	record_cf = craftSSLRecord("\x16", clientfinished)

	hs.md5.update(clientfinished)
	hs.sha1.update(clientfinished)

	# Calculate MAC
	seqnumber = struct.pack('!Q', seq.client) # First record seq number is zero
	seq.client += 1
	recordmac = hmac.HMAC(keys.client_write_MAC_secret, seqnumber+record_cf, hashlib.sha1).digest()

	if ciphersuite == CIPHER_AES128_SHA or ciphersuite == CIPHER_DHE_RSA_AES128_SHA:
		# Encrypt(finished message + HMAC + padding)
		tobeencrypted = clientfinished + recordmac + "\x0b"*12
		aescipher = AES.new(keys.client_write_key, AES.MODE_CBC, keys.client_write_IV)
		cipherfinished = aescipher.encrypt(tobeencrypted)
		keys.client_write_IV = cipherfinished[-16:]
	elif ciphersuite == CIPHER_RC4_SHA:
		# Encrypt(finished message + HMAC )
		tobeencrypted = clientfinished + recordmac 	
		keys.client_rc4 = ARC4.new(keys.client_write_key)
		cipherfinished = keys.client_rc4.encrypt(tobeencrypted)

	record_finished = craftSSLRecord("\x16", cipherfinished)	
	return record_finished
""" ################################# END Packet Crafting Functions ################################# """

""" ################################# BEGIN Formatting Functions ################################# """
def addPKCS1Padding(k, data, block_type):
	padLength = k - 3 - len(data)
	pad = ""
	if block_type == 1:
		pad = "\xFF" * padLength
		padding = "\x00\x01" + pad + "\x00"
	elif block_type == 2:		
		for i in range(0, padLength):
			pad += chr(random.randint(1,255))
		padding = "\x00\x02" + pad + "\x00"
	paddedBytes = padding + data
	return paddedBytes

def strtonum(string):
	result = 0
	length = len(string)
	for i in range(0, length):
		result += (1 << 8*(length-1-i) ) * ord(string[i]) 
	return result

def numtostr(n):
	hexnum = hex(n)[2:]
	if hexnum[-1] == 'L':
		hexnum = hexnum[:-1]
	return str(binascii.unhexlify(hexnum))
	
""" ################################# END Formatting Functions ################################# """

""" Handshaking Function """
def handshake(ciphersuite, sock, hs, nonce):
	hsdone = False
	serverCCS = False

	# send HelloClient packet
	sock.send(craftHelloClient(hs, nonce, ciphersuite))

	# expect ServerHello, Certificate and ServerHelloDone
	recvbuf = ""
	while not hsdone:
		recvbuf += sock.recv(16384)
		records = extractRecords(recvbuf)
		pos = 0
		if len(records) > 0:
			for rec in records:
				(keepalive,hsdone,serverCCS) = handleSSLRecord(rec, keys, hs, seq, hsdone, serverCCS, ciphersuite)
				pos += len(rec)
			recvbuf = recvbuf[pos:]

""" Main function """
if __name__ == "__main__":
	nonce = RandomNonce()
	keys = SessionKeys()
	dh = DHParams()
	seq = SequenceNumber()
	hs = HandshakeHash()

	host = sys.argv[1]
	port = int(sys.argv[2])
	cipher = sys.argv[3]
	if cipher == "AES128-SHA":
		ciphersuite = CIPHER_AES128_SHA
	elif cipher == "DHE-RSA-AES128-SHA":
		ciphersuite = CIPHER_DHE_RSA_AES128_SHA
	elif cipher == "RC4-SHA":
		ciphersuite = CIPHER_RC4_SHA
	else:
		print "Unknown cipher!"
		sys.exit(1)

	# Create TCP Connection
	sock = socket(AF_INET, SOCK_STREAM)
	sock.connect((host,port))

	# Handshaking
	handshake(ciphersuite, sock, hs, nonce)

	# Application layer... send HTTP GET request over SSL
	request = "GET / HTTP/1.1\r\nUser-Agent: Firefox\r\nHost: "+host+"\r\n\r\n"
	sock.send(craftAppDataRecord(request, seq, keys, ciphersuite))

	# Expect HTTP response over SSL
	recvbuf = ""
	keepalive = True
	while True:
		recvbuf += sock.recv(16384)
		records = extractRecords(recvbuf)
		pos = 0
		if len(records) > 0:
			for rec in records:
				(keepalive,hsdone,serverCCS) = handleSSLRecord(rec, keys, hs, seq, None,None, ciphersuite)
				pos += len(rec)
			recvbuf = recvbuf[pos:]

		if not keepalive:
			break

	# Done
	sock.close()
