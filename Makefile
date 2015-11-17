all:
	g++ -L /usr/local/lib -I /usr/local/include -lgmpxx -lgmp RSA.cpp -o rsa
