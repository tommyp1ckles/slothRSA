/*
 Copyright (c) 2015, Tom Hadlaw <tomhadlaw144@gmail.com>
 
 Permission is hereby granted, free of charge, to any person obtaining a copy
 of this software and associated documentation files (the "Software"), to deal
 in the Software without restriction, including without limitation the rights
 to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 copies of the Software, and to permit persons to whom the Software is
 furnished to do so, subject to the following conditions:
 
 
 
 The above copyright notice and this permission notice shall be included in
 all copies or substantial portions of the Software.
 
 
 
 THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL THE
 AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 THE SOFTWARE.

 * My implementation for the RSA encryption algorithm for my 
 * data comm class during my undergrad.
 * IMPORTANT: This was purely for learning purposes from someone who was just 
 * learning about about cryptography. IT Is
 * Author: Tom Hadlaw.
 */

#include <math.h>
#include <time.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <gmpxx.h>
#include <limits>
#include <iostream>
#include <string>

#define BUFFERSIZE 128

using namespace std;

uint64_t discretePow(uint64_t a, uint64_t n) {
    uint64_t i;
    for (i = 0; i < n; i++) {
        a *= a;
    }
    return a;
}

/*
 * Finds the modular multiplicative inverse.
 * i.e. find {x : ax = 1 (mod m)}
 * Probably a sub-linear time way to do this...
 */
uint64_t inv(uint64_t a, uint64_t m) {
    uint64_t x = 0;
    while ( (a * x) % m != 1) {
        x++;
    }
    return x;
}

mpz_class mpzInv(mpz_class a, mpz_class b) {
    mpz_class b0 = b, t, q;
    mpz_class x0("0");
    mpz_class x1("1");
    mpz_class one("1");
    if (b == 1) return one;
    while (a > 1) {
        q = a / b;
        t = b, b = a % b, a = t;
        t = x0, x0 = x1 - q * x0, x1 = t;
    }
    if (x1 < 0) x1 += b0;
    return x1;
}
/*
 * Euclids gcd function
 */
uint64_t gcd(int a, int b) {
    uint64_t c;
    while (a != 0) {
        c = a;
        a = b % a;
        b = c;
    }
    return b;
}

mpz_class mpzGcd(mpz_class a, mpz_class b) {
    mpz_class c;
    while (a != 0) {
        c = a;
        a = b % a;
        b = c;
    }
    return b;
}

/*
 * Finds a coprime of n.
 * Because gcd(n, n+1) = 1 then it is 
 * guaranteed to find a coprime.
 * Note: Right now it simply find the first prime that isnt a multiple of
 * n, although correct having e be 3 or 5 isnt very good.
 */
uint64_t coprime(uint64_t n) {
    uint64_t e;
    for (e = 2; e < n; e++) { //Clearly we dont want 1 as a coprime
        if (gcd(e, n) == 1) return e;
    }
    return 0;
}

mpz_class mpzCoprime(mpz_class n) {
    mpz_class e;
    for (e = 2; e < n; e++) {
        if (mpzGcd(e, n) == 1) return e;
    }
    mpz_class ret("-1");
    return ret;
}

int issPrime(int number) {
    int i;
    if (number <= 3) return 1;
    for (i = 2; i < number; i++) {
      if (number % i == 0 && i != number)
        return 0;
    }
    return 1;
}

/*
 * Sieve of Atkin
 * TODO: Use big integer library to implenent properly large prime generator.
 */
unsigned char *generateSieve(uint64_t limit) {
    unsigned char *isPrime;//[limit + 1];
    isPrime = (unsigned char*)malloc((limit+1)*sizeof(unsigned char));
    uint64_t i;
    isPrime[2] = 1;
    isPrime[3] = 1;
    for (i = 5; i <= limit; i++)
        isPrime[i] = 0;
    
    uint64_t x, y;
    uint64_t sqrtLimit = ceil(sqrt(limit));
    // Put in candidate  primes:
    // (Integers which have an odd number of representations
    // in certain quadratic forms)
    for (x = 0; x <= sqrtLimit; x++) {
        for (y = 1; y <= sqrtLimit; y++) {
            uint64_t n = 4 * x * x + y * y;
            if (n <= limit && (n % 12 == 1 || n % 12 == 5))
                isPrime[n] = ~isPrime[n] & 1;
            n = 3 * x * x + y * y;
            if (n <= limit && (n % 12 == 7))
                isPrime[n] = ~isPrime[n] & 1;
            n -= 2 * y * y;
            if (x > y && n <= limit && n % 12 == 11)
                isPrime[n] = ~isPrime[n] & 1;
        }
    }
    uint64_t n;
    //eliminate composite numbers by sieving.
    for (n = 5; n <= sqrtLimit; n++) {
        if (isPrime[n]) {
            //remove all multiples of n^2,
            //this is a sufficient condition 
            //because composites on list cannot
            //square free.
            uint64_t sqn = n*n;
            uint64_t k = sqn;
            while (k <= limit) {
                isPrime[k] = 0;
                k += sqn;
            }
        }
    }
    return isPrime;
}

/*
 * Generate randome prime from provided sieve
 */
uint64_t randPrime(unsigned char *isPrime, uint64_t limit) {
    srand(time(NULL));
    uint64_t randLimit = rand() % limit;
    uint64_t i;
    if (randLimit == 1) return 2;
    for (i = randLimit; i > 1; i--) {
        if (isPrime[i]) return i;
    }
    return 0;
}
/*
 * Chooses and integers between 1 < n < Phi(n) :
 * gcd(n, Phi(n)) == 1, i.e. are coprime.
 */
void mpzFindCoprime(mpz_class &src, mpz_class &Phi) {
    mpz_class n = Phi - 1;
    mpz_class gcd;
    while (n > 0) {
        mpz_gcd(gcd.get_mpz_t(), n.get_mpz_t(), Phi.get_mpz_t());
        if (gcd == 1) {
            src = n;
            return;
        }
    }
}

int main(int argv, char **argc) {
    if (!strcmp(argc[1], "-genkey")) {
        mpz_class p("0");
        mpz_class q("0");
        mpz_class l1("0");
        mpz_class l2("0");
        gmp_randstate_t state;
        gmp_randinit_mt(state);
        gmp_randseed_ui(state, time(NULL));
        mpz_urandomb(l1.get_mpz_t(), state, 2048);
        mpz_urandomb(l2.get_mpz_t(), state, 2048);
        mpz_nextprime(p.get_mpz_t(), l1.get_mpz_t());
        mpz_nextprime(q.get_mpz_t(), l2.get_mpz_t());
        mpz_class n = p * q;
        //cout << "n = " << n << endl;
        mpz_class phi_n = (p - 1)*(q - 1); 
        mpz_class e("0");
        mpzFindCoprime(e, phi_n);
        cout << "public key (e) = " << e << endl;
        FILE *f;
        f = fopen("publickey", "w");
        mpz_out_raw(f, e.get_mpz_t());
        mpz_out_raw(f, n.get_mpz_t());
        FILE *f2;
        f2 = fopen("privatekey", "w");
        mpz_class d = mpzInv(e, phi_n);
        mpz_out_raw(f2, d.get_mpz_t());
        mpz_out_raw(f2, n.get_mpz_t());
    }
    else if (!strcmp(argc[1], "-encrypt")) {
        FILE *f;
        FILE *f2;
        f = fopen("publickey", "r");
        f2 = fopen("ctext", "w");
        mpz_class e("0");
        mpz_class n("0");
        mpz_inp_raw(e.get_mpz_t(), f);
        mpz_inp_raw(n.get_mpz_t(), f);
        //cout << "n = " << n << endl;
        //cout << "e = " << e << endl;
        cout << "Enter message: ";
        string mString;
        cin >> mString;
        mpz_class m(mString);
        cout << "Encrypting message: " << m << endl;
        mpz_class c("0");
        mpz_powm(c.get_mpz_t(), m.get_mpz_t(), e.get_mpz_t(), n.get_mpz_t());
        mpz_out_raw(f2, c.get_mpz_t());
        cout << "Encrypted message written to 'ctext'" << endl;
    }
    else if (!strcmp(argc[1], "-decrypt")) {
        FILE *f = fopen("privatekey", "r");
        FILE *f2 = fopen("ctext", "r");
        mpz_class n("0");
        mpz_class d("0");
        mpz_class c("0");
        mpz_class m("0");
        mpz_inp_raw(d.get_mpz_t(), f);
        mpz_inp_raw(n.get_mpz_t(), f);
        mpz_inp_raw(c.get_mpz_t(), f2);
        mpz_powm(m.get_mpz_t(), c.get_mpz_t(),
                d.get_mpz_t(), n.get_mpz_t());
        cout << "Decrypted message is: " << m << endl;
    }
}
