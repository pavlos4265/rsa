/*
   Copyright 2023 pavlos4265

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/

#include <stdio.h>
#include <stdlib.h>
#include <time.h>

typedef unsigned int word;

//prime length. example: 16 -> 512-bit primes -> 1024-bit modulus
#define WORDS 16
#define WORD_MAX 4294967295
#define WORD_BITS sizeof(word)*8

void printN(word n[], int size) {
	char str[WORD_BITS];
	for (int i = size-1; i >= 0; i--) {	
		itoa(n[i], str, 2);
		printf("%s ", str);
	}
	printf("\n");
}

int random() {
	return rand();
}

void initarray(word a[], int length) {
	for (int i = 0; i < length; i++) {
		a[i] = 0;
	}
}

void copyarrAt(word s[], word d[], int start, int length) {
	for (int i = 0; i < length; i++) {
		d[i] = s[i+start];
	}
}

void copyarr(word s[], word d[], int length) {
	copyarrAt(s, d, 0, length);
}

word leftzerowords(word p[], int length) {
	for (int i = length-1; i >= 0; i--) {
		if (p[i] != 0)
			return length-i-1;
	}

	return length;
}

word leftzerobits(word b) {
	for (int i = 0; i < WORD_BITS; i++) {
		int mask = 1;
		mask <<= (WORD_BITS-1);
		if ((b & mask) != 0)
			return i;
		
		b <<= 1;
	}

	return WORD_BITS;
}

word equals(word a[], word b[], int length) {
	for (int i = 0; i < length; i++) {
		if (a[i] != b[i]) 
			return 0;
	}
	
	return 1;
}

word greaterthan(word a[], word b[], int length) {
	for (int i = length-1; i >= 0; i--) {
		if (a[i] == b[i])
			continue;
		
		if (a[i] > b[i])
			return 1;
		
		if (a[i] < b[i] )
			return 0;
	}

	return 0;
}

void lwshift(word p[], int length, int k, word r[]) {
	for (int i = length-1; i >= 0 ; i--) {
		if (i+k < length)
			r[i+k] = p[i];
		
		r[i] = 0;
	}
}

void rwshift(word p[], int length, int k, word r[]) {
	for (int i = 0; i < length; i++) {
		if (i-k >= 0)
			r[i-k] = p[i];

		r[i] = 0;
	}
}

void rbshift(word p[], int length, int k, word r[]) {
	word mask = 0;
	for (int j = 0; j < k; j++) {
		mask <<= 1;
		mask |= 1;
	}
	
	word prevlastbits = 0;
	for (int i = length-1; i >= 0; i--) {
		word lastbits = p[i] & mask;
		r[i] = p[i] >> k;
		r[i] |= prevlastbits;
		prevlastbits = lastbits << (WORD_BITS-k);
	}
}

void lbshift(word p[], int length, int k, word r[]) {
	int mask = 0;
	for (int j = 0; j < k; j++) {
		mask <<= 1;
		mask |= 1;
	}
	mask <<= (WORD_BITS-k);
	
	word prevlastbits = 0;
	for (int i = 0; i < length; i++) {
		word lastbits = p[i] & mask;
		r[i] = p[i] << k;
		r[i] |= prevlastbits;
		prevlastbits = lastbits >> (WORD_BITS-k);
	}		
}

void multiply_n2(word p[], word q[], int length, word n[]) {
	int max = -1;
	for (int j = 0; j < length; j++) {
		unsigned long long carry = 0;
		for (int i = 0; i < length; i++) {
			if (j+i>max) {	//initialize cells
				max = j+i;
				n[max] = 0;
			}

			unsigned long long mul = (unsigned long long)q[j] * (unsigned long long)p[i];
			unsigned long long sum = (unsigned long long)n[j+i] + mul + carry;
			n[j+i] = sum % (WORD_MAX+1);
			carry = (sum > WORD_MAX) ? (sum-(unsigned long long)n[j+i]) >> WORD_BITS : 0;
		}
		
		max = j+length;
		n[j+length] = carry;
	}
}

void addAt(word a[], int offsetA, int lengthA, word b[], int offsetB, int lengthB, word n[]) {
	unsigned long long carry = 0;
	for (int i = 0; i < lengthA; i++) {
		unsigned long long sum = (i < lengthB) ? (unsigned long long)a[i+offsetA]+(unsigned long long)b[i+offsetB]+carry : (unsigned long long)a[i]+carry;
		carry = (sum > WORD_MAX) ? 1 : 0;
		n[i] = sum % (WORD_MAX+1);
	}

	if (carry != 0)
		n[lengthA] = carry;
}

void add(word a[], int lengthA, word b[], int lengthB, word n[]) {
	addAt(a, 0, lengthA, b, 0, lengthB, n);
}

void subtract(word a[], int lengthA,  word b[], int lengthB, word n[]) {
	int carry = 0;
	for (int i = 0; i < lengthA; i++) {
		long long diff = (i < lengthB) ? (long long)a[i] - (long long)b[i] -(long long)carry : (long long)a[i]-(long long)carry;
		carry = 0;
	
		if (diff < 0) {
			diff = (WORD_MAX+1+diff);
			carry = 1;
		}

		n[i] = diff;
	}
}

void karatsuba_mul(word p[], int startp, word q[], int startq, int length, word n[]) {
	if (length <= 3) {
		int max = -1;
		for (int j = 0; j < length; j++) {
			unsigned long long carry = 0;
			for (int i = 0; i < length; i++) {
				if (j+i>max) {
					max = j+i;
					n[max] = 0;
				}

				unsigned long long mul = (unsigned long long)q[startq-length+1+j] * (unsigned long long)p[startp-length+1+i];
				unsigned long long sum = (unsigned long long)n[j+i] + mul + carry;
				n[j+i] = sum % (WORD_MAX+1);
				carry = (sum > WORD_MAX) ? (sum-(unsigned long long)n[j+i]) >> WORD_BITS : 0;
			}
			
			max = j+length;
			n[j+length] = carry;
		}

		return;
	}

	int lena_c = length/2;
	int lenb_d = length - lena_c;

	int acshift = lenb_d*2;

	word ac[2*lena_c + acshift];
	karatsuba_mul(p, startp, q, startq, lena_c, ac);

	word bd[2*lenb_d];
	karatsuba_mul(p, startp-lena_c, q, startq-lena_c, lenb_d, bd);

	int lensum = lenb_d + 1;
	word absum[lensum];
	absum[lensum-1] = 0;
	addAt(p, startp-length+1, lenb_d, p, startp-lena_c+1, lena_c, absum);

	word cdsum[lensum];
	cdsum[lensum-1] = 0;
	addAt(q, startq-length+1, lenb_d, q, startq-lena_c+1, lena_c, cdsum);

	if (absum[lensum-1] == 0 && cdsum[lensum-1] == 0)
		lensum--;

	int lenabcd = 2*lensum + lenb_d;
	word abcd[lenabcd];
	karatsuba_mul(absum, lensum-1, cdsum, lensum-1, lensum, abcd);
	subtract(abcd, lenabcd-lenb_d, ac, 2*lena_c, abcd);
	subtract(abcd, lenabcd-lenb_d, bd, 2*lenb_d, abcd);

	lwshift(ac, 2*lena_c + acshift, acshift, n);

	word abcdtemp[lenabcd];
	lwshift(abcd, lenabcd, lenb_d, abcdtemp);

	add(n, 2*length, abcdtemp, lenabcd, n);
	add(n, 2*length, bd, 2*lenb_d, n);
}

void multiply(word p[], word q[], int length, word n[]) {
	karatsuba_mul(p, length-1, q, length-1, length, n);
}

void divide(word a[], word b[], int length, word r[]) {
	word aval[length];
	copyarr(a, aval, length);

	initarray(r, length);

	word blzw = leftzerowords(b, length);
	word blzb = leftzerobits(b[length-1-blzw]);
	word bval[length];

	while (1) {	
		word alzw = leftzerowords(aval, length);
		word alzb = leftzerobits(aval[length-1-alzw]);

		int shift = (aval[length-1-alzw] < b[length-1-blzw]) ? blzw-alzw-1 : blzw-alzw;
		if (shift > 0) {
			lwshift(b, length, shift, bval);
		}else
			copyarr(b, bval, length);

		int bshift = 0;
		if (shift>=0) {
			if (alzw != blzw-shift)
				lbshift(bval, length, (bshift = blzb+WORD_BITS-alzb-1), bval);
			else if (blzb != alzb)
				lbshift(bval, length, (bshift = blzb-alzb-1), bval);
		}

		int d = 0;
		while (!greaterthan(bval, aval, length)) {
			subtract(aval, length, bval, length, aval);
			d++;
		}

		d <<= bshift;
		r[shift] |= d;

		if (greaterthan(b, aval, length))
			break;
	}
}

void modulo(word a[], word b[], int length, word r[]) {
	copyarr(a, r, length);

	word blzw = leftzerowords(b, length);
	word blzb = leftzerobits(b[length-1-blzw]);
	word bval[length];

	while (1) {	
		word alzw = leftzerowords(r, length);
		word alzb = leftzerobits(r[length-1-alzw]);

		int shift = (r[length-1-alzw] < b[length-1-blzw]) ? blzw-alzw-1 : blzw-alzw;
		if (shift > 0) {
			lwshift(b, length, shift, bval);
		}else
			copyarr(b, bval, length);

		if (shift>=0) {
			if (alzw != blzw-shift)
				lbshift(bval, length, blzb+WORD_BITS-alzb-1, bval);
			else if (blzb != alzb)
				lbshift(bval, length, blzb-alzb-1, bval);
		}

		while (!greaterthan(bval, r, length)) {
			subtract(r, length, bval, length, r);
		}

		if (greaterthan(b, r, length))
			break;
	}
}

void gcd(word a[], word b[], int length, word r[]) {
    //return b == 0 ? a : gcd(b, a % b);   
	word zeros[length];
	initarray(zeros, length);

	if (equals(b, zeros, length)) {
		copyarr(a, r, length);
		return;
	}

	word mod[length];
	modulo(a, b, length, mod);
	gcd(b, mod, length, r);
}

#define PRIMES_COUNT 100

int primes[] = {
	2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
	97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
	193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293,
	307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419,
	421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541,
	547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653,
	659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787,
	797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919,
	929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039,
	1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153,
	1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223
};

word dividesbyprimes(word p[], int length) {
	word zeros[length];
	initarray(zeros, length);

	for (int i = 0; i < PRIMES_COUNT; i++) {
		word q[length];
		initarray(q, length);
		q[0] = primes[i];

		word r[length];
		initarray(r, length);
		modulo(p, q, length, r);
		if (equals(r, zeros, length)) 
			return 1;	
	}

	return 0;
}

#define D 4
#define DWORDS (WORD_BITS/D)
void powermod(word b[], word e[], word m[], int length, word r[]) {
	word bigm[2*length];
	initarray(bigm, 2*length);
	copyarr(m, bigm, length);

	word precalc[14][length];
	for (int i = 0; i < 14; i++) {
		word mulr[2*length];
		multiply(b, (i == 0) ? b : precalc[i-1], length, mulr);
		modulo(mulr, bigm, 2*length, mulr);
		copyarr(mulr, precalc[i], length);
	}

	initarray(r, length);
	r[0] = 1;

	word w = 0;
	for (int i = 0; i < length*DWORDS; i++) {
		word mulr[2*length];

		for (int i = 0; i < D; i++) {
			multiply(r, r, length, mulr);
			modulo(mulr, bigm, 2*length, mulr);
			copyarr(mulr, r, length);
		}

		int bshift = WORD_BITS - i%DWORDS*D - D;
		int mask = 0b1111;
		w = (e[length-1-i/DWORDS] >> bshift) & mask;

		if (w != 0) {
			multiply(r, (w == 1) ? b : precalc[w-2], length, mulr);
			modulo(mulr, bigm, 2*length, mulr);
			copyarr(mulr, r, length);
		}
	}
}

word ispropablyprime(word p[], word a[], int length) {
	word one[length];
	initarray(one, length);
	one[0] = 1;

	word d[length];
	subtract(p, length, one, length, d);

	word pminus[length];
	copyarr(d, pminus, length);

	word res[length];

	unsigned int s = 0;
	while (d[0] % 2 == 0) {
		rbshift(d, length, 1, d);
		s++;
	}

	word t[length];
	powermod(a, d, p, length, t);

	if (equals(t, one, length) || equals(t, pminus, length))
		return 1;

	word bigp[2*length];
	initarray(bigp, 2*length);
	copyarr(p, bigp, length);
	for (int i = 1; i < s; i++) {
		word mulr[length*2];
		multiply(t, t, length, mulr);
		modulo(mulr, bigp, length*2, mulr);
		copyarr(mulr, t, length);
		if (equals(t, pminus, length))
			return 1;
	}
	
	return 0;
}

word isprime(word p[], int length, int reps) {
	for (int i = 0; i < reps; i++) {
		word a[length];
		for (int k = 0 ; k < length-1; k++) {
			a[k] = random() % (WORD_MAX+1);
		}
		a[length-1] = random() % p[length-1];

		if (!ispropablyprime(p, a, length))
			return 0;
	}

	return 1;
}

void generateprime(word e[], int length, word p[]) {
	word one[length];
	initarray(one, length);
	one[0] = 1;

	word two[1];
	two[0] = 2;

	for (int i = 0; i < length; i++) {
		p[i] = random() % (WORD_MAX+1);
	}
	word temp = 1;
	temp <<= (WORD_BITS-1);
	p[length-1] |= temp;
	p[0] |= 1;

	word r[length];
	while (1) {
		add(p, length, two, 1, p);

		if (dividesbyprimes(p, length) || !isprime(p, length, 1))
			continue;

		p[0] -= 1;
		gcd(p, e, length, r);
		p[0] += 1;

		if (equals(r, one, length))
			break;
	}
}

int rsa() {
	srand(time(NULL));

	word e[WORDS];
	initarray(e, WORDS);
	e[0] = 65537;
	printf("e\n");
	printN(e, 1);
	printf("\n");

	word p[WORDS];
	generateprime(e, WORDS, p); 
	printf("p\n");
	printN(p, WORDS);
	printf("\n");
	
	word q[WORDS];
	generateprime(e, WORDS, q);
	printf("q\n");
	printN(q, WORDS);
	printf("\n");
	
	word n[2*WORDS];
	multiply(p, q, WORDS, n);
	printf("n\n");
	printN(n, 2*WORDS);
	printf("\n");

	word phi[2*WORDS];
	p[0] -= 1;
	q[0] -= 1;
	multiply(p, q, WORDS, phi);
	p[0] += 1;
	q[0] += 1;

	word one[1];
	one[0] = 1;

	word zeros[4*WORDS];
	initarray(zeros, 4*WORDS);

	word bige[4*WORDS];
	initarray(bige, 4*WORDS);
	copyarr(e, bige, WORDS);

	word d[4*WORDS];
	word k[2*WORDS];
	initarray(k, 2*WORDS);
	k[0] = 1;

	//d = (1 + (k * phi)) / e
	while (1) {
		word r[4*WORDS];
		multiply(k, phi, 2*WORDS, r);
		add(r, 4*WORDS, one, 1, r);
		word modr[4*WORDS];
		modulo(r, bige, 4*WORDS, modr);
		if (equals(modr, zeros, 4*WORDS)) {
			divide(r, bige, 4*WORDS, d);
			break;
		}

		add(k, 2*WORDS, one, 1, k);
	}

	printf("d\n");
	printN(d, 2*WORDS); 

    return 0;
}

int main() {
	rsa();
	return 0;
}