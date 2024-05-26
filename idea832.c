/*
 * International Data Encryption Algorithm 832
 * IDEA-832 by Alexander Pukall 2012
 * 
 * 832-bit keys with 52 * 16-bit subkeys
 * 
 * Same speed as IDEA-128 but with 832-bit keys
 * 
 * Uses MD2II hash function to create the subkeys
 * 
 * Code free for all, even for commercial software 
 * No restriction to use. Public Domain 
 * 
 * Compile with gcc: gcc idea832.c -o idea832
 * 
 */
#include <stdio.h>
#include <string.h>
#include <stdint.h>

#define maxim 	65537
#define fuyi	65536
#define one 	65535
#define round	8	
#define nx1 108 // 54 * 16-bit subkeys = 864 bits but only 832 used

void cip(uint16_t in[5],uint16_t out[5], uint16_t z[7][10]);
void key(uint16_t z[7][10],unsigned char key[nx1]);
void de_key(uint16_t z[7][10], uint16_t dk[7][10]);
uint16_t inv(uint16_t xin);
uint16_t mul(uint16_t a, uint16_t b);


int x1,x2,i;
unsigned char h2[nx1];
unsigned char h1[nx1*3];


static void init()
{
    
   x1 = 0;
   x2 = 0;
    for (i = 0; i < nx1; i++)
        h2[i] = 0;
    for (i = 0; i < nx1; i++)
        h1[i] = 0;
}

static void hashing(unsigned char t1[], size_t b6)
{
    static unsigned char s4[256] = 
    {   13, 199,  11,  67, 237, 193, 164,  77, 115, 184, 141, 222,  73,
        38, 147,  36, 150,  87,  21, 104,  12,  61, 156, 101, 111, 145,
       119,  22, 207,  35, 198,  37, 171, 167,  80,  30, 219,  28, 213,
       121,  86,  29, 214, 242,   6,   4,  89, 162, 110, 175,  19, 157,
         3,  88, 234,  94, 144, 118, 159, 239, 100,  17, 182, 173, 238,
        68,  16,  79, 132,  54, 163,  52,   9,  58,  57,  55, 229, 192,
       170, 226,  56, 231, 187, 158,  70, 224, 233, 245,  26,  47,  32,
        44, 247,   8, 251,  20, 197, 185, 109, 153, 204, 218,  93, 178,
       212, 137,  84, 174,  24, 120, 130, 149,  72, 180, 181, 208, 255,
       189, 152,  18, 143, 176,  60, 249,  27, 227, 128, 139, 243, 253,
        59, 123, 172, 108, 211,  96, 138,  10, 215,  42, 225,  40,  81,
        65,  90,  25,  98, 126, 154,  64, 124, 116, 122,   5,   1, 168,
        83, 190, 131, 191, 244, 240, 235, 177, 155, 228, 125,  66,  43,
       201, 248, 220, 129, 188, 230,  62,  75,  71,  78,  34,  31, 216,
       254, 136,  91, 114, 106,  46, 217, 196,  92, 151, 209, 133,  51,
       236,  33, 252, 127, 179,  69,   7, 183, 105, 146,  97,  39,  15,
       205, 112, 200, 166, 223,  45,  48, 246, 186,  41, 148, 140, 107,
        76,  85,  95, 194, 142,  50,  49, 134,  23, 135, 169, 221, 210,
       203,  63, 165,  82, 161, 202,  53,  14, 206, 232, 103, 102, 195,
       117, 250,  99,   0,  74, 160, 241,   2, 113};
       
    int b1,b2,b3,b4,b5;
   
	b4=0;
    while (b6) {
    
        for (; b6 && x2 < nx1; b6--, x2++) {
            b5 = t1[b4++];
            h1[x2 + nx1] = b5;
            h1[x2 + (nx1*2)] = b5 ^ h1[x2];

            x1 = h2[x2] ^= s4[b5 ^ x1];
        }

        if (x2 == nx1)
        {
            b2 = 0;
            x2 = 0;
            
            for (b3 = 0; b3 < (nx1+2); b3++) {
                for (b1 = 0; b1 < (nx1*3); b1++)
                    b2 = h1[b1] ^= s4[b2];
                b2 = (b2 + b3) % 256;
            }
           }
          }
        }

static void end(unsigned char h4[nx1])
{
    
    unsigned char h3[nx1];
    int i, n4;
    
    n4 = nx1 - x2;
    for (i = 0; i < n4; i++) h3[i] = n4;
    hashing(h3, n4);
    hashing(h2, sizeof(h2));
    for (i = 0; i < nx1; i++) h4[i] = h1[i];
}

	/* encrypt algorithm */
void cip(uint16_t in[5],uint16_t out[5],uint16_t z[7][10]) 
{
	uint16_t r,x1,x2,x3,x4,kk,t1,t2,a;
	x1=in[1]; x2=in[2]; x3=in[3]; x4=in[4];
	for(r=1;r<=8;r++) 			/* the round function */
	{
			/* the group operation on 64-bits block */
	x1 = mul(x1,z[1][r]);		x4 = mul(x4,z[4][r]);
	x2 = (x2 + z[2][r]) & one;	x3 = (x3 + z[3][r]) & one;
			/* the function of the MA structure */
	kk = mul(z[5][r],(x1^x3));
	t1 = mul(z[6][r],(kk+(x2^x4)) & one);
	t2 = (kk+t1) & one;
			/* the involutary permutation PI */
	x1 = x1^t1;		x4=x4^t2;
	a  = x2^t2;		x2=x3^t1;	x3=a;

	}

		/* the output transformation */
	out[1] = mul(x1,z[1][round+1]);
	out[4] = mul(x4,z[4][round+1]);
	out[2] = (x3+z[2][round+1]) & one;
	out[3] = (x2+z[3][round+1]) & one;
}

	/* multiplication using the Low-High algorithm */

uint16_t mul(uint16_t a,uint16_t b) 
{
	int32_t p;
	uint32_t q;
		if(a==0) p=maxim-b;
		else
		if(b==0) p=maxim-a;
		else {
		q=(uint32_t)a*(uint32_t)b;
		p=(q & one) - (q>>16); 
		if(p<=0) p=p+maxim;
		}
	return (uint16_t)(p&one);
}

	/* compute inverse of xin by Euclidean gcd alg. */

uint16_t inv(uint16_t xin)
{
	int32_t n1,n2,q,r,b1,b2,t;
	if(xin==0) b2=0;
	else
	{ n1=maxim; n2=xin; b2=1; b1=0;
		do { r = (n1 % n2); q = (n1-r)/n2;
			 if(r==0) { if(b2<0) b2=maxim+b2; }
			 else { n1=n2; n2=r; t=b2; b2=b1-q*b2; b1=t; }
		   } while (r!=0);
	}
	return (uint16_t)b2;
}

	/* generate encryption subkeys Z's */

void key(uint16_t z[7][10], unsigned char key[nx1]) 
{
	uint16_t S[54];
	uint16_t i,j,r;

	/* get subkeys */
	
	j=0;

	for (i=0;i<54;i++)
	{
		S[i]=(key[j]<<8)+key[j+1];
		j=j+2;
	}


	for(r=1;r<=round+1;r++) 
	  {
		for(j=1;j<7;j++) {z[j][r]=S[6*(r-1)+j-1];}
	  }

		
}

	/* compute decryption subkeys DK's */

void de_key(uint16_t z[7][10],uint16_t dk[7][10])
{
	uint16_t j;
	for(j=1;j<=round+1;j++)
	{
		dk[1][round-j+2] = inv(z[1][j]);
		dk[4][round-j+2] = inv(z[4][j]);
	
		if (j==1 || j==round+1) {
			dk[2][round-j+2] = (fuyi-z[2][j]) & one;
			dk[3][round-j+2] = (fuyi-z[3][j]) & one;
		} else {
			dk[2][round-j+2] = (fuyi-z[3][j]) & one;
			dk[3][round-j+2] = (fuyi-z[2][j]) & one;
		}
	}

	for(j=1;j<=round+1;j++)
	{ dk[5][round+1-j]=z[5][j];
	  dk[6][round+1-j]=z[6][j];
	}
}


void main() 
{
	uint16_t subkeys[7][10], inv_subkeys[7][10];
	
	uint16_t plaintext[5], ciphertext[5];
	
	unsigned char text[33]; /* up to 256 chars for the password */
				/* password can be hexadecimal */
	unsigned char h4[nx1];

    printf("IDEA-832 by Alexander PUKALL 2012 \n IDEA Encryption Cipher with 832-bit subkeys \n");
    printf("Code can be freely use even for commercial software\n");
    printf("Same speed as IDEA-128 but with 832-bit keys\n\n");
       
    /* The key creation procedure is slow, it only needs to be done once */
    /* as long as the user does not change the key. You can encrypt and decrypt */
    /* as many blocks as you want without having to hash the key again. */
    /* init(); hashing(text,length);  end(h4); -> only once */
    /* key(subkeys, h4); and de_key(subkeys,inv_subkeys); -> only once too */
    

	/* EXAMPLE 1 */
	
	init();

	strcpy((char *) text,"My secret password!0123456789abc");

	hashing(text, 32);
	end(h4); /* h4 = 864-bit key from hash "My secret password!0123456789abc */
	         /* 864 bits but only 832 used -> 52 * 16-bit subkeys */
    
	key(subkeys, h4);		/* generate encryption subkeys */
	de_key(subkeys,inv_subkeys);	/* compute decryption subkeys */

	plaintext[1]=0xFEFE; /* 0xFEFEFEFEFEFEFEFE IDEA block plaintext */
	plaintext[2]=0xFEFE;
	plaintext[3]=0xFEFE;
	plaintext[4]=0xFEFE;
	
	printf("Key 1:%s\n",text);
	printf("Plaintext  1 :  %0.4X%0.4X%0.4X%0.4X\n",
	       plaintext[1],plaintext[2],plaintext[3],plaintext[4]);

	cip(plaintext,ciphertext,subkeys);	/* encipher with subkeys */
 
	printf("Ciphertext 1 :  %0.4X%0.4X%0.4X%0.4X\n",
	       ciphertext[1],ciphertext[2],ciphertext[3],ciphertext[4]);

	cip(ciphertext,plaintext,inv_subkeys);	/* decipher with inv_subkeys */

	printf("Decrypted  1 :  %0.4X%0.4X%0.4X%0.4X\n",
		plaintext[1],plaintext[2],plaintext[3],plaintext[4]);
		
	/* EXAMPLE 2 */
	
	init();

	strcpy((char *) text,"My secret password!0123456789ABC");

	hashing(text, 32);
	end(h4); /* h4 = 864-bit key from hash "My secret password!0123456789ABC */
		 /* 864 bits but only 832 used -> 52 * 16-bit subkeys */
    
	key(subkeys, h4);		/* generate encryption subkeys */
	de_key(subkeys,inv_subkeys);	/* compute decryption subkeys */
	
	plaintext[1]=0x0000; /* 0x0000000000000000 IDEA block plaintext */
	plaintext[2]=0x0000;
	plaintext[3]=0x0000;
	plaintext[4]=0x0000;
	
	printf("\nKey 2:%s\n",text);
	printf("Plaintext  2 :  %0.4X%0.4X%0.4X%0.4X\n",
	       plaintext[1],plaintext[2],plaintext[3],plaintext[4]);

	cip(plaintext,ciphertext,subkeys);	/* encipher with subkeys */
 
	printf("Ciphertext 2 :  %0.4X%0.4X%0.4X%0.4X\n",
	       ciphertext[1],ciphertext[2],ciphertext[3],ciphertext[4]);

	cip(ciphertext,plaintext,inv_subkeys);	/* decipher with inv_subkeys */

	printf("Decrypted  2 :  %0.4X%0.4X%0.4X%0.4X\n",
		plaintext[1],plaintext[2],plaintext[3],plaintext[4]);
	
	/* EXAMPLE 3 */
	
	init();

	strcpy((char *) text,"My secret password!0123456789abZ");

	hashing(text, 32);
	end(h4); /* h4 = 864-bit key from hash "My secret password!0123456789abZ */
		 /* 864 bits but only 832 used -> 52 * 16-bit subkeys */
    
	key(subkeys, h4);		/* generate encryption subkeys */
	de_key(subkeys,inv_subkeys);	/* compute decryption subkeys */
	
	plaintext[1]=0x0000; /* 0x0000000000000001 IDEA block plaintext */
	plaintext[2]=0x0000;
	plaintext[3]=0x0000;
	plaintext[4]=0x0001;
	
	printf("\nKey 3:%s\n",text);	
	printf("Plaintext  3 :  %0.4X%0.4X%0.4X%0.4X\n",
	       plaintext[1],plaintext[2],plaintext[3],plaintext[4]);

	cip(plaintext,ciphertext,subkeys);	/* encipher with subkeys */
 
	printf("Ciphertext 3 :  %0.4X%0.4X%0.4X%0.4X\n",
	       ciphertext[1],ciphertext[2],ciphertext[3],ciphertext[4]);

	cip(ciphertext,plaintext,inv_subkeys);	/* decipher with inv_subkeys */

	printf("Decrypted  3 :  %0.4X%0.4X%0.4X%0.4X\n",
		plaintext[1],plaintext[2],plaintext[3],plaintext[4]);

}

/*
 
Key 1:My secret password!0123456789abc
Plaintext  1 :  FEFEFEFEFEFEFEFE
Ciphertext 1 :  4964E2E65E18BE31
Decrypted  1 :  FEFEFEFEFEFEFEFE

Key 2:My secret password!0123456789ABC
Plaintext  2 :  0000000000000000
Ciphertext 2 :  EFA5364A386ABCFB
Decrypted  2 :  0000000000000000

Key 3:My secret password!0123456789abZ
Plaintext  3 :  0000000000000001
Ciphertext 3 :  FEE468CDA198C2EC
Decrypted  3 :  0000000000000001

*/
