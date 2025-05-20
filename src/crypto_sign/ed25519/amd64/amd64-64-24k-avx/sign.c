/*
Interface for Supercop
*/

#include "crypto_sign.h"
#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include "randombytes.h"

extern void get_ed25519_keygen(const uint8_t* sk, const uint8_t* pk);
extern void get_ed25519_sig(const uint8_t* sk, const uint8_t* m, uint64_t msg_len, const uint8_t* sig);
extern uint64_t get_ed25519_vrfy(const uint8_t* sig, const uint8_t* pk, const uint8_t* m, uint64_t msg_len);

int crypto_sign_keypair(unsigned char *pk,unsigned char *sk)
{
  get_ed25519_keygen(sk, pk);
  memmove(sk + 32,pk,32);

  return 0;
}

int crypto_sign(
    unsigned char *sm,unsigned long long *smlen,
    const unsigned char *m,unsigned long long mlen,
    const unsigned char *sk
    )
{	
	uint8_t sig[64];
	uint8_t sk_copy[32];
	memmove(sk_copy,sk,32);
  
  get_ed25519_sig(sk_copy, m, mlen, sig);
  *smlen = mlen + 64;

  memmove(sm + 64,m,mlen);
  memmove(sm, sig, 64);
	
  return 0;
}

int crypto_sign_open(
  unsigned char *m,unsigned long long *mlen,
  const unsigned char *sm,unsigned long long smlen,
  const unsigned char *pk
)
{	
	uint8_t sig[64];
	uint8_t pk_copy[32];
	uint64_t msg_len = smlen - 64;
	uint64_t res;
	
	memmove(pk_copy,pk,32);
	memmove(sig,sm,64);
	memmove(m,sm+64,msg_len);
	memset(m + smlen - 64,0,64);
	
	res = get_ed25519_vrfy(sig, pk_copy, m, msg_len);
  if (res == 0) {
    *mlen = msg_len;
    return 0;
  }
  else {
  	*mlen = -1;
  	memset(m,0,smlen);
  	return -1;
  }
}
