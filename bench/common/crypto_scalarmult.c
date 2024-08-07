#include "api.h"
#include "namespace.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

//
#define CRYPTO_BYTES           NAMESPACE(BYTES)
#define CRYPTO_SCALARBYTES     NAMESPACE(SCALARBYTES)
#define CRYPTO_ALGNAME         NAMESPACE(ALGNAME)

#define crypto_scalarmult      JADE_NAMESPACE_LC
#define crypto_scalarmult_base NAMESPACE_LC(base)

#define OP1 2

//

#include "config.h"
#include "cpucycles.c"
#include "printbench.c"
#include "alignedcalloc.c"
#include "benchrandombytes.c"

//

int main(int argc, char**argv)
{
  size_t run, i;
  uint64_t cycles[TIMINGS];
  uint64_t median_runs[OP1][RUNS];

  char *op1_str[] = { xstr(crypto_scalarmult_base,.csv),
                      xstr(crypto_scalarmult,.csv)};

  char *op1_str_short[] = { "scalarmult     ",
                            "scalarmult_base" };

  uint8_t *_m, *m; // CRYPTO_SCALARBYTES
  uint8_t *_n, *n; // CRYPTO_SCALARBYTES
  uint8_t *_p, *p; // CRYPTO_BYTES
  uint8_t *_q, *q; // CRYPTO_BYTES

  pb_init_1(argc, op1_str);

  m = alignedcalloc(&_m, CRYPTO_SCALARBYTES);
  n = alignedcalloc(&_n, CRYPTO_SCALARBYTES);
  p = alignedcalloc(&_p, CRYPTO_BYTES);
  q = alignedcalloc(&_q, CRYPTO_BYTES);

  for(run = 0; run < RUNS; run++)
  {
    benchrandombytes(m, CRYPTO_SCALARBYTES);
    benchrandombytes(n, CRYPTO_SCALARBYTES);

    // scalarmult_base
    for (i = 0; i < TIMINGS; i++)
    { cycles[i] = cpucycles();
      crypto_scalarmult_base(p, m); }
    median_runs[1][run] = cpucycles_median(cycles, TIMINGS);

    // scalarmult
    for (i = 0; i < TIMINGS; i++)
    { cycles[i] = cpucycles();
      crypto_scalarmult(q, n, p); }
    median_runs[0][run] = cpucycles_median(cycles, TIMINGS);
  }

  pb_print_1(argc, median_runs, op1_str, op1_str_short);

  free(_m);
  free(_n);
  free(_p);
  free(_q);

  return 0;
}

