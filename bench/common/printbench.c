#ifndef PRINTBENCH_C
#define PRINTBENCH_C

#include <inttypes.h>
#include <stdlib.h>
#include <stdio.h>

static void pb_init_1(int argc, char *op_str[])
{
  int op;
  FILE *f;

  if(argc == 1)
  { for (op = 0; op < OP1; op++)
    { f = fopen(op_str[op], "w");
      fclose(f);
    }
  }
}

static void pb_print_1(
  int argc,
  uint64_t results[OP1][RUNS],
  char *op_str[],
  char *op_str_short[])
{
  int op, run;
  FILE *f;

  // print to file
  f = stdout;
  for (op = 0; op < OP1; op++)
  { if(argc == 1) { f = fopen(op_str[op], "a"); }
    else          { fprintf(f, "%s, ", op_str_short[op]); }

    for(run = 0; run < (RUNS-1); run += 1)
    { fprintf(f, "%" PRIu64 ", ", results[op][run]); }
    fprintf(f, "%" PRIu64 "\n", results[op][RUNS-1]);

    if(argc == 1) { fclose(f); }
  }
}

#endif
