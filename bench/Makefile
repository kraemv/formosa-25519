# -----------------------------------------------------------------------------

CC      ?= clang
CFLAGS  ?= -Wall -Wno-unused-function -Wno-unused-parameter -O3 -march=native \
           -O3 -fomit-frame-pointer -fwrapv -fPIC -fPIE -Wextra -Wpedantic \
           -Wvla -Werror -std=c99 -Wundef -Wshadow -Wcast-align \
           -Wpointer-arith -Wmissing-prototypes -fstrict-aliasing -fno-common \
           -pipe

# -----------------------------------------------------------------------------
# ci vars

CI ?= 0
CI_REMOVE_OK_LOGS ?= "1"

CI_DIR = $(@D)
CI_CMD =
ifeq ($(CI),1)
CI_DIR = $(@D)/.ci
CI_CMD = 2> $(CI_DIR)/$(@F).log && rm -f $(CI_DIR)/$(@F).error || \
             (echo $$? | cat - $(CI_DIR)/$(@F).log > $(CI_DIR)/$(@F).error && \
              rm -f $(CI_DIR)/$(@F).log && \
              exit 127 \
             )
endif

export CI

FAIL_ON_ERROR ?= 0

# -----------------------------------------------------------------------------
# bench vars

BIN      ?= bin
COMMON   := common
SRC      := ../src
EXT      := ../ext
SSBD     := $(abspath ../submodules/ssbd-tools/ssbd-exec)

FILTER  ?= $(SRC)/crypto_%
EXCLUDE ?=
JASMIN_IMPLEMENTATIONS   ?= $(filter $(FILTER), $(filter-out $(EXCLUDE), $(sort $(dir $(shell find $(SRC) -name '*.jazz')))))
ASSEMBLY_IMPLEMENTATIONS ?= $(subst .jazz,.s,$(filter $(FILTER), $(filter-out $(EXCLUDE), $(sort $(shell find $(SRC) -name '*.jazz')))))

FILTER_BENCH :=%
BENCHS_NAMES  :=$(filter $(FILTER_BENCH),bench)

BENCHS_DIR         := $(subst $(SRC),$(BIN),$(JASMIN_IMPLEMENTATIONS))
BENCHS_BIN         := $(foreach BENCH, $(BENCHS_NAMES),$(addsuffix $(BENCH),$(BENCHS_DIR)))
BENCHS_OUT         := $(addsuffix .out, $(BENCHS_BIN))
BENCHS_SSBD_OUT    := $(addsuffix .ssbd.out, $(BENCHS_BIN))
BENCHS_STDOUT      := $(addsuffix .stdout, $(BENCHS_BIN))
BENCHS_SSBD_STDOUT := $(addsuffix .ssbd.stdout, $(BENCHS_BIN))

# -----------------------------------------------------------------------------
# compilation vars

# operation
OP_LOWERCASE = $(subst crypto_,,$(word 1, $(subst /, , $(subst $(BIN)/,,$(@D)))))
OP_UPPERCASE = $(shell echo $(OP_LOWERCASE) | tr a-z A-Z)

# namespace
NS_BASENAME  = $(subst crypto_$(OP_LOWERCASE)_,,$(subst -,_,$(subst /,_,$(subst $(BIN)/,,$(@D)))))
NS_LOWERCASE = jade_$(OP_LOWERCASE)_$(NS_BASENAME)
NS_UPPERCASE = JADE_$(OP_UPPERCASE)_$(NS_BASENAME)

# 
REL_IMPLEMENTATION_DIR = $(subst $(BIN)/,$(SRC)/,$(@D))
ASSEMBLY_FILE = $(REL_IMPLEMENTATION_DIR)/$(OP_LOWERCASE).s

#
DEFINE      ?= -DRUNS=3 -DTIMINGS=10000
DEFINE_NS    = -DJADE_NAMESPACE=$(NS_UPPERCASE) -DJADE_NAMESPACE_LC=$(NS_LOWERCASE)
INCLUDES     = -I$(REL_IMPLEMENTATION_DIR)/include/ -I$(COMMON)/ -Iinclude/

RANDOMBYTES ?= $(EXT)/randombytes/librandombytes.a
RANDOMBYTES_INCLUDE ?= -I$(EXT)/randombytes/

BENCH_COMPILE = ($(CC) $(CFLAGS) -o $@ $(DEFINE) $(DEFINE_NS) $(INCLUDES) $(RANDOMBYTES_INCLUDE) $(COMMON)/crypto_$(OP_LOWERCASE).c $(ASSEMBLY_FILE) $(RANDOMBYTES)) $(CI_CMD)


# -----------------------------------------------------------------------------
# setting the default rule as 'all'

default: all


# -----------------------------------------------------------------------------
# compile benchs

compile: $(BENCHS_BIN) $(SSBD)

$(BENCHS_BIN): $(ASSEMBLY_IMPLEMENTATIONS) | $(RANDOMBYTES)
	mkdir -p $(CI_DIR)
	($(BENCH_COMPILE)) || !(($(FAIL_ON_ERROR)))

$(ASSEMBLY_IMPLEMENTATIONS):
	$(MAKE) -C $(@D) $(@F) || !(($(FAIL_ON_ERROR)))

$(RANDOMBYTES):
	$(MAKE) -C $(@D) $(@F)

$(SSBD):
	$(MAKE) -C $(@D)

# -----------------------------------------------------------------------------
# run benchs
#
# note: %bench.out will never be created: when ./bench is run without arguments
# it creates a series of *.csv files (one for each entrypoint [function] that
# is measured. For instance:
# - bin/crypto_scalarmult/curve25519/amd64/mulx/jade_scalarmult_curve25519_amd64_mulx.csv
# - bin/crypto_scalarmult/curve25519/amd64/mulx/jade_scalarmult_curve25519_amd64_mulx_base.csv
# These files contain the cycle count.
#
# By not creating the %bench.out, file the user is able to run the benchmarks
# as many times as they wish (otherwise, if bench.out existed, make would say
# something like "make: Nothing to be done for 'run'").
# 
# As an additional note, whenever ./bench is run with any argument (argc != 1),
# the cycle count information is printed to the terminal (stdout). Previous
# apply to stdout rules as well.

run: $(BENCHS_OUT)
$(BENCHS_OUT):
%.out: %
	(cd $(dir $@) && ./bench) $(CI_CMD) || !(($(FAIL_ON_ERROR)))

run-stdout: $(BENCHS_STDOUT)
$(BENCHS_STDOUT):
%.stdout: %
	(cd $(dir $@) && ./bench -) $(CI_CMD) || !(($(FAIL_ON_ERROR)))

# -- 
run-ssbd: $(BENCHS_SSBD_OUT)
$(BENCHS_SSBD_OUT): $(SSBD)
%.ssbd.out: % | $(SSBD)
	(cd $(dir $@) && $(SSBD) -p force-disable -- ./bench) $(CI_CMD) || !(($(FAIL_ON_ERROR)))

run-ssbd-stdout: $(BENCHS_SSBD_STDOUT)
$(BENCHS_SSBD_STDOUT):
%.ssbd.stdout: %
	(cd $(dir $@) && $(SSBD) -p force-disable -- ./bench -) $(CI_CMD) || !(($(FAIL_ON_ERROR)))


# -----------------------------------------------------------------------------
# reporter

LOGS ?= libformosa25519-logs-bench.tar.gz
JLOG := ./../scripts/reporter/jlog

CI_ERROR_FILES := $(shell test -d $(BIN) && find $(BIN) -name '*.error')
CI_ALL_FILES   := $(shell test -d $(BIN) && find $(BIN) -name '*.log') $(CI_ERROR_FILES)

.PHONY: reporter logs $(LOGS) err

reporter:
	$(JLOG) "Compilation status (*.jazz -> *.s)" src/ *.s $(CI_REMOVE_OK_LOGS)
	$(JLOG) "Bench compilation status" bench/$(BIN) bench $(CI_REMOVE_OK_LOGS)
	$(JLOG) "Bench execution status" bench/$(BIN) bench.out $(CI_REMOVE_OK_LOGS)

logs: $(LOGS)

$(LOGS):
	@$(JASMIN) -version > notes
ifeq ($(words $(CI_ALL_FILES)),0)
	@echo "There are no logs with warnings or errors. Good job." >> notes
	@tar -zcvf $@ notes
else
	@tar -zcvf $@ notes $(CI_ALL_FILES)
endif
	@rm notes

err:
ifneq ($(words $(CI_ERROR_FILES)),0)
	$(error $(CI_ERROR_FILES))
endif


# -----------------------------------------------------------------------------
# to run 'everything': $ make -j$(nproc) all
.PHONY: all

all: CI=1
all:
	$(MAKE) distclean
	$(MAKE) compile
	$(MAKE) -j1 run
	$(MAKE) reporter
	$(MAKE) err


# --------------------------------------------------------------------
.PHONY: clean distclean

clean:
	rm -fr $(BIN) $(LOGS)

distclean: clean
	$(MAKE) -C $(SRC) clean
	$(MAKE) -C $(dir $(RANDOMBYTES)) clean
	$(MAKE) -C $(dir $(SSBD)) clean


# --------------------------------------------------------------------
debug-print-variables:
	@echo ""
	@echo "Test variables:\n"
	@echo "  BIN: $(BIN)\n"
	@echo "  COMMON: $(COMMON)\n"
	@echo "  SRC: $(SRC)\n"
	@echo "  EXT: $(EXT)\n"
	@echo "  SSBD: $(SSBD)\n"
	@echo "  FILTER: $(FILTER)\n"
	@echo "  EXCLUDE: $(EXCLUDE)\n"
	@echo "  JASMIN_IMPLEMENTATIONS: $(JASMIN_IMPLEMENTATIONS)\n\n"
	@echo "  ASSEMBLY_IMPLEMENTATIONS: $(ASSEMBLY_IMPLEMENTATIONS)\n\n"
	@echo "  FILTER_BENCH: $(FILTER_BENCH)\n"
	@echo "  BENCHS_NAMES: $(BENCHS_NAMES)\n\n"
	@echo "  BENCHS_DIR: $(BENCHS_DIR)\n\n" 
	@echo "  BENCHS_BIN: $(BENCHS_BIN)\n\n" 
	@echo "  BENCHS_OUT: $(BENCHS_OUT)\n\n"
	@echo "  BENCHS_STDOUT: $(BENCHS_STDOUT)\n\n" 

