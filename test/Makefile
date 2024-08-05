# -----------------------------------------------------------------------------

CC      ?= clang
CFLAGS  ?= -O3 -Wall -Wextra -Wpedantic -Wvla -Werror -std=c99 \
	         -Wundef -Wshadow -Wcast-align -Wpointer-arith -Wmissing-prototypes \
	         -fstrict-aliasing -fno-common -pipe -g

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
# test vars

BIN      ?= bin
COMMON   := common
SRC      := ../src
EXT      := ../ext

FILTER  ?= $(SRC)/crypto_%
EXCLUDE ?=
JASMIN_IMPLEMENTATIONS   ?= $(filter $(FILTER), $(filter-out $(EXCLUDE), $(sort $(dir $(shell find $(SRC) -name '*.jazz')))))
ASSEMBLY_IMPLEMENTATIONS ?= $(subst .jazz,.s,$(filter $(FILTER), $(filter-out $(EXCLUDE), $(sort $(shell find $(SRC) -name '*.jazz')))))

FILTER_TEST  :=%
TESTS_NAMES  :=$(filter $(FILTER_TEST),printparams safetyparams functest memory checksumsmall checksumbig)

TESTS_DIR    := $(subst $(SRC),$(BIN),$(JASMIN_IMPLEMENTATIONS))
TESTS_BIN    := $(foreach TEST, $(TESTS_NAMES),$(addsuffix $(TEST),$(TESTS_DIR)))
TESTS_OUT    := $(addsuffix .out, $(TESTS_BIN))
TESTS_STDOUT := $(addsuffix .stdout, $(TESTS_BIN))

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
DEFINE      ?=
DEFINE_NS    = -DJADE_NAMESPACE=$(NS_UPPERCASE) -DJADE_NAMESPACE_LC=$(NS_LOWERCASE)
INCLUDES     = -I$(REL_IMPLEMENTATION_DIR)/include/ -I$(COMMON)/ -Iinclude/
RANDOMBYTES ?= $(COMMON)/notrandombytes.c

TEST_COMPILE = ($(CC) $(CFLAGS) -o $@ $(DEFINE) $(DEFINE_NS) $(INCLUDES) crypto_$(OP_LOWERCASE)/$(@F).c $(ASSEMBLY_FILE) $(RANDOMBYTES)) $(CI_CMD)


# -----------------------------------------------------------------------------
# setting the default rule as 'all'

default: all


# -----------------------------------------------------------------------------
# compile tests

compile: $(TESTS_BIN)

$(TESTS_BIN): $(ASSEMBLY_IMPLEMENTATIONS)
	mkdir -p $(CI_DIR)
	($(TEST_COMPILE)) || !(($(FAIL_ON_ERROR)))

$(ASSEMBLY_IMPLEMENTATIONS):
	$(MAKE) -C $(@D) $(@F) || !(($(FAIL_ON_ERROR)))


# -----------------------------------------------------------------------------
# run tests

run: $(TESTS_OUT)

$(TESTS_OUT):
%memory.out: %memory
	((valgrind --leak-check=full --error-exitcode=1 --log-file=$@ ./$*memory) $(CI_CMD)) || !(($(FAIL_ON_ERROR)))

%.out: %
	((cd $(dir $*) && ./$(notdir $*) > $(notdir $*).out) $(CI_CMD)) || !(($(FAIL_ON_ERROR)))

run-stdout: $(TESTS_STDOUT)
$(TESTS_STDOUT):
%memory.stdout: %memory
	((valgrind --leak-check=full --error-exitcode=1 ./$*memory) $(CI_CMD)) || !(($(FAIL_ON_ERROR)))

%.stdout: %
	((cd $(dir $*) && ./$(notdir $*) && echo) $(CI_CMD)) || !(($(FAIL_ON_ERROR)))


# -----------------------------------------------------------------------------
# reporter

LOGS ?= formosa25519-logs-test.tar.gz
JLOG := ./../scripts/reporter/jlog
JCHK := ./../scripts/reporter/checksumsok

CI_ERROR_FILES := $(shell test -d $(BIN) && find $(BIN) -name '*.error')
CI_ALL_FILES   := $(shell test -d $(BIN) && find $(BIN) -name '*.log') $(CI_ERROR_FILES)

.PHONY: reporter logs $(LOGS) err

reporter:
	$(JLOG) "Compilation status (*.jazz -> *.s)" src/ *.s $(CI_REMOVE_OK_LOGS)
	@for type in $(TESTS_NAMES); do \
		$(JLOG) "Tests compilation status - $$type" test/$(BIN) $$type $(CI_REMOVE_OK_LOGS); \
		$(JLOG) "Tests execution status - $$type" test/$(BIN) $$type.out $(CI_REMOVE_OK_LOGS); \
	done
	$(JCHK)
	$(JLOG) "Checksums status" test/$(BIN) checksum*.ok $(CI_REMOVE_OK_LOGS);

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
	$(MAKE) run
	$(MAKE) reporter
	$(MAKE) err


# --------------------------------------------------------------------
.PHONY: clean distclean

clean:
	rm -fr $(BIN) $(LOGS)

distclean: clean
	$(MAKE) -C $(SRC) clean


# --------------------------------------------------------------------
debug-print-variables:
	@echo ""
	@echo "Test variables:\n"
	@echo "  BIN: $(BIN)\n"
	@echo "  COMMON: $(COMMON)\n"
	@echo "  SRC: $(SRC)\n"
	@echo "  EXT: $(EXT)\n"
	@echo "  FILTER: $(FILTER)\n"
	@echo "  EXCLUDE: $(EXCLUDE)\n"
	@echo "  JASMIN_IMPLEMENTATIONS: $(JASMIN_IMPLEMENTATIONS)\n\n"
	@echo "  ASSEMBLY_IMPLEMENTATIONS: $(ASSEMBLY_IMPLEMENTATIONS)\n\n"
	@echo "  FILTER_TEST: $(FILTER_TEST)\n"
	@echo "  TESTS_NAMES: $(TESTS_NAMES)\n\n"
	@echo "  TESTS_DIR: $(TESTS_DIR)\n\n" 
	@echo "  TESTS_BIN: $(TESTS_BIN)\n\n" 
	@echo "  TESTS_OUT: $(TESTS_OUT)\n\n"
	@echo "  TESTS_STDOUT: $(TESTS_STDOUT)\n\n" 

