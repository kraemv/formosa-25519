# -----------------------------------------------------------------------------

ECARGS    ?=
ECJOBS    ?= 1
ECCONF    := tests.config
JASMIN    ?= jasminc
EASYCRYPT ?= easycrypt


# -----------------------------------------------------------------------------

SRC     := $(abspath ../src)
PROOF   := .
FILTER  ?= $(PROOF)/crypto_%
EXCLUDE ?=

EXTRACTED ?= $(shell find $(PROOF) -type f -name "*_s.ec")
EXTRACTED_OUT := $(addsuffix .out, $(EXTRACTED))

ALL ?= $(shell find $(PROOF)/crypto_* -type f -name "*.ec")
ALL_OUT := $(addsuffix .out, $(ALL))


# -----------------------------------------------------------------------------

CI ?= 0
CI_REMOVE_OK_LOGS ?= "1"
CI_GITHUB?=0

CI_DIR =
CI_CMD =
ifeq ($(CI),1)
CI_DIR := .ci
CI_CMD = 2> $(@D)/$(CI_DIR)/$(@F).log && rm -f $(@D)/$(CI_DIR)/$(@F).error || \
             (echo $$? | cat - $(@D)/$(CI_DIR)/$(@F).log > $(@D)/$(CI_DIR)/$(@F).error && \
              rm $(@D)/$(CI_DIR)/$(@F).log && \
              exit 0 \
             )
CI_GITHUB:=1
endif

export CI

FAIL_ON_ERROR ?= 0

# -----------------------------------------------------------------------------
# setting the default rule as 'all'

default: all


# -----------------------------------------------------------------------------
# extract implementations

.PHONY: extract-to-easycrypt

extract-to-easycrypt:
	$(MAKE) -C $(SRC) extract-to-easycrypt


# -----------------------------------------------------------------------------
# check

.PHONY: __phony

check-all: $(ALL_OUT)
check-extracted: $(EXTRACTED_OUT)

$(ALL_OUT):
ifeq ($(CI),1)
	mkdir -p $(@D)/$(CI_DIR)
endif
	($(EASYCRYPT) -R arrays/ -R $(abspath $(@D)/../../)  $(ECARGS) $(subst .out,,$@) > $@) $(CI_CMD) || !(($(FAIL_ON_ERROR)))


# -----------------------------------------------------------------------------
# reporter: this section defines rules for reporting the current implementation
# status

LOGS ?= formosa25519-logs-proof.tar.gz
JLOG := ./../scripts/reporter/jlog

CI_ERROR_FILES := $(shell find $(PROOF) -name '*.error')
CI_ALL_FILES   := $(shell find $(PROOF) -name '*.log') $(CI_ERROR_FILES)

.PHONY: reporter logs $(LOGS) err

reporter:
	$(JLOG) "Extraction from Jasmin to EasyCrypt status" src/ *_s.ec $(CI_REMOVE_OK_LOGS) $(CI_GITHUB)
	$(JLOG) "Checking EasyCrypt - extracted files status" proof/ *_s.ec.out $(CI_REMOVE_OK_LOGS) $(CI_GITHUB)
	$(JLOG) "Checking EasyCrypt - all files status" proof/ *.ec.out $(CI_REMOVE_OK_LOGS) $(CI_GITHUB)

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
	$(MAKE) -C $(SRC) extract-to-easycrypt
	$(MAKE) check-extracted
	$(MAKE) check-all
	$(MAKE) reporter
	$(MAKE) err

# -----------------------------------------------------------------------------
# clean rules

.PHONY: clean distclean

clean:
	rm -f $(LOGS) $(ALL_OUT)
	find . -type d -name ".ci" -exec rm -fr "{}" +
	find . -name "*.eco" -exec rm {} +

distclean: CI=1
distclean: clean
	rm -f $(PROOF)/arrays/*Array*.ec
	find . -name "*_s.ec" -exec rm {} +
	make -C $(SRC)/ distclean

# -----------------------------------------------------------------------------
# debug/print rules: helps to check the effects of FILTER or EXCLUDE

debug-print-variables:
	@echo ""
	@echo "  SRC: $(SRC)\n"
	@echo "  PROOF: $(PROOF)\n"
	@echo "  FILTER: $(FILTER)\n"
	@echo "  EXCLUDE: $(EXCLUDE)\n"
	@echo "  EXTRACTED: $(EXTRACTED)\n"
	@echo "  EXTRACTED_OUT: $(EXTRACTED_OUT)\n"
	@echo "  ALL: $(ALL)\n"
	@echo "  ALL_OUT: $(ALL_OUT)\n"
