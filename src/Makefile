# -----------------------------------------------------------------------------

JASMIN ?= jasminc

# -----------------------------------------------------------------------------

CC      ?= clang
CFLAGS  ?= -O3 -Wall -Wextra -Wpedantic -Wvla -Werror -std=c99 \
	         -Wundef -Wshadow -Wcast-align -Wpointer-arith -Wmissing-prototypes \
	         -fstrict-aliasing -fno-common -pipe
AR      ?= ar
RANLIB  ?= ranlib

# -----------------------------------------------------------------------------

SRC     := .
PROOF   := $(abspath ../proof)
FILTER  ?= $(SRC)/crypto_%
EXCLUDE ?=

JASMIN_IMPLEMENTATIONS ?= $(filter $(FILTER), $(filter-out $(EXCLUDE), $(sort $(dir $(shell find $(SRC) -name '*.jazz')))))

ASSEMBLY_FILES ?= $(shell find $(SRC) -name '*.s')
OBJECT_FILES   := $(ASSEMBLY_FILES:%.s=%.o)
C_HEADER_FILES ?= $(addsuffix include/api.h, $(dir $(ASSEMBLY_FILES)))

# -----------------------------------------------------------------------------
# when CI=1, information about compilation/checking properties of the files
# will be stored under .ci/ folders in the implementations directories. Then
# the user of this Makefile can run 'make CI=1 report' to get a simple report
# of the current status: compilation, safety checking, and sct checking.
CI ?= 0
CI_REMOVE_OK_LOGS ?= "1"

export CI

# -----------------------------------------------------------------------------
# setting the default rule as 'all': compiles, and checks safety and sct for 
# all implementations

default: all

# -----------------------------------------------------------------------------
# compile Jasmin implementations to assembly and create libx25519.a 

.PHONY: libx25519.a libx25519.h $(JASMIN_IMPLEMENTATIONS)

.INTERMEDIATE: $(OBJECT_FILES)

just_compile_jasmin_implementations: $(JASMIN_IMPLEMENTATIONS)

libx25519.a: $(JASMIN_IMPLEMENTATIONS)
	$(MAKE) __libx25519

__libx25519: $(OBJECT_FILES)
	$(AR) -rc libx25519.a $(OBJECT_FILES)
	$(RANLIB) libx25519.a
	echo "" | cat - $(C_HEADER_FILES) > libx25519.h

$(JASMIN_IMPLEMENTATIONS):
	$(MAKE) -C $@

# -----------------------------------------------------------------------------
# safety checking

CHECK_SAFETY ?= $(addsuffix check-safety, $(JASMIN_IMPLEMENTATIONS))

CHECK_SAFETY_TIMEOUT ?= 10m
export CHECK_SAFETY_TIMEOUT

.PHONY: check-safety $(CHECK_SAFETY)

check-safety: $(CHECK_SAFETY)

$(CHECK_SAFETY):
	$(MAKE) -C $(@D) $(@F)

# -----------------------------------------------------------------------------
# speculative "constant-time" checking / "secret-independence" checking

CHECK_SCT ?= $(addsuffix check-sct, $(JASMIN_IMPLEMENTATIONS))

.PHONY: check-sct $(CHECK_SCT)

check-sct: $(CHECK_SCT)

$(CHECK_SCT):
	$(MAKE) -C $(@D) $(@F)

# -----------------------------------------------------------------------------
# extraction to easycrypt (updates proof/ directory)

EXTRACT_TO_EASYCRYPT ?= $(addsuffix extract-to-easycrypt, $(JASMIN_IMPLEMENTATIONS))

.PHONY: extract-to-easycrypt $(EXTRACT_TO_EASYCRYPT)

extract-to-easycrypt: $(EXTRACT_TO_EASYCRYPT)

$(EXTRACT_TO_EASYCRYPT):
	$(MAKE) -C $(@D) $(@F)

# -----------------------------------------------------------------------------
# reporter: this section defines rules for reporting the current implementation
# status

LOGS ?= libx25519-logs-src.tar.gz
JLOG := ./../scripts/reporter/jlog

CI_ERROR_FILES := $(shell find $(SRC) -name '*.error')
CI_ALL_FILES   := $(shell find $(SRC) -name '*.log') $(CI_ERROR_FILES)

.PHONY: reporter logs $(LOGS) err

reporter:
	$(JLOG) "Safety checking status" src/ *.safety $(CI_REMOVE_OK_LOGS)
	$(JLOG) "Speculative constant-time status" src/ *.sct $(CI_REMOVE_OK_LOGS)
	$(JLOG) "Extraction to EasyCrypt status" src/ *.ec $(CI_REMOVE_OK_LOGS)
	$(JLOG) "Compilation status (*.jazz -> *.s)" src/ *.s $(CI_REMOVE_OK_LOGS)

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
	$(MAKE) check-safety
	$(MAKE) check-sct
	$(MAKE) extract-to-easycrypt
	$(MAKE) libx25519.a
	$(MAKE) libx25519.h
	$(MAKE) reporter
	$(MAKE) err

# -----------------------------------------------------------------------------
# clean rules

.PHONY: clean distclean

clean:
	rm -f libx25519.a libx25519.h
	rm -f $(LOGS)
	for i in $(JASMIN_IMPLEMENTATIONS); do $(MAKE) -C $$i clean; done
	rm -f $(PROOF)/arrays/*Array*.ec

distclean: clean

# -----------------------------------------------------------------------------
# debug/print rules: helps to check the effects of FILTER or EXCLUDE

debug-print-variables:
	@echo ""
	@echo "  SRC: $(SRC)\n"
	@echo "  PROOF: $(PROOF)\n"
	@echo "  FILTER: $(FILTER)\n"
	@echo "  EXCLUDE: $(EXCLUDE)\n"
	@echo "  JASMIN_IMPLEMENTATIONS: $(JASMIN_IMPLEMENTATIONS)\n"
	
	@echo "  ASSEMBLY_FILES: $(ASSEMBLY_FILES)\n"
	@echo "  OBJECT_FILES: $(OBJECT_FILES)\n"
	@echo "  C_HEADER_FILES: $(C_HEADER_FILES)\n"
	
	@echo "  CHECK_SAFETY: $(CHECK_SAFETY)\n"
	@echo "  CHECK_SCT: $(CHECK_SCT)\n"
	@echo "  EXTRACT_TO_EASYCRYPT: $(EXTRACT_TO_EASYCRYPT)\n"
	
	@echo "  LOGS: $(LOGS)\n"

