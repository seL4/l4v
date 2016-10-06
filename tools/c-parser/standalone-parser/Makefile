#
# Copyright 2016, Data61, CSIRO
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(DATA61_BSD)
#

# note this makefile will not work entirely correctly if invoked in the local
# directory; make really needs to be invoked in the parent directory, or
# further up still

STP_PFX := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))

ISABELLE_HOME ?= $(STP_PFX)/../../../isabelle

ifndef STP_INCLUDED
STP_INCLUDED=true

ARM_DIR=$(STP_PFX)/ARM
F64_DIR=$(STP_PFX)/FAKE64
ARCH_DIRS=$(ARM_DIR) $(F64_DIR)

STPARSER_ARM=$(ARM_DIR)/c-parser
STPARSER_F64=$(F64_DIR)/c-parser
STPARSERS=$(STPARSER_ARM) $(STPARSER_F64)

TOKENIZER_ARM=$(ARM_DIR)/tokenizer
TOKENIZER_F64=$(F64_DIR)/tokenizer
TOKENIZERS=$(TOKENIZER_ARM) $(TOKENIZER_F64)

.PHONY: all cparser_tools stp_all standalone-cparser standalone-tokenizer

all: stp_all

standalone-cparser stp_all: $(STPARSERS)
standalone-tokenizer stp_all: $(TOKENIZERS)

include $(STP_PFX)/../Makefile

STP_CLEAN_TARGETS := $(STPARSERS) $(TOKENIZERS) $(STP_PFX)/c-parser.o $(STP_PFX)/table.ML

$(STP_PFX)/table.ML: $(ISABELLE_HOME)/src/Pure/General/table.ML
	sed -e '/ML.pretty-printing/,/final.declarations/d' < $< > $@

$(ARCH_DIRS):
	mkdir -p $@


ifeq ($(SML_COMPILER),mlton)
#
# compilation if the compiler is mlton
#

ARM_MLB_PATH := -mlb-path-var 'L4V_ARCH ARM'
F64_MLB_PATH := -mlb-path-var 'L4V_ARCH FAKE64'

PARSER_DEPS_ARM := $(shell mlton $(ARM_MLB_PATH) -stop f $(STP_PFX)/c-parser.mlb)
PARSER_DEPS_F64 := $(shell mlton $(F64_MLB_PATH) -stop f $(STP_PFX)/c-parser.mlb)

TOKENIZER_DEPS_ARM := $(shell mlton $(ARM_MLB_PATH) -stop f $(STP_PFX)/tokenizer.mlb)
TOKENIZER_DEPS_F64 := $(shell mlton $(F64_MLB_PATH) -stop f $(STP_PFX)/tokenizer.mlb)


$(STPARSER_ARM): $(PARSER_DEPS_ARM) | $(ARM_DIR)
	mlton $(ARM_MLB_PATH) -output $@ $<

$(STPARSER_F64): $(PARSER_DEPS_F64) | $(F64_DIR)
	mlton $(F64_MLB_PATH) -output $@ $<

$(TOKENIZER_ARM): $(TOKENIZER_DEPS_ARM) | $(ARM_DIR)
	mlton $(ARM_MLB_PATH) -output $@ $<

$(TOKENIZER_F64): $(TOKENIZER_DEPS_F64) | $(F64_DIR)
	mlton $(F64_MLB_PATH) -output $@ $<


else ifeq ($(SML_COMPILER),poly)
#
# compilation with polyml may be bit-rotted
#

PARSER0_DEPS := $(shell perl -e 'use Cwd "abs_path"; while (<>) { if (/ml$$|sig$$/i && !/^ *mlton/) { tr/ //d; print abs_path("$(STP_PFX)/$$_"); }}' < $(STP_PFX)/c-parser.mlb)
PARSER_DEPS := $(PARSER0_DEPS) $(realpath $(STP_PFX)/c-parser.mlb) $(STP_PFX)/table.ML

TOKENIZER0_DEPS := $(shell perl -e 'use Cwd "abs_path"; while (<>) { if (/ml$$|sig$$/i && !/^ *mlton/) { tr/ //d; print abs_path("$(STP_PFX)/$$_"); }}' < $(STP_PFX)/tokenizer.mlb)
TOKENIZER_DEPS := $(TOKENIZER0_DEPS) $(realpath $(STP_PFX)/tokenzier.mlb) $(STP_PFX)/table.ML

$(STPARSER): $(STP_PFX)/c-parser.o $(LIBPOLYML)
	$(POLYCC) -o $@ $<

$(STP_PFX)/c-parser.o: $(STP_PFX)/poly-cparser.ML $(PARSER_DEPS)
	STP_PFX=$(STP_PFX) $(POLY) < $<

$(STP_PFX)/tokenizer: $(STP_PFX)/tokenizer.o $(LIBPOLYML)
	$(POLYCC) -o $@ $<

$(STP_PFX)/tokenizer.o: $(STP_PFX)/poly-tokenizer.ML $(TOKENIZER_DEPS)
	STP_PFX=$(STP_PFX) $(POLY) < $<


.PHONY: stp_deps
stp_deps:
	@echo $(PARSER_DEPS)

else
$(error Can only cope with SML_COMPILER as "poly" or "mlton"; got $(SML_COMPILER))

endif


clean: stp_clean

stp_clean:
	-/bin/rm -f $(STP_CLEAN_TARGETS)

endif
