#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

# note this makefile will not work entirely correctly if invoked in the local
# directory; make really needs to be invoked in the parent directory, or
# further up still

STP_PFX := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))

ISABELLE_HOME ?= $(STP_PFX)/../../isabelle

ifndef STP_INCLUDED
STP_INCLUDED=true

STPARSER=$(STP_PFX)/c-parser

.PHONY: stp_all standalone-cparser standalone-tokenizer
standalone-cparser stp_all: $(STPARSER)
standalone-tokenizer: $(STP_PFX)/tokenizer

all: stp_all

include $(STP_PFX)/../Makefile

STP_CLEAN_TARGETS := $(STP_PFX)/c-parser $(STP_PFX)/c-parser.o $(STP_PFX)/table.ML $(STP_PFX)/tokenizer

$(STP_PFX)/table.ML: $(ISABELLE_HOME)/src/Pure/General/table.ML
	sed -e '/ML.pretty-printing/,/final.declarations/d' < $< > $@


ifeq ($(SML_COMPILER),mlton)
#
# compilation if the compiler is mlton
#
PARSER_DEPS := $(shell mlton -stop f $(STP_PFX)/c-parser.mlb)
TOKENIZER_DEPS := $(shell mlton -stop f $(STP_PFX)/tokenizer.mlb)


$(STPARSER): $(PARSER_DEPS)
	mlton $<

$(STP_PFX)/tokenizer: $(TOKENIZER_DEPS)
	mlton $<

else ifeq ($(SML_COMPILER),poly)

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
