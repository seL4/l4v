#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

NONISA_CPARSER_PFX := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))

ifndef NONISA_CPARSER_INCLUDED

NONISA_CPARSER_INCLUDED=true

.PHONY: tools_all
tools_all: $(NONISA_CPARSER_PFX)/tools/mllex/mllex $(NONISA_CPARSER_PFX)/tools/mlyacc/mlyacc

all: tools_all

include $(NONISA_CPARSER_PFX)/globalmakevars
include $(NONISA_CPARSER_PFX)/tools/mllex/Makefile
include $(NONISA_CPARSER_PFX)/tools/mlyacc/Makefile

MLYACC=$(MLYACC_PFX)/mlyacc
RUN_MLYACC=$(TOOLRUN_PFX)$(MLYACC)

%.lex.sml: %.lex $(MLLEX)
	$(RUN_MLLEX) $<

%.grm.sml %.grm.sig: %.grm $(MLYACC)
	$(RUN_MLYACC) $<

GRAMMAR_PRODUCTS = StrictC.lex.sml StrictC.grm.sig StrictC.grm.sml

c-parser-deps: $(GRAMMAR_PRODUCTS)

.PHONY: c-parser-deps



endif
