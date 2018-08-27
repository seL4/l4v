#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

ifndef CPARSER_PFX
CPARSER_PFX := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))
endif

ifndef CPARSER_INCLUDED

CPARSER_INCLUDED=true

.PHONY: all
all: CParser cparser_test cparser_tools

include $(CPARSER_PFX)/globalmakevars
include $(CPARSER_PFX)/standalone-parser/Makefile
include $(CPARSER_PFX)/tools/mllex/Makefile
include $(CPARSER_PFX)/tools/mlyacc/Makefile

.PHONY: cparser_tools
cparser_tools: stp_all

# Setup heaps we use.
HEAPS += Simpl-VCG CParser

# l4v root dir. Will be ".." if this is a separate C parser release.
L4V_ROOT_DIR = ../..

# Path to Isabelle
ifndef ISABELLE_HOME
  export ISABELLE_HOME=${L4V_ROOT_DIR}/isabelle
endif
ifndef ISABELLE
  export ISABELLE=${ISABELLE_HOME}/bin/isabelle
endif

# Setup rules for the heaps.
$(HEAPS): .FORCE
	$(ISABELLE) build -d $(L4V_ROOT_DIR) -b -v $@
.PHONY: $(HEAPS)

# Generate lexer and parser files for CParser
CParser: c-parser-deps

#
# cparser_test: Execute a large number of testcases in the "testfiles"
# directory.
#
# We dynamically generate a ROOT file containing all the test files, and
# then build it using Isabelle.
#
cparser_test: c-parser-deps testfiles/$(L4V_ARCH)/ROOT .FORCE
	$(ISABELLE) build -d $(L4V_ROOT_DIR) -d testfiles/$(L4V_ARCH) -b -v CParserTest
testfiles/$(L4V_ARCH)/ROOT: testfiles testfiles/*.c testfiles/*.thy ../../misc/scripts/gen_isabelle_root.py
	python ../../misc/scripts/gen_isabelle_root.py -i testfiles -i testfiles/$(L4V_ARCH) -o testfiles/$(L4V_ARCH)/ROOT -s CParserTest -b CParser
all_tests_$(L4V_ARCH).thy: testfiles testfiles/*.c ../../misc/scripts/gen_isabelle_root.py
	python ../../misc/scripts/gen_isabelle_root.py -T -o $@ -b CParser -i testfiles -i testfiles/$(L4V_ARCH)


.PHONY: tools_all
tools_all: $(CPARSER_PFX)/tools/mllex/mllex $(CPARSER_PFX)/tools/mlyacc/mlyacc

MLYACC=$(MLYACC_PFX)/mlyacc
RUN_MLYACC=$(TOOLRUN_PFX)$(MLYACC)

%.lex.sml: %.lex $(MLLEX)
	$(RUN_MLLEX) $<

%.grm.sml %.grm.sig: %.grm $(MLYACC)
	$(RUN_MLYACC) $<

GRAMMAR_PRODUCTS = StrictC.lex.sml StrictC.grm.sig StrictC.grm.sml

.PHONY: c-parser-deps
c-parser-deps: $(GRAMMAR_PRODUCTS)

# Regression targets.
report-regression: .FORCE
	@echo CParser cparser_test cparser_tools

.PHONY: .FORCE
.FORCE:

endif
