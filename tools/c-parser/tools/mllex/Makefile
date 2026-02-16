#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

MLLEX_PFX := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))

ifndef MLLEX_INCLUDED
MLLEX_INCLUDED=true
MLLEX=$(MLLEX_PFX)/mllex

all: $(MLLEX)

include $(MLLEX_PFX)/../../globalmakevars

RUN_MLLEX=$(TOOLRUN_PFX)$(MLLEX)



ifeq ($(SML_COMPILER),mlton)
#
# Compilation if the compiler is mlton
#
MLTON_DEPS := $(shell $(MLTON) -stop f $(MLLEX_PFX)/mllex.mlb)

$(MLLEX): $(MLTON_DEPS)
	$(MLTON) $<
else ifeq ($(SML_COMPILER),poly)
#
# Compilation if the compiler is Poly/ML
#

#
# set POLY_CC_FLAGS to -m32 if you are using 32bit poly on a 64bit architecture

$(MLLEX): $(MLLEX)0
	/bin/echo "#! /bin/sh" > $@
	/bin/echo >> $@
	/bin/echo "$(TOOLRUN_PFX)$< \"\$$@\"" >> $@
	chmod +x $@


$(MLLEX)0: $(MLLEX_PFX)/mllex.o
	$(POLYCC) -o $@ $<


$(MLLEX_PFX)/mllex.o: $(MLLEX_PFX)/poly-mllex.ML $(MLLEX_PFX)/mllex.ML
	MLLEX_PFX=$(MLLEX_PFX) $(POLY) < $<

else
$(error Can only cope with SML_COMPILER as "poly" or "mlton")


endif

#
# clean targets
#
.PHONY: mllex_clean

clean: mllex_clean
cparser_clean: mllex_clean

mllex_clean:
	-/bin/rm -f $(MLLEX_PFX)/mllex.o $(MLLEX_PFX)/mllex

endif
