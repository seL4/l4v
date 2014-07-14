#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
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
MLTON_DEPS := $(shell mlton -stop f $(MLLEX_PFX)/mllex.mlb)

$(MLLEX): $(MLTON_DEPS)
	mlton $<
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
