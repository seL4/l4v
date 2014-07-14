#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

MLYACC_PFX := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))

ifndef MLYACC_INCLUDED
MLYACC_INCLUDED=true

all: $(MLYACC_PFX)/mlyacc

include $(MLYACC_PFX)/../../globalmakevars
include $(MLYACC_PFX)/../mllex/Makefile

$(MLYACC_PFX)/src/yacc.lex.sml: $(MLYACC_PFX)/src/yacc.lex $(MLLEX)
	$(RUN_MLLEX) $<

ifeq ($(SML_COMPILER),mlton)
#
# Compilation if the compiler is mlton
#
MLTON_DEPS := $(shell mlton -stop f $(MLYACC_PFX)/mlyacc.mlb)

$(MLYACC_PFX)/mlyacc: $(MLTON_DEPS)
	mlton $<

else ifeq ($(SML_COMPILER),poly)
#
# Compilation if the compiler is Poly/ML
#

#
# set POLY_CC_FLAGS to -m32 if you are using 32bit poly on a 64bit architecture


$(MLYACC_PFX)/mlyacc: $(MLYACC_PFX)/mlyacc0
	/bin/echo "#! /bin/sh" > $@
	/bin/echo >> $@
	/bin/echo "$(TOOLRUN_PFX)$< \"\$$@\"" >> $@
	chmod +x $@

$(MLYACC_PFX)/mlyacc0: $(MLYACC_PFX)/mlyacc.o
	$(POLYCC) -o $@ $<

MLY_SRCDEPS0 = absyn-sig absyn core coreutils grammar graph hdr lalr link look \
           mklrtable mkprstruct parse poly-main shrink sigs utils verbose \
	   yacc
MLY_SRCDEPS1 = $(patsubst %,%.ML,$(MLY_SRCDEPS0)) yacc-grm-sig.sml yacc-grm.sml yacc.lex.sml
MLY_SRCDEPS = $(patsubst %,src/%,$(MLY_SRCDEPS1))

MLY_LIBDEPS0 = base-sig join lrtable parser2 stream
MLY_LIBDEPS = $(patsubst %,mlyacclib/MLY_%.ML,$(LIBDEPS0))

MLY_DEPS = $(patsubst %,$(MLYACC_PFX)/%,$(MLY_LIBDEPS) $(MLY_SRCDEPS))

$(MLYACC_PFX)/mlyacc.o: $(MLYACC_PFX)/poly-mlyacc.ML $(MLY_DEPS)
	MLYACC_PFX=$(MLYACC_PFX) $(SETDYLIB) $(POLY) < $<

else
$(error Can only cope with SML_COMPILER as "poly" or "mlton")

endif

#
# clean targets
#
.PHONY: mlyacc_clean

clean: mlyacc_clean

cparser_clean: mlyacc_clean

mlyacc_clean:
	-/bin/rm -f $(MLYACC_PFX)/mlyacc.o $(MLYACC_PFX)/mlyacc $(MLYACC_PFX)/src/yacc.lex.sml

endif
