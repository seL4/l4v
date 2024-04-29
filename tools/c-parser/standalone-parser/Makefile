#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

# note this makefile will not work entirely correctly if invoked in the local
# directory; make really needs to be invoked in the parent directory, or
# further up still

STP_PFX := $(realpath $(dir $(lastword $(MAKEFILE_LIST))))

ISABELLE_HOME ?= $(STP_PFX)/../../../isabelle

ifndef STP_INCLUDED
STP_INCLUDED=true

ARM_DIR=$(STP_PFX)/ARM
ARM_HYP_DIR=$(STP_PFX)/ARM_HYP
AARCH64_DIR=$(STP_PFX)/AARCH64
X64_DIR=$(STP_PFX)/X64
RISCV64_DIR=$(STP_PFX)/RISCV64
ARCH_DIRS=$(ARM_DIR) $(ARM_HYP_DIR) $(AARCH64_DIR) $(X64_DIR) $(RISCV64_DIR)

STPARSER_ARM=$(ARM_DIR)/c-parser
STPARSER_ARM_HYP=$(ARM_HYP_DIR)/c-parser
STPARSER_AARCH64=$(AARCH64_DIR)/c-parser
STPARSER_X64=$(X64_DIR)/c-parser
STPARSER_RISCV64=$(RISCV64_DIR)/c-parser
STPARSERS=$(STPARSER_ARM) $(STPARSER_ARM_HYP) $(STPARSER_AARCH64) \
          $(STPARSER_X64) $(STPARSER_RISCV64)

TOKENIZER_ARM=$(ARM_DIR)/tokenizer
TOKENIZER_ARM_HYP=$(ARM_HYP_DIR)/tokenizer
TOKENIZER_AARCH64=$(AARCH64_DIR)/tokenizer
TOKENIZER_X64=$(X64_DIR)/tokenizer
TOKENIZER_RISCV64=$(RISCV64_DIR)/tokenizer
TOKENIZERS=$(TOKENIZER_ARM) $(TOKENIZER_ARM_HYP) $(TOKENIZER_AARCH64) \
           $(TOKENIZER_X64) $(TOKENIZER_RISCV64)

.PHONY: all cparser_tools stp_all standalone-cparser standalone-tokenizer

# Target "all" gains additional dependencies in the included Makefile below, so
# we keep "stp_all" as the first (= default) target
stp_all: standalone-cparser standalone-tokenizer
all: stp_all

standalone-cparser: $(STPARSERS)
standalone-tokenizer: $(TOKENIZERS)

include $(STP_PFX)/../Makefile

STP_CLEAN_TARGETS := $(STPARSERS) $(TOKENIZERS) $(STP_PFX)/c-parser.o $(STP_PFX)/table.ML

$(STP_PFX)/table.ML: $(ISABELLE_HOME)/src/Pure/General/table.ML
	sed -e '/\(\* cache \*\)/,/final.declarations/d' < $< | \
	sed -e "s/^  val unsynchronized_cache:.*a/  (* removed unsynchronized_cache *)/" > $@

$(ARCH_DIRS):
	mkdir -p $@


ifeq ($(SML_COMPILER),mlton)
#
# compilation if the compiler is mlton
#

ARM_MLB_PATH := -mlb-path-var 'L4V_ARCH ARM'
ARM_HYP_MLB_PATH := -mlb-path-var 'L4V_ARCH ARM_HYP'
AARCH64_MLB_PATH := -mlb-path-var 'L4V_ARCH AARCH64'
X64_MLB_PATH := -mlb-path-var 'L4V_ARCH X64'
RISCV64_MLB_PATH := -mlb-path-var 'L4V_ARCH RISCV64'

PARSER_DEPS_ARM := $(shell mlton $(ARM_MLB_PATH) -stop f $(STP_PFX)/c-parser.mlb)
PARSER_DEPS_ARM_HYP := $(shell mlton $(ARM_HYP_MLB_PATH) -stop f $(STP_PFX)/c-parser.mlb)
PARSER_DEPS_AARCH64 := $(shell mlton $(AARCH64_MLB_PATH) -stop f $(STP_PFX)/c-parser.mlb)
PARSER_DEPS_X64 := $(shell mlton $(X64_MLB_PATH) -stop f $(STP_PFX)/c-parser.mlb)
PARSER_DEPS_RISCV64 := $(shell mlton $(RISCV64_MLB_PATH) -stop f $(STP_PFX)/c-parser.mlb)

TOKENIZER_DEPS_ARM := $(shell mlton $(ARM_MLB_PATH) -stop f $(STP_PFX)/tokenizer.mlb)
TOKENIZER_DEPS_ARM_HYP := $(shell mlton $(ARM_HYP_MLB_PATH) -stop f $(STP_PFX)/tokenizer.mlb)
TOKENIZER_DEPS_AARCH64 := $(shell mlton $(AARCH64_MLB_PATH) -stop f $(STP_PFX)/tokenizer.mlb)
TOKENIZER_DEPS_X64 := $(shell mlton $(X64_MLB_PATH) -stop f $(STP_PFX)/tokenizer.mlb)
TOKENIZER_DEPS_RISCV64 := $(shell mlton $(RISCV64_MLB_PATH) -stop f $(STP_PFX)/tokenizer.mlb)

$(STPARSER_ARM): $(PARSER_DEPS_ARM) | $(ARM_DIR)
	mlton $(ARM_MLB_PATH) -output $@ $<

$(STPARSER_ARM_HYP): $(PARSER_DEPS_ARM_HYP) | $(ARM_HYP_DIR)
	mlton $(ARM_HYP_MLB_PATH) -output $@ $<

$(STPARSER_AARCH64): $(PARSER_DEPS_AARCH64) | $(AARCH64_DIR)
	mlton $(AARCH64_MLB_PATH) -output $@ $<

$(STPARSER_X64): $(PARSER_DEPS_X64) | $(X64_DIR)
	mlton $(X64_MLB_PATH) -output $@ $<

$(STPARSER_RISCV64): $(PARSER_DEPS_RISCV64) | $(RISCV64_DIR)
	mlton $(RISCV64_MLB_PATH) -output $@ $<

$(TOKENIZER_ARM): $(TOKENIZER_DEPS_ARM) | $(ARM_DIR)
	mlton $(ARM_MLB_PATH) -output $@ $<

$(TOKENIZER_ARM_HYP): $(TOKENIZER_DEPS_ARM_HYP) | $(ARM_HYP_DIR)
	mlton $(ARM_HYP_MLB_PATH) -output $@ $<

$(TOKENIZER_AARCH64): $(TOKENIZER_DEPS_AARCH64) | $(AARCH64_DIR)
	mlton $(AARCH64_MLB_PATH) -output $@ $<

$(TOKENIZER_X64): $(TOKENIZER_DEPS_X64) | $(X64_DIR)
	mlton $(X64_MLB_PATH) -output $@ $<

$(TOKENIZER_RISCV64): $(TOKENIZER_DEPS_RISCV64) | $(RISCV64_DIR)
	mlton $(RISCV64_MLB_PATH) -output $@ $<

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
