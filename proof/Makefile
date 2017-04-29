#
# Copyright 2014, General Dynamics C4 Systems
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(GD_GPL)
#

export L4V_ARCH ?= X64

## Targets
ifeq ($(L4V_ARCH),X64)
images: AInvs BaseRefine RefineOnly
else
images: BaseRefine CBaseRefine Refine CRefine
endif

default: images test
test:
all: images test
report-regression:
	@echo Refine Access CBaseRefine CRefine \
	      DRefine InfoFlow InfoFlowCBase InfoFlowC DPolicy \
		  DSpecProofs SepTacticsExamples Bisim

#
# Setup heaps.
#

# Refine heaps.
HEAPS += AInvs BaseRefine Refine RefineOnly

# CRefine heaps.
HEAPS += CKernel CSpec CBaseRefine CRefine

# capDL heaps.
HEAPS += DBaseRefine DRefine DPolicy SepDSpec DSpecProofs

# Security Proofs
HEAPS += Access InfoFlow InfoFlowCBase InfoFlowC

# Binary Verification
HEAPS += SimplExportAndRefine

# Separation Kernel Bisimilarity
HEAPS += Bisim

# Separation Logic Tactics
HEAPS += SepTactics SepTacticsExamples

# Additional dependencies

CKernel CSpec CBaseRefine CRefine: c-kernel
SimplExportAndRefine: c-kernel

# Preprocess the kernel's source code and bitfield theory files.
c-kernel: .FORCE
	cd ../spec && $(ISABELLE_TOOL) env make c-kernel
.PHONY: c-kernel

include ../misc/isa-common.mk

# SimplExportOnly is a bit special, because we need to *not* build an image.
SimplExportOnly: c-kernel
	$(ISABELLE_TOOL) build -v -c -d $(ROOT_PATH) $@
.PHONY: SimplExportOnly
