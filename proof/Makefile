#
# Copyright 2014, General Dynamics C4 Systems
#
# SPDX-License-Identifier: GPL-2.0-only
#

## Targets
images: BaseRefine CBaseRefine Refine CRefine
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
HEAPS += AInvs BaseRefine BaseRefine2 Refine RefineOrphanage

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

BaseRefine Refine DBaseRefine DRefine: design-spec

# CKernel uses the `machinety=machine_state` option for `install_C_file`,
# and therefore depends on `design-spec`.
CKernel CSpec CBaseRefine CRefine SimplExportAndRefine: c-kernel design-spec

# Preprocess the kernel's source code and bitfield theory files.
c-kernel: .FORCE
	cd ../spec && $(ISABELLE_TOOL) env make c-kernel
.PHONY: c-kernel

# Run the haskell translator
design-spec: .FORCE
	cd ../spec && $(ISABELLE_TOOL) env make design-spec
.PHONY: design-spec

include ../misc/isa-common.mk

# SimplExportOnly is treated specially, to not save an image.
SimplExportOnly: c-kernel design-spec
	$(ISABELLE_TOOL) build -v -c -d $(ROOT_PATH) $@
.PHONY: SimplExportOnly
