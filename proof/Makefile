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

# Allow sorry command in AARCH64 CRefine during development:
ifeq "$(L4V_ARCH)" "AARCH64"
  export CREFINE_QUICK_AND_DIRTY=1
endif

#
# Setup heaps.
#

# Refine heaps.
HEAPS += AInvs BaseRefine Refine RefineOrphanage

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
HEAPS += SepTactics

# Additional dependencies

AInvs: design-spec ASpec-files

BaseRefine Refine DBaseRefine DRefine: design-spec ASpec-files

# CKernel uses the `machinety=machine_state` option for `install_C_file`,
# and therefore depends on `design-spec`.
CKernel CSpec : c-kernel design-spec

CBaseRefine CRefine SimplExportAndRefine : c-kernel design-spec ASpec-files

# Preprocess the kernel's source code and bitfield theory files.
c-kernel: .FORCE
	cd ../spec && $(ISABELLE_TOOL) env make c-kernel
.PHONY: c-kernel

# Run the haskell translator
design-spec: .FORCE
	cd ../spec && $(ISABELLE_TOOL) env make design-spec
.PHONY: design-spec

ASpec-files: .FORCE
	cd ../spec && make ASpec-files
.PHONY: ASpec-files

include ../misc/isa-common.mk

# SimplExport is treated specially, to not save an image.
SimplExport: c-kernel design-spec
	$(ISABELLE_TOOL) build -v -c -d $(ROOT_PATH) $@
.PHONY: SimplExport
