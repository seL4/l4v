#
# Copyright 2014, General Dynamics C4 Systems
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(GD_GPL)
#

SHELL=bash

## Targets
images: ASpec CKernel
default: images test
test: spec-check
all: images test
report-regression:
	@echo spec-check ASpec ExecSpec DSpec TakeGrant CKernel CSpec \
	      binary-verification-input

#
# Setup heaps.
#

# Spec heaps.
HEAPS += ASpec ExecSpec DSpec CKernel CSpec TakeGrant ASepSpec

# Additional dependencies

CKernel CSpec: c-kernel

# Ensure haskell spec is up-to-date with haskell code.
spec-check: .FORCE
	cd ../misc/scripts && bash test_spec.sh
.PHONY: spec-check

# Preprocess the kernel's source code and bitfield theory files.
c-kernel: .FORCE
	cd cspec/c && L4V_REPO_PATH=$(L4V_REPO_PATH) $(MAKE) cspec
.PHONY: c-kernel

# Produce the input data for the binary verification problem at -O1
binary-verification-input: c-kernel
	$(ISABELLE_TOOL) build -d .. -v SimplExport
	echo 'Built CFunDump.txt, md5sums of relevance are:'
	md5sum cspec/CFunDump.txt cspec/c/kernel_all.c_pp

# Clean
clean:
	rm -rf abstract/generated
	cd cspec/c && $(MAKE) clean SKIP_PATH_CHECKS=1
	rm -f umm_types.txt
.PHONY: clean

include ../misc/isa-common.mk
