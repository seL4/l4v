#
# Copyright 2014, General Dynamics C4 Systems
#
# SPDX-License-Identifier: GPL-2.0-only
#

SHELL=bash
SEL4_VERSION=../../seL4/VERSION

# default to primary verification platform
L4V_ARCH?=ARM

## Targets
images: ASpec CKernel
default: images test
all: images test

#
# Setup heaps.
#

# Spec heaps.
HEAPS += ASpec ExecSpec DSpec CKernel CSpec TakeGrant ASepSpec

# Additional dependencies

# CKernel uses the `machinety=machine_state` option for `install_C_file`,
# and therefore depends on `design-spec`.
CKernel CSpec: c-kernel design-spec

ExecSpec DSpec : design-spec

ASPEC_VERSION_FILE=abstract/document/VERSION.tex
ASPEC_GITREV_FILE=abstract/document/gitrev.tex
GIT_ROOT_FILE=abstract/document/git-root.tex

# NOTE: The abstract spec imports Events from Haskell hence the dependency
ASpec: ASpec-files design-spec

ASpec-files: $(ASPEC_VERSION_FILE) $(GIT_ROOT_FILE) $(ASPEC_GITREV_FILE)

$(ASPEC_VERSION_FILE): $(SEL4_VERSION)
	cp $< $@

$(GIT_ROOT_FILE):
	git rev-parse --show-toplevel > $@
	perl -p -i -e "s/\n//" $@

$(ASPEC_GITREV_FILE): .FORCE
	git rev-parse --short=15 HEAD > $@ || echo unknown > $@
	git diff --no-ext-diff --quiet || echo "*" >> $@
	git diff --no-ext-diff --quiet --cached || echo "+" >> $@
	perl -p -i -e "s/\n//" $@

# NOTE: the install_C_file in Kernel_C.thy invocation generates a spurious
#       umm_types.txt file in this folder. This file is never used nor
#       depended on.

# Preprocess the kernel's source code and bitfield theory files.
c-kernel: c-parser .FORCE
	cd cspec/c && L4V_REPO_PATH=$(L4V_REPO_PATH) L4V_ARCH=$(L4V_ARCH) $(MAKE) cspec
.PHONY: c-kernel

# Generate C config headers
c-config: .FORCE
	cd cspec/c && L4V_REPO_PATH=$(L4V_REPO_PATH) L4V_ARCH=$(L4V_ARCH) $(MAKE) config
.PHONY: c-config

# Run the haskell translator
design-spec: c-config .FORCE
	cd design/ && L4V_REPO_PATH=$(L4V_REPO_PATH) $(MAKE) design
.PHONY: design-spec

# Sets up the c-parser grammar files
c-parser: .FORCE
	cd ../tools/c-parser && make c-parser-deps
.PHONY: c-parser

# Produce the input data for the binary verification problem at -O1
binary-verification-input: c-kernel
	$(ISABELLE_TOOL) build -d .. -v SimplExport
	echo 'Built CFunDump.txt, md5sums of relevance are:'
	md5sum cspec/CFunDump.txt cspec/c/kernel_all.c_pp

# Clean
clean:
	rm -rf abstract/generated
	cd cspec/c && L4V_ARCH=$(L4V_ARCH) $(MAKE) clean SKIP_PATH_CHECKS=1
	rm -f umm_types.txt
.PHONY: clean

include ../misc/isa-common.mk
