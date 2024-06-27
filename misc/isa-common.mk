#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

#
# Common build targets for Isabelle Makefiles.
#
# This file should be included after defining a "HEAPS" variable containing the
# name of all Isabelle heaps that can be built.
#

# Get path to the base of the repository.
L4V_REPO_PATH := $(realpath $(dir $(lastword $(MAKEFILE_LIST)))..)

ROOT_ADD ?= ""
ROOT_PATH := $(L4V_REPO_PATH)$(ROOT_ADD)

# Ensure "ISABELLE_*" environment variables are setup.
ifndef ISABELLE_HOME
  export ISABELLE_HOME=${L4V_REPO_PATH}/isabelle
endif
ifndef ISABELLE_TOOL
  export ISABELLE_TOOL=${ISABELLE_HOME}/bin/isabelle
endif
ifndef ISABELLE_PROCESS
  export ISABELLE_PROCESS=${ISABELLE_HOME}/bin/isabelle-process
endif
ifndef ISABELLE_OUTPUT
  export ISABELLE_OUTPUT=$(shell ${ISABELLE_TOOL} getenv -b ISABELLE_OUTPUT)
endif
ifndef L4V_ARCH
  export L4V_ARCH=ARM
endif

# Setup rules for the heaps.
$(HEAPS): .FORCE
	$(ISABELLE_TOOL) build -b -v ${ISABELLE_BUILD_OPTS} -d $(ROOT_PATH) $@
.PHONY: $(HEAPS)

$(GROUPS): .FORCE
	$(ISABELLE_TOOL) build -b -v ${ISABELLE_BUILD_OPTS} -d $(ROOT_PATH) -g $@
.PHONY: $(GROUPS)

clean: clean-images
.PHONY: clean

clean-images:
	rm -f $(HEAPS:%=$(ISABELLE_OUTPUT)/%)
	rm -f $(HEAPS:%=$(ISABELLE_OUTPUT)/log/%.gz)
	rm -f $(HEAPS:%=$(ISABELLE_OUTPUT)/log/%)
.PHONY: clean-images

realclean: clean
	rm -rf $(ISABELLE_OUTPUT)
.PHONY: realclean

#
# Some targets within this Makefile depend on files, which are managed
# by independent subprojects (namely, Isabelle and the seL4 kernel).
# This Makefile is NOT aware of the respective dependencies.  Rather, it
# forces a recursive call of the corresponding subproject's Makefile
# whenever a target depends on files managed by a subproject.  For this
# purpose, we use the special phony target ".FORCE".
#
.PHONY: .FORCE
.FORCE:

# Common targets that should be considered PHONY.
.PHONY: all default images test
