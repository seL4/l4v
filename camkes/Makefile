#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: GPL-2.0-only
#

## Targets
images: Camkes
default: images test
test:
all: images test

#
# Setup heaps.
#

# CAmkES
HEAPS += CamkesAdlSpec CamkesCdlRefine CamkesGlueSpec CamkesGlueProofs
GROUPS += Camkes

# Clean
clean:
	rm -f ${ISABELLE_BROWSER_INFO}/CAmkES/CamkesGlueSpec/document.pdf
	rm -f ${ISABELLE_BROWSER_INFO}/CAmkES/CamkesAdlSpec/document.pdf
	rm -f ${ISABELLE_BROWSER_INFO}/CAmkES/CamkesGlueProofs/document.pdf

include ../misc/isa-common.mk
