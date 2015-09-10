#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(NICTA_GPL)
#

## Targets
images: Camkes
default: images test
test: 
all: images test
report-regression:
	@echo Camkes

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
