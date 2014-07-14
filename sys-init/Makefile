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
images: SysInit
default: images test
test:
all: images test
report-regression:
	@echo SysInitExamples

#
# Setup heaps.
#

HEAPS += SysInit SysInitExamples

include ../misc/isa-common.mk
