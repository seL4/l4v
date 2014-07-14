#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(NICTA_GPL)
#

# Verbosity settings.
ifeq (${V},)
V := 0
endif
ifeq (${V},1)
Q :=
else # V = 0
Q := @
endif

default: echo.pdf filter.pdf thydeps.pdf

%.pdf: %.svg
	@echo " [MK] $(notdir $@)"
	${Q}which inkscape >/dev/null 2>/dev/null || { echo "You need inkscape installed to build these images" >&2 ; exit 1 ; }
	${Q}inkscape -D -z --file=$< --export-pdf=$@
