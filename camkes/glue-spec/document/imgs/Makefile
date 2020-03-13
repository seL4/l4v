#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: GPL-2.0-only
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
