#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

all: stop killbig

stop: stop.c
	gcc -W -Wall -O2 $< -o $@

killbig: killbig.c
	gcc -W -Wall -O2 $< -o $@
