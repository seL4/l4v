#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

REPEATS ?= 1

all: \
	$(patsubst %.c,%.txt,$(wildcard *.c)) \
	$(patsubst %.i,%.txt,$(wildcard *.i))

%.txt: %.i
	python stats.py -R $(REPEATS) --root ../../.. --output $@ $<

%.txt: %.c
	python stats.py -R $(REPEATS) --root ../../.. --output $@ $<

.DELETE_ON_ERROR:

