#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
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

