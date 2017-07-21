#
# Copyright 2014, General Dynamics C4 Systems
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(GD_GPL)
#

# Config makefile for building sel4 within the l4.verified repository
SOURCE_ROOT=../../../../../seL4
UMM_TYPES=../umm_types.txt
PARSERPATH=../../../../tools/c-parser/standalone-parser
PATH:=${PARSERPATH}:${PATH}
export PATH
TOOLPREFIX ?= arm-none-eabi-
SHELL=bash

ARCH=arm
ARMV=armv7-a
PLAT=tk1
CPU=cortex-a15
CONFIG_DOMAIN_SCHEDULE=config_sched.c

ifeq ($(shell which ${TOOLPREFIX}cpp),)
  ifeq ($(shell which cpp),)
    $(error C Preprocessor '${TOOLPREFIX}cpp' not found)
  else
    $(warning C Preprocessor '${TOOLPREFIX}cpp' not found; defaulting to native cpp)
    TOOLPREFIX :=
  endif
endif

# modifies are produced by the parser
SKIP_MODIFIES=1
FASTPATH=yes
CSPEC_DIR=..

# called by ../../spec/Makefile
cspec: kernel_all.c_pp ${UMM_TYPES} theories
# theories is defined in seL4 makefile
.PHONY: cspec

# Create "umm_types" if necessary.
${UMM_TYPES}: kernel_all.c_pp
	python ../../mk_umm_types.py --root $(L4V_REPO_PATH) $< $@

include ${SOURCE_ROOT}/Makefile

