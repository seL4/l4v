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
SKIP_MODIFIES=ON
FASTPATH=yes
CSPEC_DIR=..

build/CMakeCache.txt:
	mkdir -p build
	cd build && \
	cmake -DCROSS_COMPILER_PREFIX=${TOOLPREFIX} \
		-DCMAKE_TOOLCHAIN_FILE=../${SOURCE_ROOT}/gcc.cmake -C ../${SOURCE_ROOT}/configs/${L4V_ARCH}_verified.cmake \
		-DCSPEC_DIR=`pwd`/../${CSPEC_DIR} \
		-DSKIP_MODIFIES=${SKIP_MODIFIES} \
		-DUMM_TYPES=`pwd`/../${UMM_TYPES} \
		-DKernelDomainSchedule=`pwd`/../${CONFIG_DOMAIN_SCHEDULE} -G Ninja ../${SOURCE_ROOT}

kernel_all_pp: build/CMakeCache.txt
	cd build && ninja kernel_all_pp_wrapper
	cp -a build/kernel_all_pp.c kernel_all.c_pp

.PHONY: kernel_all_pp

# called by ../../spec/Makefile
cspec: ${UMM_TYPES} kernel_all_pp
	cd build && ninja kernel_theories

.PHONY: cspec

# Create "umm_types" if necessary.
${UMM_TYPES}: kernel_all_pp
	python ../../mk_umm_types.py --root $(L4V_REPO_PATH) kernel_all.c_pp $@

