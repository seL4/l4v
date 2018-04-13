#
# Copyright 2014, General Dynamics C4 Systems
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(GD_GPL)
#

PWD = $(shell pwd)
SOURCE_ROOT=${PWD}/../../../../seL4
PARSERPATH=${PWD}/../../../tools/c-parser/standalone-parser
PATH:=${PARSERPATH}:${PATH}
export PATH
SHELL=bash
BUILDROOT=${PWD}/build/${L4V_ARCH}
CONFIG=${L4V_ARCH}_verified.cmake
UMM_TYPES=${BUILDROOT}/umm_types.txt

CONFIG_DOMAIN_SCHEDULE=${PWD}/config_sched.c

ifeq ($(findstring ARM, ${L4V_ARCH}),ARM)
    TOOLPREFIX ?= arm-none-eabi-
endif

SORRY_BITFIELD_PROOFS?=FALSE

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
CSPEC_DIR=${PWD}/..

# Build a list of every file in the kernel directory. We use this as the dependency basis
# for working out when we should rebuild the kernel
KERNEL_DEPS = $(shell find ${SOURCE_ROOT} -type f)

# Top level rule for rebuilding kernel_all.c_pp
${BUILDROOT}/kernel_all.c_pp: ${BUILDROOT}/CMakeCache.txt
	cd ${BUILDROOT} && ninja kernel_all_pp_wrapper
	cp -a ${BUILDROOT}/kernel_all_pp.c $@

# Rule for initializing the CMake build. In order to pick up changes to the configuration
# we have to purge everything and start again, so for simplicity we just make the cache
# depend upon all the kernel sources. This is mostly needed as the usage of this 'hides' the
# fact there is a configured build going on, so we accept increased rebuild times to not
# confuse users by not rebuilding when we should
${BUILDROOT}/CMakeCache.txt: ${SOURCE_ROOT}/gcc.cmake ${SOURCE_ROOT}/configs/${CONFIG} ${KERNEL_DEPS} ${CONFIG_DOMAIN_SCHEDULE}
	rm -rf ${BUILDROOT}
	mkdir -p ${BUILDROOT}
	cd ${BUILDROOT} && \
	cmake -DCROSS_COMPILER_PREFIX=${TOOLPREFIX} \
		-DCMAKE_TOOLCHAIN_FILE=${SOURCE_ROOT}/gcc.cmake -C ${SOURCE_ROOT}/configs/${CONFIG} \
		-DCSPEC_DIR=${CSPEC_DIR} \
		-DSKIP_MODIFIES=${SKIP_MODIFIES} \
		-DUMM_TYPES=${UMM_TYPES} \
		-DSORRY_BITFIELD_PROOFS=${SORRY_BITFIELD_PROOFS} \
		-DKernelDomainSchedule=${CONFIG_DOMAIN_SCHEDULE} -G Ninja ${SOURCE_ROOT}

# called by ../spec/Makefile
cspec: ${UMM_TYPES} ${BUILDROOT}/kernel_all.c_pp
	cd ${BUILDROOT} && ninja kernel_theories

${UMM_TYPES}: ${BUILDROOT}/kernel_all.c_pp
	python ../mk_umm_types.py --root $(L4V_REPO_PATH) ${BUILDROOT}/kernel_all.c_pp $@

clean:
	rm -rf build
	rm -f ${UMM_TYPES}

.PHONY: clean
