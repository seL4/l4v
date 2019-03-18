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

ifeq (${L4V_ARCH},RISCV64)
    TOOLPREFIX ?= riscv64-unknown-linux-gnu-
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
${BUILDROOT}/kernel_all.c_pp: ${BUILDROOT}/.cmake_done
	cd ${BUILDROOT} && ninja kernel_all_pp_wrapper
	cp -a ${BUILDROOT}/kernel_all_pp.c $@

# Initialize the CMake build. We purge the build directory and start again
# whenever any of the kernel sources change, so that we can reliably pick up
# changes to the build config.
# This step also generates a large number of files, so we create a dummy file
# .cmake_done to represent overall completion for make's dependency tracking.
${BUILDROOT}/.cmake_done: ${SOURCE_ROOT}/gcc.cmake ${SOURCE_ROOT}/configs/${CONFIG} ${KERNEL_DEPS} ${CONFIG_DOMAIN_SCHEDULE}
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
	touch ${BUILDROOT}/.cmake_done

# called by graph-refine's seL4-example/Makefile.common
c-kernel-source: ${BUILDROOT}/kernel_all.c_pp

# called by ../spec/Makefile
cspec: ${UMM_TYPES} ${BUILDROOT}/kernel_all.c_pp
	cd ${BUILDROOT} && ninja kernel_theories

${UMM_TYPES}: ${BUILDROOT}/kernel_all.c_pp
	python ../mk_umm_types.py --root $(L4V_REPO_PATH) ${BUILDROOT}/kernel_all.c_pp $@

clean:
	rm -rf build
	rm -f ${UMM_TYPES}

.PHONY: clean
