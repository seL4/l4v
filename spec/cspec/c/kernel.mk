# Copyright 2020, Data61
# Commonwealth Scientific and Industrial Research Organisation (CSIRO)
# ABN 41 687 119 230.
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(DATA61_GPL)

# This file contains parts of the l4v C kernel build that are reused by binary verification.
# It allows building the C kernel in locations other than the default one used by l4v,
# and assumes that KERNEL_BUILD_ROOT has already been set to specify the build location.

ifndef L4V_REPO_PATH
  L4V_REPO_PATH := $(realpath $(dir $(lastword ${MAKEFILE_LIST}))../../..)
endif

ifndef SOURCE_ROOT
  SOURCE_ROOT := $(realpath ${L4V_REPO_PATH}/../seL4)
endif

CSPEC_DIR := ${L4V_REPO_PATH}/spec/cspec
PARSERPATH := ${L4V_REPO_PATH}/tools/c-parser/standalone-parser

ifndef L4V_ARCH
  $(error L4V_ARCH is not set)
endif

ifndef CONFIG
  CONFIG := ${SOURCE_ROOT}/configs/${L4V_ARCH}_$(if ${L4V_FEATURES},${L4V_FEATURES}_,)verified.cmake
endif

ifndef CONFIG_DOMAIN_SCHEDULE
  CONFIG_DOMAIN_SCHEDULE := ${CSPEC_DIR}/c/config_sched.c
endif

ifndef TOOLPREFIX
  ifndef TRY_TOOLPREFIX
    ifeq ($(findstring ARM, ${L4V_ARCH}),ARM)
      TRY_TOOLPREFIX := arm-none-eabi-
    else ifeq (${L4V_ARCH},RISCV64)
      TRY_TOOLPREFIX := riscv64-unknown-linux-gnu- riscv64-linux-gnu-
    endif
  endif
  ifdef TRY_TOOLPREFIX
    TOOLPREFIX := $(firstword $(strip $(foreach TRY,${TRY_TOOLPREFIX},$(if $(shell which ${TRY}gcc),${TRY},))))
    ifeq (,${TOOLPREFIX})
      $(error No gcc cross-compiler found for this L4V_ARCH)
    endif
  endif
endif

ifndef OBJDUMP
  OBJDUMP := ${TOOLPREFIX}objdump
endif

ifndef UMM_TYPES
  UMM_TYPES := ${KERNEL_BUILD_ROOT}/umm_types.txt
endif

# This duplicates parts of isa-common.mk necessary for mk_umm_types.py
ifndef ISABELLE_HOME
  export ISABELLE_HOME:=${L4V_REPO_PATH}/isabelle
endif
ifndef ISABELLE_TOOL
  export ISABELLE_TOOL:=${ISABELLE_HOME}/bin/isabelle
endif
ifndef ISABELLE_PROCESS
  export ISABELLE_PROCESS:=${ISABELLE_HOME}/bin/isabelle-process
endif

KERNEL_DEPS := $(shell find ${SOURCE_ROOT} -type f)

# Top level rule for rebuilding kernel_all.c_pp
${KERNEL_BUILD_ROOT}/kernel_all.c_pp: ${KERNEL_BUILD_ROOT}/.cmake_done
	cd ${KERNEL_BUILD_ROOT} && ninja kernel_all_pp_wrapper
	cp -a ${KERNEL_BUILD_ROOT}/kernel_all_pp.c $@

# Various targets useful for binary verification.
${KERNEL_BUILD_ROOT}/kernel.elf: ${KERNEL_BUILD_ROOT}/kernel_all.c_pp
	cd ${KERNEL_BUILD_ROOT} && ninja kernel.elf

${KERNEL_BUILD_ROOT}/kernel.elf.rodata: ${KERNEL_BUILD_ROOT}/kernel.elf
	${OBJDUMP} -z -D $^ > $@

${KERNEL_BUILD_ROOT}/kernel.elf.txt: ${KERNEL_BUILD_ROOT}/kernel.elf
	${OBJDUMP} -dz $^ > $@

${KERNEL_BUILD_ROOT}/kernel.elf.symtab: ${KERNEL_BUILD_ROOT}/kernel.elf
	${OBJDUMP} -t $^ > $@

${KERNEL_BUILD_ROOT}/kernel.sigs: ${KERNEL_BUILD_ROOT}/kernel_all.c_pp
	MAKEFILES= make -C ${PARSERPATH} standalone-cparser
	${PARSERPATH}/c-parser ${L4V_ARCH} --underscore_idents --mmbytes $^ > $@.tmp
	mv $@.tmp $@

# Initialize the CMake build. We purge the build directory and start again
# whenever any of the kernel sources change, so that we can reliably pick up
# changes to the build config.
# This step also generates a large number of files, so we create a dummy file
# .cmake_done to represent overall completion for make's dependency tracking.
${KERNEL_BUILD_ROOT}/.cmake_done: ${KERNEL_DEPS} ${CONFIG_DOMAIN_SCHEDULE}
	rm -rf ${KERNEL_BUILD_ROOT}
	mkdir -p ${KERNEL_BUILD_ROOT}
	cd ${KERNEL_BUILD_ROOT} && \
	cmake -C ${CONFIG} \
		-DCROSS_COMPILER_PREFIX=${TOOLPREFIX} \
		-DCMAKE_TOOLCHAIN_FILE=${SOURCE_ROOT}/gcc.cmake \
		-DKernelDomainSchedule=${CONFIG_DOMAIN_SCHEDULE} \
		-DUMM_TYPES=$(abspath ${UMM_TYPES}) \
		-DCSPEC_DIR=${CSPEC_DIR} ${KERNEL_CMAKE_EXTRA_OPTIONS} \
		-G Ninja ${SOURCE_ROOT}
	touch ${KERNEL_BUILD_ROOT}/.cmake_done

${UMM_TYPES}: ${KERNEL_BUILD_ROOT}/kernel_all.c_pp
	python ${CSPEC_DIR}/mk_umm_types.py --root $(L4V_REPO_PATH) ${KERNEL_BUILD_ROOT}/kernel_all.c_pp $@
