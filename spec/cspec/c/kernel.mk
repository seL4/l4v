#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: GPL-2.0-only
#

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
      TRY_TOOLPREFIX := arm-none-eabi- arm-linux-gnueabi-
    else ifeq (${L4V_ARCH},RISCV64)
      TRY_TOOLPREFIX := riscv64-unknown-linux-gnu- riscv64-linux-gnu- riscv64-unknown-elf-
    else ifeq (${L4V_ARCH},AARCH64)
      TRY_TOOLPREFIX := aarch64-unknown-linux-gnu- aarch64-linux-gnu-
    endif
  endif
  ifdef TRY_TOOLPREFIX
    TOOLPREFIX := $(firstword $(strip $(foreach TRY,${TRY_TOOLPREFIX},$(if $(shell which ${TRY}gcc),${TRY},))))
    ifeq (,${TOOLPREFIX})
      $(error No gcc cross-compiler found for this L4V_ARCH)
    endif
  endif
endif

OBJDUMP := ${TOOLPREFIX}objdump
CPP := ${TOOLPREFIX}cpp

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

# __pycache__ directories are the only in-tree products of the kernel build.
# But since they are generated after the cmake setup, they would cause unnecessary
# kernel rebuilds if we treated them as dependencies of the kernel build.
# We avoid this by excluding __pycache__ directories from the kernel dependencies.
KERNEL_DEPS := $(shell find ${SOURCE_ROOT} -name .git -prune -o -name __pycache__ -prune -o -type f -print)

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
	MAKEFILES= make -C ${PARSERPATH} ${PARSERPATH}/${L4V_ARCH}/c-parser
	${PARSERPATH}/${L4V_ARCH}/c-parser --cpp=${CPP} --underscore_idents --mmbytes $^ > $@.tmp
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
	${CSPEC_DIR}/mk_umm_types.py --root $(L4V_REPO_PATH) ${KERNEL_BUILD_ROOT}/kernel_all.c_pp $@

# This target generates config files and headers only. It does not invoke
# the C tool chain or preprocessor. We force CMake to skip tests for these,
# so that ASpec and ExecSpec can be built with fewer dependencies.
${KERNEL_CONFIG_ROOT}/.cmake_done: ${KERNEL_DEPS} gen-config-thy.py
	rm -rf ${KERNEL_CONFIG_ROOT}
	mkdir -p ${KERNEL_CONFIG_ROOT}
	cd ${KERNEL_CONFIG_ROOT} && \
	cmake -C ${CONFIG} \
		-DCMAKE_TOOLCHAIN_FILE=${CSPEC_DIR}/c/no-compiler.cmake \
		${KERNEL_CMAKE_EXTRA_OPTIONS} \
		-G Ninja ${SOURCE_ROOT}
	cd ${KERNEL_CONFIG_ROOT} && ninja gen_config/kernel/gen_config.json
	touch ${KERNEL_CONFIG_ROOT}/.cmake_done
