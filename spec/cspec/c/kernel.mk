#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: GPL-2.0-only
#

# This file contains parts of the l4v C kernel build that are reused by binary verification.
# It allows building the C kernel in locations other than the default one used by l4v,
# and assumes that KERNEL_BUILD_ROOT has already been set to specify the build location.

ifndef KERNEL_BUILD_ROOT
  $(error KERNEL_BUILD_ROOT is not set)
endif

ifndef L4V_REPO_PATH
  L4V_REPO_PATH := $(realpath $(dir $(lastword ${MAKEFILE_LIST}))../../..)
endif

ifndef SOURCE_ROOT
  SOURCE_ROOT := $(realpath ${L4V_REPO_PATH}/../seL4)
endif

CSPEC_DIR := ${L4V_REPO_PATH}/spec/cspec

ifndef L4V_ARCH
  $(error L4V_ARCH is not set)
endif

SEL4_CONFIG_NAME := ${L4V_ARCH}$(if ${L4V_FEATURES},_${L4V_FEATURES},)

ifndef CONFIG
  CONFIG := ${SOURCE_ROOT}/configs/${SEL4_CONFIG_NAME}_verified.cmake
endif

ifndef CONFIG_DOMAIN_SCHEDULE
  CONFIG_DOMAIN_SCHEDULE := ${CSPEC_DIR}/c/config_sched.c
endif

# Normally, this make file is used in a context where CONFIG_OPTIMISATION
# is not set, and the CMake KernelOptimisation setting is taken from the
# settings file named by the CONFIG variable (see above).
# However, the default can be overridden by setting CONFIG_OPTIMISATION
# before loading this make file. This is useful for binary verification.
ifdef CONFIG_OPTIMISATION
  KERNEL_CMAKE_OPTIMISATION := -DKernelOptimisation=${CONFIG_OPTIMISATION}
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
		-DUMM_TYPES=$(abspath ${UMM_TYPES}) -DCSPEC_DIR=${CSPEC_DIR} \
		${KERNEL_CMAKE_OPTIMISATION} ${KERNEL_CMAKE_EXTRA_OPTIONS} \
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
		${KERNEL_CMAKE_OPTIMISATION} ${KERNEL_CMAKE_EXTRA_OPTIONS} \
		-G Ninja ${SOURCE_ROOT}
	cd ${KERNEL_CONFIG_ROOT} && ninja gen_config/kernel/gen_config.json
	touch ${KERNEL_CONFIG_ROOT}/.cmake_done

# Various targets useful for binary verification.
${KERNEL_BUILD_ROOT}/kernel.elf: ${KERNEL_BUILD_ROOT}/kernel_all.c_pp
	cd ${KERNEL_BUILD_ROOT} && ninja kernel.elf

${KERNEL_BUILD_ROOT}/kernel.elf.rodata: ${KERNEL_BUILD_ROOT}/kernel.elf
	${OBJDUMP} -z -D $^ > $@

${KERNEL_BUILD_ROOT}/kernel.elf.txt: ${KERNEL_BUILD_ROOT}/kernel.elf
	${OBJDUMP} -dz $^ > $@

${KERNEL_BUILD_ROOT}/kernel.elf.symtab: ${KERNEL_BUILD_ROOT}/kernel.elf
	${OBJDUMP} -t $^ > $@

# Normally, this make file is used in a context where STANDALONE_C_PARSER_EXE
# and STANDALONE_C_PARSER_DIR are not set. Consequently the rule for `kernel.sigs`
# attempts to build a standalone C parser before using it.
# If that is not desirable, because you want to use a pre-built C parser, you
# can set STANDALONE_C_PARSER_EXE to the location of the pre-built C parser before
# loading this make file. The `kernel.sigs` rule will then skip the C parser build
# step.
ifndef STANDALONE_C_PARSER_EXE
  STANDALONE_C_PARSER_DIR := ${L4V_REPO_PATH}/tools/c-parser/standalone-parser
  STANDALONE_C_PARSER_EXE := ${STANDALONE_C_PARSER_DIR}/${L4V_ARCH}/c-parser
endif

# We don't track dependencies of the C parser here.
${KERNEL_BUILD_ROOT}/kernel.sigs: ${KERNEL_BUILD_ROOT}/kernel_all.c_pp
ifdef STANDALONE_C_PARSER_DIR
	${MAKE} -C ${STANDALONE_C_PARSER_DIR} ${STANDALONE_C_PARSER_EXE}
endif
	${STANDALONE_C_PARSER_EXE} --cpp=${CPP} --underscore_idents --mmbytes $^ > $@.tmp
	mv $@.tmp $@

# Export kernel build for binary verification.
ifndef KERNEL_EXPORT_DIR
  KERNEL_EXPORT_DIR := ${CSPEC_DIR}/c/export/${SEL4_CONFIG_NAME}
endif

KERNEL_EXPORT_ARTIFACTS := kernel_all.c_pp kernel.elf kernel.elf.rodata kernel.elf.symtab kernel.elf.txt kernel.sigs
KERNEL_EXPORT_ARTIFACT_PATHS := $(patsubst %, $(KERNEL_EXPORT_DIR)/%, $(KERNEL_EXPORT_ARTIFACTS))

${KERNEL_EXPORT_ARTIFACT_PATHS}: ${KERNEL_EXPORT_DIR}/%: ${KERNEL_BUILD_ROOT}/%
	@mkdir -p ${KERNEL_EXPORT_DIR}
	cp $< $@

# Also record the toolchain versions used.
KERNEL_EXPORT_EXTRAS := ${KERNEL_EXPORT_DIR}/gcc.version ${KERNEL_EXPORT_DIR}/binutils.version

${KERNEL_EXPORT_DIR}/gcc.version:
	@mkdir -p ${KERNEL_EXPORT_DIR}
	${TOOLPREFIX}gcc --version > $@

${KERNEL_EXPORT_DIR}/binutils.version:
	@mkdir -p ${KERNEL_EXPORT_DIR}
	${OBJDUMP} --version > $@

kernel_export: ${KERNEL_EXPORT_ARTIFACT_PATHS} ${KERNEL_EXPORT_EXTRAS}
.PHONY: kernel_build_export
