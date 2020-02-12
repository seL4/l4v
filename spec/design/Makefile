#
#  Copyright 2017, Data61, CSIRO
#
#  This software may be distributed and modified according to the terms of
#  the GNU General Public License version 2. Note that NO WARRANTY is provided.
#  See "LICENSE_GPLv2.txt" for details.
#
#  @TAG(DATA61_GPL)
#


SHELL=bash

# Get path to the base of the repository.
MAKEFILE_PATH := $(dir $(lastword $(MAKEFILE_LIST)))
L4V_REPO_PATH := $(realpath $(MAKEFILE_PATH)../..)
SKEL_PATH     := ${L4V_REPO_PATH}/spec/design/skel
MSKEL_PATH    := ${L4V_REPO_PATH}/spec/design/m-skel
HASKELL_PATH  := ${L4V_REPO_PATH}/spec/haskell
MACHINE_PATH  := ${L4V_REPO_PATH}/spec/machine
TRANS_PATH    := ${L4V_REPO_PATH}/tools/haskell-translator

HASKELL_TRANS := ${TRANS_PATH}/make_spec.sh
TRANS_FILES   := $(HASKELL_TRANS)
TRANS_FILES   += $(shell find $(TRANS_PATH) -name "*.py" -o -name "caseconvs*" -o -name "primrecs" -o -name "supplied")
SKEL_FILES    := $(shell find ${SKEL_PATH} -name "*.thy")
MSKEL_FILES   := $(shell find ${MSKEL_PATH} -name "*.thy")
HASKELL_FILES := $(shell find ${HASKELL_PATH} -name "*hs")
ARCH_DIRS     += ARM ARM_HYP RISCV64 X64
MACHINE_FILES += ${MACHINE_PATH}/ARM/MachineTypes.thy \
                 ${MACHINE_PATH}/ARM_HYP/MachineTypes.thy \
                 ${MACHINE_PATH}/RISCV64/MachineTypes.thy \
                 ${MACHINE_PATH}/X64/MachineTypes.thy

design : version

version : ${SKEL_FILES} ${MSKEL_FILES} ${HASKELL_FILES} ${TRANS_FILES} $(MAKEFILE_PATH)/Makefile
	${HASKELL_TRANS}

clean :
	rm -fr *.thy ${ARCH_DIRS} ${MACHINE_FILES} version

.PHONY: clean design test
