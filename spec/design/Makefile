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
L4V_REPO_PATH := $(realpath $(dir $(lastword $(MAKEFILE_LIST)))../..)
SKEL_PATH     := ${L4V_REPO_PATH}/spec/design/skel
MSKEL_PATH    := ${L4V_REPO_PATH}/spec/design/m-skel
HASKELL_PATH  := ${L4V_REPO_PATH}/spec/haskell
MACHINE_PATH  := ${L4V_REPO_PATH}/spec/machine


SKEL_FILES    := $(shell find ${SKEL_PATH} -name "*.thy")
MSKEL_FILES   := $(shell find ${MSKEL_PATH} -name "*.thy")
HASKELL_FILES := $(shell find ${HASKELL_PATH} -regex ".*\.l?hs") # FIXME: add .hs
HASKELL_TRANS := ${L4V_REPO_PATH}/tools/haskell-translator/make_spec.sh
ARCH_DIRS     += ARM ARM_HYP X64
MACHINE_FILES += ${MACHINE_PATH}/ARM/MachineTypes.thy \
                 ${MACHINE_PATH}/ARM_HYP/MachineTypes.thy \
                 ${MACHINE_PATH}/X64/MachineTypes.thy

design : version

version : ${SKEL_FILES} ${MSKEL_FILES} ${HASKELL_FILES}
	${HASKELL_TRANS}

clean :
	rm -fr *.thy ${ARCH_DIRS} ${MACHINE_FILES} version

.PHONY: clean design test
