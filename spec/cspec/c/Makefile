#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: GPL-2.0-only
#

# For kernel builds (CSpec and binary verificaiton).
# We will get e.g. "ARM_" for empty L4V_PLAT, but that is preferrable to messing
# with the corresponding external_file and install_C_file commands in Isabelle.
KERNEL_BUILD_ROOT := build/${L4V_ARCH}_${L4V_PLAT}

# For building configuration headers only (not used in CSpec):
KERNEL_CONFIG_ROOT := config-build/${L4V_ARCH}_${L4V_PLAT}

# Death to recursively-expanded variables.
KERNEL_CMAKE_EXTRA_OPTIONS := ${KERNEL_CMAKE_EXTRA_OPTIONS}

ifdef SORRY_BITFIELD_PROOFS
  KERNEL_CMAKE_EXTRA_OPTIONS += -DSORRY_BITFIELD_PROOFS=${SORRY_BITFIELD_PROOFS}
endif

include kernel.mk

# called by ../../Makefile
cspec: ${UMM_TYPES} ${KERNEL_BUILD_ROOT}/kernel_all.c_pp
	cd ${KERNEL_BUILD_ROOT} && ninja kernel_theories


CONFIG_THY := ../../machine/${L4V_ARCH}/Kernel_Config.thy

# called by ../../Makefile
config: ${CONFIG_THY}

${CONFIG_THY}: ${CONFIG_DONE}
	./gen-config-thy.py


clean:
	rm -rf ${KERNEL_BUILD_ROOT}

.PHONY: cspec clean
