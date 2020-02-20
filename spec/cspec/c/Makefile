# Copyright 2020, Data61
# Commonwealth Scientific and Industrial Research Organisation (CSIRO)
# ABN 41 687 119 230.
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(DATA61_GPL)

KERNEL_BUILD_ROOT := build/${L4V_ARCH}

# Death to recursively-expanded variables.
KERNEL_CMAKE_EXTRA_OPTIONS := ${KERNEL_CMAKE_EXTRA_OPTIONS}

ifdef SORRY_BITFIELD_PROOFS
  KERNEL_CMAKE_EXTRA_OPTIONS += -DSORRY_BITFIELD_PROOFS=${SORRY_BITFIELD_PROOFS}
endif

include kernel.mk

# called by ../../Makefile
cspec: ${UMM_TYPES} ${KERNEL_BUILD_ROOT}/kernel_all.c_pp
	cd ${KERNEL_BUILD_ROOT} && ninja kernel_theories

clean:
	rm -rf ${KERNEL_BUILD_ROOT}

.PHONY: cspec clean
