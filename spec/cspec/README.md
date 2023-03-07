<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

The C Semantics of seL4
=======================

    l4v/spec/cspec/

This directory contains the entry point for the automatic translation of
the seL4 source code into Isabelle/HOL.

The C semantics of the kernel is produced by first configuring and
preprocessing the C sources for a specific platform and then parsing it into
Isabelle using the C parser in `l4v/tools/c-parser`.

To inspect the output of this translation, build the image `CSpec` and
interactively inspect the constants the parser has defined.


Top-Level Theory
----------------

The top-level theory file for this module is `Kernel_C` for the bare
translation of seL4 into Isabelle, and `KernelInc_C` for additional automatic
proofs about generated bitfield functions.


Building
--------

The corresponding Isabelle sessions for this module are `CKernel` and `CSpec`.
`CSpec` contains `CKernel` plus automated bitfield proofs.

To build the image, run the corresponding session in directory `l4v/spec`,
e.g.:

    make CSpec

This will also configure and preprocess the kernel sources.

Expect this build to take about 30 min on a modern machine and to require
close to 4GB of memory. For further sessions building on top of `CSpec`,
usually at least 16GB of main memory are required together with a 64-bit setup
of Isabelle.

The target architecture may be specified by setting the `L4V_ARCH` environment
variable. It determines both which configuration of seL4 is used, as well as
indicating the architecture-specific definitions and proofs to use. The default
architecture is `ARM` and will be selected if none is provided. See
`l4v/spec/cspec/c/Makefile` for seL4 configuration details.

The build process has an option for providing a device tree overlay file if
desired, which can customise the memory regions available to the kernel. See
the [README](c/overlays/README.md) file in `c/overlays/` for more details.

Remarks
-------

To speed up interactive development, the bitfield code generator can be
configured to skip the corresponding proofs and produce sorried
(unproven) property statements only. To achieve this, set the
environment variable `SORRY_BITFIELD_PROOFS` to `TRUE`.

