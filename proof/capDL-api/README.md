<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

CapDL API Proofs
================

This proof develops a formal API description for a number of the seL4
system calls, of the [capDL](../../spec/capDL/) kernel specification.
This API description is a set of lemmas describing the behaviour of
various system calls in terms of a [separation logic](../sep-capDL/)
defined over that kernel specification.

When reasoning about system calls this proof treats the kernel like
a library invoked directly from user-space and does not reason about
scheduling. These proofs are used by the [system initialiser
proof](../../sys-init), as described in the [ICFEM '13 paper][Boyton_13]
and Andrew Boyton's PhD thesis.

  [Boyton_13]: https://trustworthy.systems/publications/nictaabstracts/Boyton_ABFGGKLS_13.abstract "Formally Verified System Initialisation"

Building
--------

To build for the ARM architecture from the `l4v/` directory, run:

    L4V_ARCH=ARM ./run_tests DSpecProofs

Important Theories
------------------

The top-level theory is [`API_DP`](API_DP.thy). The seL4 API and kernel
model are located in [`Kernel_DP`](Kernel_DP.thy).
