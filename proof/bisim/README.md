<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

Separation Kernel Bisimilarity
==============================

This proof establishes that seL4, if configured fully statically with 1-level
CSpaces and notification caps only, is bi-similar to a static separation
kernel that has no other system calls than signalling notifications.

Building
--------

To build for the ARM architecture from the `l4v/` directory, run:

    L4V_ARCH=ARM ./run_tests Bisim

Important Theories
------------------

Theory [`Separation`](Separation.thy) defines static configurations, and
theory [`Syscall_S`](Syscall_S.thy) contains the proof that this is equivalent
to a static kernel.

The definition of a static kernel API can be found in the `spec` directory
under [`sep-abstract`](../../spec/sep-abstract/).
