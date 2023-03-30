<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

Static Separation Kernel API
============================

This specification is a cut-down version of the seL4 abstract specification
that removes all system calls apart from notifications. The resulting kernel
is a classic static separation kernel without any dynamism.

A proof that seL4 is equivalent to this cut-down version if configured
appropriately can be found in the `proof` directory under
[`bisim`](../../proof/bisim/).


Building
--------

To build from the `l4v/` directory for the ARM architecture, run:

    L4V_ARCH=ARM ./run_tests ASepSpec

Important Theories
------------------

Theory [`Syscall_SA`](Syscall_SA.thy) contains the top-level definition. The
specification directly includes parts of the 'normal' abstract specification
of seL4 from directory [`abstract`](../abstract/).
