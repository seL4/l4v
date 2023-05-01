<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

Access Control Proof
====================

This proof establishes that seL4 enforces the security properties of
*authority confinement* and *integrity*. These are essential correctness
properties of its capability-based access control system: authority
confinement means that authority propagates only in accordance with
capabilities, and integrity means that data cannot be modified without
possession of an appropriate *write* capability to the data. These
properties and proofs are described in detail in an ITP 2011 [paper][1].
These properties are phrased over seL4's
[abstract specification](../../spec/abstract/) and this proof builds on
top of the [Abstract Spec Invariant Proof](../invariant-abstract/).

  [1]: https://trustworthy.systems/publications/nictaabstracts/Sewell_WGMAK_11.abstract "seL4 Enforces Integrity"


Building
--------

To build for the ARM architecture from the `l4v/` directory, run:

    L4V_ARCH=ARM ./run_tests Access


Important Theories
------------------

The top-level theory where these two properties are proved for the
kernel is [`Syscall_AC`](Syscall_AC.thy); the bottom-level theory where
the properties are defined is [`Access`](Access.thy).
