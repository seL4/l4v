<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

Abstract Spec Invariant Proof
=============================

This proof defines and proves the global invariants of seL4's
[abstract specification](../../spec/abstract/). The invariants are
phrased and proved using a [monadic Hoare logic](../../lib/Monads/nondet/Nondet_Monad.thy)
described in a TPHOLS '08 [paper][1].

  [1]: https://trustworthy.systems/publications/nictaabstracts/Cock_KS_08.abstract "Secure Microkernels, State Monads and Scalable Refinement"

Building
--------

To build for the ARM architecture from the `l4v/` directory, run:

    L4V_ARCH=ARM ./run_tests AInvs

Important Theories
------------------

The top-level theory where the invariants are proved over the kernel is
[`Syscall_AI`](Syscall_AI.thy); the bottom-level theory where they are
defined is [`Invariants_AI`](Invariants_AI.thy).

