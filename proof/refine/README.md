<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

Design Spec Refinement Proof
============================

This proof establishes that seL4's [design specification](../../spec/design/)
is a formal *refinement* (i.e. a correct implementation) of its
[abstract specification](../../spec/abstract/). This proof also
interweaves the definition and proofs of the global invariant for the
design specification, and builds on the [Abstract Spec Invariant
Proof](../invariant-abstract/). It is described in the TPHOLS '08
[paper][1].

  [1]: https://trustworthy.systems/publications/nictaabstracts/Cock_KS_08.abstract "Secure Microkernels, State Monads and Scalable Refinement"

Building
--------

To build for the ARM architecture from the `l4v/` directory, run:

    L4V_ARCH=ARM ./run_tests Refine

Important Theories
------------------

The top-level theory where the refinement statement is established over
the entire kernel is [`Refine`](ARM/Refine.thy); the state-relation that
relates the state-spaces of the two specifications is defined in
[`StateRelation`](StateRelation.thy) and the basic correspondence
property proved over each kernel function is defined in
[`Corres`](ARM/Corres.thy).


