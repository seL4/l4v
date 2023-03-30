<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

Confidentiality Proof
=====================

This proof establishes that seL4 enforces information flow, and so
enforces the security property of confidentiality. Information flow
security is defined in terms of (intransitive) noninterference, and
implies confidentiality: data cannot be inferred without appropriate
*read* authority. This proof is described in a 2013 IEEE Symposium on
Security and Privacy [paper][1]. This proof firstly establishes
noninterference for seL4's [abstract specification](../../spec/abstract/),
building on top of the [Access Control Proof](../access-control/),
before transferring the noninterference result to the kernel's
C implementation via the [Design Spec Refinement Proof](../refine/) and
the [C Refinement Proof](../crefine/).

  [1]: https://trustworthy.systems/publications/nictaabstracts/Murray_MBGBSLGK_13.abstract "seL4: from General Purpose to a Proof of Information Flow Enforcement"

Building
--------

To build for the ARM architecture from the `l4v/` directory, run:

    L4V_ARCH=ARM ./run_tests InfoFlow

Important Theories
------------------

The top-level theory where noninterference is proved for the seL4
abstract specification is [`Noninterference`](Noninterference.thy); it
is transferred to the C implementation via refinement in the theory
[`Noninterference_Refinement`](refine/Noninterference_Refinement.thy). The base
theory where noninterference is (generically) defined is
[`Noninterference_Base`](Noninterference_Base.thy). The bottom-level
theory where confidentiality is formalised over the seL4 abstract
specification is [`InfoFlow`](InfoFlow.thy). Confidentiality is
a relational property and the theory [`EquivValid`](../../lib/EquivValid.thy)
defines these generically for the nondeterministic state monad of the
abstract specification.
