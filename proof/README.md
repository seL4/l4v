<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

Formal Proofs about seL4
========================

This directory contains the formal proofs about seL4, which mostly prove
properties about the various seL4 [specifications](../spec/).

Each such proof lives in its own subdirectory:

  * [`access-control`](access-control/) - Access Control Proof
  * [`asmrefine`](asmrefine/) - Assembly Refinement Proof
  * [`bisim`](bisim/) - Bisimilarity of seL4 with a static Separation Kernel
  * [`capDL-api`](capDL-api/) - CapDL API Proofs
  * [`crefine`](crefine/) - C Refinement Proof
  * [`drefine`](drefine/) - CapDL Refinement Proof
  * [`infoflow`](infoflow/) - Confidentiality Proof
  * [`invariant-abstract`](invariant-abstract/) - Abstract Spec Invariant Proof
  * [`refine`](refine/) - Design Spec Refinement Proof
  * [`sep-capDL`](sep-capDL/) - CapDL Separation Logic Proof

