<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

Proof Tools
===========

This directory contains proof tools, most of which are used in one or
more of the seL4 [proofs](../proof/). Each has its own directory:

 * [asmrefine](asmrefine/) - Generic Isabelle/HOL part of the binary
   verification tool, for use in the seL4
   [Assembly Refinement Proof](../proof/asmrefine).

 * [autocorres](autocorres/) - Tool for easing manual proofs about
   C code, described in this [PLDI '14 paper][1].

 * [c-parser](c-parser/) - Tool for translating C code into
   Isabelle/HOL, used to give seL4's C code its semantics in e.g. the
   seL4 [C Refinement Proof](../proof/crefine/).

 * [haskell-translator](haskell-translator/) - Tool for translating
   Haskell into Isabelle/HOL, used to generate the seL4
   [design specification](../spec/design/).

 * [proofcount](proofcount/) - Tool for collecting metrics from
   finished proofs.

  [1]: https://trustworthy.systems/publications/nictaabstracts/Greenaway_LAK_14.abstract "Don't Sweat the Small Stuff: Formal Verification of C Code Without the Pain"

