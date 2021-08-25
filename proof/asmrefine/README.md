<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

Assembly Refinement Proof
=========================

This proof contributes to a larger proof that seL4's compiled binary correctly
implements the [semantics](../../spec/cspec) of its C code. This component of
the proof generates (exports) an external version of the C semantics into the
SydTV-GL language, and proves that the exported version refines the starting C
semantics. A SydTV-GL representation of the binary is created (with proof) by
a decompilation tool based on [HOL4](https://github.com/HOL-Theorem-Prover/HOL),
and the two representations are compared by the [SydTV tool](
https://github.com/seL4proj/graph-refine).

An overview of the full proof is given with the [SydTV tool](
https://github.com/seL4proj/graph-refine). It is also described in the
PLDI '13 [paper][1].

These theories are specific to seL4, and build on the more general apparatus
in the [tools directory](../../tools/asmrefine).

  [1]: https://trustworthy.systems/publications/nictaabstracts/Sewell_MK_13.abstract  "Translation Validation for a Verified OS Kernel"

Important Theories
------------------

The [`SEL4SimplExport`](export/SEL4SimplExport.thy) theory, when executed,
exports the kernel's C semantics into the graph refinement language used by the
external graph refinement toolset. The [`SEL4GraphRefine`](SEL4GraphRefine.thy)
theory establishes that this exported graph semantics is a formal refinement of
the kernel's C semantics.
