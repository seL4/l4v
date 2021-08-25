<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

Assembly Refinement Toolchain
=============================

This toolchain is used to validate the translation of C programs into compiled
binaries. The semantics of the compiled binaries and the initial C programs are
compared via the external [SydTV tool](
https://github.com/seL4proj/graph-refine). These tools are used to convert the
Isabelle C semantics of a program into an exported SydTV-GL representation,
to verify that the exported program is a refinement of the starting semantics,
and to replay SydTV proofs in Isabelle/HOL.

These theories are generic. They are specialised to the case of seL4 in the
[proof directory](../../proof/asmrefine).

An overview of the full proof is given with the [SydTV tool](
https://github.com/seL4proj/graph-refine). It is also described in the
PLDI '13 [paper][1].

  [1]: https://trustworthy.systems/publications/nictaabstracts/Sewell_MK_13.abstract "Translation Validation for a Verified OS Kernel"

Important Theories
------------------

The [`GraphLang`](GraphLang.thy) theory introduces an Isabelle/HOL
representation of SydTV-GL programs, and a parser for them.

The [`SimplExport`](SimplExport.thy) theory contains apparatus for exporting
the C semantics of a program (created by the [C parser](../c-parser) and
expressed in the [Simpl](../c-parser/Simpl) language) into a textual SydTV-GL
representation.

The [`ProveGraphRefine`](ProveGraphRefine.thy) theory introduces proof
automation for proving the correctness of the export process of
[`SimplExport`](SimplExport.thy).

The [`GraphProof`](GraphProof.thy) theory introduces proof rules needed to
replay external SydTV refinement proofs within Isabelle/HOL. This is a work in
progress.
