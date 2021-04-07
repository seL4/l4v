<!--
     Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Other Proof Engineering Ideas

Many of these are half-baked general ideas, coming out of brainstorming sessions. They all need further refinement, and being listed here doesn't necessarily mean they should be done.

## Big tasks: new proofs or tools

- **research, task: medium, impact: marketing and sanity check** Infoflow:
  - unclear what to do with MCS (potentially not so bad)
  - may be replaced by flexible infoflow setups from time protection project (strict non-interference is too strong)

- **task: researchy, impact: soundness**
   better story for interrupt controllers and device memory
  - connects to multicore (may be solved there)

- **task: medium+; impact: scale** generic page tables; could everything be like RISC-V?
    [VER-866](<https://sel4.atlassian.net/browse/VER-866>)

- **task: medium; impact: scale** generic ASIDs, ASID pools, ASID table
    [VER-865](<https://sel4.atlassian.net/browse/VER-865>)

## Big tasks: improve proofs or tools

- **task: big, impact: less pain** DRefine - is it really that much of a better abstraction

  - CamkesCdlRefine is the one we actually want (components have separate
    address spaces etc)

  - if we can prove SysInit directly on the abstract spec, we can throw away
    DRefine (whose only justification is SysInit)
    - can maybe make lemmas about the abstract spec that "unroll" the refinement
      from capDL, and use those to simulate capDL steps
    - also possible to get to a capDL state, then prove we can arrive at the
      analogous abstract spec state by doing abstract spec ops
    - capDL captures everything needed for integrity/access/infoflow theorems
      (DPolicy)

- **task: big, impact: unknown, maybe less pain** AutoCorres - looking at applying it for CRefine

- **task: medium (good thesis student), impact: speedup** CParser String lookup is slow

- **task: medium, impact: speedup** can we make CKernel faster
  - potentially inversion theorems etc. from Harvey's memory model (finish
    merging BrianH + SimonW PR)
  - avoid record UMM proofs: make a sort-of-universal type for records by
    re-encoding them as a list of fields; deep embedding (potential issues with
    padding and unions)

- **task: large, but incremental; impact: scaling, quality of life**
   More sharing of accessors between the specs and invariants, and a more
   regular structure to these.

- **task: researchy; impact: quality-of-life**
   Figure out how to avoid long-running branches. As much as possible, work on
   master.
  - for some hard to avoid
  - smaller steps possible for things aligned to the matrix (e.g. AArch64)

- **task: medium; impact: quality-of-life** make CRefine less painful
  - how?

- **task: medium; impact: quality of life** BV: clean up graph-refine python.
  - move some of the correctness-critical things into Isabelle
  - more meta theory

- **task: medium; impact: quality of life**
   BV: rework SimplExportAndRefine so that it is rule-driven.

- **task: medium; impact: prepare for MC** Finish adding support for multicore
  structures into master

## Other issues

- **less pain** Isabelle indentation (mainly subgoal, multi-line reeindents)

- **project** generate platform config proofs
  [VER-967](<https://sel4.atlassian.net/browse/VER-967>)

- **task: unknown; impact: quality of life**
  Eisbach improvments. A specific example is adding flags, motivated by wanting to be able to do `wpsimp (trace)`

- **task: unknown; impact: quality of life**
   `try` operator that matches a pattern without focussing schematics (apply a rule if a pattern matches, but with schematics working).
   Make Eisbach more usable with schematics around.

- **task: unknown; impact: quality of life**
  on the command line: Isabelle should say when it is finished with a theory

- **task: unknown; impact: quality of life** speed up regression test more. SimplExport is now > 4h
  eg [VER-1072](<https://sel4.atlassian.net/browse/VER-1072>)

## For discussion

- Consider removing non-determinism from the abstract spec. Do we still get a benefit from it?
   Would it simplify anything if we got rid of it?
