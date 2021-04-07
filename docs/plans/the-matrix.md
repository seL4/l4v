<!--
     Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# The Matrix Project

This file contains the tasks and ideas that are related to solving the matrix
problem for the seL4 verification.

## What is the Matrix?

The matrix problem is that there are many configurations and verification
depths of seL4 and most of them are unverified. The matrix is roughly something
like this:

    {ARM, RISCV, X64, AARCH64} x
    {MCS or not} x
    {MC or not} x
    {HYP or not} x
    {IOMMU or not} x
    {functional correctness, binary, security proofs, capDL, CAmkES}

Within each of the architectures, there are again many configurations, e.g. for
each specific platform, board, set of devices, and memory configuration. For
instance, see <https://docs.sel4.systems/Hardware/> and follow the column
"Status". Almost all of these are "Unverified".

The project is to get (almost) all of them to "all proofs" without going
insane. This is a long-term goal. Getting there only half-way in a sustainable
way would already be excellent.

## Main Ideas

The more we can abstract, modularise, and generalise, the more we can support
without doing new proofs each time. Some current ideas are:

- Pushing the current arch-split further down and up the stack: re-using generic
  proofs will reduce the amount of work per feature.

- More long-term ideas for allowing more fine-grained selections of features or
  reducing the number of proofs we have to check:
  - currently there is only one switch (L4V_ARCH), no other options/dimensions
  - more abstraction layers
    - starting point: platform options (PPTR_TOP etc)
    - some intermediate point: generic page tables in C for all architectures
    - end point: one spec with all architecture and feature options,
                 with one invariant proof for them all

- More modularity between proofs (e.g. some actual abstractions):
  should allow us to change things independently of each other

- More genericity in existing proofs and code (e.g. generic page tables):
  supporting multiple configurations/scenarios in one single proof

- More sharing and cohesion between proofs (e.g. share code between specs as
  in `abstract/` and `asep-spec/`):
  - reducing the amount of proof needed for each layer,
  - reusing existing properties

- More efficient and simpler proofs (e.g. projections, making better use of
  types): should make all of the above easier to achieve

## Larger related tasks

The following tasks are medium to large and connected to the matrix problem.
Solving any of these will be a step in the right direction, but not each of
these will be equally useful to start with and not all might be necessary. Many
of these tasks are incremental, i.e. we can work on them for some time and get
benefit even without fully finishing them.

### Modularity

- **project** generate platform config proofs
  [VER-967](<https://sel4.atlassian.net/browse/VER-967>)

- **task: large, researchy; impact: scaling** Investigate modularising the proofs.
  - Provide some way to define "interfaces" between modules, consisting of the assumptions
     and theorems of the module, so that leaf modules containing proofs have fewer
     dependencies.
  - Investigate: Is this remotely feasible? What tech is needed? Is there a viable path?
       Which way(s) would we slice things up?

- **task: medium, impact: big** Access Control
  - split for other architectures
  - rename things to conform with paper and to make sense
  - assumptions too "too strong", excludes systems we might want to actually
     use (change was done for Infoflow)
  - proofs are a bit "crummy", but no immediate way of improvement visible

- **task: medium, impact: scaling, quality of life**, Refine: too big, triplicated
  - arch-splitting
  - shrinking: corres tactic, cross-over rules

- **task: medium, impact: medium, (much) less pain** remove Haskell spec
  - (precondition for sharing between specs)
  - figure out how to avoid duplication between `ARM`/`ARM_HYP`
  - implement `fun` (recursive functions) for haskell translator until then?

### Genericity

- **task: large, but incremental; impact: scaling, quality of life**
   More sharing between the abstract and intermediate specs. In a lot of
   places, these specs are identical, and so their corres proofs have low
   information content. The ideal would be that the first refinement is just
   about the interesting data refinements.
  - starting point: factor out common functions
  - end point: exec spec = abstract with more concrete data structures

- **task: medium incremental, impact: scaling, quality of life**
  - More consistent structure in the abstract spec, to improve accessibility to automation, e.g.:
    - Use the least powerful monad that gets the job done.
    - Use the most specific accessor.
    - Break large functions into smaller ones (to make it easier to state lemmas about the parts).
    - Pass more parameters to functions, if information available in the caller might be useful
      for stating properties about the called function.

- **task: medium+; impact: scale** generic page tables; could everything be like RISC-V?
  [VER-866](<https://sel4.atlassian.net/browse/VER-866>)

- **task: medium; impact: scale** generic ASIDs, ASID pools, ASID table
  [VER-865](<https://sel4.atlassian.net/browse/VER-865>)

### Tools

- **task: researchy, medium; maybe not that hard; impact: quality-of-life**
   why do locales get so slow
  - maybe can avoid exporting lemmas each time (explicit export only)

- **task: medium (good thesis student), impact: incremental parsing, less pain** CParser state spaces
  - CParser name mangling: per function scope
  - investigate if state spaces for C proofs instead of records would be faster or more pleasant than records; would enable state space merge
  - investigate if C parser could be incremental (see state spaces)

- **task: researchy, medium; maybe not that hard; impact: quality-of-life**
   more lightweight arch split (implement Isabelle name spaces?)
  - idea needs refinement
  - would have to support interaction with locales (e.g. `locale x_Arch = x + Arch`)
  - or a locale that doesn't export things (only explicitly)

- **task: medium; impact: quality of life** more principled/automatic deduplication, moving of lemmas. Is there a levity-light?
  - make Ed's dependency graph tool a real tool
  - See also [VER-544](<https://sel4.atlassian.net/browse/VER-544>)

- **task: medium; impact: quality of life** Improve and make better use of corres tactics
  - e.g. Dan's tactic in Eisbach
  - maybe more specifically corres? (without own calculus) Would achieve less
    automation, but better workflow integration.

### Depth

In some sense these make the matrix problem worse, because they add more depth
to the proof dimension, but they are proofs we want in the future, and should
keep in mind:

- **researchy, task: large, impact: soundness** kernel init

- **task: medium (more than honours student); impact: more soundness** integrate TLB reasoning
  - based on Hira's PhD
  - there is choice where to add the TLB layer

- **researchy, task: large (needs funding), impact: big (virtualisation)** IOMMU verification
  - status, value, plans?
  - how to do IOMMU without duplicating too much? (e.g. generic page tables)

## Small related tasks

The following tasks from the [Smaller Tasks List][smaller_tasks] are small, but
in some way related to the matrix problem more specifically than generally
improving documentation etc. Completing/solving them will bring us a small step
into the right direction.

[smaller_tasks]: smaller_tasks.md

- **task: small-medium (maybe); impact: be relevant** fastpath on all arches

- **task: small; impact: quality-of-life**
   faster check for the kernel team if a change breaks their proof: if CRefine
   and SimplExportAndRefine works unchanged after a C chance, can anything else
   break?
   Some details: it should be possible to split Refine into a invariants and actual refinement part.
   Only the invariants part should be needed in CRefine. This would mean that CRefine can be reduced from the whole refinement stack to just Haskell invariants, C invariants (small), and C refinement, which would reduce memory requirements and should reduce a large chunk of build time.

- **task: small; impact: quality of life** policy and maybe automated checks on session import graph, esp across sessions
  - two choke points (import + export/merge)
  - visualise/report what is being overwritten in a merge
  - avoid `[simp del]` resurrection (also for syntax etc)

- **task: small; impact: quality of life**
   Which projection approach to use when? Needs thinking/consultation.

- **task: small; impact: quality of life**
   Better performance monitoring. There's been times that we've made changes to tools and struggled to work out how it affected overall performance
  - dumps? graphs?
  - a web page which tracks AInvs, Refine, CRefine
  - some actual statistics to reduce noise

- **cleanup**: make magic numbers less magic (or remove entirely as far as possible, esp from C)

- **cleanup** device memory
  - check: in InfoFlow do we clear the device regions or do we demand there are none
  - check model of device memory in ADT/global automaton

- **cleanup** Cleanup:
  - cleanup: generic word proofs in ... everything
     (MOVE to WordLib; many done, probably more to do)
  - cleanup: Refine proofs in CRefine
     (MOVE to Move.thy first; is there more?)
  - cleanup: declarations in middle of things (mainly CRefine, affects
    moving word lemmas as well)
  - cleanup: abstract proofs in Refine
    - definitely before any attempt to arch-split Refine
    - create a staging area first (Move_To_AInvs.thy)

- **cleanup/speedup** testing for the arch matrix:
  - all possible features for all arches all the time?
  - subset for faster check?

- **task: small-medium, impact: quality of life**, arch-split interface locale
  - find narrower interface, make more things generic
  - simplification of current assumptions, as it stands it's really
     "almost everything"

- **task: smallish, incremental; impact: quality-of-life**
   remove literate Haskell, move comments/docs to either C or abstract, or keep as actual comments

- **task: small; impact: quality of life** don't include unused separation logic stuff in C semantics; clean up UMM
    [VER-962](<https://sel4.atlassian.net/browse/VER-962>)

- **task: small-medium; impact: quality of life** rework exception monad reasoning, has unnecessary complexity
    [VER-594](<https://sel4.atlassian.net/browse/VER-594>)

- **task: small; impact: quality of life** converge on crunches, deprecate crunch
    [VER-918](<https://sel4.atlassian.net/browse/VER-918>)

- **task: small-medium; impact: some quality of life** automate/improve the monadic rewrite framework
  [VER-727](<https://sel4.atlassian.net/browse/VER-727>)
  - something in the direction of `ccorres_rewrite`
  - use conversions maybe
