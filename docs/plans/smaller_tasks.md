<!--
     Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# The Small Tasks List

This file lists small strategic engineering tasks and attempts to order them
based on how interested we are in doing them. This ordering is based on multiple
factors, including our best guess on their return on investment and how soon we
might want their results. It also splits the tasks into two groups; incremental
tasks that people can contribute to whenever they have time, and small projects
that might need more commitment.

## How to work on this list

The tiers are roughly by decreasing priority, but don't necessarily need to be worked on in that order.

- pick an item you are interested in
- make a [JIRA][] issue with more information, content, a plan if necessary
- add link to [JIRA][] issue into this file
- assign issue to yourself (or someone else or multiple people if appropriate)

Feel free to edit this file and raise a pull request if you have a new task that
you think should be added to this list or if you want to edit and clarify an
existing task.

[JIRA]: https://sel4.atlassian.net

## Incremental Tasks

### Tier 1

- **cleanup**: make magic numbers less magic (or remove entirely as far as possible).
   This can start of by 'just' finding a specific magic number and refactoring or removing it.

- **task: small; impact: quality of life** converge on crunches, deprecate crunch
    [VER-918](<https://sel4.atlassian.net/browse/VER-918>)

### Tier 2

- **task: small; impact: (some) measure of tech debt**
   resolve `FIXME`s or remove them. Have a count, like the sorry count?

- **task: small; impact: quality of life**
   Use the built-in datatype selector and discriminator functions more often within the abstract spec and proofs.

### Tier 3

- **task: smallish, incremental; impact: quality-of-life**
   remove literate Haskell, move comments/docs to either C or abstract, or keep as actual comments

### Tier 4

- **task: small; impact: quality-of-life**
   add a `docs/` directory to l4v with a lot of the things we're currently keeping in Confluence.
   (This has happened, but more should be added.)

- **task: small; impact: quality of life** Easier ways for new engineers and
  contributors to find out about basic useful lemmas
  - Documentation, `wp_unsafe`, consistent naming, etc

- **cleanup** Cleanup:
  - cleanup: generic word proofs in ... everything
       (MOVE to WordLib; many done, probably more to do)
  - cleanup: refine proofs in CRefine
       (MOVE to Move.thy first; is there more?)
  - cleanup: declarations in middle of things (mainly CRefine, affects
      moving word lemmas as well)
  - cleanup: abstract proofs in refine
    - definitely before any attempt to arch-split refine!
    - create a staging area first (Move_To_AInvs.thy)

- **cleanup**
   reduce number of Isabelle warnings so that new warnings are meaningful

- **task: small-ish, impact: (somewhat) less pain** Infoflow cleanup:
  - currently hard to understand (there is a new tutorial in `docs/` which explains some parts)
  - quality of proofs is low in places

### Tier 5

- **task: small; impact: quality-of-life**
   clean up Jira, make more useful and less scary:
  - remove old labels that are used only once
  - consolidate duplicates
  - do we really use Triage? We do. Then: do triage periodically.
  - have a label for good-first-issue and use it
  - saved searches for interesting subsets (e.g. non-assigned open highish priorities, unassigned old issues, assigned old issues without progress (should there be a nag email for these?))
  - periodically clean out old issues, make sure resolved ones are closed etc. Currently Gerwin is doing this once every 2 months or so when he has time, but the duty could/should be shared.

- **task: ongoing; impact: quality of life**
   Improve documentation within proofs and tools to support new engineers and contributors.

## Small Projects

### Tier 1

- **task: small; impact: quality-of-life**
   refactor `Refine` into `DInvs` and `Refine`
   [VER-1299](<https://sel4.atlassian.net/browse/VER-1299>)

- **task: small; impact: quality-of-life**
   faster check for the kernel team if a change breaks their proof: if CRefine
   and SimplExportAndRefine works unchanged after a C chance, can anything else
   break? If the DInvs refactor above is done, it should be sufficient to check
   CRefine without composing all theorems.

- **task: small; impact: quality-of-life**
   make working with schematics less painful: `cong` rules for relation and
   guards in `corres`, `ccorres`, and `wp`. There are two sub-tasks, one quick
   (the rules), one longer (using them).
   [VER-1300](<https://sel4.atlassian.net/browse/VER-1300>)

- **task: small-medium; impact: quality of life**
  rework exception monad reasoning, has unnecessary complexity
  [VER-594](<https://sel4.atlassian.net/browse/VER-594>)

### Tier 2

- **task: small-medium (maybe); impact: be relevant** fastpath on all arches
  - related to matrix problem

- **task: small; impact: quality-of-life**
   make a `safe_vcg` method in CRefine that doesn't split the state or instantiate schematics
  - consider replacing `vcg`

- **task: small; impact: quality of life**
   Raf's go-to-error script, but for blue and yellow warnings. This will facilitate other issues that want to address warnings.
  - jump to next warning
  - auto-solve logging (but takes long)

- **task: small; impact: quality of life** Split `DetSchedSchedule` into multiple files (especially for MCS)
  - more generally: when should we split files?
  - what should be in which files? (needs more thinking)

- **task: small; impact: some quality of life** modernise Isabelle use, e.g.
    datatype accessors and discriminators, e.g.
    [VER-1015](<https://sel4.atlassian.net/browse/VER-1015>)

- **task: small; impact: quality of life** corres rule names are confusing
    [VER-317](<https://sel4.atlassian.net/browse/VER-317>)
  - some of this has happened, more to do be done

- **task: small-medium, impact: quality of life**, arch-split interface locale
  - find narrower interface, make more things generic
  - simplification of current assumptions, as it stands it's really
     "almost everything"

- **task: medium; impact: quality of life** Rework `SimplExportAndRefine` as a
   rule-driven export process, such that exported specifications are correct by
   construction. (Currently, the export is untrusted, and the proof is a
   post-hoc process that is fragile and hard to understand). This is an
   opportunity to learn how to build rule-driven automation.

- **task: small, impact: quality of life, more automation**
   Automatically derive `fun/simp`, `case`, `exists` variants for
   discriminator-style definitions like `is_ntfn_cap` (and more complex ones).
   [VER-1315](<https://sel4.atlassian.net/browse/VER-1315>)

### Tier 3

- **task: small; impact: quality-of-life** style guide
  - write style guide: started in <https://github.com/seL4/l4v/pull/265>
  - apply style guide to at least `ASpec` and important theories in other
     sessions
  - find a way to incrementally converge existing files on chosen style

- **task: small; impact: quality of life** policy and maybe automated checks on session import graph, esp across sessions
  - two choke points (import + export/merge)
  - visualise/report what is being overwritten in a merge
  - avoid `[simp del]` resurrection (also for syntax etc)

- **cleanup/automation** automatic detection of auto-solved goals
  - little blue warnings are not effective enough
  - needs a hook (e.g. as part of lemma command)
  - Thomas added an isabelle option for auto-solve etc: what's the command, how to dig it out of the log
    - how do we make use of it? Remove false positives

- **task: medium, maybe small after all?; impact: quality of life** An actually searchable output/state buffer (needs Scala experience)

- **task: small-medium; impact: quality of life** clean up wp and move to AFP
  [VER-596](<https://sel4.atlassian.net/browse/VER-596>)

- **task: small; impact: quality of life** add getter `wp` rules into the `wp` set
    [VER-1311](<https://sel4.atlassian.net/browse/VER-1311>)
  - needs reworking some very old proofs (which should be cleaned up anyway)
  - not sure how many proofs will break

### Tier 4

- **task: small; impact: quality of life** usable front-end for `unused_thms`; could add to regression test
  - about 1 month of work, needs mostly a false-positive list and some UI

- **task: small; impact: quality of life**
   Which projection approach to use when? Needs thinking/consultation.

- **task: small; impact: quality of life**
   Better performance monitoring. There's been times that we've made changes to tools and struggled to work out how it affected overall performance
  - dumps? graphs?
  - a web page which tracks AInvs, Refine, CRefine
  - some actual statistics to reduce noise

- **task: small-medium, impact: quality of life** decent dependency analysis (based on levity? see above)
  - lets us find lemmas/commands(crunch?) that lets us find things only
     dependent on certain image
  - problem with transitivity: A depending on B which is abstract-only
     but in refine
  - related to [VER-544](<https://sel4.atlassian.net/browse/VER-544>)

- **task: small-medium, impact: quality of life** `unat (x + y) = unat x + unat y`
  - but want an automatic constraint reasoner to find that `x` is limited, `y` is
     limited and so the sum is limited below overflow threshold
  - similarly `unat (of_nat x)` when it's bloody obvious that `x < M`, or `x <= M`
     and `M <` or `<=` the required constraint
  - also, this is a complete nightmare for signed words (e.g. dealing with msb)
  - student project? might be too hard... honors thesis?
  - simpproc? Eisbach?

- **task: small-medium; impact: quality of life** policy and maybe checks on global declares (esp cong and split)
    [VER-1240](<https://sel4.atlassian.net/browse/VER-1240>)

- **task: small; impact: quality of life** don't include unused separation logic stuff in C semantics; clean up UMM
    [VER-962](<https://sel4.atlassian.net/browse/VER-962>)

### Tier 5

- **task: small-medium, impact: soundness** make machine ops a locale (Refine, AInvs etc)
  - should avoid axioms
  - but means everything is in a locale -> performance problem

- **cleanup** internal/misc/regression (remove)

- **cleanup** sep algebra sync with AFP

- **cleanup** device memory
  - check: in InfoFlow do we clear the device regions or do we demand there are
     none
  - check model of device memory in ADT/global automaton

- **cleanup** Cleanup:
  - cleanup: make monadic lemmas that feature maintenance
      of the bound-to variable name
         `x >>= (\lam rv. m rv)) NOT x >>= m`
    - automatable? doubtful... maybe a warning possible?
    - monadic bind framework is renaming most binds to `x`, but
        not clear if that can be avoided

- **cleanup** rename `ASepSpec` and `Bisim` to better reflect what they are

- **cleanup/speedup** testing for the arch matrix:
  - all possible features for all arches all the time?
  - subset for faster check?

- **task: small-medium; impact: some quality of life** automate/improve the monadic rewrite framework
    [VER-727](<https://sel4.atlassian.net/browse/VER-727>)
  - something in the direction of `ccorres_rewrite`
  - use conversions maybe
