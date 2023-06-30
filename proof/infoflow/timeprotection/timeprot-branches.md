<!--
     Copyright 2022, The University of Melbourne (ABN 84 002 705 224)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Branches of L4v for Time Protection

## Remotes

- Main L4v repo `verification`: <https://github.com/seL4/l4v.git>
- Scott's fork `scottbuckley`: <https://github.com/scottbuckley/l4v.git>
- Rob's fork `robs-cse`: <https://github.com/robs-cse/l4v.git>

## Experimental synchronisation branch

Location: `verification/experimental-timeprot`

Protocol:
- Before pushing anything to this branch, we'll either (1) merge up to it or
  (2) rebase onto it -- i.e. **we won't force push** anything to this branch.
- We'll push reasonably stable versions of *features* to this branch from our
  active development branches by agreement between us, when someone else needs
  them to proceed.
- We'll keep *project documentation* (e.g. this file) up to date on this branch
  by pushing any updates to it as frequently as needed.
- To be able to keep full experimental history on this branch while avoiding
  both (1) messy rebasing of that full commit history onto *mainline*
  (`verification/master`) and (2) diverging history between our
  active development branches:
  - If any of us needs something from mainline, we'll merge this branch
    **up to** mainline on agreement -- **we won't rebase it** onto mainline.
  - Later, we'll cherrypick and rebase separable features from here to prepare
    them for merge review into L4v mainline -- i.e. we won't be rebasing this
    branch as a whole onto it.

Features:
- Time protection extension locale and example instantiation (InfoFlow)
  development by Scott and Rob from Nov 2021 to Jun 2023, including:
  - Split of extension locale into interfaces for HW + transition system.
  - Instantiation of transition system locale by seL4 InfoFlow automaton.
  - TA set equivalence integration into unwinding relation by Scott.
    (Archived: `scottbuckley/experimental-timeprot`)
  - TA subset invariant integration and lemma stubs by Rob.
    (Archived: `robs-cse/timeprot-subset-invs`)
- Partial fixes and sorries in AInvs, Access, InfoFlow for the following:
  - Initial *touched-addresses* (TA) set collection and enforcement mechanisms
    for `kheap` accesses (ASpec) by Scott.
  - TA-agnostic invariant machinery (AInvs) by Scott.
  - Initial domainswitch sequence draft (ASpec) by Rob.
    (Archived: `robs-cse/experimental-tpspec`)
- Partial fixes and sorries in AInvs for the following:
  - New `f_kheap` TA collection enforcement mechanism (ASpec) and adaptations
    to the change of interface (AInvs) by Scott, Gerwin and Rob.
    (Archived: `robs-cse/timeprot-use-f-kheap`)
  - Addition of `touch_object` TA accounting throughout ASpec by Rob.
    (Archived: `robs-cse/timeprot-touch-objs`)
- Partial progress in ExecSpec and Refine of (1) "no-fail" proofs for new
  ASpec-level TA membership assertions on address access and (2) additions of
  new TA accounting to ExecSpec with which to prove correspondence with ASpec.
  (Archived: `robs-cse/timeprot-haskell-refine`)

Status: Merged up to `verification/master` commit `e1fd4229b`.

(See: <https://github.com/seL4/l4v/compare/master...experimental-timeprot>)

## Active development branches

### `scottbuckley/experimental-timeprot`

Features: Ongoing handover cleanups.

(See: <https://github.com/seL4/l4v/compare/experimental-timeprot...scottbuckley:experimental-timeprot>)

## Archive branches we're not intending to merge

- `robs-cse/experimental-timeprot-pr425-backup`:
  Safety backup of former status of `verification/experimental-timeprot`
  before a force push by Rob to fix diverging history due to Git dropping
  Scott's DCO sign-off commits when pull request #425 was merged.

