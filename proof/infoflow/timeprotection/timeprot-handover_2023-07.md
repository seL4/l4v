<!--
     Copyright 2023, The University of Melbourne (ABN 84 002 705 224)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

Here we document the current status of the *seL4 time protection* project and
outstanding tasks towards its projected future milestones as of July 2023.

## Summary of milestones and their tasks

- **Time protection verification of new ASpec as a separation kernel:**
  Gives assurances about seL4 as specified.
  - *Labour estimate:* 1-2 person-years (FM postdoc-level)
  - **InfoFlow**: Instantiate TP extension locale with new ASpec relative to
    all needed kernel invariant/infoflow lemmas
    (~17 sorries, TimeProtectionIntegration.thy).
  - **AInvs, Access, Infoflow**: Prove all *new* needed TA subset invariant
    (~132 sorries, CachePartitionIntegrity.thy) and other infoflow lemmas like
    TA-equivalence preservation (TBC) about the new ASpec.
  - Fix all *other* breakages in **AInvs** (~245; ~1 p.y), **Access** (~94;
    original was 1 p.y over 4mo), **Infoflow** (~346 sorries after deducting
    the ones already counted above; original took longer than Access proofs).
  - **Refine**: Prove "no-fail" assertions. (Count: ~125 instances of
    `touch_object` from the new ASpec to add equivalents of to **ExecSpec**.)

- **Time protection verification of new CSpec as a separation kernel:**
  Gives assurances about seL4's C implementation.
  - *Labour estimate:* 1-2 person-years (FM postdoc-level)
  - **Refine, CRefine**: Formalise preservation of all necessary invariants.
  - **InfoFlowC**: Instantiate time protection for new CSpec.
  - **CSpec**: Add `touchObject` annotations to CSpec, possibly automate it in
    the C parser. (If manual probably easy; if automated we anticipate it may
    be an interesting task to match up to ExecSpec, ASpec-level TA accounting.)
  - Fix all *other* resulting breakages in **CRefine**.

- **Time-protected one-way notifications and shared memory support for seL4:**
  New time protection mechanisms and their empirical evaluation supporting an
  ideal use case beyond mere separation kernel policies.
  - *Labour estimate:* 3.5 person-years (systems PhD)
  - Unknown but probably significant TP verification impact, particularly on
    the modelling of the domainswitch sequence.

- **Time protection verification of IRQ partitioning:**
  Have the seL4 information-flow security proofs support more IRQs than timer.
  - *Labour estimate:* Currently not estimated (FM postdoc-level)
  - This will involve relaxing the existing interrupt oracle and
    phrasing/proving new AInvs.

## How to pre-build and open relevant Isabelle sessions

Our target for this verification project is `L4V_ARCH=RISCV64`.

To browse InfoFlow against a pre-built Access session, you'll need to use the
following `QUICK_AND_DIRTY` options both when pre-building and opening all
sessions it depends on until the sorries in those sessions have been resolved:

    cd spec
    L4V_ARCH=RISCV64 AINVS_QUICK_AND_DIRTY=true ACCESS_QUICK_AND_DIRTY=true make -j3 ASpec
    cd ../proof
    L4V_ARCH=RISCV64 AINVS_QUICK_AND_DIRTY=true ACCESS_QUICK_AND_DIRTY=true make -j3 Access
    cd ..
    L4V_ARCH=RISCV64 AINVS_QUICK_AND_DIRTY=true ACCESS_QUICK_AND_DIRTY=true ./isabelle/bin/isabelle jedit -d . -l Access

To browse Refine to work on the "no-fail" proofs you will need ExecSpec and
BaseRefine. Even though Access is not strictly needed for this, it is best to
keep the same `QUICK_AND_DIRTY` options to avoid any unnecessary rebuilds:

    cd spec
    L4V_ARCH=RISCV64 AINVS_QUICK_AND_DIRTY=true ACCESS_QUICK_AND_DIRTY=true make -j3 ExecSpec
    cd ../proof
    L4V_ARCH=RISCV64 AINVS_QUICK_AND_DIRTY=true ACCESS_QUICK_AND_DIRTY=true make -j3 BaseRefine
    cd ..
    L4V_ARCH=RISCV64 AINVS_QUICK_AND_DIRTY=true ACCESS_QUICK_AND_DIRTY=true ./isabelle/bin/isabelle jedit -d . -l BaseRefine

More relevant for any future milestones that will depend on InfoFlow, similarly
there is also an `INFOFLOW_QUICK_AND_DIRTY` option that will be needed if it
still contains any sorries:

    L4V_ARCH=RISCV64 AINVS_QUICK_AND_DIRTY=true ACCESS_QUICK_AND_DIRTY=true INFOFLOW_QUICK_AND_DIRTY=true make -j3 InfoFlow
    L4V_ARCH=RISCV64 AINVS_QUICK_AND_DIRTY=true ACCESS_QUICK_AND_DIRTY=true INFOFLOW_QUICK_AND_DIRTY=true ./isabelle/bin/isabelle jedit -d . -l InfoFlow

## Outstanding task details and examples for TP verification of ASpec

### TA equivalence proofs as part of the unwinding relation

The TP integration theory
(file: proof/infoflow/timeprotection/TimeProtectionIntegration.thy)
requires that the unwinding relation preserves the equivalence of the
*touched-addresses* (TA) set.

To that end, this equivalence was added as a new conjunct to the seL4 unwinding
relation, resulting in new sorried breakages throughout the InfoFlow session.

**These need to be fixed.**

### TA subset invariant proofs

The *TA subset invariant* states that all addresses in the TA set belong to
labels that are reachable from the label of the currently running domain,
according to the policy graph. (For a separation kernel policy, this is just
the very same label as that of the currently running domain.)

The TP integration theory
(file: proof/infoflow/timeprotection/TimeProtectionIntegration.thy)
currently leans on `wp` lemmas for preserving the TA subset invariant
throughout the various monads of the kernel, which are largely sorried
(file: proof/infoflow/timeprotection/CachePartitionIntegrity.thy).

**These need to be proved.** Some examples of completed such lemmas in
`CachePartitionIntegrity` include:
- `set_object_ta_subset_inv`
- `touch_object_ta_subset_inv`
- `resolve_address_bits_ta_subset_inv`
- `lookup_slot_for_thread_ta_subset_inv`
- `lookup_cap_and_slot_ta_subset_inv`

There may also be some scope for trimming away unneeded preconditions upon
proving the `wp` lemma stubs, which were obtained from the output of `crunch`
attempts; some of these potential opportunities are marked with comments.

### "No label-straddling objects" invariant proofs

The TA subset invariant proofs lean on a new invariant
`no_label_straddling_objs` defined in `CachePartitionIntegrity`. For now, it
is assumed via a sorried lemma in that file to follow from `pas_refined`
(lemma `pas_refined_no_label_straddling_objs`).

**This needs to be proved as invariant over the kernel**, which Gerwin expects
to be possible. We have the choice of either:
1. adding it as a new conjunct of `pas_refined` (Gerwin's suggestion) and
   repairing the resulting breakages to `pas_refined`-related proofs (`wp`
   lemmas that prove it is invariant and others) across Access and InfoFlow.
2. proving it invariant separately from `pas_refined`.

### Rework ASpec to clone the idle thread for each domain

Proving the TA subset invariant holds at mid-domainswitch point revealed
something missed in the original ASpec TP update: the ASpec and InfoFlow proofs
currently assume the idle thread to be global, but the actual C implementation
of kernel cloning creates copies of these in coloured memory for each domain.

Consequently, the current thread (`cur_thread`) is not actually of the correct
label when domainswitch happens from an idle state, as in these instances it is
the global idle thread (`idle_thread`). The resulting sorry is in lemma
`oldclean_preserves_ta_subset_inv` of `TimeProtectionIntegration`.

**The ASpec needs to be updated to reflect the actual C implementation choice
to clone the idle thread**; we expect this to cause an unpredictable number of
proof breakages across AInvs, Access and InfoFlow, **which will need to be
repaired**. However, this should make the TA subset invariant proof at
mid-domainswitch easily provable when domainswitch happens from an idle state.

### Refine "no-fail" proofs

TODO.
