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

## Task details and examples

TODO.
