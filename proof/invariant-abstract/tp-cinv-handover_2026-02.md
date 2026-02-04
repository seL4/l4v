# Time Protection Colour Invariant Handover - Feb 2026

Documenting the work done:
- proving the colour invariant on top of `AInvs`, and
- creating a proof of concept for refining that result down to the `ExecSpec`
in the pursuit of formally verifying *time protection* in seL4's proofs.

## Background

The current approach taken to proving spatial isolation of protection domains (PD) is to add touched address (TA) bounding assertions to the `CSpec` (done separately on another branch and unlinked to this work at the moment) and `ExecSpec`, which state that any address touched (by object getters/setters) must lie within the colour allocation for the current PD. The former's generated proof obligations can be dispatched in `CRefine` by the latter, but to dispatch the latter's proof obligations we add an invariant in `AInvs` which states that *any kernel object that lies in a region of memory allocated to a PD (according to cache colours) must also only reference other regions of memory allocated to that same PD*.

This *colour invariant* is the main work attempted so far, with the end goal of adding the condition to `invs` so that it can be utilised in `Refine`. A second section of attempted work was trying to prove correspondence between methods in the unmodified `ASpec` and those in the `ExecSpec` which have been annotated with the TA assertions using an extra `ASpec` precondition (saying that any TAs lie within the allocated colours for the current domain). When the first task is complete, the plan is to use it to dispatch the extra precondition by noting that any TAs come from a kernel object and hence the colour invariant says the TA satisfies the relevant bounding.

## Summary

### Colour Invariant

#### Colour Oracle
- As we need a determination of what colours are allocated to what PDs, and we don't have a concrete implementation yet, there is a colour *oracle* which can have properties added to it so that we can replace it with a concrete implementation satisfying those properties in the future, whilst using the oracle for proof work in the meantime
- So far the only properties identified are that there should be no overlap between allocated colours, and 0/`NULL` is allocated to no colour (`retype_region` explicitly requires `NULL` to be a valid address referenced in any PD, but I found it was simpler to simply add that as a separate case in the invariant, rather than have that bit of overlap)
- There will need to be some alignment properties added in the future most likely (something along the lines of entire pages are coloured the same)
    - This will be needed for `Refine` as discussed below

#### Main Invariant
- With the oracle, the main invariant was stated, quantifying over all pointers and kernel objects, and all domains in the state
- A couple of helper methods to check kernel objects and capabilities satisfy the requirements were also made

#### Proofs
- The proofs were standard Hoare logic style proofs making use of weakest preconditions
- These were completed for `KHeap_A` and then a variety of methods above, working top down from `call_kernel`
- `crunch`-ing `call_kernel` provides a list of the next methods to be approached, and in this manner I slowly worked down `handle_invocation`'s dependencies
- To the best of my knowledge, the remaining methods to approach are: `cdl_intent_op`, `cdl_intent_cap`, `cdl_intent_extras`, `lookup_cap_and_slot`, `lookup_extra_cap`, `decode_invocation`, `mark_tcb_intent_error`, `perform_invocation`, `restart` and `corrupt_ipc_buffer` along with any dependencies that require separate proofs. These may not all need manual proofs as `crunch` may do its magic on some of them
    - In particular, `decode_invocation` and `perform_invocation` are likely to be the majority of the work

### Refinement
- Proof of concept `corres` lemmas were proved for `get_object` and `set_object`. `get_cap` also had a lemma completed, though it relied on a `sorry`-ed lemma - this lemma required extra properties of the colour oracle which I did not have time to articulate and utilise. However, the core `corres` proof was the main result and that worked fine.

### Other
- As part of proving the colour invariant, an extra invariant was proved and added to `invs`, stating that the current domain always lies within the domain list.

## Setup
The build target for this work is `L4V_ARCH=RISCV64`.

The work is split between two files:
- [`proof/invariant-abstract/ColourInv_AI.thy`](./ColourInv_AI.thy) built on top of the `AInvs` session for the abstract invariant work
- [`proof/refine/RISCV64/Colour_R.thy`](../refine/RISCV64/Colour_R.thy) built on top of the `Refine` session for the refinement work

To view and edit these files without having to build the relevant sessions every time, you need to pre-build them using the make commands, and then open them using Isabelle/jedit, as seen below:

```sh
# Pre-build
cd proof
L4V_ARCH=RISCV64 AINVS_QUICK_AND_DIRTY=true make -j3 AInvs
L4V_ARCH=RISCV64 AINVS_QUICK_AND_DIRTY=true make -j3 Refine
cd ..

# Open file in jedit
L4V_ARCH=RISCV64 AINVS_QUICK_AND_DIRTY=true ./isabelle/bin/isabelle jedit -d . -l AInvs proof/invariant-abstract/ColourInv_AI.thy
# OR
L4V_ARCH=RISCV64 AINVS_QUICK_AND_DIRTY=true ./isabelle/bin/isabelle jedit -d . -l Refine proof/refine/RISCV64/Colour_R.thy
```

Running `L4V_ARCH=RISCV64 ./run_tests` will run tests for every relevant session, and will also pre-build any sessions as needed. You can use this as a way to test that your initial setup is correct, as the tests should pass.