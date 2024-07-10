<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Documentation

This directory contains markdown and theory files with conventions and other
documentation for the l4v repository.

This is work in progress and contributions are welcome. Feel encouraged to
raise pull requests for more material and/or corrections.

## Topics

Current topics are:

- [Setup](setup.md) for doing seL4 proofs
- [Naming conventions](conventions.md) in this repository
- [Commit message](commit-messages.md) conventions in this repository
- [Proof style](Style.thy) rules for this repository
- Using [`find_theorems`](find-theorems.md) effectively
- Using [`find_consts`](find-consts.md) effectively
- [De-duplicating proofs](de-duplicating-proofs.md)
- [Compacting proofs](compacting-proofs.md)
- [Architecture Split](arch-split.md) Why and How-To
- [Haskell Assertions](haskell-assertions.md): how to use assertions in Haskell to use information from AInvs on Haskell and C levels
- General [CRefine Notes](crefine-notes.md)
- [Debugging VCG](vcg-debugging.md) goals and failures in CRefine
- [Platform branches](platform-branches.md) -- what they are and how to update them

## Plans

The directory [plans/](plans/README.md) contains ideas and plans for
proof-engineering improvements in this repo. They are at the idea stage, not
fully worked out yet. Feel free to contribute new ideas, to make an existing one
more concrete, or to pick one up and work on it.
