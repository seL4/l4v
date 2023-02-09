<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

The Abstract Specification of seL4
==================================

    l4v/spec/abstract/

This directory contains the main Isabelle sources of the seL4 abstract
specification. The specification draws in additional interface files from
`design` and `machine`.

The specification is written in monadic style. See
`l4v/lib/Monads/NonDetMonad` for the definition of this monad.

Top-Level Theory
----------------

The top-level theory file that draws the whole specification together is
`Syscall_A`, the top-level function in that theory is `call_kernel`.

This top-level function defines in-kernel behaviour. Later in the proof,
in particular in `invariant-abstract`, this function is further wrapped
in an automaton that describes system behaviour.

Entry Points
------------

Two useful entry points for browsing the abstract specification are the
theories `Structures_A` and `ARM_Structs_A`. They define the state space
of the kernel model, including what capabilities and kernel objects are.

The theories `Invocations_A` and `ArchInvocation_A` define datatypes for
the capability invocations/operations the kernel understands.

Most theories are named after the subsystem of the kernel they specify.

Building
--------

The corresponding Isabelle session is `ASpec`. It is set up to build a
human-readable PDF document. `Glossary_Doc` contains definitions of common
seL4 terms.

To build, run in directory `l4v/spec`:

    make ASpec

Remarks
-------

 * Note that this specification is actually an extensible _family_ of
   specifications, with predefined extension points. These points can
   either be left generic, as for most of the abstract invariant proofs,
   or they can be instantiated to more precise behaviour, such as in
   the theory `Deterministic_A`, which is used for the information flow
   proofs.

 * The theory `Init_A` *does not* define real kernel initialisation.
   Instead it is a dummy initial state for the kernel to demonstrate
   non-emptiness of abstract kernel invariants.

 * `KernelInit_A` is a paused project and not currently included in
   the rest of the specification.

