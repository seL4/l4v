# C Refinement Proof

This proof establishes that seL4's C code, once [translated](../../spec/cspec)
into Isabelle/HOL using Michael Norrish's [C parser](../../tools/c-parser/),  is
a formal *refinement* (i.e. a correct implementation) of its [design specification](../../spec/design/) and, transitively, --using the results
of the [Design Spec Refinement Proof](../refine/)-- seL4's C code is
also a formal refinement of
its [abstract specification](../../spec/abstract/). In other words,
this proof establishes that seL4's C code correctly implements its abstract
specification.

The proof is described in the TPHOLS '09 [paper][5].

## Building

To build from the `l4v/proof` directory, run:

        make CRefine

## Important Theories

The top-level theory where the refinement statement is established over
the entire kernel is [`Refine_C`](Refine_C.thy); the state-relation that relates the state-spaces
of the two specifications is defined in [`StateRelation_C`](StateRelation_C.thy).

[5]: http://www.nicta.com.au/pub?id=1842  " Mind the gap: A verification framework for low-level C"

