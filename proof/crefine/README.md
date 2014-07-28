C Refinement Proof
==================

This proof establishes that seL4's C code, once [translated][cspec] into
Isabelle/HOL using Michael Norrish's [C parser][parser], is a formal
*refinement* (i.e. a correct implementation) of its
[design specification][dspec] and, transitively (using the results of
the [Design Spec Refinement Proof][refine]) seL4's C code is also
a formal refinement of its [abstract specification][aspec]. In other
words, this proof establishes that seL4's C code correctly implements
its abstract specification.

  [cspec]: ../../spec/cspec/
  [parser]: ../../tools/c-parser/
  [dspec]: ../../spec/design/
  [refine]: ../refine/
  [aspec]: ../../spec/abstract/

The approach used for the proof is described in the TPHOLS '09
[paper][5].

  [paper]: http://www.nicta.com.au/pub?id=1842  " Mind the gap: A verification framework for low-level C"

Building
--------

To build from the `l4v/proof` directory, run:

    make CRefine

Important Theories
------------------

The top-level theory where the refinement statement is established over
the entire kernel is [`Refine_C`](Refine_C.thy); the state-relation that
relates the state-spaces of the two specifications is defined in
[`StateRelation_C`](StateRelation_C.thy).

Note that this proof deals with two C-level semantics of seL4: one
produced directly by the C parser from the kernel's C code, and another
produced by the C spec's [`Substitute`](../../spec/cspec/Substitute.thy)
theory. These proofs largely operate on the latter, proving that it
corresponds to the design spec. Refinement between the two C-level specs
is proved in the [`CToCRefine`](../../lib/clib/CToCRefine.thy) theory.
The top-level [`Refine_C`](Refine_C.thy) theory quotes both refinement
properties.

