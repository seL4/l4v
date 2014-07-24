# Design Spec Refinement Proof

This proof establishes that seL4's [design specification](../../spec/design/)
is a formal
*refinement* (i.e. a correct implementation) of its [abstract specification](../../spec/abstract/).
This proof also interweaves the definition and proofs
of the global invariant for the design specification, and builds on the 
[Abstract Spec Invariant Proof](../invariant-abstract/). It
is described in the TPHOLS '08 [paper][3].

## Building

To build from the `l4v/` directory, run:

        ./isabelle/bin/isabelle build -d . -v -b Refine

## Important Theories

The top-level theory where the refinement statement is established over
the entire kernel is [`Refine`](Refine.thy); the state-relation that relates the state-spaces
of the two specifications is defined in [`StateRelation`](StateRelation.thy) and the basic
correspondence property proved over each kernel function is defined in
[`Corres`](Corres.thy). 

[3]: http://nicta.com.au/pub?id=483		"Secure Microkernels, State Monads and Scalable Refinement"


