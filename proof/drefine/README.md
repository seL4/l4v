CapDL Refinement Proof
======================

This proof establishes that seL4's [abstract specification][aspec] is
a formal *refinement* (i.e. a correct implementation) of its [capDL
specification][capDL]. It is described as part of an ICFEM '13
[paper][paper].

  [aspec]: ../../spec/abstract/
  [capdl]: ../../spec/capDL/
  [paper]: http://www.nicta.com.au/pub?id=7047 "Formally Verified System Initialisation"

Building
--------

To build from the `l4v/` directory, run:

    ./isabelle/bin/isabelle build -d . -v -b DRefine

Important Theories
------------------

The top-level theory where the refinement statement is established over
the entire kernel is [`Refine_D`](Refine_D.thy); the state-relation that
relates the state-spaces of the two specifications is defined in
[`StateTranslation_D`](StateTranslation_D.thy) and the basic
correspondence property proved over each kernel function is defined in
[`Corres_D`](Corres_D.thy).

