<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

CapDL Refinement Proof
======================

This proof establishes that seL4's [abstract specification][aspec] is
a formal *refinement* (i.e. a correct implementation) of its [capDL
specification][capDL]. It is described as part of an ICFEM '13
[paper][paper].

  [aspec]: ../../spec/abstract/
  [capdl]: ../../spec/capDL/
  [paper]: https://trustworthy.systems/publications/nictaabstracts/Boyton_ABFGGKLS_13.abstract "Formally Verified System Initialisation"

Building
--------

To build for the ARM architecture from the `l4v/` directory, run:

    L4V_ARCH=ARM ./run_tests DRefine

Important Theories
------------------

The top-level theory where the refinement statement is established over
the entire kernel is [`Refine_D`](Refine_D.thy); the state-relation that
relates the state-spaces of the two specifications is defined in
[`StateTranslation_D`](StateTranslation_D.thy) and the basic
correspondence property proved over each kernel function is defined in
[`Corres_D`](Corres_D.thy).

