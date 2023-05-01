<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

CapDL User-level system initialiser
===================================

This contains a formalised algorithm and the proof of correctness of
a user-level system initialiser that uses [capDL](../spec/capDL/) to
specify the state of the resultant system.

It builds on the [CapDL API Proofs](../proof/capDL-api/), and uses
a [separation logic defined for capDL](../proof/sep-capDL/).

The system initialiser and the proof are described in the
[ICFEM '13 paper][Boyton_13] and Andrew Boyton's PhD thesis.

  [Boyton_13]: https://trustworthy.systems/publications/nictaabstracts/Boyton_ABFGGKLS_13.abstract "Formally Verified System Initialisation"

Building
--------

To build from the `l4v/` directory for the ARM architecture, run:

    L4V_ARCH=ARM ./run_tests SysInit

To build the example capDL specifications, from the `l4v/` directory, run:

    L4V_ARCH=ARM ./run_tests SysInitExamples


Important Theories
------------------

* The specification for the algorithm of the system initialiser is in
  [`SysInit_SI`](SysInit_SI.thy).

* The top-level statement of the correctness of the system-initialiser
  is found in [`Proof_SI`](Proof_SI.thy).

* The definition of what it means for an object to be initialised
  (`object_initialised` and (`irq_initialised`) is found in
  [`ObjectInitialised_SI`](ObjectInitialised_SI.thy).

* Only "well-formed" capDL specifications can be initialised. The
  definition of well-formed is located in
  [`WellFormed_SI`](WellFormed_SI.thy).

* Two example capDL specifications that are "well-formed" are found in
  [`ExampleSpec_SI`](examples/ExampleSpec_SI.thy) and
  [`ExampleSpecIRQ_SI`](examples/ExampleSpecIRQ_SI.thy). The former is a simple
  capDL spec, and the latter a more complicated specifications with IRQ
  support.

