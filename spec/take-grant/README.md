<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

An Abstract Take/Grant Security Model
=====================================

    l4v/spec/take-grant/

This directory contains the Isabelle sources of an abstract take-grant
security model, studying some of the underlying concepts of seL4's protection
mechanisms.


Overview
--------

 * `System_S` contains the operations and state space of the model.
 * `Confine_S` shows authority confinement
 * `Islands_S` explicitly defines the concept of authority-isolated islands
   and authority confinement on this concept.
 * `Isolations_S` defines a notion of high-level information flow on
   take-grant authority and shows that islands stay isolated.
 * `Example` and `Example2` are two example systems in this model.


Building
--------

The corresponding Isabelle session is `TakeGrant`. To build for the ARM
architecture, run in directory `l4v/`:

    L4V_ARCH=ARM ./run_tests TakeGrant


Remarks
-------

 * This specification is *not* connected with the seL4 code and does *not*
   completely describe seL4 behaviour. Instead, it is a more abstract study
   of the underlying concepts.
 * A previous, simpler version of this model has appeared in Dhammika
   Elkaduwe's PhD thesis.
 * A description of the extended, more recent model can be found in
   Andrew Boyton's PhD thesis.
