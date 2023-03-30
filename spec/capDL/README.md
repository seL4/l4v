<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

The capDL Specification of seL4
===============================

    l4v/spec/capDL/

This directory contains the Isabelle sources of the seL4 behaviour
specification on the capDL abstraction level. The key features of this
abstraction level are that it models the complete protection state of the
kernel in terms of capabilities, and models, as far as possible, only the
protection state of the kernel (no memory or other state). This means, the
capDL specification contains a significantly higher degree of nondeterminism
compared to the other seL4 specs.

This specification is useful for the user-level initialiser that brings the
system from boot state into a defined protection state defined by a concrete
capDL description.

There is a refinement proof between the abstract specification and the capDL
specification in `proof/drefine/`. The capDL spec also forms the basis of the
system initialiser proofs.

Top-Level Theory
----------------

The top-level theory file in the specification is `Syscall_D`, the top-level
function in that theory is `call_kernel`.


Entry Points
------------

A key theory in the capDL spec is `Types_D` which defines a new capability
type that in addition to the seL4 capabilities contains 'virtual' capabilities
which store protection state information. For instance, the state of MMU page
tables is uniformly modelled as capabilities.


Building
--------

The corresponding Isabelle session is `DSpec`. To build for the ARM
architecture, run in directory `l4v/`:

    L4V_ARCH=ARM ./run_tests DSpec
