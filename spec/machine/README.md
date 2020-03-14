<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

The Machine Interface Specification of seL4
===========================================

    l4v/spec/machine/

This directory contains the Isabelle sources for the machine interface
specification used in the abstract and design specifications of seL4.

Overview
--------

 * `ARMMachineTypes`: ARM register set and related definitions.
 * `MachineOps`: definitions for the machine interface functions. Most
   interface functions are left non-deterministic. Some are assumed not to
   mutate C-observable state, others are defined in more detail.
 * `MachineTypes`: entry point to select a machine. Currently ARM only.
 * `Platform`: word size and other basic platform definitions.

Building
--------

This module is not built in isolation, but included in the `ASpec` and
`ExecSpec` sessions.

Remarks
-------

 * the theory `ARMMachineTypes` is generated from Haskell using the tool in
   `tools/haskell-translator` and the skeleton file in `spec/design/m-skel`.

