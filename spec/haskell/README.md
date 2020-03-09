<!--
     Copyright 2014, General Dynamics C4 Systems

     SPDX-License-Identifier: GPL-2.0-only
-->

The seL4 Haskell Model
======================

The sources in this directory can be used to build a Haskell Cabal package
containing an executable model of the seL4 kernel. The model cannot run
stand-alone; it must be integrated into a simulator that can run user-level
binaries and generate events that the kernel model can process.

To build it:
  - install the Haskell build tool [stack][].
  - run `make`

The `Makefile` will use `stack` to fetch appropriate versions of `ghc` and
`cabal-install`.

After that, you can compile Haskell programs using the simulator by adding
`-package SEL4` to the `ghc` command line. Note that the qemu target requires
some callback functions to be accessible via the FFI, so it is not possible to
load a model compiled for those targets in GHCi.

Currently, the simulator interface is out of date, so this model is currently
only useful as documentation and as intermediate artefact in the seL4
correctness proof. The model itself is kept up to date with the C code, only
the simulator interface is outdated.

[stack]: https://haskellstack.org/
