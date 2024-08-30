<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

[![DOI][0]](http://dx.doi.org/10.5281/zenodo.591732)

  [0]: https://zenodo.org/badge/doi/10.5281/zenodo.591732.svg


## [The L4.verified Proofs][1]

This is the L4.verified git repository with formal specifications and
proofs for the seL4 microkernel.

The proofs and specifications in this branch refer to seL4 version 12.0.0, with
proofs updated for the ZynqMP platform.

Most proofs in this repository are conducted in the interactive proof
assistant [Isabelle/HOL][2]. For an introduction to Isabelle, see its
[official website][2] and [documentation][3].

  [1]: https://github.com/seL4/l4v                   "L4.verified Repository"
  [2]: https://isabelle.in.tum.de/website-Isabelle2020/index.html  "Isabelle Website"
  [3]: http://isabelle.in.tum.de/documentation.html  "Isabelle Documentation"

## Setup

This repository is meant to be used as part of a Google [repo][5] setup. Instead
of cloning it directly, follow the instructions
[below](#checking-out-the-repository-collection).

  [5]: http://source.android.com/source/downloading.html#installing-repo     "google repo installation"

### Hardware + OS requirements

The proofs in this repository should work on Linux on x64 machines within 16B of
RAM. An 8-core or more CPU is recommended, but should not be required.

### Linux Packages - Ubuntu

On **Ubuntu 20.04**, to run all the tests against the **ARMv7-A** architecture
for the **ZynqMP** platform you will need to install the following packages:

```bash
supo apt update
sudo apt install \
    python3 python3-pip python3-dev \
    gcc-arm-none-eabi build-essential libxml2-utils ccache \
    libncurses-dev librsvg2-bin device-tree-compiler cmake \
    ninja-build curl zlib1g-dev texlive-fonts-recommended \
    texlive-latex-extra texlive-metapost texlive-bibtex-extra \
    mlton-compiler haskell-stack
```

### Google repo

Ubuntu 20.04 has no package for `repo`, so it has to be installed manually.
For instance in `~/.bin`:

```bash
mkdir -p ~/.bin
PATH=~/.bin:"${PATH}"
curl https://storage.googleapis.com/git-repo-downloads/repo > ~/.bin/repo
chmod a+rx ~/.bin/repo
```

### Python

The build system for the seL4 kernel requires several python packages, which are
collected in the meta-dependency `sel4-deps`:

```bash
pip3 install --user --upgrade pip
pip3 install --user sel4-deps
```

## Checking out the repository collection

The seL4 repositories use the [Google `repo` tool][repo] for configuration
control and managing sets of repositories. For verification, this means in
particular managing the correct combinations of the proofs, the kernel sources,
and the Isabelle/HOL theorem prover.

The [verification-manifest] repository records which versions of these are known
to work well together.

To check out a consistent set of repositories for this branch, run the following
steps:

```sh
mkdir verification
cd verification
repo init -b zynqmp-nofpu-ver-v12 -u https://git@github.com/seL4/verification-manifest.git
repo sync -j 4
```

[repo]: https://gerrit.googlesource.com/git-repo/+/HEAD/README.md
[verification-manifest]: https://github.com/seL4/verification-manifest


## Isabelle Setup

After the repository is set up using `repo` (as per the [setup section](#setup) above), you
should have following directory structure, where `l4v` is the repository you
are currently looking at:

```bash
verification/
    isabelle/
    l4v/
    seL4/
```

To set up Isabelle for use in `l4v/`, assuming you have no previous
installation of Isabelle, run the following commands in the directory
`verification/l4v/`:

```bash
mkdir -p ~/.isabelle/etc
cp -i misc/etc/settings ~/.isabelle/etc/settings
./isabelle/bin/isabelle components -a
./isabelle/bin/isabelle jedit -bf
./isabelle/bin/isabelle build -bv HOL-Word
```

These commands perform the following steps:

 * create an Isabelle user settings directory.
 * install L4.verified Isabelle settings.
   These settings initialise the Isabelle installation to use the standard
   Isabelle `contrib` tools from the Munich Isabelle repository and set up
   paths such that multiple Isabelle repository installations can be used
   side by side without interfering with each other.
 * download `contrib` components from the Munich repository. This includes
   Scala, a Java JDK, PolyML, and multiple external provers. You should
   download these, even if you have these tools previously installed
   elsewhere to make sure you have the right versions. Depending on your
   internet connection, this may take some time.
 * compile and build the Isabelle PIDE jEdit interface.
 * build basic Isabelle images, including `HOL-Word` to ensure that
   the installation works. This may take a few minutes.

Alternatively, it is possible to use the official Isabelle2020 release
bundle for your platform from the [Isabelle website][2]. In this case, the
installation steps above can be skipped, and you would replace the directory
`verification/isabelle/` with a symbolic link to the Isabelle home directory
of the release version. Note that this is not recommended for development,
since Google repo will overwrite this link when you synchronise repositories
and Isabelle upgrades will have to be performed manually as development
progresses.


## Running the Proofs

### Proof check

If Isabelle is set up correctly, a full test for the proofs in this repository
can be run with the command

    ./run_tests

from the directory `l4v/`. For the default ARM architecture and ZynqMP platform,
the command should run and report 49 sessions as passing.

### Interactive proof exploration

Not all of the proof sessions can be built directly with the `isabelle build`
command. The seL4 verification proofs depend on Isabelle specifications that are
generated from the C source code and Haskell model. Therefore, it is recommended
to always build using the supplied makefiles, which will ensure that these
generated specs are up to date.

To do this, enter one level under the `l4v/` directory and run `make <session-name>`.
For example, to build the C refinement proof session, do

    cd l4v/proof
    make CRefine

As another example, to build the session for the Haskell model, do

    cd l4v/spec
    make ExecSpec

See the `HEAPS` variable in the corresponding `Makefile` for available targets.

Proof sessions that do not depend on generated inputs can be built directly with

    ./isabelle/bin/isabelle build -d . -v -b <session name>

from the directory `l4v/`. For available sessions, see the corresponding
`ROOT` files in this repository. There is roughly one session corresponding to
each major directory in the repository.

For interactively exploring, say the invariant proof of the abstract
specification with a pre-built logic image for the abstract specification,
run

    ./isabelle/bin/isabelle jedit -d . -l ASpec

in `l4v/` and open one of the files in `proof/invariant-abstract`.


## Repository Overview

The repository is organised as follows.

 * [`docs`](docs/): documentation on conventions, style, etc.

 * [`spec`](spec/): a number of different formal specifications of seL4
    * [`abstract`](spec/abstract/): the functional abstract specification of seL4
    * [`sep-abstract`](spec/sep-abstract/): an abstract specification for a reduced
      version of seL4 that is configured as a separation kernel
    * [`haskell`](spec/haskell/): Haskell model of the seL4 kernel, kept in sync
      with the C code
    * [`machine`](spec/machine/): the machine interface of these two specifications
    * [`cspec`](spec/cspec/): the entry point for automatically translating the seL4 C code
      into Isabelle
    * [`capDL`](spec/capDL/): a specification of seL4 that abstracts from memory content and
      concrete execution behaviour, modelling the protection state of the
      system in terms of capabilities. This specification corresponds to the
      capability distribution language *capDL* that can be used to initialise
      user-level systems on top of seL4.
    * [`take-grant`](spec/take-grant/): a formalisation of the classical take-grant security
    model, applied to seL4, but not connected to the code of seL4.

    * There are additional specifications that are not tracked in this repository,
      but are generated from other files:
      * [`design`](spec/design/): the design-level specification of seL4,
        generated from the Haskell model.
      * [`c`](spec/cspec/c/): the C code of the seL4 kernel, preprocessed into a form that
        can be read into Isabelle. This is generated from the [seL4 repository](https://github.com/seL4/seL4).

 * [`proof`](proof/): the seL4 proofs
    * [`invariant-abstract`](proof/invariant-abstract/): invariants of the seL4 abstract specification
    * [`refine`](proof/refine/): refinement between abstract and design specifications
    * [`crefine`](proof/crefine/): refinement between design specification and C semantics
    * [`access-control`](proof/access-control/): integrity and authority confinement proofs
    * [`infoflow`](proof/infoflow/): confidentiality and intransitive non-interference proofs
    * [`asmrefine`](proof/asmrefine/): Isabelle/HOL part of the seL4 binary verification
    * [`drefine`](proof/drefine/): refinement between capDL and abstract specification
    * [`sep-capDL`](proof/sep-capDL/): a separation logic instance on capDL
    * [`capDL-api`](proof/capDL-api/): separation logic specifications of selected seL4 APIs

 * [`lib`](lib/): generic proof libraries, proof methods and tools. Among these,
   further libraries for fixed-size machine words, a formalisation of state
   monads with nondeterminism and exceptions, a generic verification condition
   generator for monads, a recursive invariant prover for these (`crunch`), an
   abstract separation logic formalisation, a prototype of the [Eisbach][6] proof
   method language, a prototype `levity` refactoring tool, and others.

 * [`tools`](tools/): larger, self-contained proof tools
    * [`asmrefine`](tools/asmrefine/): the generic Isabelle/HOL part of the binary
      verification tool
    * [`c-parser`](tools/c-parser/): a parser from C into the Simpl language in Isabelle/HOL.
       Includes a C memory model.
    * [`autocorres`](tools/autocorres/): an automated, proof-producing abstraction tool from
      C into higher-level Isabelle/HOL functions, based on the C parser above
    * [`haskell-translator`](tools/haskell-translator/): a basic python script for converting the Haskell
      prototype of seL4 into the executable design specification in
      Isabelle/HOL.

 * [`misc`](misc/): miscellaneous scripts and build tools

 * [`camkes`](camkes/): an initial formalisation of the CAmkES component platform
    on seL4. Work in progress.

 * [`sys-init`](sys-init/): specification of a capDL-based, user-level system initialiser
    for seL4, with proof that the specification leads to correctly initialised
    systems.


  [6]: http://www.nicta.com.au/pub?id=7847           "An Isabelle Proof Method Language"

