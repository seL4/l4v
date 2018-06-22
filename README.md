[![DOI][0]](http://dx.doi.org/10.5281/zenodo.591732)

  [0]: https://zenodo.org/badge/doi/10.5281/zenodo.591732.svg


[The L4.verified Proofs][1]
===========================

This is the L4.verified git repository with formal specifications and
proofs for the seL4 microkernel.

Most proofs in this repository are conducted in the interactive proof
assistant [Isabelle/HOL][2]. For an introduction to Isabelle, see its
[official website][2] and [documentation][3].

  [1]: https://github.com/seL4/l4v                   "L4.verified Repository"
  [2]: http://isabelle.in.tum.de                     "Isabelle Website"
  [3]: http://isabelle.in.tum.de/documentation.html  "Isabelle Documentation"

Repository Setup
----------------

This repository is meant to be used as part of a Google [repo][5] setup.
Instead of cloning it directly, please go to the following repository
and follow the instructions there:

   https://github.com/seL4/verification-manifest

For setting up the theorem prover and other dependencies, please see the
section [Dependencies](#dependencies) below.

  [5]: http://source.android.com/source/downloading.html#installing-repo     "google repo installation"

Contributing
------------

Contributions to this repository are welcome.
Please read [`CONTRIBUTING.md`](CONTRIBUTING.md) for details.

Overview
--------

The repository is organised as follows.

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
        can be read into Isabelle. This is generated from the [seL4 repository](../seL4).

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


Dependencies
------------

### Hardware

Almost all proofs in this repository should work within 4GB of RAM. Proofs
involving the C refinement, will usually need the 64bit mode of polyml and
about 16GB of RAM.

The proofs distribute reasonably well over multiple cores, up to about 8
cores are useful.

### Software

The proofs in this repository use `Isabelle2018`. A copy of Isabelle
is included in the repository setup.

The dependencies for installing Isabelle in this repository are

 * Perl 5.x with `libwww-perl`
 * Python 2.x
 * LaTeX, for instance on Ubuntu 14.04
   `sudo apt-get install texlive-fonts-recommended texlive-latex-extra texlive-metapost texlive-bibtex-extra`
 * 32-bit C/C++ standard libraries on 64-bit platforms (optional)

For running the standalone version of the C Parser you will additionally need

 * [MLton][7] ML compiler (package `mlton-compiler` on Ubuntu)

For building the Haskell kernel model, the Haskell build tool [stack][] is
required. The Haskell kernel `Makefile` will use `stack` to obtain appropriate
versions of `ghc` and `cabal-install`. Note that this repository does not
contain the QEmu interface for actually running the model.

For running the C proofs, you need a working C preprocessor setup for the seL4
repository.

*On Linux*: the best way to make sure you have everything is to install the
full build environment for seL4:

  * seL4 [development tool chain][8] on Debian and Ubuntu
  * `make` version 3.81 or higher

You can get away with avoiding a full cross compiler setup form the above,
but you will need at least these:

    sudo apt-get install python-pip python-dev libxml2-utils
    sudo pip install sel4-deps

*On MacOS*: here it is harder to get a full cross-compiler setup going. For
normal proof development, a full setup is not necessary, though. You mostly
need a gcc-compatible C pre-processor and python. Try the following steps:

  * install `XCode` from the AppStore and its command line tools. If you are
    running MacPorts, you have these already. Otherwise, after you have
    XCode installed, run `gcc --version` in a terminal window. If it reports a
    version, you're set. Otherwise it should pop up a window and prompt for
    installation of the command line tools.
  * install the seL4 Python dependencies, for instance using
    `sudo easy_install sel4-deps`.
    `easy_install` is part of Python's [`setuptools`][9].
  * install the [`misc/scripts/cpp`](misc/scripts/cpp) wrapper for clang,
    by putting it in `~/bin`, or somewhere else in your `PATH`.


[7]: http://mlton.org                               "MLton ML compiler"
[8]: http://sel4.systems/Info/GettingStarted/DebianToolChain.pml  "seL4 tool chain setup"
[9]: https://pypi.python.org/pypi/setuptools        "python package installer"
[stack]: https://haskellstack.org/


Isabelle Setup
--------------

After the repository is set up in Google repo, you should have following
directory structure, where `l4v` is the repository you are currently looking
at:

    verification/
        isabelle/
        l4v/
        seL4/

To set up Isabelle for use in `l4v/`, assuming you have no previous
installation of Isabelle, run the following commands in the directory
`verification/l4v/`:

    mkdir -p ~/.isabelle/etc
    cp -i misc/etc/settings ~/.isabelle/etc/settings
    ./isabelle/bin/isabelle components -a
    ./isabelle/bin/isabelle jedit -bf
    ./isabelle/bin/isabelle build -bv HOL-Word

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

Alternatively, it is possible to use the official Isabelle2018 release
bundle for your platform from the [Isabelle website][2]. In this case, the
installation steps above can be skipped, and you would replace the directory
`verification/isabelle/` with a symbolic link to the Isabelle home directory
of the release version. Note that this is not recommended for development,
since Google repo will overwrite this link when you synchronise repositories
and Isabelle upgrades will have to be performed manually as development
progresses.


Running the Proofs
------------------

If Isabelle is set up correctly, a full test for the proofs in this repository
can be run with the command

    ./run_tests

from the directory `l4v/`.

Not all of the proof sessions can be built directly with the `isabelle build` command.
The seL4 verification proofs depend on Isabelle specifications that are
generated from the C source code and Haskell model.
Therefore, it's recommended to always build using the supplied makefiles,
which will ensure that these generated specs are up to date.

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


License
-------

The files in this repository are released under standard open source
licenses. Please see the individual file headers and
[`LICENSE_GPLv2.txt`](LICENSE_GPLv2.txt) and
[`LICENSE_BSD2.txt`](LICENSE_BSD2.txt) files for details.


