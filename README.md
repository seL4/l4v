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

This repository is meant to be used as part of a Google [repo][4] setup.
Instead of cloning it directly, please go to the following repository
and follow the instructions there:

   https://github.com/seL4/verification-manifest

For setting up the theorem prover, please see the section
[Isabelle Setup](#isabelle-setup) below.

  [4]: http://source.android.com/source/downloading.html#installing-repo     "google repo installation"

Overview
--------

The repository is organised as follows.

 * [`spec`](spec/): a number of different formal specifications of seL4
    * [`abstract`](spec/abstract/): the functional abstract specification of seL4
    * [`design`](spec/design/): the Haskell-generated design-level specification of seL4
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
   abstract separation logic formalisation, a prototype of the [Eisbach][5] proof
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


  [5]: http://www.nicta.com.au/pub?id=7847           "An Isabelle Proof Method Language"


Isabelle Setup
--------------

The proofs in this repository use `Isabelle2013-2`. A copy of Isabelle
is included in the repository setup.

The dependencies for installing Isabelle are
  * Perl 5.x with `libwww`
  * Python 2.x
  * LaTeX (e.g. `texlive`)
  * 32-bit C/C++ standard libraries on 64-bit platforms (optional)

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

Alternatively, it is possible to use the official Isabelle2013-2 release
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

Proof sessions that do not depend on the C code can be built directly with

    ./isabelle/bin/isabelle build -d . -v -b <session name>

from the directory `l4v/`. For available sessions, see the corresponding
`ROOT` files in this repository. There is roughly one session corresponding to
each major directory in the repository.

For proof sessions that depend on the C code, for instance `CSpec`, `CRefine`,
or `CBaseRefine`, go for instance to the directory `l4v/proof` and run

    make CRefine

See the `HEAPS` variable in the corresponding `Makefile` for available
targets. The `make` command should also work for sessions that do not depend
on C code.

For interactively exploring, say the invariant proof of the abstract
specification with a pre-built logic image for the abstract specification,
run

    ./isabelle/bin/isabelle jedit -d . -l ASpec

and open one of the files in `spec/invariant-abstract`.


License
-------

The files in this repository are released under standard open source
licenses. Please see the individual file headers and
[`LICENSE_GPLv2.txt`](LICENSE_GPLv2.txt) and
[`LICENSE_BSD2.txt`](LICENSE_BSD2.txt) files for details.


