<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

ProofCount
==========

ProofCount is a tool that collects metrics from finished
Isabelle proofs. Specifically it finds the starting and ending
lines for each lemma.
The result of this count is saved in
an xml file that can then be processed for metric analysis.
Additionally the constant dependency graph is saved,
as well as the theory dependency graph. This file
can then be processed to compute metrics on the proof.


Quickstart
----------

To use ProofCount you need to install it as an isabelle component.

The script "install.sh" found in the main proofcount directory
takes an isabelle executable and adds ProofCount as a component to it.

Usage:

   ./install.sh isabelle [-P]

The -P option will patch the given isabelle install (after installing proofcount)
to enable metric collection, by applying "isabelle\_patch.diff".


Once proofcount is installed it can be executed as an isabelle tool:

   isabelle proofcount -x l4v.xml -d ~/verification/l4v -L AInvs -T AInvs

This will re-check the invariant proof and emit l4v.xml when finished. This
file contains the line information for each lemma, the lemma dependency graph,
the constants used in each lemma, the constant dependency graph and the theory
dependency graph.

Once this file exists, we can use proofcount to perform its default metric analysis.

   isabelle proofcount -x l4v.xml -N AInvs -s Lib -s CapRights\_A -b Invariants\_AI -f AInvs.akernel\_invs

This will emit a single metric calculation from the proofs in l4v.xml called "AInvs". The constant
dependency graph will be restricted to those constants which depend on the "CapRights\_A" or "Lib" theories.
The lemma dependency graph will be restricted to lemmas which depend on "Invariants\_AI", and
are present in the dependencies for the top-level lemma "AInvs.akernel\_invs".

Options
-------
Proofcount options are passed as usual command-line flags. There are roughly two categories of options,
those which affect the actual proof counting and those which are used as part of the metric analysis.


The options are:

  * `-x FILE`: The name of the xml file, either as input or output depending on
    if a proof is being counted or if metrics are being computed.

  * Counting flags:

    * `-d DIR`: The ROOT directory for building the proof to be counted.
      Similar to the same flag given to `isabelle build`.

    * `-L LOGIC`: The name of the logic image to build the proof against. It must
      appear somewhere in the ROOTS files given in the ROOT directory.

    * `-T THEORY`: The name of the top-level theory. All dependencies of this
      theory will be counting.

  * Metric flags:

    * `-N NAME`: The name of the metric to be computed. Used to name the output files and
      latex macros.

    * `-D DIR`: The directory to output the resulting metrics.

    * `-s THEORY`: A base `specification` theory. This flag may be given multiple times.
      Any constant which does not depend on a base specification theory will not be considered
      in metric collection. This is usually chosen liberally to include all constants defined as
      part of a proof development.

    * `-b THEORY`: A base `proof` theory. This flag may be given multiple times.
      Any lemma which does not depend on a base proof theory will not be considered in
      metric collection. This should be chosen carefully so that only lemmas
      part of the desired proof are counted.

    * `-t THEORY`: A top-level `proof` theory. This flag may be given multiple times.
      Any lemma which depends on a top-level theory, but is not from that theory
      (i.e. is `above` that theory) will not be considered in metric collection.
      This is used in cases where multiple proofs are part of the given logic image
      and we wish to separate them.


    * `-f LEMMA`: The name of a top-level lemma statement. This flag may ba given multiple times.
      Any lemma which is not in the recursive dependencies of a top-level lemma will
      not be considered in metric collection. This is generally a single lemma that
      is the `final` proof for the development.


Output Files
------------

Metric computing produces multiple output files which can be used for analysis. For each
named metric there are 4 files produced:

  * NAME\_report.txt: This is an overview of the metric collection. It contains the total
    number of lemmas counted, total number of lines counted as well as information
    about the top-level statement. Additionally it gives information about what
    specification and proof theories were used to compute the metric.

  * NAME\_orphans.txt: This lists lemmas which were not in the dependency graph
    of any given top-level fact. It says the same of the lemma, and its root
    in the dependency graph, i.e. the topmost lemma that depends on it.

  * NAME\_summary.tex: This is a latex file that defines
    macros for some of the numbers in the report.

  * metrics\_NAME\_num\_deps.txt: This is a machine-readable file which
    has one entry per lemma, giving the specification size, idealized
    specification size and proof size respectively.


Specification Size
------------------

The specification size of a lemma is measured as the total number of unique constants
required to write the lemma statement. This excludes constants which are outside
of the theory range given by the `-s` option. The idealized specification size
removes constants whose definitional lemmas do not appear in the dependency
graph of the lemma.
