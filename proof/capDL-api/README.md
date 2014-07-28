CapDL API Proofs
================

This proof develops a formal API description for a number of the seL4
system calls, of the [capDL](../../spec/capDL/) kernel specification.
This API description is a set of lemmas describing the behaviour of
various system calls in terms of a [separation logic](../sep-capDL/)
defined over that kernel specification.

When reasoning about system calls this proof treats the kernel like
a library invoked directly from user-space and does not reason about
scheduling. These proofs are used by the [system initialiser
proof](../../sys-init), as described in the [ICFEM '13 paper][Boyton_13]
and Andrew Boyton's PhD thesis.

  [Boyton_13]: http://www.nicta.com.au/pub?id=7047 "Formally Verified System Initialisation"

Building
--------

To build from the `l4v/` directory, run:

    ./isabelle/bin/isabelle build -d . -v -b DSpecProofs

Important Theories
------------------

The top-level theory is [`API_DP`](API_DP.thy). The seL4 API and kernel
model are located in [`Kernel_DP`](Kernel_DP.thy).

