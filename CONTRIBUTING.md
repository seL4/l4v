<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Contributions Welcome

Contributions to the seL4 kernel verification repository are welcome!

Please raise issues or pull requests on github as usual.


## Build

If you're modifying existing proofs, texts, or tools, please make sure the
repository still builds before you send the pull requests by running the overall regression test in the repository root:

    ./run_tests


## Contact

If you have larger changes or additions, it is a good idea to get in contact
with us as <devel@sel4.systems>, so we can help you get started.

The people responsible for the technical direction, procedures, and quality
control are the [Technical Steering Committee][1] (TSC) of the seL4
foundation. You can contact them either on the developer mailing list or on
directly via email available from their profile pages.

[1]: https://sel4.systems/Foundation/TSC


## Developer Certificate of Origin (DCO)

This repository uses the same sign-off process as the Linux kernel. For every
commit, use

    git commit -s

to add a sign-off line to your commit message, which will come out as:

    Signed-off-by: name <email>

By adding this line, you make the declaration that you have the right to make
this contribution under the open source license the files use that you changed
or contributed.

The full text of the declaration is at <https://developercertificate.org>.
