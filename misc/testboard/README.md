<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

Verification Testboard
=======================

The script `testboardpush` in this directory takes your current repository set
(manifest), and pushes it to a central test board repository. This push triggers
a full verification regression test for this combination.

For this to work, you have to call the script from the toplevel project directory,
i.e. if you have `l4v` in `~/verification/l4v`, you need to be in `~/verification`
and call

    l4v/misc/testboard/testboardpush

The script requires your current branch to be published somewhere on GitHub that
is accessible to the test machine. A fork is fine, a branch (or set of branches)
in the central repositories are also fine.

You will need push access to the testboard repository. Everyone in the Committer
or Reviewer role in the seL4 Foundation has access.

Results will be reported by email to the committer of the testboard commit and
as status of the corresponding commits in the `seL4` and `l4v` repositories in
the seL4 GitHub org. If these are on a PR, the status will show up there. If the
commits don't exist in `seL4/seL4` or `seL4/l4v`, the status is ignored.
