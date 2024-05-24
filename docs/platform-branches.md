<!--
     Copyright 2024, Proofcraft Pty Ltd
     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Automated Platform Branches

The following branches for additional platforms are currently automatically
rebased and tested on each push to `master`:

- [imx8mm-fpu-ver](https://github.com/seL4/l4v/tree/imx8-fpu-ver)
- [exynos5-ver](https://github.com/seL4/l4v/tree/exynos5-ver)

## How this works

The `L4V_PLAT` configuration setting provides an additional dimension to the
configuration space for verified platforms in addition to `L4V_ARCH` and
`L4V_FEATURES`. To test an `L4V_ARCH`, `L4V_FEATURES`, and `L4V_PLAT`
combination, the test setup will attempt to load a corresponding kernel config
from the seL4 repository under

```sh
configs/${L4V_ARCH}_${L4V_PLAT}_${L4V_FEATURES}_verified.cmake
```

e.g. `ARM_HYP_exynos5_verified.cmake`. Tests on the master branch will currently
keep `L4V_PLAT` empty, and tests on the platform branches will provide the
appropriate platform string.

To keep platform branches up to date, there is [a GitHub action][rebase-action]
that automatically attempts to rebase all platform branches over each new push
to the master branch. If that rebase succeeds, this action will push the rebased
platform branch to a candidate branch `<branch>-rebased`. The platform branch,
and therefore the `-rebased` branch have a corresponding action that in turn is
triggered by this push and runs a full proof test for this branch. If the test
succeeds, the branch action replaces the original platform branch with the
candidate `<branch>-rebased` branch by force push. If either step fails, CI will
signal test failure and require manual intervention.

When the test is triggered by a change in seL4 only, the rebase action will
*not* re-trigger a new proof run for the rebase branches, because the rebase on
the l4v repository itself will be empty and produce no change. However, if
something substantial changed in seL4, it is very likely that there will be a
corresponding l4v change to go with it, which then will trigger the rebase
branches.

[rebase-action]: https://github.com/seL4/l4v/blob/d869bb5ec81/.github/workflows/proof-deploy.yml#L89

## How to fix things if they go wrong

### Invariants

- you should never have to modify the original platform branches

- the original platform branches are updated by CI only

- therefore, the original platform branches always are in a state that has
  worked before with a specific seL4 version (the last one before CI signalled
  failure)

- the `-rebased` branches are ephemeral and can be force-pushed to

### Rebase fails

If the rebase action fails, for instance because there are conflicts with the
master branch during `git rebase`, the manual steps to fixing the problem are
for example:

```sh
# get up-to-date branches:
git fetch
# start from the old platform branch:
git checkout verification/exynos5-ver
# prepare a -rebased branch for it
# The name is important, you may have to delete an old one if it already exists:
git checkout -b exynos5-ver-rebased
# rebase over current master:
git rebase verification/master
# manually fix rebase conflicts
...
# usually you want to check if evervthing works --
# be sure to select correct L4V_ARCH and L4V_PLAT
L4V_ARCH=ARM_HYP L4V_PLAT=exynos5 ./run_tests
# push -rebased branch back to repo for automated test and update
git push -f exynos5-ver-rebased verification
```

Note that you don't have to modify the existing `exynos5-ver` branch at all. CI
will update it once the tests for `exynos5-ver-rebased` have passed.

### Proof runs on the `-rebased` branch fails

When the rebase has succeeded, but has resulted in a state where the proof check
on the corresponding `-rebased` branch has failed, either from a CI run or from
a manual run above, the procedure is to

- check out the `-rebased` branch,
- manually fix the proofs
- usually these are very small changes -- if so, they should be squashed into
  the original commits that make up the platform branch. If they are more
  substantial new changes that make sense as a separate commit they can go on
  top.
- force-push the `-rebased` branch back (as `-rebased`)
- CI will re-run the tests and update the main platform branch when the proofs
  succeed.
