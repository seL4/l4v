<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Verification manifest updater

Herein are scripts to manually update [verification-manifest][] whenever there
is a change to [seL4][] that cannot be automatically handled by the "preprocess"
CI job.

A manual manifest update is commonly called a *preprocess bump*.

[verification-manifest]: https://github.com/seL4/verification-manifest/
[seL4]: https://github.com/seL4/seL4/

## Rationale

The `devel.xml` file in the [verification-manifest][actual-manifest] tracks
`master` for [l4v][], but is pinned to specific commits for [seL4][]. This
allows us to freely make improvements to l4v, while keeping track of exactly
which versions of seL4 are believed to be verified.

[actual-manifest]: https://github.com/seL4/verification-manifest/blob/master/devel.xml
[l4v]: https://github.com/seL4/l4v/

However, this means that whenever seL4 is updated,
[`devel.xml`][actual-manifest] must also be updated. There is a CI job that
automatically performs the manifest update whenever the seL4 update does *not*
modify what the C parser sees for the verified kernel configurations. It uses
the [preprocess][] script to detect that case.

When the seL4 update *does* make changes to the verified configurations, the
[preprocess][] job will fail. In that case, a *bump* (manual manifest update) is
required.

[preprocess]: https://github.com/seL4/ci-actions/tree/master/preprocess

## When is a bump required?

There are typically two situations in which a bump is required:

1. A [seL4][] pull request requires a *bump* for a change to seL4 which affects
   the verified configurations, but which is believed not to require a proof
   update.

2. There is a proof update for an seL4 patch (usually with corresponding seL4
   pull request), and we want to merge both the seL4 change and the proof update.

## Bump requests from seL4 pull requests

Some changes to verified configurations do not require proof updates. This
includes most changes to boot code, and superficial changes which can be
absorbed by `ccorres_rewrite`. In these cases, the preprocess test on the seL4
pull request will fail, but the `diff` it shows in its output contains only
proof-irrelevant changes. Usually someone on the seL4 pull request will ask for
help from someone with verification experience.

An experienced proof engineer should inspect the `diff` in the [preprocess][]
logs for the test failure, and make a judgement about whether a proof update
will be required. If unsure, you can run a full proof [testboard][] on the PR.
But unless the PR is a release candidate, there is some room for error. You
should balance the desire for quick turnaround on kernel updates against the
desire to avoid broken verification regression and unplanned proof updates.

Note that changes to boot code can cause `SimplExportAndRefine` to fail,
particularly if the changes involve complex loops, or complex memory access
patterns (combinations of array access with either constant index offsets or
struct fields). In those cases, it might be worth obtaining an opinion from
someone with `SimplExportAndRefine` experience. Otherwise, don't worry about it
until it fails.

If you think no proof update is required, approve the seL4 pull request to be
merged. As soon as possible after it is merged, follow the bump script recipe
below. If you think a proof update is required, or if you bump and regression
subsequently fails, then flag the need for a verification patch.

[testboard]: https://github.com/seL4/gh-testboard

## Verification patches

A proof update for an seL4 update requires merging pull requests for both `l4v`
and `seL4`, and a manifest bump. The proof engineer who prepared the patch
should already have made sure the seL4 pull request is rebased and tested the
proof update against the rebased version of the seL4.

It doesn't hurt to double check that the manifest displayed in the proof test
log contains the commit hashes of the branches you want to merge, but if you are
sure that everything is up to date, you can skip this step.

Once you're happy that both PRs have been tested and reviewed appropriately,
both can be merged. The seL4 PR should be merged first, followed without too
much delay (see below) by the l4v PR. As soon as both PRs are merged, follow the
bump script recipe below.

Timing: in between the three merges, the repos are in an inconsistent state with
respect to each other. Don't worry if the merges take too long, the only adverse
effect is a wasted test cycle that tests the seL4 PR without the l4v PR and/or a
failure of the preprocess test. But do try to minimise the time the repositories
are in an inconsistent state with respect to each other, so that others can keep
working.

## Using the bump script

The [bump script][] can be found at `l4v/misc/bump/bump-ver-manifest` in any
checkout of [l4v][]. Unless you know `repo` well, it is advisable to keep a
separate `repo` checkout of [verification-manifest][] that you only use for
manifest bumps.

[bump script]: https://github.com/seL4/l4v/tree/master/misc/bump/

To bump the manifest:

1. `repo sync` your [verification-manifest][] checkout.

2. Ensure that for `l4v`, `HEAD` corresponds to current master, and that this is
   the `l4v` commit that verifies the new `seL4` version.

3. Note that for `seL4`, new commits will have been fetched from the remote, but
   `HEAD` will still correspond to the `seL4` commit in the *current* manifest.

4. In the `seL4` directory, look at `git log ^HEAD verification/master`. Check
   that it shows exactly the commits in the `seL4` PR for which the bump is
   required.

5. In the `seL4` directory, perform `git checkout verification/master`.

6. In the root of the `repo` checkout (i.e. parent of `l4v` directory), run
   `./l4v/misc/bump/bump-ver-manifest` and follow the prompts.

## Files in this directory

* `bump-ver-manifest`: for interactive use, to update `verification-manifest`
* `ver-bump.py`: python script that backs `bump-ver-manifest`
* `bump-local-repos`: used in CI to update the branch `successful-decompile` in
  [HOL4][] and [polyml][] repos. Not intended for manual or interactive use.

[HOL4]: https://github.com/seL4/HOL/
[polyml]: https://github.com/seL4/polyml/
