<!--
     Copyright 2022, The University of Melbourne (ABN 84 002 705 224)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Branches of L4v for Time Protection

## Remotes

- Main L4v repo `verification`: <https://github.com/seL4/l4v.git>
- Scott's fork `scottbuckley`: <https://github.com/scottbuckley/l4v.git>
- Rob's fork `robs-cse`: <https://github.com/robs-cse/l4v.git>

## Verification manifest

The time protection project now has a manifest that records which branches and
checkouts of the repositories needed for L4.verified are compatible and reflect
the latest status of our experimental and verification work in progress.

Select it by using `repo init` with `-m timeprot.xml` when following the
[setup instructions](https://github.com/seL4/l4v/blob/master/docs/setup.md)
to check out the L4.verified repositories:

    mkdir verification
    cd verification
    repo init -m timeprot.xml -u ssh://git@github.com/seL4/verification-manifest.git
    repo sync

## Experimental synchronisation branch

Location: `verification/experimental-timeprot`

Protocol:
- Before pushing anything to this branch, we'll either (1) merge up to it or
  (2) rebase onto it -- i.e. **we won't force push** anything to this branch.
- We'll push reasonably stable versions of *features* to this branch from our
  active development branches by agreement between us, when someone else needs
  them to proceed.
- We'll keep *project documentation* (e.g. this file) up to date on this branch
  by pushing any updates to it as frequently as needed.
- To be able to keep full experimental history on this branch while avoiding
  both (1) messy rebasing of that full commit history onto *mainline*
  (`verification/master`) and (2) diverging history between our
  active development branches:
  - If any of us needs something from mainline, we'll merge this branch
    **up to** mainline on agreement -- **we won't rebase it** onto mainline.
  - Later, we'll cherrypick and rebase separable features from here to prepare
    them for merge review into L4v mainline -- i.e. we won't be rebasing this
    branch as a whole onto it.

Features:
- Time protection extension locale and example instantiation (InfoFlow)
  development by Scott and Rob from Nov 2021 to Jun 2023, including:
  - Split of extension locale into interfaces for HW + transition system.
  - Instantiation of transition system locale by seL4 InfoFlow automaton.
  - TA set equivalence integration into unwinding relation by Scott.
    (Archived: `scottbuckley/experimental-timeprot`)
  - TA subset invariant integration and lemma stubs by Rob.
    (Archived: `robs-cse/timeprot-subset-invs`)
- Partial fixes and sorries in AInvs, Access, InfoFlow for the following:
  - Initial *touched-addresses* (TA) set collection and enforcement mechanisms
    for `kheap` accesses (ASpec) by Scott.
  - TA-agnostic invariant machinery (AInvs) by Scott.
  - Initial domainswitch sequence draft (ASpec) by Rob.
    (Archived: `robs-cse/experimental-tpspec`)
- Partial fixes and sorries in AInvs for the following:
  - New `f_kheap` TA collection enforcement mechanism (ASpec) and adaptations
    to the change of interface (AInvs) by Scott, Gerwin and Rob.
    (Archived: `robs-cse/timeprot-use-f-kheap`)
  - Addition of `touch_object` TA accounting throughout ASpec by Rob.
    (Archived: `robs-cse/timeprot-touch-objs`)
- Partial progress in ExecSpec and Refine of (1) "no-fail" proofs for new
  ASpec-level TA membership assertions on address access and (2) additions of
  new TA accounting to ExecSpec with which to prove correspondence with ASpec.
  (Archived: `robs-cse/timeprot-haskell-refine`)

Status: Merged up to `verification/master` commit `e1fd4229b`.

(See: <https://github.com/seL4/l4v/compare/master...experimental-timeprot>)

## Active development branches

### `scottbuckley/experimental-timeprot`

Features: Ongoing handover cleanups.

(See: <https://github.com/seL4/l4v/compare/experimental-timeprot...scottbuckley:experimental-timeprot>)

## Archive branches we're not intending to merge

- `robs-cse/experimental-timeprot-pr425-backup`:
  Safety backup of former status of `verification/experimental-timeprot`
  before a force push by Rob to fix diverging history due to Git dropping
  Scott's DCO sign-off commits when pull request #425 was merged.

# Branches of seL4 kernel cloning implementation

The build and simulation instructions below assume you have a
`seL4-CAmkES-L4v-dockerfiles` Docker container set up as documented by
<https://docs.sel4.systems/projects/dockerfiles/>.

## Initial sel4test bringup

Sync the project in a new directory and customise its repo branches as follows:

    repo init -u git@github.com:seL4/sel4test-manifest.git -b d0841209b314c02581dcc0c99e8c82176d1fcbe0
    repo sync

    cd kernel
    git remote add robs-cse git@github.com:robs-cse/seL4.git
    git fetch robs-cse
    # should be commit 8359b60aed896c730ca68512f1dcf6219437a745
    git checkout wip_timeprot-riscv64-minimal
    cd ..

    cd projects/sel4test
    git remote add robs-cse git@github.com:robs-cse/sel4test.git
    git fetch robs-cse
    # should be commit cf1f12fa57376bf5102c64d3c9aff8d993b1c204
    git checkout wip_timeprot-riscv64-minimal
    cd ../..

    cd projects/seL4_libs
    git remote add robs-cse git@github.com:robs-cse/seL4_libs.git
    git fetch robs-cse
    # should be commit 14542341995cf43447c586c85f7ef40aa00541ce
    git checkout wip_timeprot-riscv64-minimal
    cd ../..

To build and simulate the image, from inside a `seL4-CAmkES-L4v-dockerfiles`
Docker container run:

    mkdir build
    cd build
    ../init-build.sh -DSIMULATION=TRUE -DRISCV64=TRUE -DPLATFORM=qemu-riscv-virt
    # In ccmake, set DOMAINS=ON and KernelImages=ON then hit c, g to generate.
    ccmake .
    ninja
    ./simulate

To confirm `KernelImages=ON` the initial boot output should contain the string
`kernelImageClone done for colour` for each of the colours 0-3 (domains 1-4).

At current time of writing, `sel4test` is expected to run to completion and
report the following three expected failures:
- VSPACE0003 (Test create multiple ASID pools)
- VSPACE0004 (Test running out of ASID pools)
- VSPACE0006 (Test touching all available ASID pools)

(General instructions for checking out and building sel4test can be found at
<https://docs.sel4.systems/projects/sel4test/>.)

## Channel benchmarking

Sync the project in a new directory and customise its repo branches as follows:

    repo init -u https://github.com/niwis/channel-bench-manifest.git -m timing.xml
    repo sync

    cd kernel
    # should be commit 0c41464fbc54603b603ed09fccf48f046daafe71
    # of repo git@github.com:niwis/seL4.git
    git checkout colour-idx
    cd ..

    cd projects/channel-bench
    # should be of repo git@github.com:niwis/channel-bench.git
    git checkout 09963ee921b8b984216702c2fe4e83ba96872a14
    cd ../..

    cd projects/seL4_libs
    git remote add robs-cse git@github.com:robs-cse/seL4_libs.git
    git fetch robs-cse
    # should be commit 14542341995cf43447c586c85f7ef40aa00541ce
    git checkout wip_timeprot-riscv64-minimal
    cd ../..

To build the image, from inside a `seL4-CAmkES-L4v-dockerfiles` Docker
container run:

    mkdir build
    cd build
    ../init-build.sh -DRISCV64=TRUE -DPLATFORM=ariane
    # In ccmake, customise settings for desired benchmark, see notes below.
    ccmake .
    ninja

In the `ccmake .` menu, hit `t` to toggle advanced mode then customise the
settings as follows:

- BenchUntypeSizeBits: 13
- LibSel4UtilsCSpaceSizeBits: 8
- BenchCovert: ON
- KernelTimeSlice: 1
- KernelTimerTickMS: 10
- ManagerCovertBench: ON
- LibSel4CacheColouring: ON
- LibSel4CacheColourNumCacheColo: 16

Confirm these settings are at the following expected defaults:

- BenchBHTAlign: 20
- BenchBHTEntries: 64
- BenchBTBAlign: 20
- BenchBTBEntries: 16
- BenchCacheLineSize: 64
- LibSel4CacheColourMSpaceReserves: 10

Hit `c` to configure, then select between the following according to what you
want to benchmark:

- BenchDataPoints: 100000 (or whatever you want)
- KernelImages: ON or OFF
- KernelNumDomains: 2 if KernelImages OFF, 3 if KernelImages ON
- KernelColourBits: 4 (if KernelImages ON, need to hit `c` to reveal this)
- BenchCovertChoice: l1d or l1i or tlb or btb or bp or llc kernel
- KernelDomainMicroarchFlush: ON or OFF

Finally hit `g` to generate the configuration that `ninja` will build.

## Notes on the present kernel cloning implementation

- Timeslice 0 in the schedule is reserved for the initial user thread and any
  others it creates but doesn't assign to any other domain (this is why
  `CONFIG_NUM_DOMAINS` defaults to 5, not 2^2=4, when
  `CONFIG_NUM_COLOUR_BITS=2`).
- Timeslice 0 uses the initial kernel image (unpartitioned, spread across all
  colours) running when the system first boots.
- At boot time, the kernel will try to create `CONFIG_NUM_DOMAINS-1` kernel
  image clones in up to `2^CONFIG_NUM_COLOUR_BITS` coloured partitions.
- A compile-time assertion ensures there's enough colour bits to create enough
  clones for that number of domains. `CONFIG_NUM_COLOUR_BITS` defaults to 2 but
  should be customised according to the actual colour bits on the given L2.
- The domains in timeslices `1..(CONFIG_NUM_DOMAINS-1)` in the schedule will
  use these kernel image clones. Only round-robin schedules are supported
  (i.e. a given domain id can't appear more than once in the schedule).
- A `domain` (id) argument has been added to the `seL4_RISCV_ASIDPool`'s
  `Assign` API.
- At runtime, a user program that creates a thread to run in some domain X is
  responsible for calling both that `ASIDPool` API and the `seL4_DomainSet` API
  to assign the *same* domain X to the vspace for that thread and (resp.) the
  thread itself, *before* running it. (i.e. No promises about behaviour if a
  user program assigns inconsistent domains to a thread and its vspace, or
  tries to reassign a thread's domain when it's already running.)
- The `wip_timeprot-riscv64-minimal` branch of
  <https://github.com/robs-cse/seL4_libs> has been developed to facilitate
  the use of these kernel API changes.
