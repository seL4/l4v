<!--
     Copyright 2023, Proofcraft Pty Ltd

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Commit Messages

## Objective

The l4v repository is relatively large, active, and long-lived. It has a public
history of about one decade, and an additional decade of unreleased private
history. It will hopefully live on for another 20 years.

This means that the commit history is important. Examples of questions the commit
history should be able to answer reasonably quickly and painlessly are:

- > Is this written in a strange way for good reasons, or were we just in a hurry?
  > What was the reason? Does it still apply?

- > When did we change doing things this way and why?

- > Has this always been broken or was there a seemingly unrelated change that broke it?

- > How long did it take to finish this proof?

- > How much change was necessary to do this proof?

- > Where did this library lemma come from?

## General

The [seL4 repository guidelines][git-conventions] apply to the `l4v` repository,
with the following exceptions and additions:

- header can be max 78 characters
- body is wrapped at 78 characters
- we use tags in the header to indicate which part of the repository
  the commit applies to

We are using 78 for the header because of the tags, which take up some space. If
you can manage to stay within 50 characters anyway, that is appreciated, but it's
not always practical. Using a body wrap of 72 is also allowed, since that is the
default for other seL4 repositories.

We use tags, because the repository is relatively large and most commits only
apply to small parts of it. The tags make it easy to identify relevance of a
commit at a glance while scanning through a large number of commits.

The general guidelines prescribe capitalising the commit header. We do not
capitalise the tag or after the tag, but we do capitalise the (rare) cases where
there is no tag in the commit header.

## Header and Body

There is good general advice on [commit message writing][commit-messages]
available on the internet and it is as relevant to proofs as it is to code.
You should read it, it's not long and it's good advice.

Repeating some high-level points:

- Use imperative voice (e.g. `proof: rename lemma foo to bar`)
- The header should be a short summary, focusing on "what"
- The body should explain what is going on in more detail (also in imperative
  voice), but much more importantly *why* it is going on (is `bar` more
  consistent than `foo`? Is the name `foo` needed for something else? Does `bar`
  just better describe what is going on?).
- You are trying to explain things to your future self or a future colleague
  5-10 years from now. You can assume knowledge of the repository in general,
  but you should not assume specific context that is obvious to you right now,
  but that will not be known to a different person 5 years from now.

## Tags

- We use tags to indicate which part of the repository the commit applies to,
  and if it is architecture-specific, then to which architecture it applies to.

- We do not usually use branch tags, because git branches are ephemeral and we
  are using rebase branches for most of our work. The one exception is the `rt`
  branch, which has been alive for over half a decade. For this branch, we allow
  merge commits (from branch `master` into `rt` only), and we want to be able to
  reconstruct a rebase history from that at the end of the branch's life.

  This means, we do use the tag `rt` for commits that only make sense on this
  branch. If you could apply the commit to the master branch directly (e.g. you're
  adding a lemma to a library), it should not get the tag. Otherwise it should.

### Tag Examples

The main tags we use are mostly the directory names of the main proof something
is in, e.g. `refine`, `crefine`, `sys-init`, `camkes`. For some of these, there
are abbreviations, mainly `aspec` for the abstract spec and `ainvs` for the
abstract invariants.

For large directories that have logical sub parts, we use slashes, e.g.
`lib/monads`. Not so much because the change is in that directory, but because
we want to see that it's a library change and applies to the monad part of the
library.

If the change applies to many proofs, for instance large lemma renaming commits,
we use tags such as `proof` and `spec`.

We combine tags with `+` if a change applies to multiple parts, e.g.
`clib+crefine` or `lib+proof`.

If something is specific to an architecture we preface the tag with the
architecture, e.g. `arm refine:` or `aarch64 aspec+ainvs:`. The current
architecture tags are: `arm`, `arm-hyp`, `x64`, `riscv`, `aarch64`.
Please use these spellings only.

More tag examples:

- `trivial`: for small trivial changes like fixing a typo, where no proofs or
  specs have changed, i.e.\ that would not need a proof CI run.
- `cleanup:` for cleanups that do not change proof content
- `github:` for GitHub CI changes
- `run_tests`: for changes to the top-level `run_tests` file
- `isabelle20xx`: for easily identifying commits related to Isabelle updates

For more consistency there is an order between tags. More abstract/general
things should come first, e.g. `lib` < `aspec` < `haskell` < `ainvs` < `refine`
`orphanage` < `crefine`. Or `dspec` < `drefine` and `access` < `infoflow`. Specs
< proofs and `infoflow` < refinement proofs. This is not a total order, it's Ok
to use your own judgement.

Because `lib` has many subdirectories and separate parts, it's fine to use
session names as tags there to shorten things a bit, e.g. `clib`, `monads`,
`word_lib` instead of `lib/clib`, `lib/monads`, or `lib/word_lib`. This makes
sense when the tags are session names.

See also the longer example list of [good tags](#good-tags) below.

## Tips and Tools

### Looking at history

The main tools to interact with the git history are browsing it on GitHub and
various forms of `git log`:

```sh
git log --oneline  # show only headings
git log            # show commit info with author, date, message
git log --stat     # additionally show which files have changed
git log --p        # additionally show full diff
```

For all of these, you can supply a path to restrict the log to a certain file
or directory in the repo. You can also supply a branch, or a commit range like
`master..rt` to restrict the output.

Especially `git log --oneline` is useful for quickly getting an overview. Example
output:

```
b3c6df48a clib: improve ccorres_While
49ff8457f clib+crefine: improve and consolidate variants of ccorres_to_vcg
8c433c085 clib: add some rules for hoarep
82b954817 clib: improve ccorres_call_getter_setter
8c59df449 lib/monads: remove more uses of _tac methods
563232397 run_tests+proof: exclude SimplExportAndRefine for AARCH64
1cce5b3ff proof: switch AArch64 quick_and_dirty from Refine to CRefine
402a8342d run_tests: enable CBaseRefine for AARCH64
32a672412 aarch64 cspec: add Kernel_C.thy to base CKernel image on
b2cd1ce4a aarch64 asmrefine: copy ArchSetup from RISCV64
67c0109b7 lib/monads: avoid clarsimp as initial Isar method
bd5026438 lib/monads: fix remaining document preparation issues
4d0086567 lib/monads: add new Trace_* files to ROOT
598e19dd6 lib/monads: coherent document structure
4cbfb4ab0 lib/monads: minor style + warning cleanup
b2dd5db6d lib/monads: fix document preparation issues
03a045309 lib/monads: add AFP document setup
d0bab9c79 misc/scripts: remove Darwin cpp wrapper
```

You can very quickly see that C verification has been active recently, that
new tests were added, that AARCH64 refinement proofs have been done, and that there was
some work to do with the AFP and the monad library. You can see that nothing
has happened with the system initialiser or other user-level proofs, and that there
are no changes that should affect, for instance, the C parser.

You only see such things quickly when the messages are consistent and follow the
same kind of pattern. It's not so important what the pattern is. It is important
that it is consistent.

Note in e.g. `proof: switch AArch64 quick_and_dirty from Refine to CRefine` that
the architecture tag is used only when the change is specific to files for that
architecture. In this commit, the overall ROOTS file is changed, so it shouldn't
get the architecture tag.

### What tag should I pick?

If you're uncertain what tag to pick for a certain file or directory, the
easiest way to figure it out is to do

```sh
git log --oneline <that-file>
```

Do your tags the same way people have done before. This will make the pattern
consistent and should be reasonably easy to read even if it's not perfect. Look
at a few commits, not only a single one, so you can course correct instead of
amplify if someone happened to invent a new flavour.

You can even do that when you're in the middle of writing a commit message, it's
safe to interrupt `git commit` with `Ctrl-Z`, then `bg` in your shell to put
it into the background, and then `git log --online <file>` to see the history.

Any operation that doesn't change the state of the repository is fine (even
those that do are fine, but then the commit will probably fail).

When you're looking into history for tags, use mainly commits from roughly 2018
onwards. We weren't very consistent with tags before that. The more recent the
more consistent.

### Good tags

Here's a list of tags that have been used in the past and that follow the
guidelines above.

```
aarch64 ainvs
aarch64 ainvs+refine
aarch64 asmrefine
aarch64 aspec
aarch64 aspec+ainvs
aarch64 aspec+design
aarch64 aspec+haskell
aarch64 aspec+machine
aarch64 cspec
aarch64 design
aarch64 design+machine
aarch64 haskell
aarch64 haskell+design
aarch64 haskell+machine
aarch64 machine+ainvs
aarch64 proof
aarch64 refine
aarch64 spec+haskell
access+infoflow+drefine
access+infoflow+crefine+drefine
ainvs
ainvs+crefine
ainvs+refine
arm aspec+design
arm access
arm access+infoflow
arm ainvs
arm aspec
arm crefine
arm haskell
arm infoflow
arm refine
arm+arm-hyp crefine
arm+arm-hyp machine
arm-hyp aspec
arm-hyp aspec+design
arm-hyp ainvs
arm-hyp crefine
arm-hyp design
arm-hyp haskell
arm-hyp haskell+refine
arm-hyp machine
arm-hyp refine
asmrefine
aspec
aspec+access
aspec+ainvs
aspec+design+haskell
aspec+haskell
autocorres
bisim
c-parser
c-parser+autocorres
c-parser+crefine
camkes
capDL
ckernel
cleanup
cleanup ainvs
clib
clib+crefine
crefine
crefine+capDL
cspec
design
docs
dpolicy
drefine
dspec
dspec+drefine+infoflow
github
haskell
haskell+design
haskell-translator
infoflow
infoflow+crefine
infoflow+dpolicy+cdl-refine
isabelle-2021
isabelle-2021 access
isabelle-2021 c-parser
lib
lib+READMEs
lib+aarch64 ainvs
lib+aarch64 refine
lib+ainvs
lib+ainvs+aarch64 ainvs
lib+ainvs+aarch64 refine
lib+ainvs+access+refine
lib+autocorres
lib+c-parser
lib+crefine
lib+proof
lib+proof+autocorres
lib+proof+tools
lib+proof
lib+refine+crefine
lib+spec
lib+spec+proof+autocorres
lib+spec+proof
lib+sysinit
lib+tools
lib/apply_debug
lib/clib
lib/corres_method
lib/crunch
lib/monads
lib/sep_algebra
license
misc
misc/regression
misc/scripts
misc/stats
proof
proof+autocorres
proof/Makefile
proof/ROOT
refine
refine cleanup
refine+crefine
refine+orphanage
riscv
riscv access
riscv ainvs
riscv ainvs+access
riscv aspec
riscv aspec+ainvs
riscv aspec+haskell
riscv crefine
riscv cspec+crefine
riscv design
riscv haskell
riscv haskell+design
riscv haskell+proof
riscv haskell+refine
riscv infoflow
riscv machine
riscv machine+ainvs
riscv machine+design+crefine
riscv orphanage
riscv platform
riscv refine
riscv access+infoflow+refine+crefine
riscv spec
riscv+aarch64 ainvs+refine
riscv+x64 crefine
riscv64+aarch64 ainvs
run_tests
run_tests+proof
spec+proof
style
sys-init
tools
tools/asmrefine
trivial
word_lib
word_lib+crefine
x64 ainvs+refine+crefine
x64 aspec
x64 crefine
x64 design
x64 design/skel
x64 haskell
x64 machine
x64 refine
x64 refine+crefine
```

Most of these could be prefixed with `rt` if they only made sense on the `rt`
branch, e.g. `rt arm ainv+refine:`

[git-conventions]: https://docs.sel4.systems/processes/git-conventions.html
[commit-messages]: https://chris.beams.io/posts/git-commit/
