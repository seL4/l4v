<!--
     Copyright 2022, Proofcraft Pty Ltd
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

<!-- This file is also included on https://docs.sel4.systems/projects/buildsystem/host-dependencies.html  -->

# Proof and Isabelle Dependencies

## Proof Dependencies

### Linux Packages - Debian

On **Buster** or **Bullseye**, to run all proofs against the
**ARMv7-A** architecture you will need to install the following packages:

```bash
sudo apt-get install \
    python3 python3-pip python3-dev \
    gcc-arm-none-eabi build-essential libxml2-utils ccache \
    ncurses-dev librsvg2-bin device-tree-compiler cmake \
    ninja-build curl zlib1g-dev texlive-fonts-recommended \
    texlive-latex-extra texlive-metapost texlive-bibtex-extra \
    rsync
```

There is no package for the MLton compiler on Buster or Bullseye, so you will
need to install it from the [MLton website](http://www.mlton.org).

The Haskell Stack package is unavailable on Bullseye and out-of-date on Buster,
so you will need to install it from the [Haskell Stack
website](https://docs.haskellstack.org/en/stable/).

Continue with the [python setup step](#python) below.

### Linux Packages - Ubuntu

These instructions are intended for Ubuntu LTS versions 20.04, and 22.04.

To run all proofs against the **ARMv7-A** architecture you will need to install
the following packages:

```bash
sudo apt-get install \
    python3 python3-pip python3-dev \
    gcc-arm-none-eabi build-essential libxml2-utils ccache \
    ncurses-dev librsvg2-bin device-tree-compiler cmake \
    ninja-build curl zlib1g-dev texlive-fonts-recommended \
    texlive-latex-extra texlive-metapost texlive-bibtex-extra \
    mlton-compiler haskell-stack repo
```

Continue with the [python setup step](#python) below.

### macOS packages

The proofs work well on Intel Macs. For Apple silicon Macs, the `mlton` compiler
is currently not well supported. One approach would be to cross-compile `mlton` on
another architecture and transfer it. Most proof sessions work without `mlton`,
but the C parser and therefore the C refinement proofs depend on it.

These instructions use Homebrew, which can be installed from [their website][homebrewwebsite].
To install the main dependencies and cross compilers, use the following steps:

```sh
brew install git libxml2 ncurses librsvg dtc cmake ninja texlive rsync python ccache \
    zstd haskell-stack mlton arm-none-eabi-gcc repo

brew install --cask gcc-arm-embedded

brew tap messense/macos-cross-toolchains
brew install x86_64-unknown-linux-gnu aarch64-unknown-linux-gnu

brew tap riscv/riscv
brew install riscv-tools
```

The instructions in the sections below apply for both Linux and macOS.

[homebrewwebsite]: https://brew.sh

### Python

The build system for the seL4 kernel requires several python packages:

```bash
pip3 install --user --upgrade pip
pip3 install --user sel4-deps
```

### Haskell Stack

After installing [haskell-stack](https://docs.haskellstack.org/en/stable/)
(already included in the packages above on Mac and Ubuntu), make sure you've
adjusted your `PATH` to include `$HOME/.local/bin`, and that you're running an
up-to-date version:

```bash
stack upgrade --binary-only
which stack # should be $HOME/.local/bin/stack
```

## Checking out the repository collection

The seL4 repositories use the [Google `repo` tool][repo] for configuration
control and managing sets of repositories. For verification, this means in
particular managing the correct combinations of the proofs, the kernel sources,
and the Isabelle/HOL theorem prover.

The [verification-manifest] repository records which versions of these are known
to work well together.

To check out a consistent set of repositories, run the following steps:

```sh
mkdir verification
cd verification
repo init -u https://git@github.com/seL4/verification-manifest.git
repo sync
```

If you are developing proofs, intending to contribute, and have `ssh` set up
for GitHub, use

```sh
repo init -m devel.xml -u ssh://git@github.com/seL4/verification-manifest.git
```

instead for the `init` line. The `-m devel.xml` gives you the `master` branch of
the `l4v` repository instead of the last known-good version. To set up `git` for
`ssh` make sure to use the `ssh://` protocol explicitly as above instead of just
`git@github.com`, because the short form seems to confuse `repo`.

[repo]: https://gerrit.googlesource.com/git-repo/+/HEAD/README.md
[verification-manifest]: https://github.com/seL4/verification-manifest

## Isabelle Setup

After the repository is set up using `repo` with the [verification-manifest]
repository, you should have following directory structure, where `l4v` is the
repository you are currently looking at:

```bash
verification/
    HOL4/
    graph-refine/
    isabelle/
    l4v/
    seL4/
```

To set up Isabelle for use in `l4v/`, assuming you have no previous
installation of Isabelle, run the following commands in the directory
`verification/l4v/`:

```bash
mkdir -p ~/.isabelle/etc
cp -i misc/etc/settings ~/.isabelle/etc/settings
./isabelle/bin/isabelle components -a
./isabelle/bin/isabelle jedit -bf
./isabelle/bin/isabelle build -bv HOL
```

These commands perform the following steps:

* create an Isabelle user settings directory.
* install L4.verified Isabelle settings.
  These settings initialise the Isabelle installation to use the standard
  Isabelle `contrib` tools from the Munich Isabelle repository and set up
  paths such that multiple Isabelle repository installations can be used
  side by side without interfering with each other.
* download `contrib` components from the Isabelle repository. This includes
  Scala, a Java JDK, PolyML, and multiple external provers. You should
  download these, even if you have these tools previously installed
  elsewhere to make sure you have the right versions. Depending on your
  internet connection, this may take some time.
* compile and build the Isabelle PIDE jEdit interface.
* build basic Isabelle images to ensure that
  the installation works. This may take a few minutes.

Alternatively, it is possible to use the official Isabelle2022 release
bundle for your platform from the [Isabelle website][isabelle]. In this case, the
installation steps above can be skipped, and you would replace the directory
`verification/isabelle/` with a symbolic link to the Isabelle home directory
of the release version. Note that this is not recommended for development,
since Google repo will overwrite this link when you synchronise repositories
and Isabelle upgrades will have to be performed manually as development
progresses.

You are now set up to process proofs, for instance by following the instructions
at the bottom of the main [README page][running-proofs].

The sections below contain a few tools and tips for proof development on seL4.

[running-proofs]: https://github.com/seL4/l4v/blob/master/README.md#running-the-proofs

## PIDE Tools

The following tools and tips can make writing proofs easier and more efficient
when using the Isabelle PIDE jEdit interface.

### WhiteSpace plugin

The WhiteSpace plugin can highlight normally invisible whitespace characters
such as tabs and spaces, and can remove trailing whitespace on save. To
install and configure the WhiteSpace plug-in for jEdit, follow
the instructions below.

1. Go to Plugins -> Plugin manager -> Install.
2. Search for `WhiteSpace` and install the plugin.
3. Go to Plugins -> Plugin Options -> WhiteSpace -> On save actions.
4. Check "Remove trailing whitespace" and click Apply.

### Key bindings for Navigator

The Isabelle PIDE provides "Back" and "Forward" actions that allow you to
easily navigate to previous positions in your edit history. Follow the steps
below to bind a key to the "Back" function. We recommend ``[ctrl]+[`]``.

1. Go to Utilities -> Global Options -> jEdit -> Shortcuts.
2. Select Action Set -> Plugin: Navigator.
3. Set a shortcut for `Back`.

### Go-to-error macro

Run the following commands in the directory `verification/l4v/`:

```sh
mkdir -p ~/.isabelle/jedit/macros
cp misc/jedit/macros/goto-error.bsh ~/.isabelle/jedit/macros/.
```

You can add keybindings for this macro in the usual way, by going to
`Utilities -> Global Options -> jEdit -> Shortcuts`.

Additionally, our fork of Isabelle/jEdit has an updated indenter which is more
proof-context aware than the 'original' indenter. Pressing `ctrl+i` while some
`apply`-script text is selected should auto-indent the script while respecting
subgoal depth and maintaining the relative indentation of multi-line `apply`
statements.

[isabelle]: http://isabelle.in.tum.de
