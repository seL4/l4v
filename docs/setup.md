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

### Linux Packages - Ubuntu

These instructions are intended for Ubuntu LTS versions 18.04, 20.04, and 22.04.

To run all proofs against the **ARMv7-A** architecture you will need to install
the following packages:

```bash
sudo apt-get install \
    python3 python3-pip python3-dev \
    gcc-arm-none-eabi build-essential libxml2-utils ccache \
    ncurses-dev librsvg2-bin device-tree-compiler cmake \
    ninja-build curl zlib1g-dev texlive-fonts-recommended \
    texlive-latex-extra texlive-metapost texlive-bibtex-extra \
    mlton-compiler haskell-stack
```

### macOS packages

These instructions use Homebrew, which can be installed from [their website][homebrewwebsite].
The main packages that are needed are:

```
brew install git libxml2 ncurses librsvg dtc cmake ninja texlive rsync python ccache \
    zstd haskell-stack
```

The installation of mlton on Apple silicon is currently not well supported. One
approach would be to cross-compile mlton on another architecture and transfer it. On
Intel machines, the following works:

```
brew install mlton
```

To install the cross-compilers, run

```
brew install --cask gcc-arm-embedded

brew install arm-none-eabi-gcc

brew tap messense/macos-cross-toolchains
brew install x86_64-unknown-linux-gnu aarch64-unknown-linux-gnu

brew tap riscv/riscv
brew install riscv-tools
```

Note that CMake will require the x86 compiler before it can be invoked.

The instructions in the sections below should apply for both Linux and macOS.

[homebrewwebsite]: https://brew.sh

### Python

The build system for the seL4 kernel requires several python packages:

```bash
pip3 install --user --upgrade pip
pip3 install --user sel4-deps
```

### Haskell Stack

After installing
[haskell-stack](https://docs.haskellstack.org/en/stable/), make sure
you've adjusted your `PATH` to include `$HOME/.local/bin`, and that you're
running an up-to-date version:

```bash
stack upgrade --binary-only
which stack # should be $HOME/.local/bin/stack
```

## Isabelle Setup

After the repository is set up using `repo` with
`seL4/verification-manifest`, you should have following directory
structure, where `l4v` is the repository you are currently looking at:

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

Alternatively, it is possible to use the official Isabelle2021 release
bundle for your platform from the [Isabelle website][isabelle]. In this case, the
installation steps above can be skipped, and you would replace the directory
`verification/isabelle/` with a symbolic link to the Isabelle home directory
of the release version. Note that this is not recommended for development,
since Google repo will overwrite this link when you synchronise repositories
and Isabelle upgrades will have to be performed manually as development
progresses.

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

```
mkdir -p ~/.isabelle/jedit/macros
cp misc/jedit/macros/goto-error.bsh ~/.isabelle/jedit/macros/.
```

You can add keybindings for this macro in the usual way, by going to
Utilities -> Global Options -> jEdit -> Shortcuts.

[isabelle]: http://isabelle.in.tum.de
