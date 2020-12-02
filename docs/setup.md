<!--
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
website](https://docs.haskellstack.org/en/stable/README).

### Linux Packages - Ubuntu
On **Ubuntu 18.04**, to run all proofs against the **ARMv7-A**
architecture you will need to install the following packages:
```bash
sudo apt-get install \
    python3 python3-pip python3-dev \
    gcc-arm-none-eabi build-essential libxml2-utils ccache \
    ncurses-dev librsvg2-bin device-tree-compiler cmake \
    ninja-build curl zlib1g-dev texlive-fonts-recommended \
    texlive-latex-extra texlive-metapost texlive-bibtex-extra \
    mlton-compiler haskell-stack
```

### Python
The build system for the seL4 kernel requires several python packages:
```bash
sudo pip3 install --upgrade pip
sudo pip3 install sel4-deps
```

### Haskell Stack
After installing
[haskell-stack](https://docs.haskellstack.org/en/stable/README), make sure
you've adjusted your `PATH` to include `$HOME/.local/bin`, and that you're
running an up-to-date version:
```bash
stack upgrade --binary-only
which stack # should be $HOME/.local/bin/stack
```

### MacOS
Other than the cross-compiler `gcc` toolchain, setup on MacOS should be similar
to that on Ubuntu. To set up a cross-compiler, try the following:
* Install `XCode` from the AppStore and its command line tools. If you are
  running MacPorts, you have these already. Otherwise, after you have XCode
  installed, run `gcc --version` in a terminal window. If it reports a version,
  you're set. Otherwise it should pop up a window and prompt for installation
  of the command line tools.
* Install the seL4 Python dependencies, for instance using `sudo easy_install
  sel4-deps`.  `easy_install` is part of Python's [`setuptools`][setuptools].
* Install the [`misc/scripts/cpp`][ccp-script] wrapper for clang, by
  putting it in `~/bin`, or somewhere else in your `PATH`.

[setuptools]: https://pypi.python.org/pypi/setuptools "python package installer"
[cpp-script]: https://github.com/seL4/l4v/blob/master/misc/scripts/cpp "cpp wrapper script"

## Isabelle Setup

After the repository is set up using `repo` with
`seL4/verification-manifest`, you should have following directory
structure, where `l4v` is the repository you are currently looking at:

```bash
verification/
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
./isabelle/bin/isabelle build -bv HOL-Word
```

These commands perform the following steps:

 * create an Isabelle user settings directory.
 * install L4.verified Isabelle settings.
   These settings initialise the Isabelle installation to use the standard
   Isabelle `contrib` tools from the Munich Isabelle repository and set up
   paths such that multiple Isabelle repository installations can be used
   side by side without interfering with each other.
 * download `contrib` components from either the Munich or TS repository. This includes
   Scala, a Java JDK, PolyML, and multiple external provers. You should
   download these, even if you have these tools previously installed
   elsewhere to make sure you have the right versions. Depending on your
   internet connection, this may take some time.
 * compile and build the Isabelle PIDE jEdit interface.
 * build basic Isabelle images, including `HOL-Word` to ensure that
   the installation works. This may take a few minutes.

Alternatively, it is possible to use the official Isabelle2020 release
bundle for your platform from the [Isabelle website][isabelle]. In this case, the
installation steps above can be skipped, and you would replace the directory
`verification/isabelle/` with a symbolic link to the Isabelle home directory
of the release version. Note that this is not recommended for development,
since Google repo will overwrite this link when you synchronise repositories
and Isabelle upgrades will have to be performed manually as development
progresses.

[isabelle]: http://isabelle.in.tum.de
