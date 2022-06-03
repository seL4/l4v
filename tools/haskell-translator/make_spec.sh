#!/bin/bash
#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

set -e

ORIG_PWD="$PWD"

function find_dir () {
    cd $ORIG_PWD
    while [[ "/$PWD" != '//' ]]
    do
        if [[ -d "./$1" ]]
        then
            FOUND_PWD="$(pwd)/$1"
            if [[ ! -z "$V" ]]
            then echo "Found $FOUND_PWD" 1>&2
            fi
            echo "$FOUND_PWD"
            return 0
        fi
        cd ..
    done
    echo "Could not find a directory containing $1" 1>&2
    echo "  in any parent directory." 1>&2
    exit 1
}

TRANSLATOR=$(find_dir "tools/haskell-translator")

SPEC=$(find_dir "spec/design")

if [[ -z $L4CAP ]]
then
    L4CAP=$(find_dir "spec/haskell")
    export L4CAP
fi

if [[ ! -d $L4CAP/src/SEL4 ]]
then
    echo "This script is using L4CAP == $L4CAP"
    echo Set the L4CAP environment variable to the location
    echo of the haskell kernel source.
    exit 1
fi

SKEL="$SPEC/skel"
MSKEL="$SPEC/m-skel"

MACH="$SPEC/../machine"

if [[ ! -d $SKEL ]]
then
    echo Error: $SKEL is not a directory.
    echo "(this script may have found the wrong spec $SPEC)"
    exit
fi

# which architectures to process
ARCHES=("AARCH64" "ARM" "RISCV64" "X64" "ARM_HYP")

# Match the CPP configuration used by SEL4.cabal and Setup.hs for Haskell build
# Note: these should be in sync with both the Haskell .cabal and Setup.hs,
#       If these are not in sync, expect the unexpected.
#       spec_check.sh has a copy of these, which should be updated in tandem.
#       FIXME: move to a common location in haskell-translator (D.R.Y.)
function cpp_opts () {
    case ${1} in
        ARM)
            L4CPP="-DPLATFORM=QEmu -DPLATFORM_QEmu -DTARGET=ARM -DTARGET_ARM"
            ;;
        ARM_HYP)
            L4CPP="-DPLATFORM=TK1 -DPLATFORM_TK1 -DTARGET=ARM -DTARGET_ARM -DCONFIG_ARM_HYPERVISOR_SUPPORT"
            ;;
        RISCV64)
            L4CPP="-DPLATFORM=HiFive -DPLATFORM_HiFive -DTARGET=RISCV64 -DTARGET_RISCV64"
            ;;
        AARCH64)
            L4CPP="-DPLATFORM=TX2 -DPLATFORM_TX2 -DTARGET=AARCH64 -DTARGET_AARCH64"
            ;;
        X64)
            # this space intentionally left blank:
            L4CPP=""
            ;;
        *)
            echo "Warning: No CPP configuration for achitecture ${1}"
            L4CPP=""
    esac
    export L4CPP
}

NAMES=`cd $SKEL; ls *.thy`

SPECNONARCH="/tmp/make_spec_temp_nonarch_$$"
TMPFILE="/tmp/make_spec_temp_$$"

# Delete on exit
trap "rm -fr $SPECNONARCH $TMPFILE" EXIT

function send_filenames () {
    local arch=${1}
    local archnames=`cd $SKEL/${arch}; ls *.thy`
    local archmnames=`cd $MSKEL/${arch}; ls *.thy`
    mkdir -p "$SPEC/${arch}"
    mkdir -p "$SPECNONARCH/${arch}"

    # Theory files common to all haskell specifications
    for NAME in $NAMES
    do
        echo "$SKEL/$NAME --> $SPECNONARCH/${arch}/$NAME"
    done

    # Arch-specific haskell specifications
    for NAME in ${archnames}
    do
        echo "$SKEL/${arch}/$NAME --> $SPEC/${arch}/$NAME"
    done

    # Arch-specific machine theories, imported by haskell and abstract
    for MNAME in ${archmnames}
    do
        echo "$MSKEL/${arch}/$MNAME --> $MACH/${arch}/$MNAME"
    done
}

# Ensure that non-arch-specific theories are identical after preprocessing
for ARCH in ${ARCHES[@]}
do
    send_filenames $ARCH > $TMPFILE
    cpp_opts $ARCH
    cd $TRANSLATOR
    python3 pars_skl.py $TMPFILE
done

for ARCH in ${ARCHES[@]}
do
    specdiff=`diff "$SPECNONARCH/${ARCHES[0]}" "$SPECNONARCH/$ARCH"`
    if [ -n "${specdiff}" ]; then
        echo "Non arch-specific haskell translations differ:" 1>&2
        echo "${specdiff}" 1>&2
        exit 1
    fi
done

for thy in $SPECNONARCH/${ARCHES[0]}/*.thy; do rsync -c "$thy" "$SPEC/"; done

echo Built from git repo at $L4CAP by $USER > $SPEC/version
echo >> $SPEC/version
echo Generated from changeset: >> $SPEC/version
(cd $L4CAP && git show --oneline | head -1) >> $SPEC/version
echo >> $SPEC/version
if [ "$(cd $L4CAP && git status --short)" != "" ]
then
    echo >> $SPEC/version
    echo Warning - uncomitted changes used: >> $SPEC/version
    (cd $L4CAP && git status --short) >> $SPEC/version
fi
