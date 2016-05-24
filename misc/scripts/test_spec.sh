#!/bin/bash
#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

# Fetch this scripts directory.
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

# Base
BASE="${SCRIPT_DIR}/../.."

# Haskell translator directory
HASKELL_TRANS="${BASE}/tools/haskell-translator"

# Isabelle skeleton files.
SKEL="${BASE}/spec/design/skel"
MSKEL="${BASE}/spec/design/m-skel"
if [[ ! -d $SKEL ]]
then
	echo "Could not find directory: $SKEL"
	exit 1
fi

ARCHES=("ARM")

NAMES=`cd $SKEL; ls *.thy`

# Output specification.
SPEC="${BASE}/spec/design"

# Machine specification.
MACH="${BASE}/spec/machine"

# Create temporary directory to store generated spec.
case $(uname -s) in
	Linux)
		SPEC_TMP=$(mktemp --tmpdir -d spec-check.XXXXXXXX) || exit 1
		;;
	Darwin)
		SPEC_TMP=$(pwd)/$(mktemp  -d spec-check.XXXXXXXX) || exit 1
		;;
	*)
		echo "OS not supported"
		exit 1
		;;
esac
trap "rm -rf $SPEC_TMP" EXIT
mkdir -p "$SPEC_TMP/machine"

# Generate list of files to generate.

function send_filenames () {
        local arch=${1}

        local archnames=`cd $SKEL/${arch}; ls *.thy`
        local archmnames=`cd $MSKEL/${arch}; ls *.thy`
        mkdir -p "$SPEC_TMP/${arch}" 
        mkdir -p "$SPEC_TMP/machine/${arch}"
 
        # Theory files common to all haskell specifications
	for NAME in $NAMES
	do
		echo "$SKEL/$NAME --> $SPEC_TMP/$NAME"
	done

        # Arch-specific haskell specifications
        for NAME in ${archnames}
        do
                echo "$SKEL/${arch}/$NAME --> $SPEC_TMP/${arch}/$NAME"
        done

        # Arch-specific machine theories, imported by haskell and abstract
        for MNAME in ${archmnames}
        do
                echo "$MSKEL/${arch}/$MNAME --> $SPEC_TMP/machine/${arch}/$MNAME"
        done
}


# Assert files $1 and $2 are the same.
function test_files () {
	if diff -u $1 $2
	then
		true
	else
		FAILURE=$?
		echo "Spec deviates at $2"
		echo "Spec deviates at $2" 1>&2
		exit $FAILURE
	fi
}

# Assert that all the files in $NAMES are identical.
function test_filenames () {
        local tmpthys=`cd $SPEC_TMP; find . -name "*.thy" | grep -v "./machine"`
       
	for tmpthy in $tmpthys
	do
                local tmpthy=${tmpthy:2}
		test_files "$SPEC_TMP/$tmpthy" "$SPEC/$tmpthy"
	done

        local tmpmthys=`cd "$SPEC_TMP/machine"; find . -name "*.thy"`

	for tmpthy in $tmpmthys
	do
                local tmpthy=${tmpthy:2}
		test_files "$SPEC_TMP/machine/$tmpthy" "$MACH/$tmpthy"
	done

 
}

# Generate spec.
cd ${HASKELL_TRANS}
export L4CAP="${BASE}/spec/haskell"
echo "Generating spec from haskell..."

for ARCH in ${ARCHES[@]}
do
        L4CPP="-DTARGET=$ARCH -DTARGET_$ARCH -DPLATFORM=QEmu -DPLATFORM_QEmu"
        export L4CPP
        cd ${HASKELL_TRANS}
        send_filenames ${ARCH} | python pars_skl.py -q /dev/stdin
done

# Ensure committed files match generated files.
echo "Testing conformity of spec to haskell..."
test_filenames

echo "Spec conforms to haskell."

