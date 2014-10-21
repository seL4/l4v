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

# Load custom config.
. ${HASKELL_TRANS}/CONFIG

# Isabelle skeleton files.
SKEL="${BASE}/spec/design/skel"
MSKEL="${BASE}/spec/design/m-skel"
if [[ ! -d $SKEL ]]
then
	echo "Could not find directory: $SKEL"
	exit 1
fi
NAMES=`ls $SKEL`

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

# Generate list of files to generate.
function send_filenames () {
	for NAME in $NAMES
	do
		echo "$SKEL/$NAME --> $SPEC_TMP/$NAME"
	done
	echo "$MSKEL/ARMMachineTypes.thy --> $SPEC_TMP/ARMMachineTypes.thy"
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
	for NAME in $NAMES
	do
		test_files "$SPEC_TMP/$NAME" "$SPEC/$NAME"
	done
	test_files "$SPEC_TMP/ARMMachineTypes.thy" "$MACH/ARMMachineTypes.thy"
}

# Generate spec.
cd ${HASKELL_TRANS}
export L4CAP="${BASE}/../seL4/haskell"
echo "Generating spec from haskell..."
send_filenames | python pars_skl.py -q /dev/stdin

# Ensure committed files match generated files.
echo "Testing conformity of spec to haskell..."
test_filenames

echo "Spec conforms to haskell."

