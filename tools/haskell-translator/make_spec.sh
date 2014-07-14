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

. ./CONFIG 

test -z $L4CAP && export L4CAP=../../../seL4/haskell

if [[ ! -d $L4CAP/src/SEL4 ]]
then
	echo Set the L4CAP environment variable to the location
	echo of the haskell mercurial source.
	exit
fi

SPEC="../../spec/design"

SKEL="$SPEC/skel"
MSKEL="$SPEC/m-skel"

MACH="../../spec/machine"

if [[ ! -d $SKEL ]]
then
	echo Error: $SKEL is not a directory.
	echo '(this script needs to be run in the scripts directory)'
	exit
fi

echo Built from git repo at $L4CAP on `uname -n` by $USER > $SPEC/version
echo >> $SPEC/version
echo Generated from changeset: >> $SPEC/version
(cd $L4CAP && git show --oneline | head -1 >> $SPEC/version)
echo >> $SPEC/version
if [ "$(cd $L4CAP && git status --short)" != "" ]
then
  echo >> $SPEC/version
  echo Warning - uncomitted changes used: >> $SPEC/version
  $(cd $L4CAP && git status --short) >> $SPEC/version
fi

NAMES=`ls $SKEL`

TMPFILE="/tmp/make_spec_temp_$$"

function send_filenames () {
	for NAME in $NAMES
	do
		echo "$SKEL/$NAME --> $SPEC/$NAME"
	done
	echo "$MSKEL/ARMMachineTypes.thy --> $MACH/ARMMachineTypes.thy"
}

send_filenames > $TMPFILE

python pars_skl.py $TMPFILE

rm $TMPFILE
