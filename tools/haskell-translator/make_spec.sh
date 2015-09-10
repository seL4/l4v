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

. "$TRANSLATOR/CONFIG"

SPEC=$(find_dir "spec/design")

if [[ -z $L4CAP ]]
then
  L4CAP=$(find_dir "seL4/haskell")
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

cd $TRANSLATOR
python pars_skl.py $TMPFILE

rm $TMPFILE
