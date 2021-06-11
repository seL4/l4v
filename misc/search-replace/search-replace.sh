#!/bin/bash
#
# Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

do_replace () {

if ! grep -r -w -q $2 .;
  # target string exists
  then
  if grep -r -w -q $1 .;
    # source string exists
    then
    # search and replace
    find . -type f -exec sed -i "s/\b$1\b/$2/g" {} +
    echo "renamed: $1 --> $2"
  else
    # Error 1
    echo "source not found: $1"
  fi
else
  # Error 2
  echo "target not found: $2"
fi
}

echo "READING: " $1

cat $1 | while read line
do
	if [[ $line =~ (rename )([^ ]*)( to )([^ ]*) ]]
	then
	old=${BASH_REMATCH[2]}
	new=${BASH_REMATCH[4]}
	do_replace $old $new
	else
	echo "CANNOT PARSE LINE: $line"
	fi
done

echo "DONE"
