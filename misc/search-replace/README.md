<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# search-replace.sh

This script takes an input file which is a list of text replacements and
applies those replacements to all files in the current directory.

Usage: `bash search-replace.sh renames.txt`

where each line of `renames.txt` is of the form `renames mysearchtext to
myreplacetext`.

Caution: if `renames.txt` is in the current directory then this script will act
on that file and make it useless for future invocations.
