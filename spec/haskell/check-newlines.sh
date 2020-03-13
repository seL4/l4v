#!/bin/sh
#
# Copyright 2014, General Dynamics C4 Systems
#
# SPDX-License-Identifier: GPL-2.0-only
#

# A rough check to ensure LaTeX won't hang during compilation due to
# missing newlines at the end of files.

wontcompile=0
for file in $(find . -name *.lhs);
do
    if [ ! -z "$( tail -n 1 ${file} | tr -d '\n' )" ]; then
        echo "${file} needs a newline appended for LaTeX to compile."
        wontcompile=1
    fi
done
exit $wontcompile
