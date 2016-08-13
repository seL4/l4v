#!/bin/sh
# Copyright 2014, General Dynamics C4 Systems
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(GD_GPL)

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
