#!/bin/bash
#
# Copyright 2021 ProofCraft Pty Ltd
#
# SPDX-License-Identifier: BSD-2-Clause
#

# Count number of sorries per major proof directory

count() {
    D="$1"
    TMP=`mktemp -q` || exit 1
    git grep -w sorry -- "${D}" > "${TMP}"
    if [ "$?" = "0" ]
    then
        SORRIES=$(wc -l < "${TMP}")
        echo "Sorries in ${D}: ${SORRIES}"
    fi
    rm "${TMP}"
}

TOP_DIRS="lib sys-init camkes"
SND_DIRS="spec proof"

for D in ${TOP_DIRS}; do count "$D"; done

for L1 in ${SND_DIRS}; do
    for D in $(find ${L1} -maxdepth 1 -mindepth 1 -type d); do count "$D"; done
done
