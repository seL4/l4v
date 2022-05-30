#!/bin/bash
#
# Copyright 2022 Proofcraft Pty Ltd
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

git rev-parse --show-toplevel 2> /dev/null || fail "Must be run inside l4v repo."
cd "$(git rev-parse --show-toplevel)"

TOP_DIRS="lib sys-init camkes"
SND_DIRS="spec proof"

for D in ${TOP_DIRS}; do count "$D"; done

for L1 in ${SND_DIRS}; do
    for D in $(find ${L1} -maxdepth 1 -mindepth 1 -type d); do count "$D"; done
done

cd - > /dev/null
