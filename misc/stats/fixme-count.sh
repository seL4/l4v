#!/bin/bash
#
# Copyright 2022 Proofcraft Pty Ltd
#
# SPDX-License-Identifier: BSD-2-Clause
#

# Count number of FIXMEs with provided tag.

usage()
{
    echo "$0 TAG: Count number of FIXMEs with provided tag."
    echo
    echo "Example:"
    echo "$0 AARCH64"
}

fail()
{
    echo "$@"
    exit 1
}

count() {
    D="$1"
    TAG="$2"
    TMP=`mktemp -q` || exit 1
    git grep "FIXME ${TAG}" -- "${D}" > "${TMP}"
    if [ "$?" = "0" ]
    then
        FIXMES=$(wc -l < "${TMP}" | sed -e 's/^[[:space:]]*//')
        if [ "$D" = "." ]; then
          DIR="total"
        else
          DIR="${D}"
        fi
        echo "FIXME ${TAG} in ${DIR}: ${FIXMES}"
    fi
    rm "${TMP}"
}

git rev-parse --show-toplevel 2> /dev/null || fail "Must be run inside l4v repo."
cd "$(git rev-parse --show-toplevel)"

if [ "$#" -lt 1 ]; then
    usage && exit 1
fi

TAG=$1

TOP_DIRS="lib sys-init camkes"
SND_DIRS="spec proof"

for D in ${TOP_DIRS}; do count "$D" "$TAG"; done

for L1 in ${SND_DIRS}; do
    for D in $(find ${L1} -maxdepth 1 -mindepth 1 -type d); do count "$D" "$TAG"; done
done

count "." "$TAG"

cd - > /dev/null
