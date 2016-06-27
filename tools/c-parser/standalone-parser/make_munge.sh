#!/bin/bash
#
# Copyright 2016, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#
function usage () {
    cat <<EOF 1>&2
USAGE: make_munge.sh [-h|-o] <git-ref>
  -o         Output directory
  -h         Print help
EOF
}

#Defaults
SEL4REF=HEAD
OUT_DIR=.

# Argument parsing
while getopts ":ho:" opts
do
    case $opts in
        h)
            usage
            exit 0
            ;;
        o)
            OUT_DIR=${OPTARG}
            ;;
        *)
            echo "Invalid option: -${OPTARG}" >&2
    esac
done

shift $((OPTIND - 1))
[[ $# -gt 0 ]] && SEL4REF=$1 && shift
[[ $# -gt 0 ]] && echo "Ignoring $*"

set -e
# Find the script directory
CPARSER_DIR=$(cd $(dirname ${BASH_SOURCE[0]} ) && pwd)
[ -d $CPARSER_DIR ] || (echo "no c-parser dir" >&2 ; exit 1)

# Find the l4v/ base folder
L4V=$(cd ${CPARSER_DIR}/../../../../l4v ; pwd)
[ -d ${L4V} ] || (echo "Couldn't find l4v folder" >&2 ; exit 1)

# Find the seL4/ base folder
SEL4=$(cd ${CPARSER_DIR}/../../../../seL4 ; pwd)
[ -d ${SEL4} ] || (echo "Couldn't find seL4 folder" >&2 ; exit 1)

# Create temporary directory to store stuff
MUN_TMP=$(mktemp --tmpdir -d munge-seL4.XXXXXXXX) || \
    (echo "Error creating temporal directory" >&2 ; exit 1)
trap "rm -rf ${MUN_TMP}" EXIT
mkdir -p ${MUN_TMP}

# Useful refs
CKERNEL_DIR=${L4V}/spec/cspec/c
CKERNEL=${CKERNEL_DIR}/kernel_all.c_pp
CPARSER=${CPARSER_DIR}/c-parser
MUNGE_FILE=${MUN_TMP}/ckernel_munge.txt
SEL4_CLONE=${MUN_TMP}/sel4-clone

# Cloning seL4 repo into temporal folder
git clone -q -n ${SEL4} ${SEL4_CLONE} || \
    ( echo "Error cloning seL4 repo from \n ${SEL4}" >&2 && \
          exit 1 )

# Getting correct reference
SEL4REF=$(git -C ${SEL4} rev-parse --short ${SEL4REF}) || \
    ( echo "Error retriving reference ${SEL4REF} on local seL4 repo" >&2 && \
          exit 1 )

# Checking out the reference
git -C ${SEL4_CLONE} checkout -q ${SEL4REF} || \
    ( echo "Error checking out reference in temporary repo" >&2 && \
          exit 1 )

set +e
# Save the current kernel_all.c_pp
[ -f ${CKERNEL} ] && mv ${CKERNEL} ${CKERNEL}.orig

set -e
# Defaults
[ -n ${L4V_ARCH} ] || export L4V_ARCH=ARM
[ -n ${CONFIG_KERNEL_EXTRA_CPPFLAGS} ] || export CONFIG_KERNEL_EXTRA_CPPFLAGS=-P
# build kernel_all.c_pp
make -C ${CKERNEL_DIR} SOURCE_ROOT=${SEL4_CLONE} kernel_all.c_pp

# does the c-parser exist?
[ -x ${CPARSER} ] || (echo "Building c-parser..." ; make -C ${CPARSER_DIR})

# build munge file!!
${CPARSER} --munge_info_fname=${MUNGE_FILE} ${CKERNEL}

# move back kernel_all.c_pp
if [ -f ${CKERNEL}.orig ]
then
    rm ${CKERNEL}
    mv ${CKERNEL}.orig ${CKERNEL}
fi

# copy the munge file back!
[ -d ${OUT_DIR} ] || echo "${OUT_DIR} is not a directory using $PWD"
[ -d ${OUT_DIR} ] || OUT_DIR=.
cp ${MUNGE_FILE} ${OUT_DIR}/ckernel_munge.txt
