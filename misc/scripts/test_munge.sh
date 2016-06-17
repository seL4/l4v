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
USAGE: test_munge.sh [-h|-d|-v] <git-ref> [git-ref]
  -d    Preserve both munge files
  -v    Verbose
  -h    Print help
EOF
}

#color
RED='\033[0;31m'
YEL='\033[0;33m'
GRE='\033[0;32m'
NC='\033[0m'

# Argument parsing
while getopts ":hdv" opts
do
    case $opts in
        h)
            usage
            exit 0
            ;;
        d)
            DUMP=true
            ;;
        v)
            VERBOSE=true
            ;;
        *)
            echo "Invalid option: -${OPTARG}" >&2
            ;;
    esac
done

shift $((OPTIND - 1))
REF1=$1
REF2=$2

[ -z $DUMP ] && trap "rm -f ckernel_munge_*.txt" EXIT

set -e
[ -z ${REF1} ] && (echo "At least 1 ref is required" >&2 ; exit 1)
[[ $# -gt 2 ]] && echo "Ignoring ${@:3}"

# Find the script directory
SCRIPT_DIR=$(cd $(dirname ${BASH_SOURCE[0]} ) && pwd)
[ -d ${SCRIPT_DIR} ] || (echo "no script dir" 1>&2 ; exit 1)

# Find the l4v/ base folder
L4V=$(cd ${SCRIPT_DIR}/../../../l4v ; pwd)
[ -d ${L4V} ] || (echo "Couldn't find l4v folder" ; exit 1)

CPARSER_DIR=${L4V}/tools/c-parser/standalone-parser
MAKE_MUNGE=${CPARSER_DIR}/make_munge.sh

echo -e "${YEL}WORKING...${NC}"

if [ -z ${VERBOSE} ]
then ${MAKE_MUNGE} $REF1  > /dev/null 2>&1
else ${MAKE_MUNGE} $REF1
fi

mv ckernel_munge.txt ckernel_munge_1.txt

if [ -z ${VERBOSE} ]
then ${MAKE_MUNGE} $REF2 > /dev/null 2>&1
else ${MAKE_MUNGE} $REF2
fi
mv ckernel_munge.txt ckernel_munge_2.txt

set +e

# Check for differences
echo -e "${RED}"
if ! diff -q ckernel_munge_1.txt ckernel_munge_2.txt
then
    echo -e "${RED}"
    echo "#################################"
    echo "#   Some symbols have changed   #"
    echo -e "#################################\n"
    echo "please address this issue appropriately"
    echo "and run make_muge.sh afterwards."
    echo -e "${NC}${YEL}"
    echo "Running this might help:"
    echo "$ diff -uw ckernel_munge_1.txt ckernel_munge_2.txt"
    exit 1
else
    echo -e "${GRE}Everything seems fine${NC}"
fi
