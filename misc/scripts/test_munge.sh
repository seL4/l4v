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
  -d    Preserve files
  -a    AST check
  -v    Verbose
  -c    Colorized output
  -h    Print help
EOF
}


# Argument parsing
while getopts ":hadvc" opts
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
        a)  AST=true
            AST_OPTS="-a"
            ;;
        c)  COLOR=''
            ;;
        *)
            echo "Invalid option: -${OPTARG}" >&2
            ;;
    esac
done

#color
RED=${COLOR+'\033[0;31m'}
YEL=${COLOR+'\033[0;33m'}
GRE=${COLOR+'\033[0;32m'}
NC=${COLOR+'\033[0m'}

shift $((OPTIND - 1))
REF1=$1
REF2=$2

[ -z ${DUMP+x} ] && trap "rm -f ckernel_*.txt" EXIT

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
then ${MAKE_MUNGE} ${AST_OPTS} ${REF1}  > /dev/null 2>&1
else ${MAKE_MUNGE} ${AST_OPTS} ${REF1}
fi
sort -o ckernel_names_1.txt ckernel_names.txt
rm ckernel_names.txt
mv kernel_all.txt kernel_all_1.txt
[ -z ${AST+x} ] || mv ckernel_ast.txt ckernel_ast_1.txt

if [ -z ${VERBOSE} ]
then ${MAKE_MUNGE} ${AST_OPTS} ${REF2} > /dev/null 2>&1
else ${MAKE_MUNGE} ${AST_OPTS} ${REF2}
fi
sort -o ckernel_names_2.txt ckernel_names.txt
rm ckernel_names.txt
mv kernel_all.txt kernel_all_2.txt
[ -z ${AST+x} ] || mv ckernel_ast.txt ckernel_ast_2.txt

set +e
ERRORS=false
# Check for differences in
echo -en "${RED}"
if ! diff ckernel_names_1.txt ckernel_names_2.txt &> /dev/null
then
    echo -e "${RED}"
    echo "#################################"
    echo "#   Some symbols have changed   #"
    echo -e "#################################\n"
    echo "please address this issue appropriately"
    echo "and run make_muge.sh afterwards."
    echo -e "\n${YEL}Symbols diff:${NC}"
    diff -uw ckernel_names_1.txt ckernel_names_2.txt
    ERRORS=true
fi

echo -en "${RED}"
if ! ([ -z ${AST+x} ] || diff ckernel_ast_1.txt ckernel_ast_2.txt &> /dev/null)
then
    echo -e "${RED}"
    echo "#################################"
    echo "#   The ASTs differ             #"
    echo -e "#################################\n"
    echo "please address this issue appropriately"
    echo "and run make_muge.sh afterwards."
    echo -e "${NC}${YEL}"
    ERRORS=true
fi

echo -en "${NC}"

if ! ${ERRORS}
then echo -e "${GRE}Everything seems fine${NC}"
else
    echo -en "${RED}"
    if ! diff ckernel_all_1.txt ckernel_all_2.txt &> /dev/null
    then
        echo -e "${RED}"
        echo "#################################"
        echo "#   Something has changed       #"
        echo -e "#################################\n"
        echo "please address this issue appropriately"
        echo "and run make_muge.sh afterwards."
        echo -e "\n${NC}${YEL}kernel_all diff:${NC}"
        diff -uw kernel_all_1.txt kernel_all_2.txt
    fi
    exit 1
fi
