#!/bin/zsh

#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

if [ ! "$1" ]; then
  echo "Print AutoCorres translation time"
  echo "Usage: $0 SESSION-NAME"
  exit 1
fi

gunzip -c $(isabelle env sh -c 'echo $ISABELLE_OUTPUT')/log/"$1".gz |\
tr -cd '[:print:]\n' |\
command egrep '\([a-zA-Z0-9_ \) [a-zA-Z0-9_]+ in [0-9.]+ s' -o |\
sed 's/\(.*\) in \([0-9.]\+\) s/\2s \1/' |\
sort -nr |\
 (
 l1=0.0; l2=0.0; hl=0.0; wa=0.0; ts=0.0
 while read -r time stage fn; do
   echo "$time $stage $fn"
   time="$(sed 's/s$//' <<<"$time")"
   if [ $stage = '(L1)' ]; then l1=$(($l1 + $time)); fi
   if [ $stage = '(L2)' ]; then l2=$(($l2 + $time)); fi;
   if [ $stage = '(HL)' ]; then hl=$(($hl + $time)); fi
   if [ $stage = '(WA)' ]; then wa=$(($wa + $time)); fi
   if [ $stage = '(TS)' ]; then ts=$(($ts + $time)); fi
 done
 echo ------
 printf "L1: %10.3fs\n" "$l1"
 printf "L2: %10.3fs\n" "$l2"
 printf "HL: %10.3fs\n" "$hl"
 printf "WA: %10.3fs\n" "$wa"
 printf "TS: %10.3fs\n" "$ts"
 )
