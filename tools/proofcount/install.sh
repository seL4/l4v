#!/usr/bin/env bash
#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

DIR=$( cd "$( dirname "$BASH_SOURCE[0]}" )" && pwd)

if [ -z $1 ] ; then
 echo
 echo "Usage: install.sh ISABELLE_BIN [-P]"
 echo
 echo "      ISABELLE_BIN   isabelle command proofcount should be installed to"
 echo "      -P             attempt to patch isabelle to allow metric collection"
 exit 1
fi

ISABELLE_TOOL="$1"

export `$ISABELLE_TOOL getenv ISABELLE_PROOFCOUNT_HOME`
export `$ISABELLE_TOOL getenv ISABELLE_HOME_USER`

if [ -z "$ISABELLE_HOME_USER" ] ; then
  echo "Missing Isabelle Home"
  exit 1
fi

if [ -z "$ISABELLE_PROOFCOUNT_HOME" ] ; then
  echo "init_component "$DIR/"" >> "$ISABELLE_HOME_USER/etc/settings"
fi

if [ "$2" = "-P" ] ; then
  "$ISABELLE_TOOL" proofcount -P
fi

