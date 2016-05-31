(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory GhostAssertions

imports "../c-parser/CTranslation"

begin

text {* Some framework constants for adding assertion data to the ghost
state and accessing it. These constants don't do much, but using them
allows the SimplExport mechanism to recognise the intent of ghost state
operations. *}
