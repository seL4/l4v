(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchTCB_H
imports "../TCBDecls_H"
begin
(* FIXME: Clagged from ARM version *)

context X64 begin

#INCLUDE_HASKELL SEL4/Object/TCB/X64.lhs CONTEXT X64

end (* context X64 *)

end
