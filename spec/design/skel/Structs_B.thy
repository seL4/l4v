(*
 * Copyright 2024, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Generic data types shared by design and abstract specs. *)

chapter "Common, Generic Data Types"

theory Structs_B
imports Arch_Structs_B
begin

arch_requalify_types (H)
  arch_tcb_flag

arch_requalify_consts (H)
  archTcbFlagToWord

#INCLUDE_SETTINGS keep_constructor = tcb_flag
#INCLUDE_HASKELL SEL4/Object/Structures.lhs ONLY TcbFlag tcbFlagToWord

end
