(*
 * Copyright 2024, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Generic data types shared by design and abstract specs. *)

chapter "Common, Generic Data Types"

theory Structs_B
imports
  Setup_Locale
  Lib.HaskellLib_H
  MachineExports
begin

#INCLUDE_SETTINGS keep_constructor = tcb_flag
#INCLUDE_HASKELL SEL4/Object/Structures.lhs ONLY TcbFlag tcbFlagToWord tcbFlagMask

text \<open>Ticks are always 64 bits, even on 32-bit platforms\<close>
type_synonym ticks_len = 64
type_synonym ticks = "ticks_len word"

definition timeArgLen :: nat where
  "timeArgLen \<equiv> LENGTH(ticks_len) div LENGTH(machine_word_len)"

end
