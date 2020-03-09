(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory codetests
imports "CParser.CTranslation"
begin

ML \<open>Context.>> (Context.map_theory (
        TermsTypes.prim_mk_defn "foo" @{term "33::nat"}))
\<close>

thm foo_def

ML \<open>
  Context.>> (Context.map_theory (
    RecursiveRecordPackage.define_record_type [
      {record_name = "myrecord",
       fields = [{fldname = "fld1", fldty = @{typ "nat"}},
                 {fldname = "myset", fldty = @{typ "nat \<Rightarrow> bool"}}]}
    ]))
\<close>

thm myrecord_accupd_same

end
