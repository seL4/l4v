(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
