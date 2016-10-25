(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

chapter {* Event Send *}
(*<*)
theory EventFrom imports
  "../../tools/c-parser/CTranslation"
  "../../tools/autocorres/AutoCorres"
begin

(* THIS THEORY IS GENERATED. DO NOT EDIT. *)

declare [[allow_underscore_idents=true]]

install_C_file "EventFrom.c"

autocorres [ts_rules = nondet] "EventFrom.c"

locale EventFrom_glue = EventFrom
  + assumes swi_safe_to_ignore[simplified, simp]:
    "asm_semantics_ok_to_ignore TYPE(nat) true (''swi '' @ x)"
begin

lemma EventFrom__run_nf: "\<lbrace>\<lambda>s. \<forall>r. P r s\<rbrace> EventFrom__run' \<lbrace>P\<rbrace>!"
  apply (unfold EventFrom__run'_def)
  apply wp
  apply simp
  done

lemma seL4_Notify_wp[wp_unsafe]:
  "\<lbrace>\<lambda>s. \<forall>x. P x s\<rbrace>
    seL4_Notify' cap data
   \<lbrace>P\<rbrace>!"
  apply (simp add:seL4_Notify'_def seL4_MessageInfo_new'_def)
  apply wp
  apply simp
  done
(*>*)

text {*
  The CAmkES glue code for the sending side of an event consists of a single function for emitting
  a single instance of that event. The generated code is as follows.
  \clisting{eventfrom-emit-underlying.c}

  The safety of this function is straightforward to show as follows.
*}
lemma EventFrom_emit_nf: "\<lbrace>\<lambda>s. \<forall>r. P r s\<rbrace> EventFrom_emit_underlying' \<lbrace>P\<rbrace>!"
  apply (simp add:EventFrom_emit_underlying'_def)
  apply (wp seL4_Notify_wp)
  apply simp
  done

(*<*)
end

end
(*>*)
