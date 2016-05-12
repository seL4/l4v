(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Sep_Attribs
imports Separation_Algebra Sep_Tactic_Helpers
begin

text{* Beyond the tactics above, there is also a set of attributes implemented to make proving
       things in separation logic easier. These rules should be considered internals and are not
       intended for direct use. *}


lemma sep_curry_atomised: "\<lbrakk>(\<And>s. (P \<and>* Q) s \<longrightarrow> R s); P s \<rbrakk> \<Longrightarrow> (Q \<longrightarrow>* R) s"
  by (clarsimp simp: sep_conj_sep_impl)

lemma sep_remove_pure_imp_sep_imp: "( P \<longrightarrow>* (\<lambda>s. P' \<longrightarrow> Q s)) s \<Longrightarrow> P' \<Longrightarrow> (P \<longrightarrow>* Q) s"
  by (clarsimp)

lemma sep_backward: "\<lbrakk>\<And>s. P s \<longrightarrow> (Q \<and>* T) s; (P \<and>* (Q \<longrightarrow>* R)) s \<rbrakk> \<Longrightarrow> (T \<and>* R) s"
  by (metis sep_conj_commute sep_conj_impl1 sep_mp_frame)

lemma sep_remove_conj: "\<lbrakk>(P \<and>* R) s ; Q\<rbrakk> \<Longrightarrow> ((\<lambda>s. P s \<and> Q) \<and>* R) s "
  apply (clarsimp)
  done

lemma curry: "(P \<longrightarrow> Q \<longrightarrow> R) \<Longrightarrow> (P \<and> Q) \<longrightarrow> R"
  apply (safe)
  done


ML {*
local
  fun atomize_thm ctxt thm = Conv.fconv_rule (Object_Logic.atomize ctxt) thm
  fun setup_simpset ctxt = put_simpset HOL_basic_ss ctxt addsimps [(sym OF [@{thm sep_conj_assoc}])]
  fun simp ctxt thm = simplify (setup_simpset ctxt) thm

  fun REPEAT_TRYOF_N _ thm2 0 = thm2
    | REPEAT_TRYOF_N thm1 thm2 n = REPEAT_TRYOF_N thm1 (thm1 OF [thm2]) (n-1)

  fun REPEAT_TRYOF'_N thm1 _    0 = thm1
    | REPEAT_TRYOF'_N thm1 thm2 n = REPEAT_TRYOF'_N (thm1 OF [thm2]) thm2 (n-1)

  fun attribute_thm ctxt thm  thm' = 
    REPEAT_TRYOF_N @{thm sep_remove_pure_imp_sep_imp} (thm OF [atomize_thm ctxt thm']) (Thm.nprems_of thm' - 1)

  fun attribute_thm' thm ctxt thm' =
    thm OF [REPEAT_TRYOF_N @{thm curry} (thm' |> atomize_thm ctxt o simp ctxt) (Thm.nprems_of thm' - 1)]

in

(*
 By attributing a theorem with [sep_curry], we can now take a rule (A \<and>* B) \<Longrightarrow> C and turn it into A \<Longrightarrow> (B \<longrightarrow>* C)
*)

fun sep_curry_inner ctxt = attribute_thm ( ctxt) @{thm sep_curry_atomised}
val sep_curry = Thm.rule_attribute [] (fn ctxt => sep_curry_inner (Context.proof_of ctxt))

(*
 The attribute sep_back takes a rule of the form A \<Longrightarrow> B and returns a rule (A \<and>* (B \<longrightarrow>* R)) \<Longrightarrow> R.
 The R then matches with any conclusion. If the theorem is of form (A \<and>* B) \<Longrightarrow> C, it is advised to
 use sep_curry on the theorem first, and then sep_back. This aids sep_cancel in simplifying the result.
*)

fun backward ctxt thm =
  REPEAT_TRYOF'_N (attribute_thm' @{thm sep_backward} ctxt thm) @{thm sep_remove_conj} (Thm.nprems_of thm - 1)

fun backward' ctxt thm = backward (Context.proof_of ctxt) thm

val sep_backward = Thm.rule_attribute [] (backward')

end
*}

attribute_setup sep_curry =  {* Scan.succeed sep_curry *}
attribute_setup sep_backward =  {* Scan.succeed sep_backward *}

end
