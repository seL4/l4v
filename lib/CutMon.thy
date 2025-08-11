(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* The cutMon predicate and supporting lemmas.
   "cutMon P f" executes f when P is true, otherwise fails. Cuts off uninteresting executions. *)

theory CutMon
  imports
    Monads.Nondet_Empty_Fail
    Monads.Nondet_VCG
begin

definition
  cutMon :: "('c, 's) mpred \<Rightarrow> ('c, 's, 'a) nondet_monad \<Rightarrow> ('c, 's, 'a) nondet_monad" where
 "cutMon P f \<equiv> \<lambda>s. if P s then f s else fail s"

lemma cutMon_walk_bind:
  "cutMon ((=) s) (f >>= g) =
   (cutMon ((=) s) f >>= (\<lambda>rv. cutMon (\<lambda>s'. (rv, mstate s') \<in> fst (f s)) (g rv)))"
  apply (rule ext, simp add: cutMon_def bind_def fail_def)
  apply (auto simp: split_def)
  done

lemma cutMon_walk_bindE:
  "cutMon ((=) s) (f >>=E g) =
   (cutMon ((=) s) f >>=E (\<lambda>rv. cutMon (\<lambda>s'. (Inr rv, mstate s') \<in> fst (f s)) (g rv)))"
  apply (simp add: bindE_def cutMon_walk_bind)
  apply (rule bind_cong, rule refl)
  apply (simp add: cutMon_def lift_def fail_def split: if_split_asm)
  apply (clarsimp split: sum.split)
  done

lemma cutMon_walk_if:
  "cutMon ((=) s) (if P then f else g) = (if P then cutMon ((=) s) f else cutMon ((=) s) g)"
  by (simp add: cutMon_def)

lemma cutMon_valid_drop:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> cutMon R f \<lbrace>Q\<rbrace>"
  by (simp add: cutMon_def valid_def fail_def)

lemma cutMon_validE_drop:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> cutMon R f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  by (simp add: validE_def cutMon_valid_drop)

lemma snd_cutMon:
  "snd (cutMon P f s) = (P s \<longrightarrow> snd (f s))"
  by (simp add: cutMon_def fail_def split: if_split)

lemma cutMon_assert_opt:
  "cutMon P (gets_the f >>= g) = gets_the (\<lambda>s. if P s then f s else None) >>= g"
  by (simp add: cutMon_def gets_the_def exec_gets
                bind_assoc fun_eq_iff assert_opt_def
         split: if_split)


(* empty_fail: *)

lemma empty_fail_use_cutMon:
  "\<lbrakk> \<And>s. empty_fail (cutMon ((=) s) f) \<rbrakk> \<Longrightarrow> empty_fail f"
  by (fastforce simp add: empty_fail_def cutMon_def split: if_split_asm)

lemma empty_fail_drop_cutMon:
  "empty_fail f \<Longrightarrow> empty_fail (cutMon P f)"
  by (simp add: empty_fail_def fail_def cutMon_def split: if_split)

lemma empty_fail_cutMon:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> empty_fail (cutMon ((=) s) f) \<rbrakk> \<Longrightarrow> empty_fail (cutMon P f)"
  by (fastforce simp: empty_fail_def cutMon_def fail_def split: if_split_asm)

lemmas empty_fail_cutMon_intros =
     cutMon_walk_bind[THEN arg_cong[where f=empty_fail], THEN iffD2,
                      OF empty_fail_bind, OF _ empty_fail_cutMon]
     cutMon_walk_bindE[THEN arg_cong[where f=empty_fail], THEN iffD2,
                       OF empty_fail_bindE, OF _ empty_fail_cutMon]
     cutMon_walk_if[THEN arg_cong[where f=empty_fail], THEN iffD2,
                    OF empty_fail_If]

end
