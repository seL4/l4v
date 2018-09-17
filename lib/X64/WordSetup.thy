(*
 * Copyright 2017, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)


theory WordSetup (* part of non-AFP Word_Lib *)
imports
  "../Distinct_Prop"
  "../Word_Lib/Word_Lemmas_64_Internal"
begin

(* Distinct_Prop lemmas that need word lemmas: *)

lemma distinct_prop_enum:
  "\<lbrakk> \<And>x y. \<lbrakk> x \<le> stop; y \<le> stop; x \<noteq> y \<rbrakk> \<Longrightarrow> P x y \<rbrakk>
     \<Longrightarrow> distinct_prop P [0 :: 'a :: len word .e. stop]"
  apply (simp add: upto_enum_def distinct_prop_map del: upt.simps)
  apply (rule distinct_prop_distinct)
   apply simp
  apply (simp add: less_Suc_eq_le del: upt.simps)
  apply (erule_tac x="of_nat x" in meta_allE)
  apply (erule_tac x="of_nat y" in meta_allE)
  apply (frule_tac y=x in unat_le)
  apply (frule_tac y=y in unat_le)
  apply (erule word_unat.Rep_cases)+
  apply (simp add: toEnum_of_nat[OF unat_lt2p]
                   word_le_nat_alt)
  done

lemma distinct_prop_enum_step:
  "\<lbrakk> \<And>x y. \<lbrakk> x \<le> stop div step; y \<le> stop div step; x \<noteq> y \<rbrakk> \<Longrightarrow> P (x * step) (y * step) \<rbrakk>
     \<Longrightarrow> distinct_prop P [0, step .e. stop]"
  apply (simp add: upto_enum_step_def distinct_prop_map)
  apply (rule distinct_prop_enum)
  apply simp
  done

end
