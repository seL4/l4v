(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Methods (* FIXME: bitrotted *)
imports Lib
begin

ML_file "Schema.ML"

method_setup schema = {* Schema.sch_method *}
  "discards arguments to schematic variables unneeded in current subgoal"

lemma "\<And>x. ?P arbitrary arbitrary (arbitrary x) \<Longrightarrow> False"
  apply schema
  apply assumption
  done

method_setup schemac = {* Schema.sch_cons_method *}
  "expands schematic variables applied to constructor arguments"

lemma "\<And>x y. \<lbrakk> ?P (Inl x); ?P (Inr y) \<rbrakk> \<Longrightarrow> (arbitrary x) \<and> (arbitrary y)"
  apply schemac
  apply (unfold sum.simps)
  apply safe
   apply assumption+
  done

lemma "\<lbrakk> ?P x \<rbrakk> \<Longrightarrow> case x of Inl y \<Rightarrow> arbitrary y | Inr z \<Rightarrow> Q"
  apply (case_tac x)
   apply clarsimp
   apply schemac
   apply clarsimp
   apply assumption
  apply clarsimp
  apply assumption
  done

end
