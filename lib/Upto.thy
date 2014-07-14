(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Upto
imports "~~/src/HOL/Main"
begin

(* FIXME: in fact, overhaul this whole business now that interval is defined properly in the dist *)
(* FIXME: move to distribution *)
instantiation nat :: finite_intvl_succ 
begin
  definition 
  suc_nat_def: "List.finite_intvl_succ_class.successor == Suc"

  instance
  apply intro_classes
  apply (auto simp: suc_nat_def)
  done
end

lemma (in finite_intvl_succ) singleton_intvl [simp]:
  "[x..x] = [x]"
  apply (subst upto_rec)
  apply simp
  apply (clarsimp simp: upto_def)
  apply (subgoal_tac "{successor x ..x} = {}")
   apply simp
  apply (insert successor_incr [of x])
  apply simp
  done

lemma (in finite_intvl_succ) upto_suc_rec:
  "[n..successor m] = (if n \<le> successor m then [n..m] @ [successor m] else [])"
  apply simp
  apply (rule conjI)
   prefer 2
   apply (clarsimp simp: upto_def)
  apply clarsimp
  apply (simp add: upto_def sorted_list_of_set_def)
  apply (rule the1_equality[OF finite_sorted_distinct_unique])
   apply (simp add:finite_intvl)
  apply(rule the1I2[OF finite_sorted_distinct_unique])
   apply (simp add:finite_intvl)
  apply simp
  apply (insert successor_incr [of m])
  apply clarsimp
  apply (rule conjI)
   apply rule
    apply fastforce
   apply (clarsimp simp: not_le)
   apply (cut_tac a=m in ord_discrete)
   apply clarsimp
   apply (erule_tac x=xa in allE)
   apply simp
  apply (clarsimp simp: sorted_append)
  apply (fastforce)
  done

lemma upto_Suc:
  "[n..Suc m] = (if n \<le> Suc m then [n..m] @ [Suc m] else [])"
  apply (fold suc_nat_def)
  apply (rule upto_suc_rec)
  done

lemma upto_upt:
  "[n..m] = [n..<Suc m]"
  apply (induct m)
   apply (clarsimp simp: upto_rec suc_nat_def)
  apply (simp add: upto_Suc del: upt.simps)
  apply (clarsimp simp add: upto_Suc)
  done

end
