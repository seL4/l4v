(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Alloc_Simp

imports
  "AutoCorres.AutoCorres"
  "Sep_Algebra.Separation_Algebra"
  "Sep_Algebra.Sep_Algebra_L4v"
  "Hoare_Sep_Tactics.Hoare_Sep_Tactics"
begin

external_file  "alloc_simp.c"

(* Parse the input file. *)
install_C_file  "alloc_simp.c"

(* Abstract the input file. *)
autocorres "alloc_simp.c"

(* Bodies of translated functions. *)
thm alloc_simp.align_up'_def
thm alloc_simp.alloc'_def
thm alloc_simp.add_mem_pool'_def
thm alloc_simp.init_allocator'_def

record my_state =
  heap_w32 :: "word32 ptr \<Rightarrow> word32 option"
(*  is_valid_w32 :: "word32 ptr \<Rightarrow> bool"
*)
term "a :: my_state"
term "a :: 'a my_state_ext"

instantiation my_state_ext :: (sep_algebra) sep_algebra
begin

definition "zero_my_state_ext \<equiv> \<lparr> heap_w32 = \<lambda>p. None, \<dots> = 0 \<rparr> "
definition "sep_disj_my_state_ext
              (a :: 'a my_state_ext) (b :: 'a my_state_ext) \<equiv>
                (\<forall>p. (heap_w32 a) p = None \<or> (heap_w32 b) p = None) \<and> (more a ## more b)"
definition "plus_my_state_ext (a :: 'a my_state_ext) (b :: 'a my_state_ext) \<equiv>
                     \<lparr> heap_w32 = \<lambda>p. if (heap_w32 a p = None) then (heap_w32 b p) else (heap_w32 a p)  , \<dots> = more a + more b \<rparr>"

instance
  apply default
         apply (unfold zero_my_state_ext_def sep_disj_my_state_ext_def plus_my_state_ext_def)
        apply (clarsimp)
        apply (clarsimp simp: sep_disj_commute)
       apply (metis Some_helper)
       apply (clarsimp)
       apply (rule my_state.equality)
        apply (clarsimp)
        defer
        apply (clarsimp)
      apply (auto)[1]
       apply (metis)
      apply (auto intro: sep_add_commute)[1]
     apply (auto intro: sep_add_assoc)[1]
    apply (auto dest: sep_disj_addD)[1]
   apply (auto)[1]
    apply (metis option.distinct(1))
   apply (auto elim: sep_disj_addI1)[1]
  apply (auto)[1]
  done
end

definition
    "set_val a v  =
        modify (my_state.heap_w32_update (\<lambda>s. s(a := Some v)))"

definition
      "get_val p = gets (\<lambda>s. the (my_state.heap_w32 s p))"

lemma set_val_wp: "\<lbrace>\<lambda>s. ((\<lambda>s. heap_w32 s a = Some any) \<and>* R) s\<rbrace>
     set_val a x
    \<lbrace>\<lambda>_ s.  ((\<lambda>s. heap_w32 s a = Some x) \<and>* R) s\<rbrace>"
   apply(clarsimp simp: set_val_def sep_conj_def)
   apply(rule_tac x="my_state.heap_w32_update (\<lambda>s. s(a \<mapsto> x)) xa " in exI)
   apply(rule_tac x=y in exI)
   apply (clarsimp)
   apply (safe)
   apply (clarsimp simp: sep_disj_my_state_ext_def)
   apply (erule_tac x=a in allE)
   apply (clarsimp)
   apply(clarsimp simp: plus_my_state_ext_def)
   apply (rule ext)
   apply (clarsimp)
done

lemma get_val_wp: "\<lbrace>\<lambda>s. ((\<lambda>s. heap_w32 s a = Some x) \<and>* R) s\<rbrace>
     get_val a
    \<lbrace>\<lambda>rv.  ((\<lambda>s. heap_w32 s a = Some x) \<and>* R)  and K (rv = x) \<rbrace>"
  apply(clarsimp simp: get_val_def sep_conj_def)
  apply(rule conjI)
  apply(rule_tac x=xa in exI)
  apply(rule_tac x=y in exI)
  apply(simp)
  apply(clarsimp simp: plus_my_state_ext_def)
done

lemma fixes a :: "word32 ptr" and b :: "word32 ptr"
  shows "\<lbrace> \<lambda>s. heap_w32 s a = Some x
           \<and> heap_w32 s b = Some y\<rbrace>
           my_swap a b
         \<lbrace>\<lambda>r s. heap_w32 s a = Some y \<and> heap_w32 s b = Some x \<rbrace>!"
sorry

end
