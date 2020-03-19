(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Sep_Tactic_Examples
imports
  "SepDSpec.Sep_Tactic_Helper"
  KHeap_DP
begin


(* Thesis : Automated Tactics for Seperation Logic *)

(* seperation logic *)

(* after we show that addition and disjointedness on our heap obeys certain laws, we get a seperation algebra *)

(* connectives *)

term "P \<and>* Q"

term "P \<longrightarrow>* Q"

lemma frame_rule:
  "\<And>R. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. Q\<rbrace> \<Longrightarrow> \<lbrace>P \<and>* R\<rbrace> f \<lbrace>\<lambda>_. Q \<and>* R\<rbrace>"
  oops

lemma
 "\<lbrace><dest \<mapsto>c - \<and>* src \<mapsto>c cap \<and>* R>\<rbrace>
    move_cap cap' src dest
  \<lbrace>\<lambda>_. <dest \<mapsto>c cap'  \<and>* src \<mapsto>c NullCap \<and>* R>\<rbrace>"
  apply (simp add: move_cap_def)
  apply (wp swap_parents_wp set_cap_wp) (* set_cap doesn't apply *)
thm set_cap_wp[no_vars]
   apply (rule hoare_strengthen_post)
    apply (wp set_cap_wp)
   apply (clarsimp simp: sep_conj_ac )
oops


(* tactics we had pre-thesis *)

lemma "(A \<and>* B \<and>* C \<and>* D) s  \<Longrightarrow>  (A \<and>* B \<and>* C \<and>* D) s"
  apply (sep_select 4)
  apply (sep_select_asm 3)
  apply (sep_select 2)
  apply (sep_cancel)
  apply (sep_cancel)
  apply (sep_cancel)
done

(* forward reasoning *)


lemma example_drule:
  "(ptr \<mapsto>o obj) s
  \<Longrightarrow> (ptr \<mapsto>S obj \<and>* ptr \<mapsto>f obj) s"
  by (metis sep_conj_commute sep_map_o_decomp)

lemma sep_drule_example:
  "(ptr \<mapsto>o obj \<and>* A \<and>* B ) s
  \<Longrightarrow> (A \<and>* B \<and>* ptr \<mapsto>f obj \<and>* ptr \<mapsto>S obj) s"
  apply (sep_drule  example_drule)
  apply (sep_solve)
done

(* backwards reasoning *)

lemma example_rule:
  "(ptr \<mapsto>f obj \<and>* ptr \<mapsto>S obj) s
  \<Longrightarrow> (ptr \<mapsto>o obj) s"
  by (metis sep_map_o_decomp)

lemma sep_rule_example: "(ptr \<mapsto>f obj \<and>* A \<and>* B \<and>* ptr \<mapsto>S obj ) s \<Longrightarrow> (ptr \<mapsto>o obj \<and>* A \<and>* B) s"
  apply (sep_rule example_rule)
  apply (sep_solve)
done



(* the state of proving before new stuff *)

lemma swap_cap_wp_old:
  "\<lbrace><dest \<mapsto>c cap \<and>*  src \<mapsto>c cap' \<and>* R>\<rbrace>
    swap_cap cap' src cap dest
   \<lbrace>\<lambda>_.<dest \<mapsto>c cap' \<and>* src \<mapsto>c cap \<and>* R>\<rbrace>"
  apply (clarsimp simp add: swap_cap_def)
  apply (wp swap_parents_wp set_cap_wp)
  apply (rule hoare_chain)
    apply (rule set_cap_wp)
    apply (sep_solve)+
done


lemma move_cap_wp_old:
 "\<lbrace><dest \<mapsto>c - \<and>* src \<mapsto>c cap \<and>* R>\<rbrace>
    move_cap cap' src dest
  \<lbrace>\<lambda>_. <dest \<mapsto>c cap'  \<and>* src \<mapsto>c NullCap \<and>* R>\<rbrace>"
  including no_pre
  apply (simp add: move_cap_def)
  apply (wp swap_parents_wp)
   apply (rule hoare_strengthen_post)
    apply (rule set_cap_wp)
   apply (sep_select 2)
   apply (sep_solve)
  apply (rule hoare_chain)
    apply (rule insert_cap_orphan_wp)
   apply (sep_solve)
  apply (sep_solve)
done

lemma invoke_cnode_rotate2_wp_old:
  "(dest) \<noteq> (rnd) \<Longrightarrow>
  \<lbrace><dest \<mapsto>c cap1 \<and>* src \<mapsto>c cap2 \<and>*
    rnd \<mapsto>c - \<and>* R>\<rbrace>
     invoke_cnode (RotateCall cap1 cap2 dest src rnd)
  \<lbrace>\<lambda>_. <dest \<mapsto>c NullCap \<and>* src \<mapsto>c cap1 \<and>*
    rnd \<mapsto>c cap2 \<and>* R>\<rbrace>"
  including no_pre
  apply (clarsimp simp: invoke_cnode_def)
  apply (wp)
   apply (rule hoare_strengthen_post)
    apply (rule move_cap_wp)
   apply (sep_solve )
  apply (rule hoare_chain)
    apply (rule move_cap_wp)
   apply (sep_select_asm 2, sep_select_asm 3)
   apply (sep_solve)
  apply (sep_solve)
done

(* new sep_select/asm *)

lemma "(A \<and>* B \<and>* C \<and>* D) s  \<Longrightarrow>  (A \<and>* B \<and>* C \<and>* D) s"
  apply (sep_select 4 3 2 1)
  apply (sep_select_asm 4 3 2 1)
  apply (sep_select_asm 2 4)
oops


(* sep_select_pre/post *)

lemma "\<lbrace>A \<and>* B \<and>* C \<and>* D\<rbrace> f \<lbrace>\<lambda>_. A \<and>* B \<and>* C \<and>* D\<rbrace>"
  apply (sep_select_pre 4 1 2 3)
  apply (sep_select_post 3 4 2 1)
  apply (sep_select_post 3 4)
oops

(* can be made to work for arbitrary monads *)

lemma "\<lbrace>A \<and>* B \<and>* C \<and>* D\<rbrace> f \<lbrace>\<lambda>_. A \<and>* B \<and>* C \<and>* D\<rbrace>, \<lbrace>E\<rbrace>"
  apply (sep_select_pre 4 1 2 3)
  apply (sep_select_post 3 4 2 1)
  apply (sep_select_post 3 4)
oops

lemma "\<lbrace>A \<and>* B \<and>* C \<and>* D\<rbrace> f \<lbrace>\<lambda>_. A \<and>* B \<and>* C \<and>* D\<rbrace>, -"
  apply (sep_select_pre 4 1 2 3)
  apply (sep_select_post 3 4 2 1)
  apply (sep_select_post 3 4)
oops

lemma "(P \<and>* (P \<longrightarrow>* Q)) s \<Longrightarrow> Q s"
  apply (sep_mp, assumption )
  done

lemma "P s \<Longrightarrow> (Q \<longrightarrow>* (P \<and>* Q)) s"
  apply (erule sep_curry[rotated])
  apply (assumption)
  done


(* wp tactic testing *)


(* sep_wand approach *)

method_setup debug = \<open>
  Attrib.thms >> (fn _ => fn ctxt =>
   let
     val wp_pre_tac = SELECT_GOAL (NO_CONTEXT_TACTIC ctxt
                      (Method_Closure.apply_method ctxt @{method wp_pre} [] [] [] ctxt []))
   in
     SIMPLE_METHOD' (CHANGED o wp_pre_tac)
   end
)
\<close>

lemma move_cap_wp2:
 "\<lbrace><dest \<mapsto>c - \<and>* src \<mapsto>c cap \<and>* R>\<rbrace>
    move_cap cap' src dest
  \<lbrace>\<lambda>_. <dest \<mapsto>c cap'  \<and>* src \<mapsto>c NullCap \<and>* R>\<rbrace>"
  apply (simp add: move_cap_def)
  apply (sep_wp set_cap_wp swap_parents_wp insert_cap_orphan_wp)+
  apply (sep_solve)
  done

lemma swap_cap_wp2:
  "\<lbrace><dest \<mapsto>c cap \<and>*  src \<mapsto>c cap' \<and>* R>\<rbrace>
    swap_cap cap' src cap dest
   \<lbrace>\<lambda>_.<dest \<mapsto>c cap' \<and>* src \<mapsto>c cap \<and>* R>\<rbrace>"
  apply (clarsimp simp: swap_cap_def)
  apply (sep_wp swap_parents_wp set_cap_wp)+
  apply (sep_solve)
  done

lemma invoke_cnode_rotate2_wp:
  "(dest) \<noteq> (rnd) \<Longrightarrow>
  \<lbrace><dest \<mapsto>c cap1 \<and>* src \<mapsto>c cap2 \<and>*
    rnd \<mapsto>c - \<and>* R>\<rbrace>
     invoke_cnode (RotateCall cap1 cap2 dest src rnd)
  \<lbrace>\<lambda>_. <dest \<mapsto>c NullCap \<and>* src \<mapsto>c cap1 \<and>*
    rnd \<mapsto>c cap2 \<and>* R>\<rbrace>"
  apply (clarsimp simp: invoke_cnode_def)
  apply (sep_wp move_cap_wp)+
  apply (sep_solve)
  done


(* sep_drule/rule *)

lemma sep_rule_example2:
 "\<lbrakk>(ptr \<mapsto>o obj) s; finite (dom (object_slots obj))\<rbrakk> \<Longrightarrow>
   (ptr \<mapsto>E obj \<and>* ptr \<mapsto>f obj \<and>* (\<And>* slot\<in>dom (object_slots obj). (ptr, slot) \<mapsto>s obj)) s"
  apply (subst (asm) sep_map_o_decomp)
  apply (subst (asm) sep_map_S_decomp, simp+)
  apply sep_solve
  done

lemma sep_drule_example2:
 "\<lbrakk>(ptr \<mapsto>f obj \<and>* (\<And>* slot\<in>dom (object_slots obj). (ptr, slot) \<mapsto>s obj) \<and>* ptr \<mapsto>E obj) s;
   finite (dom (object_slots obj))\<rbrakk>
    \<Longrightarrow>
  (ptr \<mapsto>o obj) s"
  by (metis sep_map_S_decomp sep_map_o_decomp)

(* sep_curry *)

lemma sep_drule_example_lemma:
  "\<lbrakk>(H \<and>* Z \<and>* J \<and>* L \<and>* Y \<and>* ptr \<mapsto>f obj \<and>* A \<and>* B \<and>*
    (\<And>* slot\<in>dom (object_slots obj). (ptr, slot) \<mapsto>s obj) \<and>* D \<and>* G \<and>* E \<and>* F \<and>* ptr \<mapsto>E obj ) s;
    finite (dom (object_slots obj))\<rbrakk>
  \<Longrightarrow>
   (D \<and>* G \<and>* E \<and>* F  \<and>* ptr \<mapsto>o obj \<and>* H \<and>* Z \<and>* J \<and>* L \<and>* Y \<and>* A \<and>* B) s"
  apply (sep_drule sep_drule_example2)
   apply assumption
  apply sep_solve
  done


(* sep_back *)


lemma sep_rule_example_lemma:
 "\<lbrakk>(H \<and>* Z \<and>* J \<and>* L \<and>* Y \<and>* ptr \<mapsto>o obj \<and>* A \<and>* B \<and>* D \<and>* G \<and>* E \<and>* F ) s;
  finite (dom (object_slots obj))\<rbrakk> \<Longrightarrow>
  (D \<and>* G \<and>* E \<and>* F  \<and>* ptr \<mapsto>f obj \<and>* H \<and>* Z \<and>* J \<and>* L \<and>* Y \<and>* ptr \<mapsto>E obj \<and>*
   A \<and>* B \<and>* (\<And>* slot\<in>dom (object_slots obj). (ptr, slot) \<mapsto>s obj)) s"
  apply (sep_rule sep_rule_example2)
   apply sep_solve
  apply assumption
  done


(* works even with multiple conjuncts in assumptions and conclusions *)
lemma sep_rule_double_conjunct_example:
  "\<lbrakk>((obj_id, slot) \<mapsto>c cap \<and>* obj_id \<mapsto>f obj) s;
    object_slots obj slot = Some cap\<rbrakk>
  \<Longrightarrow> ((obj_id, slot) \<mapsto>s obj \<and>* obj_id \<mapsto>f obj) s"
  apply (sep_drule sep_map_s_sep_map_c)
   apply assumption
  apply (sep_cancel)+
  done

lemma sep_rule_double_conjunct_lemma:
  "\<lbrakk>(H \<and>* Z \<and>* J \<and>* L \<and>* Y \<and>* obj_id \<mapsto>f obj \<and>* A \<and>* B \<and>* D \<and>* G \<and>* E \<and>* F \<and>* (obj_id, slot) \<mapsto>c cap ) s;
    object_slots obj slot = Some cap\<rbrakk> \<Longrightarrow>
   (D \<and>* G \<and>* E \<and>* F  \<and>*(obj_id, slot) \<mapsto>s obj \<and>* H \<and>* Z \<and>* J \<and>* L \<and>* Y \<and>* A \<and>* B \<and>*  obj_id \<mapsto>f obj) s"
  apply (sep_rule sep_rule_double_conjunct_example)
   apply sep_solve
  apply assumption
  done

(* side-conditions*)


lemma sep_drule_side_condition_lemma:
 "\<lbrakk>(H \<and>* Z \<and>* J \<and>* L \<and>* Y \<and>* obj_id \<mapsto>f obj \<and>* A \<and>* B \<and>* D \<and>* G \<and>* E \<and>* F \<and>* (obj_id, slot) \<mapsto>c cap ) s;
    object_slots obj slot = Some cap\<rbrakk> \<Longrightarrow>
   (D \<and>* G \<and>* E \<and>* F  \<and>*(obj_id, slot) \<mapsto>s obj \<and>* H \<and>* Z \<and>* J \<and>* L \<and>* Y \<and>* A \<and>* B \<and>*  obj_id \<mapsto>f obj) s"
  apply (sep_drule sep_rule_double_conjunct_example, assumption)
  apply (sep_solve)
  done

schematic_goal "(P \<and>* ?A) s \<Longrightarrow> (A \<and>* B \<and>* P) s"
  apply (sep_solve)
  done


end
