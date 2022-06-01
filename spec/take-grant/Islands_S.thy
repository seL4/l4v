(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Title:   Confinement_S
 * Description: Rephrasing of the confinement proof using the concept of islands.
 *)

theory Islands_S
imports Confine_S
begin

definition
  island :: "state \<Rightarrow> entity_id \<Rightarrow> entity_id set" where
  "island s x \<equiv> {e\<^sub>i. s \<turnstile> x \<leftrightarrow>* e\<^sub>i}"

definition
  island_caps :: "state \<Rightarrow> entity_id \<Rightarrow> cap set" where
  "island_caps s x \<equiv> \<Union>(caps_of s ` island s x)"

lemma island_caps_def2:
  "island_caps s x \<equiv> \<Union> e \<in> island s x. caps_of s e"
  by(simp add: island_caps_def)

lemma island_caps_def3:
  "island_caps s x =  \<Union>(direct_caps_of s ` island s x)"
  apply (clarsimp simp: island_caps_def)
  apply rule
   apply (clarsimp simp: island_def caps_of_def)
   apply (drule store_connected_directly_tgs_connected)
   apply (metis directly_tgs_connected_rtrancl_into_rtrancl)
  apply (fastforce simp: caps_of_def store_connected_def)
  done

lemma island_caps_dom:
  "island_caps s e\<^sub>x \<le>cap c =
  (\<forall>e\<^sub>i. (e\<^sub>x, e\<^sub>i) \<in> tgs_connected s \<longrightarrow> caps_of s e\<^sub>i \<le>cap c)"
  by (auto simp add: island_caps_def caps_dominated_by_def island_def)

lemma authority_confinement_islands:
  "\<lbrakk>s' \<in> execute cmds s;
    island_caps s x \<le>cap c\<rbrakk>
  \<Longrightarrow> island_caps s' x \<le>cap c"
  apply (simp add: island_caps_dom)
  apply clarsimp
  apply (frule (1) tgs_connected_preserved)
  apply (subst (asm) tgs_connected_comm_eq)
  apply (erule authority_confinement)
  apply clarsimp
  apply (erule_tac x=e\<^sub>i' in allE)
  apply (erule impE)
  apply (metis (opaque_lifting, no_types) tgs_connected_comm_eq tgs_connected_def rtrancl_trans)
  apply clarsimp
  done

end
