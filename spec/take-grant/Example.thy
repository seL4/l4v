(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Example
imports System_S
begin

definition "id0 \<equiv> 0"
definition  "id1 \<equiv> 1"
definition  "id2 \<equiv> 2"

definition "e0 \<equiv> Entity {\<lparr> target = id1, rights = {Store}\<rparr>}"
definition "e1 \<equiv> Entity {\<lparr> target = id2, rights = {Grant}\<rparr>}"
definition "e2 \<equiv> Entity {}"

lemmas id_defs = id0_def id1_def id2_def
lemmas entity_defs = e0_def e1_def e2_def

definition example_state :: "state" where
"example_state \<equiv> [0 \<mapsto> e0, 1 \<mapsto> e1, 2 \<mapsto> e2] "

lemma de0:
  "direct_caps_of example_state id0 =
   {\<lparr> target = id1, rights = {Store}\<rparr>}"
  by (simp add: direct_caps_of_def example_state_def
                id_defs entity_defs
         split: option.splits)

lemma de1:
  "direct_caps_of example_state id1 =
   {\<lparr> target = id2, rights = {Grant}\<rparr>}"
  by (simp add: direct_caps_of_def example_state_def
                id_defs entity_defs
         split: option.splits)

lemma de2: "direct_caps_of example_state id2 = {}"
  by (simp add: direct_caps_of_def example_state_def
                id_defs entity_defs
         split: option.splits)


lemma scd:
  "store_connected_direct example_state = {(id0,id1)}"
  by (auto simp: store_connected_direct_def direct_caps_of_def
                 example_state_def id_defs entity_defs
          split: if_split_asm option.splits
           cong: conj_cong)

lemma sc:
  "store_connected example_state = {(id0,id1)} \<union> Id"
  apply simp
  apply (rule equalityI)
  apply (insert scd)
   apply (simp add: store_connected_def)
   apply clarsimp
   apply (erule converse_rtranclE)
    apply simp
   apply clarsimp
   apply (erule rtranclE)
    apply simp
   apply clarsimp
  apply (fastforce simp: store_connected_def)
  done

lemma sc': "store_connected example_state = Id \<union> {(0,1)}"
  by (clarsimp simp: sc id_defs)

lemma ce0:
  "caps_of example_state id0 =
   {\<lparr>target = id1, rights = {Store}\<rparr>,
    \<lparr>target = id2, rights = {Grant}\<rparr>}"
  by (fastforce simp: caps_of_def sc Collect_disj_eq de0 de1)

lemma ce1:
  "caps_of example_state id1 =
   {\<lparr> target = id2, rights = {Grant}\<rparr>}"
  apply (clarsimp simp: caps_of_def sc Collect_disj_eq de0 de1)
  apply (simp add: id0_def id1_def)
  done

lemma ce2: "caps_of example_state id2 = {}"
  apply (simp add: caps_of_def sc)
  apply (rule allI)
  apply (rule conjI)
   apply (simp add: id0_def id2_def)
  apply (simp add: de2)
  done

end
