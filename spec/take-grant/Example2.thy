(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Example2
imports Isolation_S
begin

lemma direct_caps_of_update [simp]:
  "direct_caps_of (s(x := y)) =
  (direct_caps_of s)(x:= case y of None \<Rightarrow> {} | Some (Entity c) \<Rightarrow> c)"
  by (rule ext, simp add: direct_caps_of_def split:option.splits)

lemma direct_caps_of_empty [simp]:
  "direct_caps_of Map.empty = ( \<lambda> x. {})"
  by (simp add: direct_caps_of_def fun_eq_iff)

definition "id\<^sub>0 \<equiv> 0"
definition "id\<^sub>1 \<equiv> 1"
definition "id\<^sub>2 \<equiv> 2"
definition "id\<^sub>3 \<equiv> 3"
definition "id\<^sub>4 \<equiv> 4"
definition "id\<^sub>5 \<equiv> 5"

(* e0 has create caps to all of memory, and full rights to itself. *)
definition
  e0_caps :: "cap set"
where
  "e0_caps \<equiv> range create_cap \<union> {full_cap 0}"

definition
  s0  :: "state"
where
  "s0  \<equiv> [0 \<mapsto> Entity e0_caps]"

definition
  s1  :: "state"
where
  "s1  \<equiv> [0 \<mapsto> Entity (e0_caps \<union> {full_cap 1}),
          1 \<mapsto> null_entity]"

definition
  s2  :: "state" where
  "s2  \<equiv> [0 \<mapsto> Entity (e0_caps \<union> {full_cap 1}),
          1 \<mapsto> Entity {create_cap 2}]"

definition
  s3  :: "state" where
  "s3  \<equiv> [0 \<mapsto> Entity (e0_caps \<union> {full_cap 1}),
          1 \<mapsto> Entity {create_cap 2, \<lparr> target = 1, rights = {Write, Store}\<rparr>}]"

definition
  s4  :: "state" where
  "s4  \<equiv> [0 \<mapsto> Entity (e0_caps \<union> {full_cap 1}),
          1 \<mapsto> Entity {create_cap 2, \<lparr> target = 1, rights = {Write, Store}\<rparr>, full_cap 2},
          2 \<mapsto> null_entity]"

definition
  s5  :: "state" where
  "s5  \<equiv> [0 \<mapsto> Entity (e0_caps \<union> {full_cap 1, write_cap 2}),
          1 \<mapsto> Entity {create_cap 2, \<lparr> target = 1, rights = {Write, Store}\<rparr>, full_cap 2},
          2 \<mapsto> null_entity]"

definition
  s6  :: "state" where
  "s6  \<equiv> [0 \<mapsto> Entity (e0_caps \<union> {full_cap 1, write_cap 2}),
          1 \<mapsto> Entity {create_cap 2, \<lparr> target = 1, rights = {Write, Store}\<rparr>, full_cap 2, read_cap 2},
          2 \<mapsto> null_entity]"

definition
  s7  :: "state" where "s7  \<equiv> s4"

definition
  s8  :: "state" where
  "s8  \<equiv> [0 \<mapsto> Entity (e0_caps \<union> {full_cap 1, full_cap 3}),
          1 \<mapsto> Entity {create_cap 2, \<lparr> target = 1, rights = {Write, Store}\<rparr>, full_cap 2},
          2 \<mapsto> null_entity,
          3 \<mapsto> null_entity]"

definition
  s9  :: "state" where
  "s9  \<equiv> [0 \<mapsto> Entity (e0_caps \<union> {full_cap 1}),
          1 \<mapsto> Entity {create_cap 2, \<lparr> target = 1, rights = {Write, Store}\<rparr>, full_cap 2},
          2 \<mapsto> null_entity,
          3 \<mapsto> null_entity]"

definition
  s10 :: "state" where "s10 \<equiv> s4"

definition
  s   :: "state" where
  "s   \<equiv> [0 \<mapsto> Entity (e0_caps - {create_cap 1, create_cap 2}),
          1 \<mapsto> Entity {create_cap 2, \<lparr> target = 1, rights = {Write, Store}\<rparr>, full_cap 2},
          2 \<mapsto> null_entity]"

definition
  op0  :: "sysOPs" where
  "op0  \<equiv> SysCreate  0 (full_cap 0) (create_cap 1)"
definition
  op1  :: "sysOPs" where
  "op1  \<equiv> SysGrant   0 (full_cap 1) (create_cap 2) UNIV"
definition
  op2  :: "sysOPs" where
  "op2  \<equiv> SysGrant   0 (full_cap 1) (full_cap   1) {Write, Store}"
definition
  op3  :: "sysOPs" where
  "op3  \<equiv> SysCreate  1 \<lparr>target = 1, rights = {Write, Store}\<rparr> (create_cap 2)"
definition
  op4  :: "sysOPs" where
  "op4  \<equiv> SysTake    0 (full_cap 1) (full_cap   2) {Write}"
definition
  op5  :: "sysOPs" where
  "op5  \<equiv> SysCopy    1 \<lparr>target = 1, rights = {Write, Store}\<rparr> (full_cap   2) {Read}"
definition
  op6  :: "sysOPs" where
  "op6  \<equiv> SysRevoke  0 (write_cap 2)"
definition
  op7  :: "sysOPs" where
  "op7  \<equiv> SysCreate  0 (full_cap 0) (create_cap 3)"
definition
  op8  :: "sysOPs" where
  "op8  \<equiv> SysRemove  0 (full_cap 0) (full_cap 3)"
definition
  op9  :: "sysOPs" where
  "op9  \<equiv> SysDestroy  0 (create_cap 3)"
definition
  op10 :: "sysOPs" where
  "op10 \<equiv> SysRemoveSet 0 (full_cap 0) {full_cap 1, create_cap 1, create_cap 2}"

definition ops :: "sysOPs list" where
(* since the CDT isn't defined, op6 is skipped
  "ops \<equiv> [op10, op9, op8, op7, op6, op5, op4, op3, op2, op1, op0]"
*)
  "ops \<equiv> [op10, op9, op8, op7, op3, op2, op1, op0]"


(* is_entity lemmas *)

lemma is_entity_s0_e0 [simp]:
  "is_entity s0 0"
  by (simp add: is_entity_def s0_def)

lemma is_entity_s1_e0 [simp]:
  "is_entity s1 0"
  by (simp add: is_entity_def s1_def)

lemma is_entity_s2_e0 [simp]:
  "is_entity s2 0"
  by (simp add: is_entity_def s2_def)

lemma is_entity_s3_e0 [simp]:
  "is_entity s3 0"
  by (simp add: is_entity_def s3_def)

lemma is_entity_s4_e0 [simp]:
  "is_entity s4 0"
  by (simp add: is_entity_def s4_def)

lemma is_entity_s5_e0 [simp]:
  "is_entity s5 0"
  by (simp add: is_entity_def s5_def)

lemma is_entity_s6_e0 [simp]:
  "is_entity s6 0"
  by (simp add: is_entity_def s6_def)

lemma is_entity_s8_e0 [simp]:
  "is_entity s8 0"
  by (simp add: is_entity_def s8_def)

lemma is_entity_s9_e0 [simp]:
  "is_entity s9 0"
  by (simp add: is_entity_def s9_def)

lemma is_entity_s_e0 [simp]:
  "is_entity s 0"
  by (simp add: is_entity_def s_def)


lemma is_entity_s0_e1 [simp]:
  "\<not> is_entity s0 1"
  by (simp add: is_entity_def s0_def)

lemma is_entity_s1_e1 [simp]:
  "is_entity s1 1"
  by (simp add: is_entity_def s1_def)

lemma is_entity_s2_e1 [simp]:
  "is_entity s2 1"
  by (simp add: is_entity_def s2_def)

lemma is_entity_s3_e1 [simp]:
  "is_entity s3 1"
  by (simp add: is_entity_def s3_def)

lemma is_entity_s4_e1 [simp]:
  "is_entity s4 1"
  by (simp add: is_entity_def s4_def)

lemma is_entity_s5_e1 [simp]:
  "is_entity s5 1"
  by (simp add: is_entity_def s5_def)


lemma is_entity_s3_e2 [simp]:
  "\<not> is_entity s3 2"
  by (simp add: is_entity_def s3_def)

lemma is_entity_s4_e3 [simp]:
  "\<not> is_entity s4 3"
  by (simp add: is_entity_def s4_def)



(* direct_caps_of, caps_of and similar lemmas *)

lemma direct_caps_of_s0_e0_caps [simp]:
  "direct_caps_of s0 0 = e0_caps"
  by (simp add: direct_caps_of_def s0_def e0_caps_def)

lemma direct_caps_of_s1_e0_caps [simp]:
  "direct_caps_of s1 0 = e0_caps \<union> {full_cap 1}"
  by (simp add: direct_caps_of_def s1_def e0_caps_def)

lemma direct_caps_of_s2_e0_caps [simp]:
  "direct_caps_of s2 0 = e0_caps \<union> {full_cap 1}"
  by (simp add: direct_caps_of_def s2_def e0_caps_def)

lemma direct_caps_of_s4_e0_caps [simp]:
  "direct_caps_of s4 0 = e0_caps \<union> {full_cap 1}"
  by (simp add: direct_caps_of_def s4_def e0_caps_def)

lemma direct_caps_of_s5_e0_caps [simp]:
  "direct_caps_of s5 0 = e0_caps \<union> {full_cap 1, write_cap 2}"
  by (simp add: direct_caps_of_def s5_def e0_caps_def)

lemma direct_caps_of_s6_e0_caps [simp]:
  "direct_caps_of s6 0 = e0_caps \<union> {full_cap 1, write_cap 2}"
  by (simp add: direct_caps_of_def s6_def e0_caps_def)

lemma direct_caps_of_s8_e0_caps [simp]:
  "direct_caps_of s8 0 = e0_caps \<union> {full_cap 1, full_cap 3}"
  by (simp add: direct_caps_of_def s8_def e0_caps_def)

lemma direct_caps_of_s9_e0_caps [simp]:
  "direct_caps_of s9 0 = e0_caps \<union> {full_cap 1}"
  by (simp add: direct_caps_of_def s9_def e0_caps_def)


lemma direct_caps_of_s2_e1 [simp]:
  "direct_caps_of s2 1 = {create_cap 2}"
  by (simp add: direct_caps_of_def s2_def)

lemma direct_caps_of_s3_e1 [simp]:
  "direct_caps_of s3 1 = {create_cap 2, \<lparr> target = 1, rights = {Write, Store}\<rparr>}"
  by (simp add: direct_caps_of_def s3_def)

lemma direct_caps_of_s4_e1 [simp]:
  "direct_caps_of s4 1 = {create_cap 2, \<lparr> target = 1, rights = {Write, Store}\<rparr>, full_cap 2}"
  by (simp add: direct_caps_of_def s4_def)

lemma direct_caps_of_s6_e1 [simp]:
  "direct_caps_of s5 1 = {create_cap 2, \<lparr> target = 1, rights = {Write, Store}\<rparr>, full_cap 2}"
  by (simp add: direct_caps_of_def s5_def)

lemma direct_caps_of_s9_e1 [simp]:
  "direct_caps_of s9 1 = {create_cap 2, \<lparr> target = 1, rights = {Write, Store}\<rparr>, full_cap 2}"
  by (simp add: direct_caps_of_def s9_def)


lemma full_cap_e0_caps_in_caps_of_s0_e0_caps [simp]:
  "full_cap 0 \<in> caps_of s0 0"
  by (rule direct_cap_in_cap, simp add: e0_caps_def)

lemma full_cap_e1_in_caps_of_s1_e0_caps [simp]:
  "full_cap 1 \<in> caps_of s1 0"
  by (rule direct_cap_in_cap, simp)

lemma full_cap_e1_in_caps_of_s2_e0_caps [simp]:
  "full_cap 1 \<in> caps_of s2 0"
  by (rule direct_cap_in_cap, simp add: e0_caps_def)

lemma full_cap_e0_caps_in_caps_of_s4_e0_caps [simp]:
  "full_cap 0 \<in> caps_of s4 0"
  by (rule direct_cap_in_cap, simp add: e0_caps_def)

lemma full_cap_e1_in_caps_of_s4_e0_caps [simp]:
  "full_cap 1 \<in> caps_of s4 0"
  by (rule direct_cap_in_cap, simp add: e0_caps_def)

lemma full_cap_e2_in_caps_of_s4_e1 [simp]:
  "full_cap 2 \<in> caps_of s4 1"
  by (rule direct_cap_in_cap, simp)

lemma full_cap_e1_in_caps_of_s5_e0_caps [simp]:
  "full_cap 1 \<in> caps_of s5 0"
  by (rule direct_cap_in_cap, simp add: e0_caps_def)

lemma full_cap_e2_in_caps_of_s5_e0_caps [simp]:
  "full_cap 2 \<in> caps_of s5 1"
  by (rule direct_cap_in_cap, simp)

lemma full_cap_e0_caps_in_caps_of_s8_e0_caps [simp]:
  "full_cap 0 \<in> caps_of s8 0"
  by (rule direct_cap_in_cap, simp add: e0_caps_def)

lemma create_cap_in_caps_of_s0_e0_caps [simp]:
  "create_cap i \<in> caps_of s0 0"
  by (rule direct_cap_in_cap, simp add: e0_caps_def)

lemma create_cap_in_caps_of_s1_e0_caps [simp]:
  "create_cap i \<in> caps_of s1 0"
  by (rule direct_cap_in_cap, simp add: e0_caps_def)

lemma create_cap_in_caps_of_s2_e1 [simp]:
  "create_cap 2 \<in> caps_of s2 1"
  by (rule direct_cap_in_cap, simp)

lemma create_cap_in_caps_of_s3_e1 [simp]:
  "create_cap 2 \<in> caps_of s3 1"
  by (rule direct_cap_in_cap, simp)

lemma create_cap_in_caps_of_s4_e3 [simp]:
  "create_cap 3 \<in> caps_of s4 0"
  by (rule direct_cap_in_cap, simp add: e0_caps_def)

lemma create_cap_in_caps_of_s9_e3 [simp]:
  "create_cap 3 \<in> caps_of s9 0"
  by (rule direct_cap_in_cap, simp add: e0_caps_def)

lemma write_store_e1_in_caps_of_s3_e1 [simp]:
  "\<lparr>target = 1, rights = {Write, Store}\<rparr>  \<in> caps_of s3 1"
  by (rule direct_cap_in_cap, simp)

lemma write_store_e1_in_caps_of_s5_e1 [simp]:
  "\<lparr>target = 1, rights = {Write, Store}\<rparr> \<in> caps_of s5 1"
  by (rule direct_cap_in_cap, simp)

lemma write_cap_e2_in_caps_of_s6_e0_caps [simp]:
  "write_cap 2 \<in> caps_of s6 0"
  by (rule direct_cap_in_cap, simp)



(*********************************)
(*  State after the opeartions   *)
(*********************************)

(* "op0 \<equiv> SysCreate 0 (full_cap 0) (create_cap 1)" *)
lemma op0_legal:
  "legal op0 s0"
  by  (clarsimp simp: op0_def all_rights_def)

lemma execute_op0_safe:
  "step op0 s0 \<subseteq> ({s0, s1})"
  by (fastforce simp: op0_def step_def createOperation_def s0_def s1_def
                 split: if_split_asm)

lemma execute_op0_live:
  "step op0 s0 \<supseteq> ({s0, s1})"
  apply clarsimp
  apply (rule conjI)
   apply (simp add: step_def)
  apply (simp add: step_def op0_legal)
  apply (rule disjI2)
  apply (clarsimp simp: op0_def createOperation_def)
  apply (rule ext)
  apply (clarsimp simp: s0_def s1_def)
  done

lemma execute_op0:
  "step op0 s0 = ({s0, s1})"
  apply rule
   apply (rule execute_op0_safe)
  apply (rule execute_op0_live)
  done


(* "op1 \<equiv> SysGrant  0 (full_cap 1) (create_cap 2) UNIV" *)
lemma op1_legal:
  "legal op1 s1"
  by  (clarsimp simp: op1_def all_rights_def)

lemma execute_op1_safe:
  "step op1 s1 \<subseteq> ({s1, s2})"
  by (clarsimp simp: op1_def step_def grantOperation_def diminish_def
                     s1_def s2_def create_cap_def null_entity_def
              split: if_split_asm)

lemma execute_op1_live:
  "step op1 s1 \<supseteq> ({s1, s2})"
  apply clarsimp
  apply (rule conjI)
   apply (simp add: step_def)
  apply (simp add: step_def op1_legal)
  apply (rule disjI2)
  apply (clarsimp simp: op1_def grantOperation_def)
  apply (rule ext)
  apply (clarsimp simp: s1_def s2_def null_entity_def)
  done

lemma execute_op1:
  "step op1 s1 = ({s1, s2})"
  apply rule
   apply (rule execute_op1_safe)
  apply (rule execute_op1_live)
  done


(* "op2 \<equiv> SysGrant  0 (full_cap 1) (full_cap   1) {Write, Store}" *)
lemma op2_legal:
  "legal op2 s2"
  by  (clarsimp simp: op2_def all_rights_def)

lemma execute_op2_safe:
  "step op2 s2 \<subseteq> ({s2, s3})"
  apply clarsimp
  apply (rule ext)
  apply (auto simp: op2_def step_def grantOperation_def diminish_def s2_def s3_def full_cap_def all_rights_def
             split: if_split_asm)
  done

lemma execute_op2_live:
  "step op2 s2 \<supseteq> ({s2, s3})"
  apply clarsimp
  apply (simp add: step_def op2_legal)
  apply (rule disjI2)
  apply (simp add: op2_def)
  apply (rule ext)
  apply (fastforce simp: s2_def s3_def grantOperation_def diminish_def all_rights_def full_cap_def)
  done

lemma execute_op2:
  "step op2 s2 = ({s2, s3})"
  apply rule
   apply (rule execute_op2_safe)
  apply (rule execute_op2_live)
  done


(* "op3 \<equiv> SysCreate 1 (full_cap 1) (create_cap 2)" *)
lemma op3_legal:
  "legal op3 s3"
  by  (clarsimp simp: op3_def all_rights_def)

lemma execute_op3_safe:
  "step op3 s3 \<subseteq> ({s3, s4})"
  apply (clarsimp, rule ext)
  apply (auto simp: op3_def step_def createOperation_def s3_def s4_def
             split: if_split_asm)
  done

lemma execute_op3_live:
  "step op3 s3 \<supseteq> ({s3, s4})"
  apply clarsimp
  apply (simp add: step_def op3_legal)
  apply (rule disjI2)
  apply (clarsimp simp: op3_def createOperation_def)
  apply (rule ext)
  apply (fastforce simp: s3_def s4_def)
  done

lemma execute_op3:
  "step op3 s3 = ({s3, s4})"
  apply rule
   apply (rule execute_op3_safe)
  apply (rule execute_op3_live)
  done

(* op4 \<equiv> SysTake    0 (full_cap 1) (full_cap   2) {Write} *)
lemma op4_legal:
  "legal op4 s4"
  by  (clarsimp simp: op4_def all_rights_def)

lemma execute_op4_safe:
  "step op4 s4 \<subseteq> ({s4, s5})"
  apply (clarsimp, rule ext)
  apply (auto simp: s4_def s5_def op4_def step_def takeOperation_def
                    diminish_def all_rights_def write_cap_def
             split: if_split_asm)
  done

lemma execute_op4_live:
  "step op4 s4 \<supseteq> ({s4, s5})"
  apply clarsimp
  apply (simp add: op4_legal step_def)
  apply (rule disjI2)
  apply (simp add: op4_def)
  apply (rule ext)
  apply (fastforce simp: s4_def s5_def takeOperation_def diminish_def all_rights_def write_cap_def)
  done

lemma execute_op4:
  "step op4 s4 = ({s4, s5})"
  apply rule
   apply (rule execute_op4_safe)
  apply (rule execute_op4_live)
  done


(* op5  \<equiv> SysCopy    1 (full_cap 1) (full_cap   2) {Read} *)
lemma op5_legal:
  "legal op5 s5"
  by  (clarsimp simp: op5_def all_rights_def)

lemma execute_op5_safe:
  "step op5 s5 \<subseteq> ({s5, s6})"
  apply (clarsimp, rule ext)
  apply (auto simp: s5_def s6_def op5_def step_def copyOperation_def diminish_def all_rights_def read_cap_def
             split: if_split_asm)
  done

lemma execute_op5_live:
  "step op5 s5 \<supseteq> ({s5, s6})"
  apply clarsimp
  apply (simp add: step_def op5_legal)
  apply (rule disjI2)
  apply (simp add: op5_def)
  apply (rule ext)
  apply (fastforce simp: s5_def s6_def copyOperation_def diminish_def all_rights_def read_cap_def)
  done

lemma execute_op5:
  "step op5 s5 = ({s5, s6})"
  apply rule
   apply (rule execute_op5_safe)
  apply (rule execute_op5_live)
  done

(* op6  \<equiv> SysRevoke  0 (read_cap 2) *)
lemma op6_legal:
  "legal op6 s6"
  by  (clarsimp simp: op6_def all_rights_def)

lemma execute_op6_safe:
  "step op6 s6 \<subseteq> ({s6, s7})"
  apply (clarsimp, rule ext)
  apply (auto simp: s6_def s7_def s4_def op7_def step_def revokeOperation_def
          split: if_split_asm)
  oops

lemma execute_op6_live:
  "step op6 s6 \<supseteq> ({s6, s7})"
  apply (insert op6_legal)
  oops (*
  apply (auto simp: step_def op6_legal op6_def s6_def s7_def s4_def revokeOperation_def fun_eq_iff)
  done*)

(* Since cdt is not defined, this proof can't be done *)
lemma execute_op6_live:
  "s7 \<in> step op6 s6"
  oops

lemma execute_op6:
  "step op6 s6 = ({s6, s7})"
  oops


(* op7  \<equiv> SysCreate  0 (full_cap 0) (create_cap 3) *)
lemma op7_legal:
  "legal op7 s7"
  by  (clarsimp simp: s7_def op7_def all_rights_def)

lemma execute_op7_safe:
  "step op7 s7 \<subseteq> ({s7, s8})"
  apply (clarsimp, rule ext)
  apply (auto simp: s7_def s8_def s4_def op7_def step_def createOperation_def
             split: if_split_asm)
  done

lemma execute_op7_live:
  "step op7 s7 \<supseteq> ({s7, s8})"
  apply clarsimp
  apply (simp add: step_def op7_legal)
  apply (rule disjI2)
  apply (simp add: op7_def)
  apply (rule ext)
  apply (fastforce simp: s7_def s8_def s4_def createOperation_def)
  done

lemma execute_op7:
  "step op7 s7 = ({s7, s8})"
  apply rule
   apply (rule execute_op7_safe)
  apply (rule execute_op7_live)
  done


(* op8  \<equiv> SysRemove  0 (full_cap 0) (full_cap 3) *)
lemma op8_legal:
  "legal op8 s8"
  by  (clarsimp simp: op8_def)

lemma execute_op8_safe:
  "step op8 s8 \<subseteq> ({s8, s9})"
  apply clarsimp
  apply (rule ext)
  apply (insert op8_legal)
  apply (fastforce simp: step_def op8_def s8_def s9_def removeOperation_def
                        full_cap_def create_cap_def all_rights_def e0_caps_def)
  done

lemma execute_op8_live:
  "step op8 s8 \<supseteq> ({s8, s9})"
  apply (simp add: step_def op8_legal op8_def)
  apply (rule disjI2)
  apply (rule ext)
  apply (clarsimp simp: removeOperation_def)
  apply (fastforce simp: s8_def s9_def full_cap_def create_cap_def all_rights_def e0_caps_def)
  done

lemma execute_op8:
  "step op8 s8 = ({s8, s9})"
  apply rule
   apply (rule execute_op8_safe)
  apply (rule execute_op8_live)
  done

(* op9  \<equiv> SysDelete  0 (create_cap 3) *)

lemma op9_legal:
  "legal op9 s9"
  apply (simp add: op9_def)
  apply (fastforce simp: s9_def e0_caps_def null_entity_def split:if_split_asm)
  done

lemma execute_op9_safe:
  "step op9 s9 \<subseteq> ({s9, s10})"
  apply (clarsimp, rule ext)
  apply (auto simp: s9_def s10_def s4_def op9_def step_def destroyOperation_def
             split: if_split_asm)
  done

lemma execute_op9_live:
  "step op9 s9 \<supseteq> ({s9, s10})"
  apply (simp add: step_def op9_legal)
  apply (rule disjI2)
  apply (simp add: op9_def)
  apply (rule ext)
  apply (clarsimp simp: destroyOperation_def step_def op9_def s9_def s10_def s4_def)
  done

lemma execute_op9:
  "step op9 s9 = ({s9, s10})"
  apply rule
   apply (rule execute_op9_safe)
  apply (rule execute_op9_live)
  done

(* op10 \<equiv> SysRemoveSet 0 (full_cap 0) {full_cap 1, create_cap 1, create_cap 2} *)
lemma op10_legal:
  "legal op10 s10"
  by  (clarsimp simp: s10_def op10_def all_rights_def)

lemma e0_caps_diminished [simp]:
  "e0_caps - {full_cap 1, create_cap 1, create_cap 2} = e0_caps - {create_cap 1, create_cap 2}"
  by (fastforce simp: e0_caps_def create_cap_def full_cap_def all_rights_def)


lemma execute_op10_safe:
  "step op10 s10 \<subseteq> ({s10, s})"
  apply (clarsimp, rule ext)
  apply (auto simp: s10_def op10_def step_def removeSetOperation_def s4_def s_def
              split: if_split_asm)
  done

lemma execute_op10_live:
  "step op10 s10 \<supseteq> ({s10, s})"
  apply clarsimp
  apply (rule conjI)
   apply (simp add: step_def)
  apply (simp add: step_def op10_legal)
  apply (rule disjI2)
  apply (clarsimp simp: s10_def op10_def removeSetOperation_def)
  apply (rule ext)
  apply (fastforce simp: s4_def s_def)
  done

lemma execute_op10:
  "step op10 s10 = ({s10, s})"
  apply rule
   apply (rule execute_op10_safe)
  apply (rule execute_op10_live)
  done


lemma execute_ops:
  "s \<in> execute ops s0"
  apply (clarsimp simp: ops_def)
  apply (insert execute_op0_live execute_op1_live execute_op2_live execute_op3_live
                execute_op4_live execute_op5_live                  execute_op7_live
                execute_op8_live execute_op9_live execute_op10_live)
  apply (simp add: s7_def)
  apply fastforce
  done



(*********************************)
(* Results about the final state *)
(*********************************)

lemma store_not_in_create_cap [simp]:
  "Store \<notin> rights (create_cap i)"
  by (simp add: create_cap_def)

lemma store_not_in_create_cap2 [simp]:
  "Store \<in> rights c \<Longrightarrow> c \<noteq> create_cap i"
  by (clarsimp simp: create_cap_def)


(*********************************)
(*    store_connected_direct     *)
(*********************************)

lemma store_connected_direct_s_helper1:
  "{c'.(c' = \<lparr>target = 0, rights = UNIV\<rparr> \<or> c' \<in> range create_cap) \<and>
        c' \<noteq> \<lparr>target = 1, rights = {Create}\<rparr> \<and> c' \<noteq> \<lparr>target = 2, rights = {Create}\<rparr> \<and>
        Store \<in> rights c'} = {full_cap 0}"
 by (auto simp: create_cap_def full_cap_def all_rights_def e0_caps_def)

lemma store_connected_direct_s_helper2:
  "{c'. (c' = \<lparr>target = 2, rights = {Create}\<rparr> \<or> c' = \<lparr>target = 1, rights = {Write, Store}\<rparr> \<or>
         c' = \<lparr>target = 2, rights = UNIV\<rparr>)    \<and>  Store \<in> rights c'}
   = {\<lparr>target = 1, rights = {Write, Store}\<rparr>, full_cap 2}"
  by (auto simp: create_cap_def full_cap_def all_rights_def e0_caps_def)


lemma store_connected_direct_s:
  "store_connected_direct s = {(0,0), (1,1), (1,2)}"
  by (fastforce simp: store_connected_direct_def s_def e0_caps_def
                      full_cap_def all_rights_def create_cap_def null_entity_def
                      store_connected_direct_s_helper1 store_connected_direct_s_helper2
               split: if_split_asm)

(*********************************)
(*        store_connected        *)
(*********************************)

lemma into_rtrancl [rule_format]:
  "(a,b) \<in> r^* \<Longrightarrow> (\<forall>x. (x,b) \<in> r \<longrightarrow> x = b) \<longrightarrow> a = b"
  apply (erule converse_rtrancl_induct)
   apply simp
  apply clarsimp
  done

lemma into_rtrancl2 [rule_format]:
  " \<And> B. \<lbrakk>(a,b) \<in> r^*; b \<in> B\<rbrakk> \<Longrightarrow> (\<forall>x.(x,b) \<in> r \<longrightarrow> x \<in> B) \<longrightarrow> a \<in> B"
  thm rtrancl_induct converse_rtrancl_induct
  apply (erule converse_rtrancl_induct)
   apply clarsimp
  apply clarsimp
  oops

lemma store_connected_id:
 "{(0::word32, 0), (1, 1), (1, 2)}\<^sup>* = {(1, 2)}\<^sup>* "
  apply rule
   apply clarsimp
   apply (erule rtranclE)
    apply simp
   apply (fastforce dest: into_rtrancl)
  apply clarsimp
  apply (erule rtranclE)
   apply simp
  apply (fastforce dest: into_rtrancl)
  done

lemma store_connected_s: "store_connected s = {(1,2)} \<union> Id"
  apply simp
  apply (rule equalityI)
  apply (insert store_connected_direct_s)
   apply (simp add: store_connected_def)
   apply clarsimp
   apply (erule converse_rtranclE)
    apply simp
   apply clarsimp
   apply (erule rtranclE)
    apply fastforce
   apply (simp add: store_connected_id)
   apply (drule rtranclD)
   apply (safe, simp_all, (erule tranclE, simp, fastforce)+)
  apply (fastforce simp: store_connected_def)
  done

(*********************************)
(*            caps_of            *)
(*********************************)

lemma caps_of_s_e0_caps: "caps_of s 0 = e0_caps - {create_cap 1, create_cap 2}"
  apply (clarsimp simp: caps_of_def store_connected_s Collect_disj_eq)
  apply (simp add: s_def)
  done

lemma caps_of_s_e0_caps_2: "caps_of s 0 = {full_cap 0} \<union> ( range create_cap - {create_cap 1, create_cap 2})"
  by (fastforce simp: caps_of_s_e0_caps e0_caps_def full_cap_def create_cap_def)


lemma caps_of_s_e1: "caps_of s 1 = {create_cap 2, \<lparr> target = 1, rights = {Write, Store}\<rparr>, full_cap 2}"
  apply (clarsimp simp: caps_of_def store_connected_s Collect_disj_eq)
  apply (simp add: s_def null_entity_def)
  done

lemma caps_of_s_e2: "caps_of s 2 = {}"
  apply (simp add: caps_of_def store_connected_s)
  apply (simp add: s_def null_entity_def)
  done

lemma caps_of_s_e3: "\<lbrakk>e \<noteq> 0; e \<noteq> 1\<rbrakk> \<Longrightarrow> caps_of s e = {}"
  apply (simp add: caps_of_def store_connected_s)
  apply (simp add: s_def null_entity_def)
  done


(*********************************)
(*            caps_of'             *)
(*********************************)

lemma extra_rights_create_cap:
  "extra_rights (create_cap i) = full_cap i"
  by (simp add: create_cap_def full_cap_def extra_rights_def)


lemma extra_rights_full_cap:
  "extra_rights (full_cap i) = full_cap i"
  by (simp add: full_cap_def extra_rights_def)

lemma extra_rights_take_cap:
  "extra_rights (take_cap i) = take_cap i"
  by (simp add: take_cap_def extra_rights_def)

lemma extra_rights_grant_cap:
  "extra_rights (grant_cap i) = grant_cap i"
  by (simp add: take_cap_def extra_rights_def)

lemma caps_of'_s_e0_caps_helper:
  "extra_rights ` (range create_cap - {create_cap 1, create_cap 2}) =
  range full_cap - {full_cap 1, full_cap 2}"
  apply rule
   apply (fastforce simp: create_cap_def extra_rights_def all_rights_def full_cap_def)
  apply rule
  apply (erule DiffE)
  apply clarsimp
  apply (rule image_eqI)
   apply (rule extra_rights_create_cap [THEN sym])
  apply (simp add: full_cap_def create_cap_def)
  done



(*********************************)
(*          connected            *)
(*********************************)

lemma extra_rights_increases_rights:
  "rights c \<subseteq> rights (extra_rights c)"
  by (simp add: extra_rights_def all_rights_def)

lemma cap_in_caps_take_cap:
  "\<lbrakk>create_cap x \<in> caps_of s y\<rbrakk> \<Longrightarrow> take_cap x \<in>cap caps_of s y"
  apply (auto simp: cap_in_caps_def caps_of_def extra_rights_take_cap)
  apply (rule exI, rule conjI, assumption)
  apply (rule rev_bexI, simp)
  apply (rule conjI)
   apply (subgoal_tac "target (full_cap x) = x", simp+)
  apply (simp add: extra_rights_create_cap all_rights_def)
  done


lemma e0_connected_to:
  "\<lbrakk>x \<noteq> 1; x \<noteq> 2\<rbrakk> \<Longrightarrow> s \<turnstile> 0 \<leftrightarrow> x"
  apply (rule directly_tgs_connected_comm)
  apply (simp add: directly_tgs_connected_def4)
  apply (rule disjI1)
  apply (rule cap_in_caps_take_cap)
  apply (simp add: caps_of_s_e0_caps e0_caps_def create_cap_def)
  done

lemma e1_connected_to_e2:
  "s \<turnstile> 1 \<leftrightarrow> 2"
  apply (simp add: directly_tgs_connected_def4)
  apply (rule disjI2)+
  apply (simp add: shares_caps_def)
  apply (simp add: store_connected_s)
  done

lemma e0_caps_not_connected_to_e1:
  "\<not> (s \<turnstile> 0 \<leftrightarrow> 1)"
  apply (simp add: directly_tgs_connected_def4)
  apply (rule conjI)
   apply (simp add: cap_in_caps_def caps_of_s_e1)
  apply (rule conjI)
   apply (clarsimp simp add: cap_in_caps_def caps_of_s_e0_caps e0_caps_def)
   apply (erule disjE)
    apply (simp add: full_cap_def)
   apply clarsimp
  apply (rule conjI)
     apply (clarsimp simp add: cap_in_caps_def caps_of_s_e0_caps e0_caps_def)
   apply (erule disjE)
    apply (simp add: full_cap_def)
   apply clarsimp
  apply (rule conjI)
   apply (simp add: cap_in_caps_def caps_of_s_e1)
  apply (simp add: shares_caps_def)
  apply (simp add: store_connected_s)
  done

lemma e0_caps_not_connected_to_e2:
  "\<not> (s \<turnstile> 0 \<leftrightarrow> 2)"
  apply (simp add: directly_tgs_connected_def4)
  apply (rule conjI)
   apply (simp add: cap_in_caps_def caps_of_s_e2)
  apply (rule conjI)
   apply (clarsimp simp add: cap_in_caps_def caps_of_s_e0_caps e0_caps_def)
   apply (erule disjE)
    apply (simp add: full_cap_def)
   apply clarsimp
  apply (rule conjI)
     apply (clarsimp simp add: cap_in_caps_def caps_of_s_e0_caps e0_caps_def)
   apply (erule disjE)
    apply (simp add: full_cap_def)
   apply clarsimp
  apply (rule conjI)
   apply (simp add: cap_in_caps_def caps_of_s_e2)
  apply (simp add: shares_caps_def)
  apply (simp add: store_connected_s)
  done




(*********************************)
(*       connected_trans         *)
(*********************************)


lemma e1_connected_trans_to_e2:
  "s \<turnstile> 1 \<leftrightarrow>* 2"
  apply (insert e1_connected_to_e2)
  apply (simp add: tgs_connected_def)
  done


lemma caps_of_to_e1:
  "\<lbrakk>c \<in> caps_of s x; target c = 1\<rbrakk> \<Longrightarrow> x = 1 \<or> x = 2"
  apply (case_tac "x = 0")
   apply (fastforce simp: caps_of_s_e0_caps_2)
  apply (case_tac "x = 1")
   apply (fastforce simp: caps_of_s_e1)
  apply (fastforce simp: caps_of_s_e3)
  done

lemma caps_of_to_e2:
  "\<lbrakk>c \<in> caps_of s x; target c = 2\<rbrakk> \<Longrightarrow> x = 1"
  apply (case_tac "x = 0")
   apply (fastforce simp: caps_of_s_e0_caps_2)
  apply (case_tac "x = 1")
   apply (fastforce simp: caps_of_s_e1)
  apply (fastforce simp: caps_of_s_e3)
  done

lemma cap_in_caps_caps_of_e1:
  "c \<in>cap caps_of s 1 \<Longrightarrow> target c = 1 \<or> target c = 2"
  by (clarsimp simp: cap_in_caps_def caps_of_s_e1)

lemma cap_in_caps_caps_of_e2:
  "c \<in>cap caps_of s 2 \<Longrightarrow> False"
  by (clarsimp simp: cap_in_caps_def caps_of_s_e2)

lemma cap_in_caps_caps_of_to_e1:
  "\<lbrakk>c \<in>cap caps_of s x; target c = 1\<rbrakk> \<Longrightarrow> x = 1 \<or> x = 2"
  apply (clarsimp simp: cap_in_caps_def)
  apply (drule (1) caps_of_to_e1, simp)
  done

lemma cap_in_caps_caps_of_to_e2:
  "\<lbrakk>c \<in>cap caps_of s x; target c = 2\<rbrakk> \<Longrightarrow> x = 1"
  apply (clarsimp simp: cap_in_caps_def)
  apply (erule (1) caps_of_to_e2)
  done

lemma e1_connected_to:
  "s \<turnstile> 1 \<leftrightarrow> x \<Longrightarrow> x = 1 \<or> x = 2"
  apply (simp add: directly_tgs_connected_def4)
  apply (erule disjE)
   apply (erule cap_in_caps_caps_of_to_e1, simp)
  apply (erule disjE)
   apply (drule cap_in_caps_caps_of_e1, simp)
  apply (erule disjE)
   apply (drule cap_in_caps_caps_of_e1, simp)
  apply (erule disjE)
   apply (erule cap_in_caps_caps_of_to_e1, simp)
  apply (fastforce simp: shares_caps_def store_connected_s)
  done


lemma e2_connected_to:
  "s \<turnstile> 2 \<leftrightarrow> x \<Longrightarrow> x = 1 \<or> x = 2"
  apply (simp add: directly_tgs_connected_def4)
  apply (erule disjE, rule disjI1)
   apply (erule cap_in_caps_caps_of_to_e2, simp)
  apply (erule disjE, rule disjI1)
   apply (drule cap_in_caps_caps_of_e2, simp)
  apply (erule disjE, rule disjI1)
   apply (drule cap_in_caps_caps_of_e2, simp)
  apply (erule disjE, rule disjI1)
   apply (erule cap_in_caps_caps_of_to_e2, simp)
  apply (clarsimp simp: shares_caps_def store_connected_s)
  done


lemma directly_tgs_connected_in_inv_image:
  "(directly_tgs_connected s) \<subseteq> inv_image Id (\<lambda> x. x=1 \<or> x=2)"
  by (fastforce simp: inv_image_def
              dest!: e1_connected_to e1_connected_to [OF directly_tgs_connected_comm]
                     e2_connected_to e2_connected_to [OF directly_tgs_connected_comm])

lemma connected_inv_image_trans:
  "trans (inv_image Id (\<lambda> x. x=1 \<or> x=2))"
  by (rule trans_inv_image [OF trans_Id])

lemma eq_inv_image_connected:
  "(inv_image Id (\<lambda> x. x=1 \<or> x=2))\<^sup>= = inv_image Id (\<lambda> x. x=1 \<or> x=2)"
  by (fastforce simp: inv_image_def)

lemma rtrancl_inv_image_connected:
  "(inv_image Id (\<lambda> x. x=1 \<or> x=2))\<^sup>* = inv_image Id (\<lambda> x. x=1 \<or> x=2)"
  apply (subst trancl_reflcl [symmetric])
  apply (subst eq_inv_image_connected)
  apply (rule trancl_id)
  apply (rule connected_inv_image_trans)
  done

lemma tgs_connected_in_inv_image:
  "(tgs_connected s) \<subseteq> inv_image Id (\<lambda> x. x=1 \<or> x=2)"
  apply (simp add: tgs_connected_def)
  apply (subst rtrancl_inv_image_connected [symmetric])
  apply (rule rtrancl_mono)
  apply (rule directly_tgs_connected_in_inv_image)
  done

lemma e0_not_connected_trans_e1:
  "\<not> s \<turnstile> 0 \<leftrightarrow>* 1"
  apply clarsimp
  apply (drule set_mp [OF tgs_connected_in_inv_image])
  apply (simp add: inv_image_def)
  done

lemma e0_not_ever_connected_trans_e1:
  "s' \<in> execute cmds s \<Longrightarrow> \<not> s' \<turnstile> 0 \<leftrightarrow>* 1"
  apply clarsimp
  apply (drule (1) tgs_connected_preserved)
  apply (simp add: e0_not_connected_trans_e1)
  done


lemma e0_e1_leakage:
  "s' \<in> execute cmds s \<Longrightarrow> \<not> leak s' 0 1"
  apply (insert e0_not_connected_trans_e1)
  apply (drule (2) leakage_rule)
  done





(*********************************)
(*         islandtems            *)
(*********************************)
lemma island_e0:
  "island s 0 = {i. i \<noteq> 1 \<and> i \<noteq> 2}"
  apply rule
   apply (clarsimp simp: island_def)
   apply (insert tgs_connected_in_inv_image)[1]
   apply fastforce
  apply (clarsimp simp: island_def)
  apply (drule (1) e0_connected_to)
  apply (drule directly_tgs_connected_comm)
  by (metis directly_tgs_connected_def2 tgs_connected_comm leakImplyConnectedTrans)

lemma island_e1:
  "island s 1 = {1,2}"
  apply rule
   apply (clarsimp simp: island_def)
   apply (insert tgs_connected_in_inv_image)[1]
   apply fastforce
  apply (clarsimp simp: island_def)
  apply (rule e1_connected_trans_to_e2)
  done

lemma island_e2:
  "island s 2 = {1,2}"
  apply rule
   apply (clarsimp simp: island_def)
   apply (insert tgs_connected_in_inv_image)[1]
   apply fastforce
  apply (clarsimp simp: island_def)
  apply (rule e1_connected_trans_to_e2  [THEN tgs_connected_comm])
  done

lemma island_e3:
  "\<lbrakk>x \<noteq> 1; x \<noteq> 2\<rbrakk> \<Longrightarrow> island s x =  {i. i \<noteq> 1 \<and> i \<noteq> 2}"
  apply rule
   apply (clarsimp simp: island_def)
   apply (insert tgs_connected_in_inv_image)[1]
   apply fastforce
  apply (clarsimp simp: island_def)
  apply (frule_tac x=x  in e0_connected_to, simp)
  apply (frule_tac x=xa in e0_connected_to, simp)
  apply (drule_tac x=0 and y=xa in directly_tgs_connected_comm)
  apply (rule tgs_connected_comm)
  apply (simp add: tgs_connected_def)
  done


(*********************************)
(*          isolation            *)
(*********************************)

lemma e1_flow_to:
  "s \<turnstile> 1 \<leadsto> x \<Longrightarrow> x = 1 \<or> x = 2"
  apply (rule ccontr)
  apply (clarsimp simp: flow_def set_flow_def island_e1 island_e3)
  apply (erule disjE, clarsimp)
   apply (erule disjE)
    apply (drule cap_in_caps_caps_of_to_e1, clarsimp+)
   apply (drule cap_in_caps_caps_of_e1, clarsimp+)
  apply (erule disjE)
   apply (drule cap_in_caps_caps_of_to_e2, clarsimp+)
  apply (drule cap_in_caps_caps_of_e2, clarsimp+)
  done

lemma e2_flow_to:
  "s \<turnstile> 2 \<leadsto> x \<Longrightarrow> x = 1 \<or> x = 2"
  apply (rule ccontr)
  apply (clarsimp simp: flow_def set_flow_def island_e2 island_e3)
  apply (erule disjE, clarsimp)
   apply (erule disjE)
    apply (drule cap_in_caps_caps_of_to_e1, clarsimp+)
   apply (drule cap_in_caps_caps_of_e1, clarsimp+)
  apply (erule disjE)
   apply (drule cap_in_caps_caps_of_to_e2, clarsimp+)
  apply (drule cap_in_caps_caps_of_e2, clarsimp+)
  done

lemma flow_to_e1:
  "s \<turnstile> x \<leadsto> 1 \<Longrightarrow> x = 1 \<or> x = 2"
  apply (rule ccontr)
  apply (clarsimp simp: flow_def set_flow_def island_e1 island_e3)
  apply (erule disjE)
   apply (drule cap_in_caps_caps_of_e1, clarsimp+)
  apply (erule disjE)
   apply (drule cap_in_caps_caps_of_to_e1, clarsimp+)
  apply (erule disjE)
   apply (drule cap_in_caps_caps_of_e2, clarsimp+)
  apply (drule cap_in_caps_caps_of_to_e2, clarsimp+)
  done

lemma flow_to_e2:
  "s \<turnstile> x \<leadsto> 2 \<Longrightarrow> x = 1 \<or> x = 2"
  apply (rule ccontr)
  apply (clarsimp simp: flow_def set_flow_def island_e2 island_e3)
  apply (erule disjE)
   apply (drule cap_in_caps_caps_of_e1, clarsimp+)
  apply (erule disjE)
   apply (drule cap_in_caps_caps_of_to_e1, clarsimp+)
  apply (erule disjE)
   apply (drule cap_in_caps_caps_of_e2, clarsimp+)
  apply (drule cap_in_caps_caps_of_to_e2, clarsimp+)
  done


lemma flow_in_inv_image:
  "(flow s) \<subseteq> inv_image Id (\<lambda> x. x=1 \<or> x=2)"
  by (fastforce simp: inv_image_def
              dest!: e1_flow_to flow_to_e1
                     e2_flow_to flow_to_e2)


lemma flow_trans_in_inv_image:
  "(flow_trans s) \<subseteq> inv_image Id (\<lambda> x. x=1 \<or> x=2)"
  apply (simp add: flow_trans_def)
  apply (subst rtrancl_inv_image_connected [symmetric])
  apply (rule rtrancl_mono)
  apply (rule flow_in_inv_image)
  done

lemma e0_not_flow_trans_e1:
  "\<not> s \<turnstile> 0 \<leadsto>* 1"
  apply clarsimp
  apply (drule set_mp [OF flow_trans_in_inv_image])
  apply (simp add: inv_image_def)
  done

lemma e1_not_flow_trans_e0:
  "\<not> s \<turnstile> 1 \<leadsto>* 0"
  apply clarsimp
  apply (drule set_mp [OF flow_trans_in_inv_image])
  apply (simp add: inv_image_def)
  done

lemma e0_e1_isolated:
  "s' \<in> execute cmds s \<Longrightarrow> \<not> s' \<turnstile> 0 \<leadsto>* 1 \<and> \<not> s' \<turnstile> 1 \<leadsto>* 0"
  apply (rule conjI)
   apply (erule information_flow)
   apply (rule e0_not_flow_trans_e1)
  apply (erule information_flow)
  apply (rule e1_not_flow_trans_e0)
  done

end
