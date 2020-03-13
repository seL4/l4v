(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Title:   System_S
 * Description: High-level security model of the kernel.
 *)

(*
  Naming conventions:
  - Names of sets end with an `s'.
    Hence `rights', `caps', `states'.
    Try to avoid other names that end in `s'.
 *)

theory System_S
imports "Word_Lib.WordSetup"
begin

(* System entities: Definition of entities that constitute the system
 *)

type_synonym entity_id = word32 (* kernel objects - identified by a UID *)

datatype
  right = Read      (* Authorise reading of information *)
         | Write    (* Authorise writing of information *)
         | Take     (* Having sufficient authority to take a capability from another entity *)
         | Grant    (* Having sufficient authority to propagate a capability to another entity *)
         | Create   (* Confers the authority to create new entities *)
         | Store    (* Simulates CNodeCap - get caps of said entity *)

record cap =
  target :: entity_id      (* The entity over which it has control *)
  rights :: "right set"    (* The control it has over that entity  *)

datatype entity = Entity "cap set"
declare entity.splits [split]

type_synonym state = "entity_id \<Rightarrow> entity option"

type_synonym modify_state   = "state \<Rightarrow> state"
type_synonym modify_state_n = "state \<Rightarrow> state set"
type_synonym mask = "right set"

definition
  null_entity :: "entity" where
  "null_entity \<equiv> Entity {}"

definition
  all_rights :: "right set" where
  "all_rights \<equiv> UNIV"

lemma all_rights_def2:
  "all_rights = {Read, Write, Take, Grant, Create, Store}"
  apply (clarsimp simp: all_rights_def, rule, simp_all, rule, simp)
  apply (metis right.exhaust)
  done

definition
  entity_ids :: "state \<Rightarrow> entity_id set" where
  "entity_ids s \<equiv> dom s"

definition
  is_entity :: "state \<Rightarrow> entity_id \<Rightarrow> bool" where
  "is_entity s e \<equiv> s e \<noteq> None"

definition
  exist :: "state \<Rightarrow> cap \<Rightarrow> bool" where
  "exist s c \<equiv> is_entity s (target c)"

(* Manipulating entities. *)
definition
  direct_caps :: "entity \<Rightarrow> cap set"
where
  "direct_caps e \<equiv> case e of (Entity c) \<Rightarrow> c"

definition
  direct_caps_of :: "state \<Rightarrow> entity_id \<Rightarrow> cap set"
where
  "direct_caps_of s p \<equiv>
  case s p of
    None \<Rightarrow> {}
  | Some (Entity e) \<Rightarrow> e"

definition
  store_connected_direct :: "state \<Rightarrow> (entity_id \<times> entity_id) set" where
  "store_connected_direct s \<equiv> {(e\<^sub>x, e\<^sub>y). \<exists>cap. cap \<in> direct_caps_of s e\<^sub>x \<and>
                                               Store \<in> rights cap \<and>
                                               target cap = e\<^sub>y}"

definition
  store_connected :: "state \<Rightarrow> (entity_id \<times> entity_id) set" where
  "store_connected s \<equiv> (store_connected_direct s)^*"

definition
  (* returns all capabilities an entity has access to
    (via store or directly) *)
  caps_of :: "state \<Rightarrow> entity_id \<Rightarrow> cap set" where
  "caps_of s e  \<equiv> \<Union>(direct_caps_of s ` {e' . (e,e') \<in> store_connected s})"

lemma caps_rel:
  "caps_of s e = \<Union>(direct_caps_of s ` store_connected s `` {e})"
  by (simp add: caps_of_def Image_def)

definition  (* All the different capabilities of the system *)
  all_caps_of :: "state \<Rightarrow> cap set" where
  "all_caps_of s \<equiv> \<Union>e. direct_caps_of s e"

definition
  read_cap :: "entity_id \<Rightarrow> cap" where
  "read_cap e\<^sub>x \<equiv> \<lparr>target = e\<^sub>x, rights = {Read}\<rparr>"

definition
  write_cap :: "entity_id \<Rightarrow> cap" where
  "write_cap e\<^sub>x \<equiv> \<lparr>target = e\<^sub>x, rights = {Write}\<rparr>"

definition
  take_cap :: "entity_id \<Rightarrow> cap" where
  "take_cap e\<^sub>x \<equiv> \<lparr>target = e\<^sub>x, rights = {Take}\<rparr>"

definition
  grant_cap :: "entity_id \<Rightarrow> cap" where
  "grant_cap e\<^sub>x \<equiv> \<lparr>target = e\<^sub>x, rights = {Grant}\<rparr>"

definition
  create_cap :: "entity_id \<Rightarrow> cap" where
  "create_cap e\<^sub>x \<equiv> \<lparr>target = e\<^sub>x, rights = {Create}\<rparr>"

definition
  store_cap :: "entity_id \<Rightarrow> cap" where
  "store_cap e \<equiv> \<lparr>target = e, rights = {Store}\<rparr>"

definition
  full_cap :: "entity_id \<Rightarrow> cap" where
  "full_cap e \<equiv> \<lparr>target = e, rights = all_rights \<rparr>"



(* System operations: primitive kernel operations *)

datatype sysOPs =
    SysCreate entity_id cap cap
  | SysTake   entity_id cap cap mask
  | SysGrant  entity_id cap cap mask
  | SysCopy   entity_id cap cap mask
  | SysRemove entity_id cap cap
  | SysRemoveSet entity_id cap "cap set"
  | SysRevoke entity_id cap
  | SysDestroy entity_id cap


(* determine if an operation is allowed in the given state_s *)
primrec
  legal :: "sysOPs \<Rightarrow> state \<Rightarrow> bool"
where
  "legal (SysCreate e c\<^sub>1 c\<^sub>2) s = (is_entity s e \<and> is_entity s (target c\<^sub>1) \<and> \<not> (is_entity s (target c\<^sub>2)) \<and>
                                   {c\<^sub>1, c\<^sub>2} \<subseteq> caps_of s e \<and>
                                   Write \<in> rights c\<^sub>1 \<and> Store \<in> rights c\<^sub>1 \<and> Create \<in> rights c\<^sub>2)"

| "legal (SysTake  e c\<^sub>1 c\<^sub>2 r) s = (is_entity s e \<and>  is_entity s (target c\<^sub>1) \<and>
                                  c\<^sub>1 \<in> caps_of s e \<and> c\<^sub>2 \<in> caps_of s (target c\<^sub>1) \<and> Take \<in> rights c\<^sub>1)"

| "legal (SysGrant e c\<^sub>1 c\<^sub>2 r) s = (is_entity s e \<and>  is_entity s (target c\<^sub>1) \<and>
                                  {c\<^sub>1,c\<^sub>2} \<subseteq> caps_of s e \<and> Grant \<in> rights c\<^sub>1)"

| "legal (SysCopy  e c\<^sub>1 c\<^sub>2 r) s   = (is_entity s e \<and>  is_entity s (target c\<^sub>1) \<and>
                                  {c\<^sub>1,c\<^sub>2} \<subseteq> caps_of s e \<and> Store \<in> rights c\<^sub>1)"

| "legal (SysRemove e c\<^sub>1 c\<^sub>2) s = (is_entity s e \<and> c\<^sub>1 \<in> caps_of s e)"

| "legal (SysRemoveSet e c C) s = (is_entity s e \<and> c \<in> caps_of s e)"

| "legal (SysRevoke e c) s = (is_entity s e \<and> c \<in> caps_of s e)"

| "legal (SysDestroy e c) s = (is_entity s e \<and> c \<in> caps_of s e \<and> {Create} = rights c \<and>
                              target c \<notin> target ` (all_caps_of s - {c}))"

(* Following functions define how each of the sysOPs modifies the
 * system state_s
 *)

definition
  diminish :: "right set \<Rightarrow> cap \<Rightarrow> cap" where
  "diminish R cap \<equiv> cap \<lparr> rights := rights cap \<inter> R \<rparr>"

definition
  createOperation ::
  "entity_id \<Rightarrow> cap \<Rightarrow> cap \<Rightarrow> modify_state" where
  "createOperation e c\<^sub>1 c\<^sub>2 s \<equiv>
  s (target c\<^sub>1 \<mapsto> Entity (insert (full_cap (target c\<^sub>2))
                                (direct_caps_of s (target c\<^sub>1))),
     target c\<^sub>2 \<mapsto> null_entity)"

lemma createOperation_def2:
  "createOperation e c\<^sub>1 c\<^sub>2 s \<equiv>
  let new_cap = \<lparr> target = target c\<^sub>2, rights = all_rights \<rparr>;
      newTarget = ({new_cap} \<union> direct_caps_of s (target c\<^sub>1) )
  in
  s (target c\<^sub>1 \<mapsto> Entity newTarget, target c\<^sub>2 \<mapsto> null_entity)"
  by (simp add: createOperation_def Let_def full_cap_def null_entity_def)

definition
  takeOperation :: "entity_id \<Rightarrow> cap \<Rightarrow> cap \<Rightarrow> right set \<Rightarrow> modify_state" where
  "takeOperation e c\<^sub>1 c\<^sub>2 R s \<equiv>
  s (e \<mapsto> Entity (insert (diminish R c\<^sub>2) (direct_caps_of s e)))"

lemma takeOperation_def2:
  "takeOperation e c\<^sub>1 c\<^sub>2 R s \<equiv>
  s (e \<mapsto> Entity ({diminish R c\<^sub>2} \<union> direct_caps_of s e))"
  by (clarsimp simp: takeOperation_def caps_of_def)

definition
  grantOperation ::
  "entity_id \<Rightarrow> cap \<Rightarrow> cap \<Rightarrow> right set \<Rightarrow> modify_state" where
  "grantOperation e c\<^sub>1 c\<^sub>2 R s \<equiv>
  s (target c\<^sub>1 \<mapsto> Entity (insert (diminish R c\<^sub>2) (direct_caps_of s (target c\<^sub>1)) )) "

lemma grantOperation_def2:
  "grantOperation e c\<^sub>1 c\<^sub>2 R s \<equiv>
  s (target c\<^sub>1 \<mapsto> Entity ( {diminish R c\<^sub>2} \<union> direct_caps_of s (target c\<^sub>1)))"
  by (clarsimp simp: grantOperation_def caps_of_def)

definition
  copyOperation ::
  "entity_id \<Rightarrow> cap \<Rightarrow> cap \<Rightarrow> right set \<Rightarrow> modify_state" where
  "copyOperation sRef c\<^sub>1 c\<^sub>2 R s \<equiv>
  s (target c\<^sub>1 \<mapsto> Entity (insert (diminish R c\<^sub>2) (direct_caps_of s (target c\<^sub>1)))) "

definition
  removeOperation ::
  "entity_id \<Rightarrow> cap \<Rightarrow> cap \<Rightarrow> modify_state" where
  "removeOperation e c\<^sub>1 c\<^sub>2 s \<equiv>
  if is_entity s (target c\<^sub>1)
  then
     s ((target c\<^sub>1) \<mapsto> Entity ((direct_caps_of s (target c\<^sub>1)) - {c\<^sub>2} ))
  else
     s"

lemma removeOperation_simpler:
  "removeOperation e c\<^sub>1 c\<^sub>2 s \<equiv>
  (case s (target c\<^sub>1) of
    None \<Rightarrow> s
  | Some (Entity caps) \<Rightarrow> s (target c\<^sub>1 \<mapsto> Entity (caps - {c\<^sub>2})))"
  by (rule eq_reflection, simp add: removeOperation_def is_entity_def direct_caps_of_def
                             split: if_split_asm option.splits)

definition
  removeSetOperation ::
  "entity_id \<Rightarrow> cap \<Rightarrow> cap set \<Rightarrow> modify_state" where
  "removeSetOperation e c C s \<equiv>
  if is_entity s (target c) then
   s ((target c) \<mapsto> Entity ((direct_caps_of s (target c)) - C ))
  else
   s"

lemma removeSetOperation_simpler:
  "removeSetOperation e c caps s \<equiv>
  (case s (target c) of
    None \<Rightarrow> s
  | Some (Entity caps') \<Rightarrow> s (target c \<mapsto> Entity (caps' - caps)))"
  by (auto simp: removeSetOperation_def is_entity_def direct_caps_of_def
         intro!: eq_reflection
          split: if_split_asm option.splits)

lemma removeSetOperation_fold_removeOperation:
  "removeSetOperation e c (set caps) s = fold (removeOperation e c) caps s"
  apply (subst foldr_fold [symmetric])
   apply (fastforce simp: removeOperation_def direct_caps_of_def is_entity_def)
  apply (rule sym)
  apply (induct caps)
   apply (fastforce simp: removeSetOperation_def removeOperation_def direct_caps_of_def is_entity_def)
  apply (fastforce simp: removeSetOperation_def removeOperation_def direct_caps_of_def is_entity_def)
  done

definition
  removeSetOfCaps :: "(entity_id \<Rightarrow> cap set) \<Rightarrow> modify_state"
where
  "removeSetOfCaps cap_map s \<equiv> \<lambda>e.
     if is_entity s e
     then Some (Entity ((direct_caps_of s e) - cap_map e ))
     else None"

definition
  caps_to_entity :: "entity_id \<Rightarrow> entity_id \<Rightarrow> state \<Rightarrow> cap set"
where
  "caps_to_entity e e' s \<equiv> {cap. cap \<in> direct_caps_of s e' \<and> target cap = e}"

definition
  revokeOperation :: "entity_id \<Rightarrow> cap \<Rightarrow> modify_state_n" where
  "revokeOperation e c s \<equiv>
    {s'. \<exists>cap_map. \<forall>e'. cap_map e' \<subseteq> caps_to_entity (target c) e' s \<and>
         s' = removeSetOfCaps cap_map s}"

definition
  destroyOperation :: "entity_id \<Rightarrow> cap \<Rightarrow> modify_state" where
  "destroyOperation e c s \<equiv> s(target c := None)"


(* Non deterministically executing system calls:
 * How we execute a single operation
 *)
primrec
  step' :: "sysOPs \<Rightarrow> modify_state_n"
where
  "step' (SysCreate    e c\<^sub>1 c\<^sub>2) s   = {createOperation e c\<^sub>1 c\<^sub>2 s}"
| "step' (SysTake      e c\<^sub>1 c\<^sub>2 R) s = {takeOperation  e c\<^sub>1 c\<^sub>2 R s}"
| "step' (SysGrant     e c\<^sub>1 c\<^sub>2 R) s = {grantOperation  e c\<^sub>1 c\<^sub>2 R s}"
| "step' (SysCopy      e c\<^sub>1 c\<^sub>2 R) s = {copyOperation e c\<^sub>1 c\<^sub>2 R s}"
| "step' (SysRemove    e c\<^sub>1 c\<^sub>2)   s = {removeOperation e c\<^sub>1 c\<^sub>2 s}"
| "step' (SysRemoveSet e c C)    s = {removeSetOperation e c C s}"
| "step' (SysRevoke    e c) s      =  revokeOperation e c s"
| "step' (SysDestroy   e c) s      = {destroyOperation e c s}"

(* single operation is allowed only if it is legal in the current state_s *)
definition
  step :: "sysOPs \<Rightarrow> modify_state_n" where
  "step cmd s \<equiv> if legal cmd s then (step' cmd s) \<union> {s} else {s}"

(* execution of a list of commands (from back of list)
 *)
primrec
  execute :: "sysOPs list \<Rightarrow> state \<Rightarrow> state set"
where
  "execute [] s = {s}"
| "execute (cmd#cmds) s = \<Union> (step cmd ` ( execute cmds s ))"



(***************************
 * Lemmas about the model. *
 ***************************)

lemma Int_all_rights [simp]: "c \<inter> all_rights = c"
  by (simp add: all_rights_def)

lemma is_entity_dom: "is_entity s e = (e \<in> dom s)"
  by (simp add: is_entity_def dom_def)

lemma is_entity_imp_not_None:
  "is_entity s e \<Longrightarrow> s e \<noteq> None"
  by (simp add: is_entity_def)

lemma store_connected_refl [simp]:
  "(e, e) \<in> store_connected s"
  by (simp add: store_connected_def)

lemma no_caps_of_imp_not_connected [rule_format]:
  "\<lbrakk>(e, x) \<in> store_connected s\<rbrakk>
  \<Longrightarrow> direct_caps_of s e = {} \<longrightarrow> x = e"
  apply (unfold store_connected_def)
  apply (erule rtrancl.induct)
   apply simp
  apply (clarsimp simp: store_connected_direct_def direct_caps_of_def)
  done

lemma no_direct_caps_of_no_caps_of:
  "(direct_caps_of s e = {}) = (caps_of s e = {})"
  apply (rule iffI)
   apply (clarsimp simp add: caps_of_def)
   apply (drule (1) no_caps_of_imp_not_connected)
   apply simp
  apply (clarsimp simp add: caps_of_def store_connected_def)
  done

lemma no_direct_caps_of_imp_no_caps_of:
  "direct_caps_of s e = {} \<Longrightarrow> caps_of s e = {}"
  by (rule no_direct_caps_of_no_caps_of [THEN iffD1])

lemma no_caps_of_imp_no_direct_caps_of:
  "caps_of s e = {} \<Longrightarrow> direct_caps_of s e = {}"
  by (rule no_direct_caps_of_no_caps_of [THEN iffD2])

lemma store_connected_direct_in_store_connected:
  "(x, y) \<in> store_connected_direct s \<Longrightarrow> (x, y) \<in> store_connected s"
  by (simp add: store_connected_def)

lemma no_diminish [simp]:
  "diminish all_rights c = c"
  by (simp add: diminish_def)

lemma no_diminish_image [simp]:
  "diminish all_rights ` C = C"
  by (fastforce)

lemma diminish_diminish [simp]:
  "diminish dimR2 (diminish dimR1 sc) = diminish (dimR1 \<inter> dimR2) sc"
  by (clarsimp simp add: diminish_def Int_assoc)

lemma diminish_range_diminish [simp]:
  "diminish dimR2 ` diminish dimR1 ` ssc = diminish (dimR1 \<inter> dimR2) ` ssc"
  apply (rule set_eqI)
  apply (rule iffI)
   apply (clarsimp)
  apply (clarsimp simp del: diminish_diminish simp add: diminish_diminish [symmetric])
  done

lemma execute_not_empty:
  "execute ops s \<noteq> {}"
  apply (induct ops)
   apply (simp)
  apply (simp add: step_def del: if_image_distrib, fast)
  done

lemma execute_append [intro]:
  "\<And> s s' s'' opsA. \<lbrakk> s'' \<in> execute opsA s; s' \<in> execute opsB s'' \<rbrakk> \<Longrightarrow> s' \<in> execute (opsB @ opsA) s"
  apply (induct opsB)
   apply (simp)
  apply (atomize)
  apply (clarsimp)
  apply (rule bexI)
   apply (assumption)
  by (drule spec | drule(1) mp)+

(* Lemma on caps *)

lemma heapAdd_read_cap [simp]:
  "target (read_cap e) = e"
  by (simp add: read_cap_def)

lemma rights_read_cap [simp]:
  "rights (read_cap e) = {Read}"
  by (simp add: read_cap_def)

lemma heapAdd_write_cap [simp]:
  "target (write_cap e) = e"
  by (simp add: write_cap_def)

lemma rights_write_cap [simp]:
  "rights (write_cap e) = {Write}"
  by (simp add: write_cap_def)

lemma heapAdd_take_cap [simp]:
  "target (take_cap e) = e"
  by (simp add: take_cap_def)

lemma rights_take_cap [simp]:
  "rights (take_cap e) = {Take}"
  by (simp add: take_cap_def)

lemma heapAdd_grant_cap [simp]:
  "target (grant_cap e) = e"
  by (simp add: grant_cap_def)

lemma rights_grant_cap [simp]:
  "rights (grant_cap e) = {Grant}"
  by (simp add: grant_cap_def)

lemma heapAdd_create_cap [simp]:
  "target (create_cap e) = e"
  by (simp add: create_cap_def)

lemma rights_create_cap [simp]:
  "rights (create_cap e) = {Create}"
  by (simp add: create_cap_def)

lemma heapAdd_store_cap [simp]:
  "target (store_cap e) = e"
  by (simp add: store_cap_def)

lemma rights_store_cap [simp]:
  "rights (store_cap e) = {Store}"
  by (simp add: store_cap_def)

lemma heapAdd_full_cap [simp]:
  "target (full_cap e) = e"
  by (simp add: full_cap_def)

lemma rights_full_cap [simp]:
  "rights (full_cap e) = all_rights"
  by (simp add: full_cap_def)

lemma entity_diminish [simp]:
  "target (diminish R c) = target c"
  by (simp add: diminish_def)

lemma rights_diminish [simp]:
  "rights (diminish R c) = rights c \<inter> R"
  by (simp add: diminish_def)

(* Lemmas on caps_of *)

lemma caps_of_imp_some_direct_cap:
  "c \<in> caps_of s e \<Longrightarrow> \<exists>e'. c \<in> direct_caps_of s e'"
  by (auto simp: caps_of_def)

lemma caps_of_imp_some_store_connected_direct_cap:
  "c \<in> caps_of s e \<Longrightarrow> \<exists>e'. (e, e') \<in> store_connected s \<and> c \<in> direct_caps_of s e'"
  by (auto simp: caps_of_def)

lemma direct_cap_in_cap:
  "c \<in> direct_caps_of s e \<Longrightarrow> c \<in> caps_of s e"
  by (auto simp: caps_of_def store_connected_def)

lemma all_caps_ofE [elim!]:
  "\<lbrakk> c \<in> all_caps_of s; \<And>e'. c \<in> direct_caps_of s e' \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (fastforce simp add: all_caps_of_def)

lemma all_caps_ofI [intro]:
  "c \<in> direct_caps_of s e' \<Longrightarrow> c \<in> all_caps_of s"
  by (fastforce simp add: all_caps_of_def)

(* Lemmas on entities *)

lemma entity_not_not_entity:
  "\<lbrakk>is_entity s e\<^sub>1; \<not> is_entity s e\<^sub>2\<rbrakk> \<Longrightarrow> e\<^sub>1 \<noteq> e\<^sub>2"
  by (auto simp: is_entity_def)

lemma no_direct_caps_of_in_nonEntity:
  "\<not> is_entity s e \<Longrightarrow> direct_caps_of s e = {}"
  by (auto simp: direct_caps_of_def is_entity_def split:option.splits)

lemma not_is_entity_imp_no_direct_caps_of:
  "\<not> is_entity s e \<Longrightarrow> caps_of s e = {}"
  by (drule no_direct_caps_of_in_nonEntity, erule no_direct_caps_of_imp_no_caps_of)

lemma direct_caps_of_imp_is_entity:
  "c \<in> direct_caps_of s e \<Longrightarrow> is_entity s e"
  by (auto intro: classical dest: no_direct_caps_of_in_nonEntity)

lemma caps_of_imp_is_entity:
  "c \<in> caps_of s e \<Longrightarrow> is_entity s e"
  by (auto intro: classical dest: not_is_entity_imp_no_direct_caps_of)

(* Lemmas on store_connected *)

lemma store_caps_of_store_connected_direct:
  "\<lbrakk>c \<in> direct_caps_of s e; Store \<in> rights c\<rbrakk>
  \<Longrightarrow> (e, target c) \<in> store_connected_direct s"
  by (fastforce simp: store_connected_direct_def)

lemma store_caps_store_connected:
  "\<lbrakk>c \<in> caps_of s e; Store \<in> rights c\<rbrakk> \<Longrightarrow> (e, target c) \<in> store_connected s"
  apply (clarsimp simp: store_connected_def caps_of_def)
  by (frule (1) store_caps_of_store_connected_direct, simp)

end
