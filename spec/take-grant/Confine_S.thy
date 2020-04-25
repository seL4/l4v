(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Title:   Confinement_S
 * Description: confinement proof of the security model
 *)

theory Confine_S
imports System_S
begin

(* These translate Create into all_rights *)
definition
  extra_rights :: "cap \<Rightarrow> cap" where
  "extra_rights c \<equiv>
  if (Create \<in> rights c)
  then c\<lparr>rights := all_rights\<rparr>
  else c"


lemma extra_rights_idem [simp]:
  "(extra_rights (extra_rights c)) = (extra_rights c)"
  apply (clarsimp simp add: extra_rights_def)
  done

lemma extra_rights_image_idem [simp]:
  "(extra_rights ` (extra_rights ` S)) = (extra_rights ` S)"
  by (rule set_eqI) (simp add: image_iff)

lemma extra_rights_empty_rights_ident [simp]:
   "extra_rights \<lparr> target = e, rights = {} \<rparr> = \<lparr> target = e, rights = {} \<rparr>"
  by (simp add: extra_rights_def)

lemma entity_extra_rights [simp]:
  "target (extra_rights c) = target c"
  by (simp add: extra_rights_def)

lemma rights_extra_rights:
  "rights (extra_rights c) =
   (if Create \<in> (rights c)
    then all_rights
    else rights c)"
  by (simp add: extra_rights_def)

(* The following two definitions both translate Create into all_rights *)

(* A cap is in a set, or a cap with more access is. *)
definition
  cap_in_caps :: "cap \<Rightarrow> cap set \<Rightarrow> bool" (infix "\<in>cap" 50) where
  "c \<in>cap C \<equiv> \<exists>c' \<in> C. target c = target c' \<and> rights (extra_rights c) \<subseteq> rights (extra_rights c')"

abbreviation not_cap_in_caps where
  "not_cap_in_caps x A \<equiv> ~ (x \<in>cap A)" \<comment> \<open>non-membership\<close>

notation (input) cap_in_caps (infix ":cap" 50)
notation (latex output)  cap_in_caps (infix "\<in>\<^sub>c\<^sub>a\<^sub>p" 50)

notation
  not_cap_in_caps  ("(\<notin>cap)") and
  not_cap_in_caps  ("(_/ \<notin>cap _)" [51, 51] 50)

notation (latex output)
  not_cap_in_caps  ("(\<notin>\<^sub>c\<^sub>a\<^sub>p)") and
  not_cap_in_caps  (infix "\<notin>\<^sub>c\<^sub>a\<^sub>p" 50)

(* A set of caps "caps" have less (or equal) access to an entity as "cap" does. *)
definition
  caps_dominated_by :: "cap set \<Rightarrow> cap \<Rightarrow> bool" (infix "\<le>cap" 50) where
  "caps \<le>cap cap \<equiv> \<forall>cap' \<in> caps. target cap' = target cap \<longrightarrow> rights (extra_rights cap') \<subseteq> rights (extra_rights cap)"

notation (input) caps_dominated_by (infix "<=cap" 50)
notation (latex output) caps_dominated_by (infix "\<unlhd>\<^sub>c\<^sub>a\<^sub>p" 50)

definition
  shares_caps :: "state \<Rightarrow> entity_id \<Rightarrow> entity_id \<Rightarrow> bool" where
  "shares_caps s e\<^sub>x e\<^sub>y \<equiv> \<exists>e\<^sub>i . (e\<^sub>x, e\<^sub>i) \<in> store_connected s \<and> (e\<^sub>y, e\<^sub>i) \<in> store_connected s"

definition
  leak :: "state \<Rightarrow> entity_id \<Rightarrow> entity_id \<Rightarrow> bool" ("_ \<turnstile> _ \<rightarrow> _") where
  "leak s e\<^sub>x e\<^sub>y \<equiv> take_cap e\<^sub>x \<in>cap caps_of s e\<^sub>y \<or> grant_cap e\<^sub>y \<in>cap caps_of s e\<^sub>x \<or> shares_caps s e\<^sub>x e\<^sub>y"


definition
  directly_tgs_connected :: "state \<Rightarrow> (entity_id \<times> entity_id) set" where
  "directly_tgs_connected s \<equiv> {(e\<^sub>x, e\<^sub>y). leak s e\<^sub>x e\<^sub>y \<or> leak s e\<^sub>y e\<^sub>x}"

lemma directly_tgs_connected_def2:
  "(e\<^sub>x, e\<^sub>y) \<in> directly_tgs_connected s = (leak s e\<^sub>x e\<^sub>y \<or> leak s e\<^sub>y e\<^sub>x)"
  by (simp add: directly_tgs_connected_def)

abbreviation
  in_directly_tgs_connected :: "state \<Rightarrow> entity_id \<Rightarrow> entity_id \<Rightarrow> bool" ("_ \<turnstile> _ \<leftrightarrow> _" [60,0,60] 61)
where
  "s \<turnstile> x \<leftrightarrow> y \<equiv> (x,y) \<in> directly_tgs_connected s"

definition
  tgs_connected :: "state \<Rightarrow> (entity_id \<times> entity_id) set" where
  "tgs_connected s \<equiv> (directly_tgs_connected s)\<^sup>*"

abbreviation
  in_tgs_connected :: "state \<Rightarrow> entity_id \<Rightarrow> entity_id \<Rightarrow> bool" ("_ \<turnstile> _ \<leftrightarrow>* _" [60,0,60] 61)
where
  "s \<turnstile> x \<leftrightarrow>* y == (x,y) \<in> tgs_connected s"

notation (latex output)
  in_tgs_connected ("_ \<turnstile> _ \<leftrightarrow>\<^sup>* _" [60,0,60] 61)

translations
  "\<not> (s \<turnstile> x \<leftrightarrow> y)" <= "(x,y) \<notin> CONST directly_tgs_connected s"
  "\<not> (s \<turnstile> x \<leftrightarrow>* y)" <= "(x,y) \<notin> CONST tgs_connected s"

lemma shares_caps_sym [simp]:
 "shares_caps s y x = shares_caps s x y"
  by (auto simp: shares_caps_def)

lemma directly_tgs_connected_def4:
  "s \<turnstile> e\<^sub>x \<leftrightarrow> e\<^sub>y = (take_cap e\<^sub>x \<in>cap caps_of s e\<^sub>y \<or> take_cap e\<^sub>y \<in>cap caps_of s e\<^sub>x \<or>
                  grant_cap e\<^sub>y \<in>cap caps_of s e\<^sub>x \<or> grant_cap e\<^sub>x \<in>cap caps_of s e\<^sub>y \<or>
                  shares_caps s e\<^sub>x e\<^sub>y)"
  by (auto simp: directly_tgs_connected_def leak_def)

(* Note: e\<^sub>0 is unused. *)
definition
  generalOperation ::
  "entity_id \<Rightarrow> entity_id \<Rightarrow> cap \<Rightarrow> right set \<Rightarrow> modify_state" where
  "generalOperation e\<^sub>0 e\<^sub>1 c r s \<equiv>
  s (e\<^sub>1 \<mapsto> Entity ( insert (diminish r (extra_rights c)) (direct_caps_of s e\<^sub>1) ))"

lemma is_entity_general [simp]:
  "is_entity s e\<^sub>1 \<Longrightarrow> is_entity (generalOperation e\<^sub>0 e\<^sub>1 c r s) e' = is_entity s e'"
  by (simp add: is_entity_def generalOperation_def)

definition
  make_entity :: "entity_id \<Rightarrow> modify_state" where
  "make_entity n s \<equiv>
  s (n \<mapsto> null_entity)"

lemma direct_caps_of_store_connected_eq:
  "\<forall> e. direct_caps_of s e = direct_caps_of s' e
  \<Longrightarrow> store_connected s = store_connected s'"
  by (simp add: store_connected_def store_connected_direct_def
                direct_caps_of_def)

lemma direct_caps_of_caps_of_eq:
  "\<forall> e. direct_caps_of s e = direct_caps_of s' e \<Longrightarrow> caps_of s e = caps_of s' e"
  by (simp add: caps_of_def store_connected_def store_connected_direct_def
                direct_caps_of_def)

lemma direct_caps_of_caps_of_eq2:
  "\<lbrakk>\<forall> e. direct_caps_of s e = direct_caps_of s' e; c \<in>cap caps_of s e\<rbrakk> \<Longrightarrow> c \<in>cap caps_of s' e"
  apply (drule direct_caps_of_caps_of_eq)
  apply (simp add: cap_in_caps_def)
  by auto

lemma direct_caps_of_directly_tgs_connected_eq:
  "\<forall> e. direct_caps_of s e = direct_caps_of s' e \<Longrightarrow> s \<turnstile> x \<leftrightarrow> y = s' \<turnstile> x \<leftrightarrow> y"
  apply (simp add: directly_tgs_connected_def4 shares_caps_def)
  apply rule
   apply (erule disjE, drule (1) direct_caps_of_caps_of_eq2, clarsimp)+
   apply (drule direct_caps_of_store_connected_eq, clarsimp)
  apply (erule disjE, drule direct_caps_of_caps_of_eq2 [rotated, where s=s' and s'=s], simp+)+
  apply (drule direct_caps_of_store_connected_eq, simp)
  done

lemma direct_caps_of_make_entity:
  "\<not> is_entity s n \<Longrightarrow> direct_caps_of (make_entity n s) e = direct_caps_of s e"
  by (simp add: direct_caps_of_def make_entity_def is_entity_def
                null_entity_def)

lemma caps_of_make_entity:
  "\<not> is_entity s n \<Longrightarrow> caps_of (make_entity n s) e = caps_of s e"
  apply (rule direct_caps_of_caps_of_eq)
  apply clarsimp
  apply (erule direct_caps_of_make_entity)
  done

lemma caps_of_make_entity2:
  "\<lbrakk>\<not> is_entity s n; c \<in> caps_of (make_entity n s) e\<rbrakk> \<Longrightarrow> c \<in> caps_of s e"
  apply (drule caps_of_make_entity)
  apply fastforce
  done

lemma directly_tgs_connected_make_entity:
 "\<not> is_entity s n \<Longrightarrow> make_entity n s \<turnstile> x \<leftrightarrow> y = s \<turnstile> x \<leftrightarrow> y"
  apply (rule direct_caps_of_directly_tgs_connected_eq)
  apply clarsimp
  apply (drule (1) direct_caps_of_make_entity)
  done

lemma directly_tgs_connected_make_entity2:
 "\<lbrakk>\<not> is_entity s n; make_entity n s \<turnstile> x \<leftrightarrow> y\<rbrakk> \<Longrightarrow> s \<turnstile> x \<leftrightarrow> y"
  apply (drule directly_tgs_connected_make_entity)
  apply fastforce
  done

lemma diminish_extra_rights [simp]:
  "diminish (rights c) (extra_rights c) = c"
  by (simp add: diminish_def all_rights_def rights_extra_rights)

lemma diminish_extra_rights2 [simp]:
  "diminish (r \<inter> rights c) (extra_rights c) = diminish r c"
  apply (simp add: diminish_def extra_rights_def all_rights_def)
  apply (simp add: Int_commute)
  apply (subgoal_tac "rights c \<inter> (r \<inter> rights c) = r \<inter> rights c")
   apply simp
  apply fastforce
  done

lemma create_general_helper:
  "Create \<in> rights c\<^sub>2 \<Longrightarrow>
   \<lparr>target = target c\<^sub>2, rights = UNIV\<rparr> = c\<^sub>2\<lparr>rights := UNIV\<rparr>"
  by auto

lemma extra_rights_full_cap [simp]:
  "extra_rights (full_cap e) = full_cap e"
  by (simp add: extra_rights_def)

lemma create_general_alt:
  "createOperation e c\<^sub>1 c\<^sub>2 s =
   make_entity (target c\<^sub>2)
               (generalOperation  e (target c\<^sub>1) (full_cap (target c\<^sub>2)) (all_rights) s)"
  by (simp add: createOperation_def generalOperation_def make_entity_def)

lemma create_general:
  "Create \<in> rights c\<^sub>2 \<Longrightarrow> createOperation e c\<^sub>1 c\<^sub>2 s =
   make_entity (target c\<^sub>2)
               (generalOperation  e (target c\<^sub>1) c\<^sub>2 (all_rights) s)"
  by (simp add: createOperation_def generalOperation_def make_entity_def
                full_cap_def all_rights_def diminish_def
                extra_rights_def create_general_helper null_entity_def)

lemma take_general:
  "takeOperation e c\<^sub>1 c\<^sub>2 r s =
   generalOperation (target c\<^sub>1) e c\<^sub>2 (r \<inter> rights c\<^sub>2) s"
  by (simp add: takeOperation_def generalOperation_def)

lemma grant_general:
  "grantOperation e c\<^sub>1 c\<^sub>2 r s =
   generalOperation e (target c\<^sub>1) c\<^sub>2 (r \<inter> rights c\<^sub>2) s"
  by (simp add: grantOperation_def generalOperation_def)

lemma copy_general:
  "copyOperation e c\<^sub>1 c\<^sub>2 r s =
   generalOperation e (target c\<^sub>1) c\<^sub>2 (r \<inter> rights c\<^sub>2) s"
  by (simp add: copyOperation_def generalOperation_def)

(* Lemmas on the directly_tgs_connected predicate *)
lemma directly_tgs_connected_comm:
  "s \<turnstile> x \<leftrightarrow> y \<Longrightarrow> s \<turnstile> y \<leftrightarrow> x"
  by(auto simp: directly_tgs_connected_def)

lemma tgs_connected_refl [simp]:
  "s \<turnstile> x \<leftrightarrow>* x"
  by (metis tgs_connected_def rtrancl.rtrancl_refl)

lemma tgs_connected_comm:
  "s \<turnstile> x \<leftrightarrow>* y \<Longrightarrow> s \<turnstile> y \<leftrightarrow>* x"
  apply(simp add: tgs_connected_def)
  apply(erule rtrancl_induct, simp)
  apply(case_tac "s \<turnstile> z \<leftrightarrow> y")
   apply(simp add: directly_tgs_connected_comm)
  apply(simp add: directly_tgs_connected_comm)
  done

lemma tgs_connected_comm_eq:
  "s \<turnstile> x \<leftrightarrow>* y = s \<turnstile> y \<leftrightarrow>* x"
  by (metis tgs_connected_comm)

lemmas tgs_connected_trans =
       rtrancl_trans [where r="directly_tgs_connected s"  for s, simplified tgs_connected_def[symmetric]]

lemmas directly_tgs_connected_rtrancl_into_rtrancl =
       rtrancl_into_rtrancl [where r="directly_tgs_connected s" for s, simplified tgs_connected_def[symmetric]]

lemma take_caps_directly_tgs_connected:
  "\<lbrakk>c \<in> caps_of s e; Take \<in> rights c\<rbrakk> \<Longrightarrow> s \<turnstile> e \<leftrightarrow> target c"
  by (auto simp: directly_tgs_connected_def leak_def take_cap_def cap_in_caps_def extra_rights_def all_rights_def)

lemma grant_caps_directly_tgs_connected:
  "\<lbrakk>c \<in> caps_of s e; Grant \<in> rights c\<rbrakk> \<Longrightarrow> s \<turnstile> e \<leftrightarrow> target c"
  by (auto simp: directly_tgs_connected_def leak_def grant_cap_def cap_in_caps_def extra_rights_def all_rights_def)

lemma create_caps_directly_tgs_connected:
  "\<lbrakk>c \<in> caps_of s e; Create \<in> rights c\<rbrakk> \<Longrightarrow> s \<turnstile> e \<leftrightarrow> target c"
  by (auto simp: directly_tgs_connected_def leak_def cap_in_caps_def rights_extra_rights all_rights_def)

lemma store_connected_directly_tgs_connected:
  "(x, y) \<in> store_connected s \<Longrightarrow> s \<turnstile> x \<leftrightarrow> y"
  by (auto simp: directly_tgs_connected_def leak_def shares_caps_def store_connected_def)

(* Lemmas on caps *)

lemma cap_in_caps_insert [simp]:
  "c \<in>cap insert c' S = (target c = target c' \<and>
  rights (extra_rights c) \<subseteq> rights (extra_rights c') \<or> c \<in>cap S)"
  by (simp add: cap_in_caps_def)

lemma cap_in_caps_singleton [simp]:
  "c \<in>cap {c'} = (target c = target c' \<and> rights (extra_rights c) \<subseteq> rights (extra_rights c'))"
  by (simp add: cap_in_caps_def)

lemma not_in [simp]:
  "{} \<le>cap c"
  by(simp add: caps_dominated_by_def)

lemma extra_rights_diminish:
  "x \<in> rights (extra_rights (diminish r c))
   \<Longrightarrow> x \<in> rights (extra_rights c)"
  by (auto simp: rights_extra_rights all_rights_def split:if_split_asm)

(* Lemmas on system operations *)

definition
  in_store_connected :: "state \<Rightarrow> entity_id \<Rightarrow> entity_id \<Rightarrow> bool" where
  "in_store_connected s x y \<equiv> (x, y) \<in> store_connected s"

(* Lemmas about the general operation *)

lemma direct_caps_of_generalOp:
  "direct_caps_of (generalOperation e\<^sub>0 e\<^sub>1 c r s) e =
  (if e = e\<^sub>1
   then insert (diminish r (extra_rights c)) (direct_caps_of s (e\<^sub>1))
   else direct_caps_of s e)"
  by (clarsimp simp: generalOperation_def direct_caps_of_def split:option.splits)

lemma direct_caps_of_generalOp2:
  "\<lbrakk>c' \<in> direct_caps_of (generalOperation e\<^sub>0 e\<^sub>1 c r s) x\<rbrakk> \<Longrightarrow>
   c' \<in> direct_caps_of s x \<or> (c' \<in>cap {c} \<and> x = e\<^sub>1)"
  apply (clarsimp simp: direct_caps_of_generalOp extra_rights_diminish
           split:if_split_asm)
  apply (drule extra_rights_diminish)
  by simp

lemma store_connected_direct_generalOp:
  "\<lbrakk>(x, y) \<in> store_connected_direct (generalOperation e\<^sub>0 e\<^sub>1 c r s)\<rbrakk> \<Longrightarrow>
   (x, y) \<in> store_connected_direct s \<or>
   (x = e\<^sub>1 \<and> y = target c \<and> Store \<in> rights (extra_rights c))"
  by (auto simp: store_connected_direct_def direct_caps_of_generalOp all_rights_def
          split: if_split_asm)

lemma store_connected_generalOp:
  "\<lbrakk>(x, y) \<in> store_connected (generalOperation e\<^sub>0 e\<^sub>1 c r s)\<rbrakk> \<Longrightarrow>
   (x, y) \<in> store_connected s \<or>
   ((x, e\<^sub>1) \<in> store_connected s \<and>
   (e\<^sub>1, target c) \<in> store_connected_direct (generalOperation e\<^sub>0 e\<^sub>1 c r s) \<and>
   (target c, y) \<in> store_connected s)"
  apply (unfold store_connected_def)
  apply (erule rtrancl_induct)
   apply clarsimp
  apply (clarsimp)
  apply (fold store_connected_def)
  apply (subgoal_tac "(y, z) \<in> store_connected_direct s")
   apply (clarsimp simp: store_connected_def)
   apply (erule disjE)
    apply fastforce
   apply clarsimp
   apply (erule notE)
   apply fastforce
  apply (frule store_connected_direct_generalOp)
  apply (clarsimp simp: store_connected_def)
  done


lemma store_connected_generalOp_not_new:
  "\<lbrakk>(e\<^sub>1, target c) \<in> store_connected_direct (generalOperation e\<^sub>0 e\<^sub>1 c r s);
   c \<in> caps_of s e\<^sub>0\<rbrakk> \<Longrightarrow>
   (e\<^sub>1, target c) \<in> store_connected_direct s \<or>
   (e\<^sub>0, target c) \<in> store_connected s \<or>
   Create \<in> rights c"
  apply (drule store_connected_direct_generalOp)
  apply (clarsimp simp: rights_extra_rights split:if_split_asm)
   apply (drule (1) store_caps_store_connected, simp)
  done

lemma store_connected_generalOp2:
  "\<lbrakk>(x, y) \<in> store_connected (generalOperation e\<^sub>0 e\<^sub>1 c r s);
   c \<in> caps_of s e\<^sub>0; s \<turnstile> e\<^sub>0 \<leftrightarrow> e\<^sub>1\<rbrakk> \<Longrightarrow>
   s \<turnstile> x \<leftrightarrow>* y"
  apply (drule store_connected_generalOp)
  apply (erule disjE)
   apply (simp add: tgs_connected_def)
   apply (drule store_connected_directly_tgs_connected, simp)
  apply clarsimp
  apply (drule store_connected_directly_tgs_connected [where x=x and y=e\<^sub>1])
  apply (drule store_connected_directly_tgs_connected [where x="target c" and y=y])
  apply (drule (1) store_connected_generalOp_not_new)
  apply (erule disjE)
   apply (drule store_connected_direct_in_store_connected)
   apply (drule store_connected_directly_tgs_connected [where x=e\<^sub>1 and y="target c"])
   apply (simp add: tgs_connected_def)
  apply (drule directly_tgs_connected_comm [where x="e\<^sub>0" and y="e\<^sub>1"])
  apply (erule disjE)
   apply (drule store_connected_directly_tgs_connected [where x=e\<^sub>0 and y="target c"])
   apply (simp add: tgs_connected_def)
  apply (drule (1) create_caps_directly_tgs_connected)
  apply (simp add: tgs_connected_def)
  done

lemma shares_caps_of_generalOp:
  "\<lbrakk>shares_caps (generalOperation e\<^sub>0 e\<^sub>1 c r s) x y;
   c \<in> caps_of s e\<^sub>0; s \<turnstile> e\<^sub>0 \<leftrightarrow> e\<^sub>1\<rbrakk>
  \<Longrightarrow> s \<turnstile> x \<leftrightarrow>* y"
  apply (clarsimp simp: shares_caps_def)
  apply (frule (2) store_connected_generalOp2 [where x=x])
  apply (drule (2) store_connected_generalOp2 [where x=y])
  apply (drule tgs_connected_comm [where x=y])
  apply (simp add: tgs_connected_def)
  done

lemma caps_of_generalOp:
  "\<lbrakk>c' \<in> caps_of (generalOperation e\<^sub>0 e\<^sub>1 c r s) x;
   c \<in> caps_of s e\<^sub>0; s \<turnstile> e\<^sub>0 \<leftrightarrow> e\<^sub>1\<rbrakk>
  \<Longrightarrow> \<exists>z. (x,z) \<in> tgs_connected s \<and> c' \<in>cap caps_of s z"
  apply (simp add: caps_of_def[where e=x])
  apply clarsimp
  apply (frule (2) store_connected_generalOp2)
  apply (drule direct_caps_of_generalOp2)
  apply (erule disjE)
   apply (drule direct_cap_in_cap)
   apply (fastforce simp: cap_in_caps_def)
  apply (subgoal_tac "s \<turnstile> x \<leftrightarrow>* e\<^sub>0")
   apply (subgoal_tac "c' \<in>cap caps_of s e\<^sub>0")
    apply fastforce
   apply (fastforce simp: cap_in_caps_def)
  apply clarsimp
  apply (drule directly_tgs_connected_comm [where x="e\<^sub>0" and y="e\<^sub>1"])
  apply (simp add: tgs_connected_def)
  done

lemma take_cap_generalOp:
  "\<lbrakk>take_cap y \<in>cap caps_of (generalOperation e\<^sub>0 e\<^sub>1 c r s) x;
   c \<in> caps_of s e\<^sub>0; s \<turnstile> e\<^sub>0 \<leftrightarrow> e\<^sub>1\<rbrakk>
  \<Longrightarrow> \<exists>z.  s \<turnstile> x \<leftrightarrow>* z \<and> take_cap y \<in>cap caps_of s z"
  apply (simp add: cap_in_caps_def)
  apply clarsimp
  apply (drule (2) caps_of_generalOp)
  apply (fastforce simp: cap_in_caps_def)
  done

lemma grant_cap_generalOp:
  "\<lbrakk>grant_cap y \<in>cap caps_of (generalOperation e\<^sub>0 e\<^sub>1 c r s) x;
   c \<in> caps_of s e\<^sub>0; s \<turnstile> e\<^sub>0 \<leftrightarrow> e\<^sub>1\<rbrakk>
  \<Longrightarrow> \<exists>z.  s \<turnstile> x \<leftrightarrow>* z \<and> grant_cap y \<in>cap caps_of s z"
  apply (simp add: cap_in_caps_def)
  apply clarsimp
  apply (drule (2) caps_of_generalOp)
  apply (fastforce simp: cap_in_caps_def)
  done

lemma take_cap_generalOp2:
  "\<lbrakk>take_cap y \<in>cap caps_of (generalOperation e\<^sub>0 e\<^sub>1 c r s) x;
   c \<in> caps_of s e\<^sub>0; s \<turnstile> e\<^sub>0 \<leftrightarrow> e\<^sub>1\<rbrakk>
  \<Longrightarrow> (x, y) \<in> tgs_connected s"
  apply (drule (2) take_cap_generalOp)
  apply clarsimp
  apply (subgoal_tac "s \<turnstile> z \<leftrightarrow> y")
   apply (simp add: tgs_connected_def)
  apply (simp add: directly_tgs_connected_def leak_def)
  done

lemma grant_cap_generalOp2:
  "\<lbrakk>grant_cap y \<in>cap caps_of (generalOperation e\<^sub>0 e\<^sub>1 c r s) x;
   c \<in> caps_of s e\<^sub>0; s \<turnstile> e\<^sub>0 \<leftrightarrow> e\<^sub>1\<rbrakk>
  \<Longrightarrow> (x, y) \<in> tgs_connected s"
  apply (drule (2) grant_cap_generalOp)
  apply clarsimp
  apply (subgoal_tac "s \<turnstile> z \<leftrightarrow> y")
   apply (simp add: tgs_connected_def)
  apply (simp add: directly_tgs_connected_def leak_def)
  done

lemma generalOp_directly_tgs_connected:
 "\<lbrakk>generalOperation e\<^sub>0 e\<^sub>1 c r s \<turnstile> x \<leftrightarrow> y;
   c \<in> caps_of s e\<^sub>0; s \<turnstile> e\<^sub>0 \<leftrightarrow> e\<^sub>1\<rbrakk>
  \<Longrightarrow> s \<turnstile> x \<leftrightarrow>* y"
  apply (simp add: directly_tgs_connected_def [where s="generalOperation e\<^sub>0 e\<^sub>1 c r s"] leak_def)
  apply safe
       apply (rule tgs_connected_comm)
       apply (drule (3) take_cap_generalOp2)
      apply (drule (3) grant_cap_generalOp2)
     apply (erule (2) shares_caps_of_generalOp)
    apply (drule (3) take_cap_generalOp2)
   apply (rule tgs_connected_comm)
   apply (drule (3) grant_cap_generalOp2)
  apply (erule (2) shares_caps_of_generalOp)
  done



(* results from general operation *)

lemma create_legal_directly_tgs_connected:
  "legal (SysCreate e c\<^sub>1 c\<^sub>2) s \<Longrightarrow> s  \<turnstile> target c\<^sub>1 \<leftrightarrow> e"
  apply clarsimp
  apply (rule directly_tgs_connected_comm)
  apply (drule (1) create_caps_directly_tgs_connected)
  apply (drule (1) store_caps_store_connected)
  apply (drule (1) store_connected_directly_tgs_connected)
  done

lemma take_legal_directly_tgs_connected:
  "legal (SysTake e c\<^sub>1 c\<^sub>2 r) s \<Longrightarrow> s  \<turnstile> target c\<^sub>1 \<leftrightarrow> e"
  apply clarsimp
  apply (rule directly_tgs_connected_comm)
  apply (drule (2) take_caps_directly_tgs_connected)
  done

lemma grant_legal_directly_tgs_connected:
  "legal (SysGrant e c\<^sub>1 c\<^sub>2 r) s \<Longrightarrow> s \<turnstile> e \<leftrightarrow> target c\<^sub>1"
  apply clarsimp
  apply (drule (2) grant_caps_directly_tgs_connected)
  done

lemma copy_legal_directly_tgs_connected:
  "legal (SysCopy e c\<^sub>1 c\<^sub>2 r) s \<Longrightarrow> s \<turnstile> e \<leftrightarrow> target c\<^sub>1"
  apply clarsimp
  apply (drule (1) store_caps_store_connected)
  apply (drule (1) store_connected_directly_tgs_connected)
  done

lemma caps_of_create:
  "\<lbrakk>c' \<in> caps_of (createOperation e c\<^sub>1 c\<^sub>2 s) x; legal (SysCreate e c\<^sub>1 c\<^sub>2) s\<rbrakk>
  \<Longrightarrow> \<exists>z. (x,z) \<in> tgs_connected s \<and> c' \<in>cap caps_of s z"
  apply (frule create_legal_directly_tgs_connected)
  apply (clarsimp simp: create_general)
  apply (drule caps_of_make_entity2 [rotated], clarsimp)
  apply (drule (1) caps_of_generalOp)
   apply (drule (2) directly_tgs_connected_comm)
  done

lemma caps_of_take:
  "\<lbrakk>c' \<in> caps_of (takeOperation e c\<^sub>1 c\<^sub>2 r s) x; legal (SysTake e c\<^sub>1 c\<^sub>2 r) s\<rbrakk>
  \<Longrightarrow> \<exists>z. (x,z) \<in> tgs_connected s \<and> c' \<in>cap caps_of s z"
  apply (frule take_legal_directly_tgs_connected)
  apply (clarsimp simp: take_general)
  apply (drule (2) caps_of_generalOp)
   apply (drule (1) directly_tgs_connected_comm)
  done

lemma caps_of_grant:
  "\<lbrakk>c' \<in> caps_of (grantOperation e c\<^sub>1 c\<^sub>2 r s) x; legal (SysGrant e c\<^sub>1 c\<^sub>2 r) s\<rbrakk>
  \<Longrightarrow> \<exists>z. (x,z) \<in> tgs_connected s \<and> c' \<in>cap caps_of s z"
  apply (frule grant_legal_directly_tgs_connected)
  apply (clarsimp simp: grant_general)
  apply (drule (2) caps_of_generalOp)
   apply (drule (1) directly_tgs_connected_comm)
  done

lemma caps_of_copy:
  "\<lbrakk>c' \<in> caps_of (copyOperation e c\<^sub>1 c\<^sub>2 r s) x; legal (SysCopy e c\<^sub>1 c\<^sub>2 r) s\<rbrakk>
  \<Longrightarrow> \<exists>z. (x,z) \<in> tgs_connected s \<and> c' \<in>cap caps_of s z"
  apply (frule copy_legal_directly_tgs_connected)
  apply (clarsimp simp: copy_general)
  apply (drule (2) caps_of_generalOp)
   apply (drule (1) directly_tgs_connected_comm)
  done

lemma create_directly_tgs_connected:
 "\<lbrakk>createOperation e c\<^sub>1 c\<^sub>2 s \<turnstile> x \<leftrightarrow> y; legal (SysCreate e c\<^sub>1 c\<^sub>2) s\<rbrakk>
  \<Longrightarrow> s \<turnstile> x \<leftrightarrow>* y"
  apply (frule create_legal_directly_tgs_connected)
  apply (clarsimp simp: create_general)
  apply (drule directly_tgs_connected_make_entity2 [rotated], clarsimp)
  apply (drule (1) generalOp_directly_tgs_connected)
   apply (drule (2) directly_tgs_connected_comm)
  done

lemma take_directly_tgs_connected:
 "\<lbrakk>takeOperation e c\<^sub>1 c\<^sub>2 r s \<turnstile> x \<leftrightarrow> y; legal (SysTake e c\<^sub>1 c\<^sub>2 r) s\<rbrakk>
  \<Longrightarrow> s \<turnstile> x \<leftrightarrow>* y"
  apply (frule take_legal_directly_tgs_connected)
  apply (clarsimp simp: take_general)
  apply (drule (3) generalOp_directly_tgs_connected)
  done

lemma grant_directly_tgs_connected:
 "\<lbrakk>grantOperation e c\<^sub>1 c\<^sub>2 r s \<turnstile> x \<leftrightarrow> y; legal (SysGrant e c\<^sub>1 c\<^sub>2 r) s\<rbrakk>
  \<Longrightarrow> s \<turnstile> x \<leftrightarrow>* y"
  apply (frule grant_legal_directly_tgs_connected)
  apply (clarsimp simp: grant_general)
  apply (drule (3) generalOp_directly_tgs_connected)
  done

lemma copy_directly_tgs_connected:
 "\<lbrakk>copyOperation e c\<^sub>1 c\<^sub>2 r s \<turnstile> x \<leftrightarrow> y; legal (SysCopy e c\<^sub>1 c\<^sub>2 r) s\<rbrakk>
  \<Longrightarrow> s \<turnstile> x \<leftrightarrow>* y"
  apply (frule copy_legal_directly_tgs_connected)
  apply (clarsimp simp: copy_general)
  apply (drule (3) generalOp_directly_tgs_connected)
  done



lemma create_conTrans:
  "\<lbrakk>s' \<in> step cmd s; (x, y) \<in> directly_tgs_connected s'; cmd = (SysCreate e c\<^sub>1 c\<^sub>2)\<rbrakk>
  \<Longrightarrow> (x, y) \<in> tgs_connected s"
  apply(clarsimp simp: step_def split: if_split_asm)
   apply (erule disjE, fastforce simp: tgs_connected_def, clarsimp)
   apply (drule create_directly_tgs_connected, clarsimp, assumption)
  apply (simp add: tgs_connected_def)
  done

lemma take_conTrans:
  "\<lbrakk>s' \<in> step cmd s; (x, y) \<in> directly_tgs_connected s'; cmd = (SysTake e c\<^sub>1 c\<^sub>2 r)\<rbrakk>
  \<Longrightarrow> (x, y) \<in> tgs_connected s"
  apply(clarsimp simp: step_def split: if_split_asm)
   apply (erule disjE, fastforce simp: tgs_connected_def, clarsimp)
   apply (drule take_directly_tgs_connected, clarsimp, assumption)
  apply (simp add: tgs_connected_def)
  done

lemma grant_conTrans:
  "\<lbrakk>s' \<in> step cmd s; (x, y) \<in> directly_tgs_connected s'; cmd = (SysGrant e c\<^sub>1 c\<^sub>2 r)\<rbrakk>
  \<Longrightarrow> (x, y) \<in> tgs_connected s"
  apply(clarsimp simp: step_def split: if_split_asm)
   apply (erule disjE, fastforce simp: tgs_connected_def, clarsimp)
   apply (drule grant_directly_tgs_connected, clarsimp, assumption)
  apply (simp add: tgs_connected_def)
  done

lemma copy_conTrans:
  "\<lbrakk>s' \<in> step cmd s; (x, y) \<in> directly_tgs_connected s'; cmd = (SysCopy e c\<^sub>1 c\<^sub>2 r)\<rbrakk>
  \<Longrightarrow> (x, y) \<in> tgs_connected s"
  apply(clarsimp simp: step_def split: if_split_asm)
   apply (erule disjE, fastforce simp: tgs_connected_def, clarsimp)
   apply (drule copy_directly_tgs_connected, clarsimp, assumption)
  apply (simp add: tgs_connected_def)
  done

(* Lemmas about destroy *)

lemma direct_caps_of_destroy:
  "c \<in> direct_caps_of (s(e := None)) x \<Longrightarrow> c \<in> direct_caps_of s x"
  by (simp add: direct_caps_of_def split: option.splits split: if_split_asm)

lemma store_connected_destroy:
 "(x, y) \<in> store_connected (s(e := None)) \<Longrightarrow> (x, y) \<in> store_connected s"
  apply (simp add: store_connected_def)
  apply (erule rtrancl_induct)
   apply simp
  apply (fold store_connected_def)
  apply (subgoal_tac "(y,z) \<in> store_connected_direct s")
   apply (fastforce simp: store_connected_def)
  apply (simp add: store_connected_direct_def)
  apply clarsimp
  by (metis direct_caps_of_destroy)

lemma shares_caps_destroy:
  "shares_caps (destroyOperation e c s) x y
  \<Longrightarrow> shares_caps s x y"
  apply (clarsimp simp: shares_caps_def destroyOperation_def)
  apply (frule store_connected_destroy [where x=x])
  apply (drule store_connected_destroy [where x=y])
  by auto

lemma caps_of_destroy:
  "c \<in> caps_of (destroyOperation e' c' s) e \<Longrightarrow>
  c \<in> caps_of s e"
  apply (clarsimp simp add: destroyOperation_def caps_of_def)
  apply (rule_tac x=x in exI)
  apply (drule direct_caps_of_destroy)
  apply simp
  apply (erule store_connected_destroy)
  done

lemma destroy_directly_tgs_connected:
  "\<lbrakk>s' \<in> step (SysDestroy e c) s; (x, y) \<in> directly_tgs_connected s'\<rbrakk> \<Longrightarrow>
  (x, y) \<in> directly_tgs_connected s"
  apply(clarsimp simp: step_def split: if_split_asm)
  apply(erule disjE, simp)
  apply(simp add: directly_tgs_connected_def leak_def)
  apply (erule disjE)
   apply(fastforce simp add: cap_in_caps_def dest!: caps_of_destroy)
  apply (erule disjE)
   apply(fastforce simp add: cap_in_caps_def dest!: caps_of_destroy)
  apply (erule disjE)
   apply (drule shares_caps_destroy, simp)
  apply (erule disjE)
   apply(fastforce simp add: cap_in_caps_def dest!: caps_of_destroy)
  apply (erule disjE)
   apply(fastforce simp add: cap_in_caps_def dest!: caps_of_destroy)
  apply (drule shares_caps_destroy, simp)
  done

lemma destroy_conTrans:
  "\<lbrakk>s' \<in> step cmd s; (x, y) \<in> directly_tgs_connected s'; cmd = (SysDestroy e c)\<rbrakk>
  \<Longrightarrow> (x, y) \<in>  directly_tgs_connected s"
  by(auto dest!: destroy_directly_tgs_connected)


(* lemmas about remove *)

lemma direct_caps_of_remove:
  "c \<in> direct_caps_of (removeOperation e c\<^sub>1 c\<^sub>2 s) x \<Longrightarrow>
  c \<in> direct_caps_of s x"
  by (clarsimp simp: removeOperation_simpler direct_caps_of_def
              split: option.splits if_split_asm)

lemma direct_caps_of_remove_eq:
  "direct_caps_of (removeOperation e c\<^sub>1 c\<^sub>2 s) x =
  ( if   is_entity s (target c\<^sub>1) \<and> x = target c\<^sub>1
   then  direct_caps_of s (target c\<^sub>1) - {c\<^sub>2}
   else  direct_caps_of s x )"
  by(simp add: direct_caps_of_def is_entity_def removeOperation_def)

lemma store_connected_remove [rule_format]:
  "(x, y) \<in> store_connected (s(e \<mapsto> Entity C')) \<Longrightarrow>
  s e = Some (Entity C) \<longrightarrow> C' \<subseteq> C \<longrightarrow> (x, y) \<in> store_connected s"
  apply (unfold store_connected_def)
  apply (erule rtrancl_induct)
   apply simp
  apply clarsimp
  apply (subgoal_tac "(y,z) \<in> store_connected_direct s")
   apply (erule rtrancl_trans)
   apply fastforce
  apply (fold store_connected_def)
  apply (clarsimp simp add: store_connected_direct_def)
  apply (fastforce simp: direct_caps_of_def
                  split: option.splits if_split_asm)
  done

lemma caps_of_remove:
  "c \<in> caps_of (removeOperation e c\<^sub>1 c\<^sub>2 s) x \<Longrightarrow>
  c \<in> caps_of s x"
  apply (clarsimp simp: caps_of_def)
  apply (rule_tac x=xa in exI)
  apply (drule direct_caps_of_remove)
  apply (simp add: removeOperation_simpler
            split: option.splits)
  apply (erule (1) store_connected_remove)
  apply blast
  done

(* Might equal either  "caps s (target c\<^sub>1) - {c\<^sub>2}" or "caps s x" depending if the caps are duplicated.*)
lemma caps_of_remove2:
  "caps_of (removeOperation e c\<^sub>1 c\<^sub>2 s) x \<subseteq> caps_of s x"
  apply(simp add: caps_of_def is_entity_def removeOperation_def direct_caps_of_def)
  apply (clarsimp split: if_split_asm)
   apply (auto dest!: store_connected_remove)
  done

lemma shares_caps_remove:
  "shares_caps (removeOperation e c\<^sub>1 c\<^sub>2 s) x y
  \<Longrightarrow> shares_caps s x y"
  apply (clarsimp simp: shares_caps_def removeOperation_simpler
                 split:option.splits)
  apply (frule (1) store_connected_remove [where x=x], clarsimp)
  apply (drule (1) store_connected_remove [where x=y], clarsimp)
  by auto

lemma remove_directly_tgs_connected:
  "\<lbrakk>s' \<in> step (SysRemove e c\<^sub>1 c\<^sub>2) s; (x, y) \<in> directly_tgs_connected s'\<rbrakk> \<Longrightarrow>
  (x, y) \<in> directly_tgs_connected s"
  apply(simp add: step_def split: if_split_asm)
  apply(erule disjE, simp)
  apply(simp add: directly_tgs_connected_def leak_def)
  apply(simp add: cap_in_caps_def)
  apply(clarsimp)
  apply safe
     prefer 3
     apply (drule shares_caps_remove, simp)
    prefer 5
    apply (drule shares_caps_remove, simp)
   apply(auto dest!: caps_of_remove)
  done

lemma remove_conTrans:
  "\<lbrakk>s' \<in> step cmd s; (x, y) \<in> directly_tgs_connected s'; cmd = (SysRemove e c\<^sub>1 c\<^sub>2)\<rbrakk>
  \<Longrightarrow> (x, y) \<in>  directly_tgs_connected s"
  by(auto dest!: remove_directly_tgs_connected)

lemma direct_caps_of_removeSet:
  "c' \<in> direct_caps_of (removeSetOperation e c C s) x \<Longrightarrow>
  c' \<in> direct_caps_of s x"
  by (clarsimp simp: removeSetOperation_simpler direct_caps_of_def
              split: option.splits if_split_asm)

lemma caps_of_removeSet:
  "c' \<in> caps_of (removeSetOperation e c C s) x \<Longrightarrow>
  c' \<in> caps_of s x"
  apply (clarsimp simp: caps_of_def)
  apply (rule_tac x=xa in exI)
  apply (drule direct_caps_of_removeSet)
  apply (simp add: removeSetOperation_simpler split: option.splits)
  apply (erule (1) store_connected_remove)
  apply blast
  done

lemma shares_caps_removeSet:
  "shares_caps (removeSetOperation e c C s) x y
  \<Longrightarrow> shares_caps s x y"
  apply (clarsimp simp: shares_caps_def removeSetOperation_simpler split:option.splits)
  apply (frule (1) store_connected_remove [where x=x], clarsimp)
  apply (drule (1) store_connected_remove [where x=y], clarsimp)
  by auto

lemma removeSet_connected:
  " \<lbrakk>s' \<in> step (SysRemoveSet e c C) s; s' \<turnstile> x \<leftrightarrow> y\<rbrakk> \<Longrightarrow> s \<turnstile> x \<leftrightarrow> y"
  apply(simp add: step_def split: if_split_asm)
  apply(erule disjE, simp)
  apply(simp add: directly_tgs_connected_def leak_def)
  apply(simp add: cap_in_caps_def)
  apply(clarsimp)
  apply safe
     prefer 3
     apply (drule shares_caps_removeSet, simp)
    prefer 5
    apply (drule shares_caps_removeSet, simp)
   apply (auto dest!: caps_of_removeSet)
  done

lemma removeSet_conTrans:
  "\<lbrakk>s' \<in> step cmd s; s' \<turnstile> x \<leftrightarrow> y; cmd = (SysRemoveSet n c C)\<rbrakk>
  \<Longrightarrow> s \<turnstile> x \<leftrightarrow> y"
  by(auto dest!: removeSet_connected)

(* lemmas about revoke *)
lemma direct_caps_of_removeSetOfCaps:
  "c' \<in> direct_caps_of (removeSetOfCaps cap_map s) x \<Longrightarrow>
  c' \<in> direct_caps_of s x"
  by (clarsimp simp: removeSetOfCaps_def direct_caps_of_def
              split: option.splits if_split_asm)
thm store_connected_remove

lemma store_connected_removeSetOfCaps:
  "(x, y) \<in> store_connected (\<lambda>e. if is_entity s e
                                 then Some (Entity (direct_caps_of s e - cap_map e))
                                 else None) \<Longrightarrow>
    (x, y) \<in> store_connected s"
  apply (unfold store_connected_def)
  apply (erule rtrancl_induct)
   apply simp
  apply (subgoal_tac "(y,z) \<in> store_connected_direct s")
   apply (erule rtrancl_trans)
   apply fastforce
  apply (fold store_connected_def)
  apply (clarsimp simp add: store_connected_direct_def)
  apply (fastforce simp: direct_caps_of_def
                  split: option.splits if_split_asm)
  done

lemma caps_of_removeSetOfCaps:
  "c' \<in> caps_of (removeSetOfCaps cap_map s) x \<Longrightarrow>
  c' \<in> caps_of s x"
  apply (clarsimp simp: caps_of_def)
  apply (rule_tac x=xa in exI)
  apply (drule direct_caps_of_removeSetOfCaps)
  apply (simp add: removeSetOfCaps_def split: option.splits)
  apply (erule store_connected_removeSetOfCaps)
  done

lemma caps_of_revoke:
  "\<lbrakk>s' \<in> revokeOperation sub c\<^sub>1 s ;  c \<in> caps_of s' e \<rbrakk>
  \<Longrightarrow> c \<in> caps_of s e"
  apply (clarsimp simp: revokeOperation_def
                 split: if_split_asm)
  apply (drule (1) caps_of_removeSetOfCaps)
  done

lemma direct_caps_of_revoke:
  "\<lbrakk>s' \<in> revokeOperation e c s; c' \<in> direct_caps_of s' x\<rbrakk>
   \<Longrightarrow> c' \<in> direct_caps_of s x"
  apply (clarsimp simp: revokeOperation_def
                 split: if_split_asm)
  apply (drule (1) direct_caps_of_removeSetOfCaps)
  done

lemma store_connected_revoke:
 "\<lbrakk>(x, y) \<in> store_connected s'; s' \<in> revokeOperation e c s\<rbrakk>
  \<Longrightarrow> (x, y) \<in> store_connected s"
  apply (simp add: store_connected_def)
  apply (erule rtrancl_induct)
   apply simp
  apply (fold store_connected_def)
  apply (subgoal_tac "(y,z) \<in> store_connected_direct s")
   apply (fastforce simp: store_connected_def)
  apply (clarsimp simp: store_connected_direct_def)
  apply (metis direct_caps_of_revoke)
  done

lemma shares_caps_revoke:
  "\<lbrakk>shares_caps s' x y; s' \<in> revokeOperation e c s\<rbrakk>
  \<Longrightarrow> shares_caps s x y"
  apply (clarsimp simp: shares_caps_def)
  apply (frule (1) store_connected_revoke [where x=x])
  apply (drule (1) store_connected_revoke [where x=y])
  by auto

lemma removeOperation_entity_ids [simp]:
  "is_entity (removeOperation e c c' s) e' = is_entity s e'"
  by (simp add: is_entity_def removeOperation_def)

lemma removeSetOfCaps_entity_ids [simp]:
  "is_entity (removeSetOfCaps cap_map s) e' = is_entity s e'"
  by (simp add: is_entity_def removeSetOfCaps_def)

lemma revoke_entities:
  "s' \<in> revokeOperation sub c\<^sub>1 s \<Longrightarrow> is_entity s' e = is_entity s e"
  by (clarsimp simp: revokeOperation_def split: if_split_asm)

lemma revoke_directly_tgs_connected:
  "\<lbrakk>s' \<in> step (SysRevoke n c\<^sub>1) s; (x, y) \<in> directly_tgs_connected s'\<rbrakk>
  \<Longrightarrow> (x, y) \<in>  directly_tgs_connected s"
  apply (simp add: step_def split: if_split_asm)
  apply (erule disjE, simp)
  apply (simp add: directly_tgs_connected_def leak_def)
  apply (erule disjE)
   apply(auto simp add: cap_in_caps_def dest!: caps_of_revoke)[1]
  apply (erule disjE)
   apply(auto simp add: cap_in_caps_def dest!: caps_of_revoke)[1]
  apply (erule disjE)
   apply (drule (1) shares_caps_revoke, simp)
  apply (erule disjE)
   apply(auto simp add: cap_in_caps_def dest!: caps_of_revoke)[1]
  apply (erule disjE)
   apply(auto simp add: cap_in_caps_def dest!: caps_of_revoke)[1]
  apply (drule (1) shares_caps_revoke, simp)
  done

lemma revoke_conTrans:
  "\<lbrakk>s' \<in> step cmd s; (x, y) \<in> directly_tgs_connected s'; cmd = (SysRevoke n c\<^sub>1)\<rbrakk>
  \<Longrightarrow> (x, y) \<in>  directly_tgs_connected s"
  by(auto dest!: revoke_directly_tgs_connected)



(* lemmas about grant *)

lemma is_entity_grant [simp]:
  "is_entity s (target c\<^sub>1) \<Longrightarrow>
  is_entity (grantOperation e c\<^sub>1 c\<^sub>2 r s) e' = is_entity s e'"
  by (simp add: is_entity_def grantOperation_def)

lemma is_entity_destroy:
  "is_entity (destroyOperation e' c s) e \<Longrightarrow> is_entity s e"
  by (simp add: destroyOperation_def is_entity_def split: if_split_asm)


(********************************************
 ********************************************
 ***** Connected transitively preserved *****
 ********************************************
 ********************************************)

lemma connected_tgs_connected:
  "\<lbrakk>s' \<in> step cmd s; (e\<^sub>x, e\<^sub>y) \<in> directly_tgs_connected s'\<rbrakk> \<Longrightarrow>
  (e\<^sub>x, e\<^sub>y) \<in> tgs_connected s"
  apply(case_tac "(e\<^sub>x, e\<^sub>y) \<in> directly_tgs_connected s")
   apply(simp add: tgs_connected_def)
   apply(case_tac cmd)
         apply(rule create_conTrans, fastforce+)
        apply(rule take_conTrans, fastforce+)
       apply(rule grant_conTrans, fastforce+)
      apply(frule copy_conTrans, fastforce+)
     apply(frule remove_conTrans, fastforce+)
    apply(frule removeSet_conTrans, fastforce+)
   apply(frule revoke_conTrans, fastforce+)
  apply(frule destroy_conTrans, fastforce+)
  done

lemma tgs_connected_preserved_step:
  "\<lbrakk>s' \<in> step cmd s; s' \<turnstile> x \<leftrightarrow>* z\<rbrakk> \<Longrightarrow> s \<turnstile> x \<leftrightarrow>* z"
  thm rtrancl_induct [where r="directly_tgs_connected s'" and a=x and b=z and P="\<lambda>z. (x, z) \<in> (directly_tgs_connected s)\<^sup>*", simplified,
                      simplified tgs_connected_def [symmetric]]
  apply(erule rtrancl_induct [where r="directly_tgs_connected s'",
                              simplified tgs_connected_def [symmetric]], simp)
  apply(case_tac "s \<turnstile> y \<leftrightarrow>* z")
   apply (erule (1) tgs_connected_trans)
  apply (simp add: connected_tgs_connected)
  done

lemma leakImplyConnected:
  "leak s\<^sub>i e\<^sub>x e\<^sub>i \<Longrightarrow> (e\<^sub>x, e\<^sub>i) \<in> directly_tgs_connected s\<^sub>i"
 by(simp add: directly_tgs_connected_def)

lemma leakImplyConnectedTrans:
  "leak s\<^sub>i e\<^sub>x e\<^sub>i \<Longrightarrow> (e\<^sub>x, e\<^sub>i) \<in> tgs_connected s\<^sub>i"
  by(simp add: tgs_connected_def, frule leakImplyConnected, auto)


lemma tgs_connected_preserved [rule_format]:
  "\<forall>s'. s' \<in> execute cmds s \<longrightarrow>
    s' \<turnstile> x \<leftrightarrow>* y \<longrightarrow>
    s \<turnstile> x \<leftrightarrow>* y"
  apply(induct_tac cmds, simp)
  apply clarsimp
  apply(rename_tac cmd cmds s'' s')
  apply(erule_tac x=s' in allE)
  apply(simp add: tgs_connected_preserved_step)
  done

lemma leak_conTrans [rule_format]:
  "\<lbrakk>s \<in> execute cmds s\<^sub>0; leak s x y\<rbrakk>
  \<Longrightarrow> (x, y) \<in> tgs_connected s\<^sub>0"
  by (auto intro: leakImplyConnectedTrans tgs_connected_preserved)

lemma leakage_rule:
  "\<lbrakk>s' \<in> execute cmds s; \<not> s \<turnstile> x \<leftrightarrow>* y\<rbrakk> \<Longrightarrow> \<not> (s' \<turnstile> x \<rightarrow> y)"
  by(auto simp add: leak_conTrans)




(*******************************************
 *******************************************
 *****      Authority confinement     *****
 *******************************************
 *******************************************)

lemma caps_of_op:
  "\<lbrakk>s' \<in> step cmd s; c' \<in> caps_of s' x\<rbrakk>
  \<Longrightarrow> \<exists>z. s \<turnstile> x \<leftrightarrow>* z \<and> c' \<in>cap caps_of s z"
  apply (simp add: step_def split:if_split_asm)
   prefer 2
   apply (fastforce simp: cap_in_caps_def tgs_connected_def rights_extra_rights)
  apply (erule disjE)
   apply (fastforce simp: cap_in_caps_def tgs_connected_def rights_extra_rights)
  apply (case_tac cmd)
         apply (simp add: caps_of_create)
        apply (simp add: caps_of_take)
       apply (simp add: caps_of_grant)
      apply (simp add: caps_of_copy)
     apply (clarsimp, drule caps_of_remove)
     apply (fastforce simp: cap_in_caps_def tgs_connected_def rights_extra_rights)
    apply (clarsimp, drule caps_of_removeSet)
    apply (fastforce simp: cap_in_caps_def tgs_connected_def rights_extra_rights)
   apply (clarsimp, drule (1) caps_of_revoke)
   apply (fastforce simp: cap_in_caps_def tgs_connected_def rights_extra_rights)
  apply (clarsimp, drule caps_of_destroy)
  apply (fastforce simp: cap_in_caps_def tgs_connected_def rights_extra_rights)
  done

lemma authority_confinement_induct_step:
  "\<lbrakk>s' \<in> step cmd s;
    \<forall>e\<^sub>i. s \<turnstile> e\<^sub>x \<leftrightarrow>* e\<^sub>i \<longrightarrow> caps_of s e\<^sub>i \<le>cap c\<rbrakk>
  \<Longrightarrow> caps_of s' e\<^sub>x \<le>cap c"
  apply (clarsimp simp: caps_dominated_by_def)
  apply (drule (1) caps_of_op)
  apply (fastforce simp: cap_in_caps_def)
  done

lemma authority_confinement_helper:
  "s' \<in> execute cmds s \<longrightarrow>
   (\<forall>e\<^sub>i. s \<turnstile> e\<^sub>x \<leftrightarrow>* e\<^sub>i \<longrightarrow> caps_of s e\<^sub>i \<le>cap c) \<longrightarrow>
   (\<forall>e\<^sub>i. s' \<turnstile> e\<^sub>x \<leftrightarrow>* e\<^sub>i \<longrightarrow> caps_of s' e\<^sub>i \<le>cap c)"
proof (induct cmds arbitrary: s')
case Nil
  show ?case by clarsimp
next
case (Cons cmd cmds s')
show ?case
  apply clarsimp
  apply (rule authority_confinement_induct_step, assumption)
  apply clarsimp
  apply (rule Cons.hyps[rule_format], simp_all)
  apply (drule(1) tgs_connected_preserved_step)
  apply (simp add: tgs_connected_def)
  done
qed

lemma authority_confinement:
  "\<lbrakk>s' \<in> execute cmds s;
    \<forall>e\<^sub>i. s \<turnstile> e\<^sub>x \<leftrightarrow>* e\<^sub>i \<longrightarrow> caps_of s e\<^sub>i \<le>cap c\<rbrakk>
  \<Longrightarrow> caps_of s' e\<^sub>x \<le>cap c"
  by (erule authority_confinement_helper [rule_format, where e\<^sub>x=e\<^sub>x], simp_all)

end
