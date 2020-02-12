(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

chapter \<open>More properties of maps plus map disjuction.\<close>

theory MapExtra
imports Main
begin

text \<open>
  BEWARE: we are not interested in using the @{term "dom x \<inter> dom y = {}"}
  rules from Map for our separation logic proofs. As such, we overwrite the
  Map rules where that form of disjointness is in the assumption conflicts
  with a name we want to use with @{text "\<bottom>"}.\<close>

text \<open>
  A note on naming:
  Anything not involving heap disjuction can potentially be incorporated
  directly into Map.thy, thus uses @{text "m"}.
  Anything involving heap disjunction is not really mergeable with Map, is
  destined for use in separation logic, and hence uses @{text "h"}
\<close>

text \<open>---------------------------------------\<close>
text \<open>Things that should go into Option Type\<close>
text \<open>---------------------------------------\<close>

text \<open>Misc option lemmas\<close>

lemma None_not_eq: "(None \<noteq> x) = (\<exists>y. x = Some y)" by (cases x) auto

lemma None_com: "(None = x) = (x = None)" by fast

lemma Some_com: "(Some y = x) = (x = Some y)" by fast

text \<open>---------------------------------------\<close>
text \<open>Things that should go into Map.thy\<close>
text \<open>---------------------------------------\<close>

text \<open>Map intersection: set of all keys for which the maps agree.\<close>

definition
  map_inter :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> 'a set" (infixl "\<inter>\<^sub>m" 70) where
  "m\<^sub>1 \<inter>\<^sub>m m\<^sub>2 \<equiv> {x \<in> dom m\<^sub>1. m\<^sub>1 x = m\<^sub>2 x}"

text \<open>Map restriction via domain subtraction\<close>

definition
  sub_restrict_map :: "('a \<rightharpoonup> 'b) => 'a set => ('a \<rightharpoonup> 'b)" (infixl "`-"  110)
  where
  "m `- S \<equiv> (\<lambda>x. if x \<in> S then None else m x)"

subsection \<open>Properties of maps not related to restriction\<close>

lemma empty_forall_equiv: "(m = Map.empty) = (\<forall>x. m x = None)"
  by (rule fun_eq_iff)

lemma map_le_empty2 [simp]:
  "(m \<subseteq>\<^sub>m Map.empty) = (m = Map.empty)"
  by (auto simp: map_le_def)

lemma dom_iff:
  "(\<exists>y. m x = Some y) = (x \<in> dom m)"
  by auto

lemma non_dom_eval:
  "x \<notin> dom m \<Longrightarrow> m x = None"
  by auto

lemma non_dom_eval_eq:
  "x \<notin> dom m = (m x = None)"
  by auto

lemma map_add_same_left_eq:
  "m\<^sub>1 = m\<^sub>1' \<Longrightarrow> (m\<^sub>0 ++ m\<^sub>1 = m\<^sub>0 ++ m\<^sub>1')"
  by simp

lemma map_add_left_cancelI [intro!]:
  "m\<^sub>1 = m\<^sub>1' \<Longrightarrow> m\<^sub>0 ++ m\<^sub>1 = m\<^sub>0 ++ m\<^sub>1'"
  by simp

lemma dom_empty_is_empty:
  "(dom m = {}) = (m = Map.empty)"
proof (rule iffI)
  assume a: "dom m = {}"
  { assume "m \<noteq> Map.empty"
    hence "dom m \<noteq> {}"
      by - (subst (asm) empty_forall_equiv, simp add: dom_def)
    hence False using a by blast
  }
  thus "m = Map.empty" by blast
next
  assume a: "m = Map.empty"
  thus "dom m = {}" by simp
qed

lemma map_add_dom_eq:
  "dom m = dom m' \<Longrightarrow> m ++ m' = m'"
  by (rule ext) (auto simp: map_add_def split: option.splits)

lemma map_add_right_dom_eq:
  "\<lbrakk> m\<^sub>0 ++ m\<^sub>1 = m\<^sub>0' ++ m\<^sub>1'; dom m\<^sub>1 = dom m\<^sub>1' \<rbrakk> \<Longrightarrow> m\<^sub>1 = m\<^sub>1'"
  unfolding map_add_def
  by (rule ext, rule ccontr,
      drule_tac x=x in fun_cong, clarsimp split: option.splits,
      drule sym, drule sym, force+)

lemma map_le_same_dom_eq:
  "\<lbrakk> m\<^sub>0 \<subseteq>\<^sub>m m\<^sub>1 ; dom m\<^sub>0 = dom m\<^sub>1 \<rbrakk> \<Longrightarrow> m\<^sub>0 = m\<^sub>1"
  by (simp add: map_le_antisym map_le_def)

subsection \<open>Properties of map restriction\<close>

lemma restrict_map_cancel:
  "(m |` S = m |` T) = (dom m \<inter> S = dom m \<inter> T)"
  by (fastforce intro: set_eqI dest: fun_cong
               simp: restrict_map_def None_not_eq
               split: if_split_asm)

lemma map_add_restricted_self [simp]:
  "m ++ m |` S = m"
  by (auto simp: restrict_map_def map_add_def split: option.splits)

lemma map_add_restrict_dom_right [simp]:
  "(m ++ m') |` dom m' = m'"
  by (rule ext, auto simp: restrict_map_def map_add_def split: option.splits)

lemma restrict_map_UNIV [simp]:
  "m |` UNIV = m"
  by (simp add: restrict_map_def)

lemma restrict_map_dom:
  "S = dom m \<Longrightarrow> m |` S = m"
  by (fastforce simp: restrict_map_def None_not_eq)

lemma restrict_map_subdom:
  "dom m \<subseteq> S \<Longrightarrow> m |` S = m"
  by (fastforce simp: restrict_map_def None_com)

lemma map_add_restrict:
  "(m\<^sub>0 ++ m\<^sub>1) |` S = ((m\<^sub>0 |` S) ++ (m\<^sub>1 |` S))"
  by (force simp: map_add_def restrict_map_def)

lemma map_le_restrict:
  "m \<subseteq>\<^sub>m m' \<Longrightarrow> m = m' |` dom m"
  by (force simp: map_le_def restrict_map_def None_com)

lemma restrict_map_le:
  "m |` S \<subseteq>\<^sub>m m"
  by (auto simp: map_le_def)

lemma restrict_map_remerge:
  "\<lbrakk> S \<inter> T = {} \<rbrakk> \<Longrightarrow> m |` S ++ m |` T = m |` (S \<union> T)"
  by (rule ext, clarsimp simp: restrict_map_def map_add_def
                         split: option.splits)

lemma restrict_map_empty:
  "dom m \<inter> S = {} \<Longrightarrow> m |` S = Map.empty"
  by (fastforce simp: restrict_map_def)

lemma map_add_restrict_comp_right [simp]:
  "(m |` S ++ m |` (UNIV - S)) = m"
  by (force simp: map_add_def restrict_map_def split: option.splits)

lemma map_add_restrict_comp_right_dom [simp]:
  "(m |` S ++ m |` (dom m - S)) = m"
  by (fastforce simp: map_add_def restrict_map_def split: option.splits)

lemma map_add_restrict_comp_left [simp]:
  "(m |` (UNIV - S) ++ m |` S) = m"
  by (subst map_add_comm, auto)

lemma restrict_self_UNIV:
  "m |` (dom m - S) = m |` (UNIV - S)"
  by (fastforce simp: restrict_map_def)

lemma map_add_restrict_nonmember_right:
  "x \<notin> dom m' \<Longrightarrow> (m ++ m') |` {x} = m |` {x}"
  by (rule ext, auto simp: restrict_map_def map_add_def split: option.splits)

lemma map_add_restrict_nonmember_left:
  "x \<notin> dom m \<Longrightarrow> (m ++ m') |` {x} = m' |` {x}"
  by (rule ext, auto simp: restrict_map_def map_add_def split: option.splits)

lemma map_add_restrict_right:
  "x \<subseteq> dom m' \<Longrightarrow> (m ++ m') |` x = m' |` x"
  by (rule ext, auto simp: restrict_map_def map_add_def split: option.splits)

lemma restrict_map_compose:
  "\<lbrakk> S \<union> T = dom m ; S \<inter> T = {} \<rbrakk> \<Longrightarrow> m |` S ++ m |` T = m"
  by (fastforce simp: map_add_def restrict_map_def)

lemma map_le_dom_subset_restrict:
  "\<lbrakk> m' \<subseteq>\<^sub>m m; dom m' \<subseteq> S \<rbrakk> \<Longrightarrow> m' \<subseteq>\<^sub>m (m |` S)"
  by (force simp: restrict_map_def map_le_def)

lemma map_le_dom_restrict_sub_add:
  "m' \<subseteq>\<^sub>m m \<Longrightarrow> m |` (dom m - dom m') ++ m' = m"
  by (metis map_add_restrict_comp_right_dom map_le_iff_map_add_commute map_le_restrict)

lemma subset_map_restrict_sub_add:
  "T \<subseteq> S \<Longrightarrow> m |` (S - T) ++ m |` T = m |` S"
  by (fastforce simp: restrict_map_def map_add_def split: option.splits)

lemma restrict_map_sub_union:
  "m |` (dom m - (S \<union> T)) = (m |` (dom m - T)) |` (dom m - S)"
  by (auto simp: restrict_map_def)

lemma prod_restrict_map_add:
  "\<lbrakk> S \<union> T = U; S \<inter> T = {} \<rbrakk> \<Longrightarrow> m |` (X \<times> S) ++ m |` (X \<times> T) = m |` (X \<times> U)"
  by (auto simp: map_add_def restrict_map_def split: option.splits)


text \<open>---------------------------------------\<close>
text \<open>Things that should NOT go into Map.thy\<close>
text \<open>---------------------------------------\<close>

section \<open>Definitions\<close>

text \<open>Map disjuction\<close>

definition
  map_disj :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> bool" (infix "\<bottom>" 51) where
  "h\<^sub>0 \<bottom> h\<^sub>1 \<equiv> dom h\<^sub>0 \<inter> dom h\<^sub>1 = {}"

declare None_not_eq [simp]

text \<open>Heap monotonicity and the frame property\<close>

definition
  heap_mono :: "(('a \<rightharpoonup> 'b) \<Rightarrow> 'c option) \<Rightarrow> bool" where
  "heap_mono f \<equiv> \<forall>h h' v. h \<bottom> h' \<and> f h = Some v \<longrightarrow> f (h ++ h') = Some v"

lemma heap_monoE:
  "\<lbrakk> heap_mono f ; f h = Some v ; h \<bottom> h' \<rbrakk> \<Longrightarrow> f (h ++ h') = Some v"
  unfolding heap_mono_def by blast

lemma heap_mono_simp:
  "\<lbrakk> heap_mono f ; f h = Some v ; h \<bottom> h' \<rbrakk> \<Longrightarrow> f (h ++ h') = f h"
  by (frule (2) heap_monoE, simp)

definition
  heap_frame :: "(('a \<rightharpoonup> 'b) \<Rightarrow> 'c option) \<Rightarrow> bool" where
  "heap_frame f \<equiv> \<forall>h h' v. h \<bottom> h' \<and> f (h ++ h') = Some v
                           \<longrightarrow> (f h = Some v \<or> f h = None)"

lemma heap_frameE:
  "\<lbrakk> heap_frame f ; f (h ++ h') = Some v ; h \<bottom> h' \<rbrakk>
   \<Longrightarrow> f h = Some v \<or> f h = None"
  unfolding heap_frame_def by fastforce


section \<open>Properties of @{term "sub_restrict_map"}\<close>

lemma restrict_map_sub_disj: "h |` S \<bottom> h `- S"
  by (fastforce simp: sub_restrict_map_def restrict_map_def map_disj_def
               split: option.splits if_split_asm)

lemma restrict_map_sub_add: "h |` S ++ h `- S = h"
  by (fastforce simp: sub_restrict_map_def restrict_map_def map_add_def
               split: option.splits if_split)


section \<open>Properties of map disjunction\<close>

lemma map_disj_empty_right [simp]:
  "h \<bottom> Map.empty"
  by (simp add: map_disj_def)

lemma map_disj_empty_left [simp]:
  "Map.empty \<bottom> h"
  by (simp add: map_disj_def)

lemma map_disj_com:
  "h\<^sub>0 \<bottom> h\<^sub>1 = h\<^sub>1 \<bottom> h\<^sub>0"
  by (simp add: map_disj_def, fast)

lemma map_disjD:
  "h\<^sub>0 \<bottom> h\<^sub>1 \<Longrightarrow> dom h\<^sub>0 \<inter> dom h\<^sub>1 = {}"
  by (simp add: map_disj_def)

lemma map_disjI:
  "dom h\<^sub>0 \<inter> dom h\<^sub>1 = {} \<Longrightarrow> h\<^sub>0 \<bottom> h\<^sub>1"
  by (simp add: map_disj_def)


subsection \<open>Map associativity-commutativity based on map disjuction\<close>

lemma map_add_com:
  "h\<^sub>0 \<bottom> h\<^sub>1 \<Longrightarrow> h\<^sub>0 ++ h\<^sub>1 = h\<^sub>1 ++ h\<^sub>0"
  by (drule map_disjD, rule map_add_comm, force)

lemma map_add_left_commute:
  "h\<^sub>0 \<bottom> h\<^sub>1 \<Longrightarrow> h\<^sub>0 ++ (h\<^sub>1 ++ h\<^sub>2) = h\<^sub>1 ++ (h\<^sub>0 ++ h\<^sub>2)"
  by (simp add: map_add_com map_disj_com)

lemma map_add_disj:
  "h\<^sub>0 \<bottom> (h\<^sub>1 ++ h\<^sub>2) = (h\<^sub>0 \<bottom> h\<^sub>1 \<and> h\<^sub>0 \<bottom> h\<^sub>2)"
  by (simp add: map_disj_def, fast)

lemma map_add_disj':
  "(h\<^sub>1 ++ h\<^sub>2) \<bottom> h\<^sub>0 = (h\<^sub>1 \<bottom> h\<^sub>0 \<and> h\<^sub>2 \<bottom> h\<^sub>0)"
  by (simp add: map_disj_def, fast)

text \<open>
  We redefine @{term "map_add"} associativity to bind to the right, which
  seems to be the more common case.
  Note that when a theory includes Map again, @{text "map_add_assoc"} will
  return to the simpset and will cause infinite loops if its symmetric
  counterpart is added (e.g. via @{text "map_ac_simps"})
\<close>

declare map_add_assoc [simp del]

text \<open>
  Since the associativity-commutativity of @{term "map_add"} relies on
  map disjunction, we include some basic rules into the ac set.
\<close>

lemmas map_ac_simps =
  map_add_assoc[symmetric] map_add_com map_disj_com
  map_add_left_commute map_add_disj map_add_disj'


subsection \<open>Basic properties\<close>

lemma map_disj_None_right:
  "\<lbrakk> h\<^sub>0 \<bottom> h\<^sub>1 ; x \<in> dom h\<^sub>0 \<rbrakk> \<Longrightarrow> h\<^sub>1 x = None"
  by (auto simp: map_disj_def dom_def)

lemma map_disj_None_left:
  "\<lbrakk> h\<^sub>0 \<bottom> h\<^sub>1 ; x \<in> dom h\<^sub>1 \<rbrakk> \<Longrightarrow> h\<^sub>0 x = None"
  by (auto simp: map_disj_def dom_def)

lemma map_disj_None_left':
  "\<lbrakk> h\<^sub>0 x = Some y ; h\<^sub>1 \<bottom> h\<^sub>0 \<rbrakk> \<Longrightarrow> h\<^sub>1 x = None "
  by (auto simp: map_disj_def)

lemma map_disj_None_right':
  "\<lbrakk> h\<^sub>1 x = Some y ; h\<^sub>1 \<bottom> h\<^sub>0 \<rbrakk> \<Longrightarrow> h\<^sub>0 x = None "
  by (auto simp: map_disj_def)

lemma map_disj_common:
  "\<lbrakk> h\<^sub>0 \<bottom> h\<^sub>1 ; h\<^sub>0 p = Some v ; h\<^sub>1 p = Some v' \<rbrakk> \<Longrightarrow> False"
  by (frule (1) map_disj_None_left', simp)


subsection \<open>Map disjunction and addition\<close>

lemma map_add_eval_left:
  "\<lbrakk> x \<in> dom h ; h \<bottom> h' \<rbrakk> \<Longrightarrow> (h ++ h') x = h x"
  by (auto dest!: map_disj_None_right simp: map_add_def cong: option.case_cong)

lemma map_add_eval_right:
  "\<lbrakk> x \<in> dom h' ; h \<bottom> h' \<rbrakk> \<Longrightarrow> (h ++ h') x = h' x"
  by (auto elim!: map_disjD simp: map_add_comm map_add_eval_left map_disj_com)

lemma map_add_eval_left':
  "\<lbrakk> x \<notin> dom h' ; h \<bottom> h' \<rbrakk> \<Longrightarrow> (h ++ h') x = h x"
  by (clarsimp simp: map_disj_def map_add_def split: option.splits)

lemma map_add_eval_right':
  "\<lbrakk> x \<notin> dom h ; h \<bottom> h' \<rbrakk> \<Longrightarrow> (h ++ h') x = h' x"
  by (clarsimp simp: map_disj_def map_add_def split: option.splits)

lemma map_add_left_dom_eq:
  assumes eq: "h\<^sub>0 ++ h\<^sub>1 = h\<^sub>0' ++ h\<^sub>1'"
  assumes etc: "h\<^sub>0 \<bottom> h\<^sub>1" "h\<^sub>0' \<bottom> h\<^sub>1'" "dom h\<^sub>0 = dom h\<^sub>0'"
  shows "h\<^sub>0 = h\<^sub>0'"
proof -
  from eq have "h\<^sub>1 ++ h\<^sub>0 = h\<^sub>1' ++ h\<^sub>0'" using etc by (simp add: map_ac_simps)
  thus ?thesis using etc
    by (fastforce elim!: map_add_right_dom_eq simp: map_ac_simps)
qed

lemma map_add_left_eq:
  assumes eq: "h\<^sub>0 ++ h = h\<^sub>1 ++ h"
  assumes disj: "h\<^sub>0 \<bottom> h" "h\<^sub>1 \<bottom> h"
  shows "h\<^sub>0 = h\<^sub>1"
proof (rule ext)
  fix x
  from eq have eq': "(h\<^sub>0 ++ h) x = (h\<^sub>1 ++ h) x" by auto
  { assume "x \<in> dom h"
    hence "h\<^sub>0 x = h\<^sub>1 x" using disj by (simp add: map_disj_None_left)
  } moreover {
    assume "x \<notin> dom h"
    hence "h\<^sub>0 x = h\<^sub>1 x" using disj eq' by (simp add: map_add_eval_left')
  }
  ultimately show "h\<^sub>0 x = h\<^sub>1 x" by cases
qed


lemma map_add_right_eq:
  "\<lbrakk>h ++ h\<^sub>0 = h ++ h\<^sub>1; h\<^sub>0 \<bottom> h; h\<^sub>1 \<bottom> h\<rbrakk> \<Longrightarrow> h\<^sub>0 = h\<^sub>1"
  by (rule_tac h=h in map_add_left_eq, auto simp: map_ac_simps)

lemma map_disj_add_eq_dom_right_eq:
  assumes merge: "h\<^sub>0 ++ h\<^sub>1 = h\<^sub>0' ++ h\<^sub>1'" and d: "dom h\<^sub>0 = dom h\<^sub>0'" and
      ab_disj: "h\<^sub>0 \<bottom> h\<^sub>1" and cd_disj: "h\<^sub>0' \<bottom> h\<^sub>1'"
  shows "h\<^sub>1 = h\<^sub>1'"
proof (rule ext)
  fix x
  from merge have merge_x: "(h\<^sub>0 ++ h\<^sub>1) x = (h\<^sub>0' ++ h\<^sub>1') x" by simp
  with d ab_disj cd_disj show  "h\<^sub>1 x = h\<^sub>1' x"
    by - (case_tac "h\<^sub>1 x", case_tac "h\<^sub>1' x", simp, fastforce simp: map_disj_def,
          case_tac "h\<^sub>1' x", clarsimp, simp add: Some_com,
          force simp: map_disj_def, simp)
qed

lemma map_disj_add_eq_dom_left_eq:
  assumes add: "h\<^sub>0 ++ h\<^sub>1 = h\<^sub>0' ++ h\<^sub>1'" and
          dom: "dom h\<^sub>1 = dom h\<^sub>1'" and
          disj: "h\<^sub>0 \<bottom> h\<^sub>1" "h\<^sub>0' \<bottom> h\<^sub>1'"
  shows "h\<^sub>0 = h\<^sub>0'"
proof -
  have "h\<^sub>1 ++ h\<^sub>0 = h\<^sub>1' ++ h\<^sub>0'" using add disj by (simp add: map_ac_simps)
  thus ?thesis using dom disj
    by - (rule map_disj_add_eq_dom_right_eq, auto simp: map_disj_com)
qed

lemma map_add_left_cancel:
  assumes disj: "h\<^sub>0 \<bottom> h\<^sub>1" "h\<^sub>0 \<bottom> h\<^sub>1'"
  shows "(h\<^sub>0 ++ h\<^sub>1 = h\<^sub>0 ++ h\<^sub>1') = (h\<^sub>1 = h\<^sub>1')"
proof (rule iffI, rule ext)
  fix x
  assume "(h\<^sub>0 ++ h\<^sub>1) = (h\<^sub>0 ++ h\<^sub>1')"
  hence "(h\<^sub>0 ++ h\<^sub>1) x = (h\<^sub>0 ++ h\<^sub>1') x" by auto
  hence "h\<^sub>1 x = h\<^sub>1' x" using disj
    by - (cases "x \<in> dom h\<^sub>0",
          simp_all add: map_disj_None_right map_add_eval_right')
  thus "h\<^sub>1 x = h\<^sub>1' x" by auto
qed auto

lemma map_add_lr_disj:
  "\<lbrakk> h\<^sub>0 ++ h\<^sub>1 = h\<^sub>0' ++ h\<^sub>1'; h\<^sub>1 \<bottom> h\<^sub>1'  \<rbrakk> \<Longrightarrow> dom h\<^sub>1 \<subseteq> dom h\<^sub>0'"
  by (clarsimp simp: map_disj_def map_add_def, drule_tac x=x in fun_cong)
     (auto split: option.splits)


subsection \<open>Map disjunction and updates\<close>

lemma map_disj_update_left [simp]:
  "p \<in> dom h\<^sub>1 \<Longrightarrow> h\<^sub>0 \<bottom> h\<^sub>1(p \<mapsto> v) = h\<^sub>0 \<bottom> h\<^sub>1"
  by (clarsimp simp add: map_disj_def, blast)

lemma map_disj_update_right [simp]:
  "p \<in> dom h\<^sub>1 \<Longrightarrow> h\<^sub>1(p \<mapsto> v) \<bottom> h\<^sub>0 = h\<^sub>1 \<bottom> h\<^sub>0"
  by (simp add: map_disj_com)

lemma map_add_update_left:
  "\<lbrakk> h\<^sub>0 \<bottom> h\<^sub>1 ; p \<in> dom h\<^sub>0 \<rbrakk> \<Longrightarrow> (h\<^sub>0 ++ h\<^sub>1)(p \<mapsto> v) = (h\<^sub>0(p \<mapsto> v) ++ h\<^sub>1)"
  by (drule (1) map_disj_None_right)
     (auto simp: map_add_def cong: option.case_cong)

lemma map_add_update_right:
  "\<lbrakk> h\<^sub>0 \<bottom> h\<^sub>1 ; p \<in> dom h\<^sub>1  \<rbrakk> \<Longrightarrow> (h\<^sub>0 ++ h\<^sub>1)(p \<mapsto> v) = (h\<^sub>0 ++ h\<^sub>1 (p \<mapsto> v))"
  by (drule (1) map_disj_None_left)
     (auto simp: map_add_def cong: option.case_cong)

lemma map_add3_update:
  "\<lbrakk> h\<^sub>0 \<bottom> h\<^sub>1 ; h\<^sub>1  \<bottom> h\<^sub>2 ; h\<^sub>0 \<bottom> h\<^sub>2 ; p \<in> dom h\<^sub>0 \<rbrakk>
  \<Longrightarrow> (h\<^sub>0 ++ h\<^sub>1 ++ h\<^sub>2)(p \<mapsto> v) = h\<^sub>0(p \<mapsto> v) ++ h\<^sub>1 ++ h\<^sub>2"
  by (auto simp: map_add_update_left[symmetric] map_ac_simps)


subsection \<open>Map disjunction and @{term "map_le"}\<close>

lemma map_le_override [simp]:
  "\<lbrakk> h \<bottom> h' \<rbrakk> \<Longrightarrow> h \<subseteq>\<^sub>m h ++ h'"
  by (auto simp: map_le_def map_add_def map_disj_def split: option.splits)

lemma map_leI_left:
  "\<lbrakk> h = h\<^sub>0 ++ h\<^sub>1 ; h\<^sub>0 \<bottom> h\<^sub>1 \<rbrakk> \<Longrightarrow> h\<^sub>0 \<subseteq>\<^sub>m h" by auto

lemma map_leI_right:
  "\<lbrakk> h = h\<^sub>0 ++ h\<^sub>1 ; h\<^sub>0 \<bottom> h\<^sub>1 \<rbrakk> \<Longrightarrow> h\<^sub>1 \<subseteq>\<^sub>m h" by auto

lemma map_disj_map_le:
  "\<lbrakk> h\<^sub>0' \<subseteq>\<^sub>m h\<^sub>0; h\<^sub>0 \<bottom> h\<^sub>1 \<rbrakk> \<Longrightarrow> h\<^sub>0' \<bottom> h\<^sub>1"
  by (force simp: map_disj_def map_le_def)

lemma map_le_on_disj_left:
  "\<lbrakk> h' \<subseteq>\<^sub>m h ; h\<^sub>0 \<bottom> h\<^sub>1 ; h' = h\<^sub>0 ++ h\<^sub>1 \<rbrakk> \<Longrightarrow> h\<^sub>0 \<subseteq>\<^sub>m h"
  unfolding map_le_def
  by (rule ballI, erule_tac x=a in ballE, auto simp: map_add_eval_left)+

lemma map_le_on_disj_right:
  "\<lbrakk> h' \<subseteq>\<^sub>m h ; h\<^sub>0 \<bottom> h\<^sub>1 ; h' = h\<^sub>1 ++ h\<^sub>0 \<rbrakk> \<Longrightarrow> h\<^sub>0 \<subseteq>\<^sub>m h"
  by (auto simp: map_le_on_disj_left map_ac_simps)

lemma map_le_add_cancel:
  "\<lbrakk> h\<^sub>0 \<bottom> h\<^sub>1 ; h\<^sub>0' \<subseteq>\<^sub>m h\<^sub>0 \<rbrakk> \<Longrightarrow> h\<^sub>0' ++ h\<^sub>1 \<subseteq>\<^sub>m h\<^sub>0 ++ h\<^sub>1"
  by (auto simp: map_le_def map_add_def map_disj_def split: option.splits)

lemma map_le_override_bothD:
  assumes subm: "h\<^sub>0' ++ h\<^sub>1 \<subseteq>\<^sub>m h\<^sub>0 ++ h\<^sub>1"
  assumes disj': "h\<^sub>0' \<bottom> h\<^sub>1"
  assumes disj: "h\<^sub>0 \<bottom> h\<^sub>1"
  shows "h\<^sub>0' \<subseteq>\<^sub>m h\<^sub>0"
unfolding map_le_def
proof (rule ballI)
  fix a
  assume a: "a \<in> dom h\<^sub>0'"
  hence sumeq: "(h\<^sub>0' ++ h\<^sub>1) a = (h\<^sub>0 ++ h\<^sub>1) a"
    using subm unfolding map_le_def by auto
  from a have "a \<notin> dom h\<^sub>1" using disj' by (auto dest!: map_disj_None_right)
  thus "h\<^sub>0' a = h\<^sub>0 a" using a sumeq disj disj'
    by (simp add: map_add_eval_left map_add_eval_left')
qed

lemma map_le_conv:
  "(h\<^sub>0' \<subseteq>\<^sub>m h\<^sub>0 \<and> h\<^sub>0' \<noteq> h\<^sub>0) = (\<exists>h\<^sub>1. h\<^sub>0 = h\<^sub>0' ++ h\<^sub>1 \<and> h\<^sub>0' \<bottom> h\<^sub>1 \<and> h\<^sub>0' \<noteq> h\<^sub>0)"
  unfolding map_le_def map_disj_def map_add_def
  using exI[where x="\<lambda>x. if x \<notin> dom h\<^sub>0' then h\<^sub>0 x else None"]
  by (rule iffI, clarsimp)
     (fastforce intro: set_eqI split: option.splits if_split_asm)+

lemma map_le_conv2:
  "h\<^sub>0' \<subseteq>\<^sub>m h\<^sub>0 = (\<exists>h\<^sub>1. h\<^sub>0 = h\<^sub>0' ++ h\<^sub>1 \<and> h\<^sub>0' \<bottom> h\<^sub>1)"
  by (case_tac "h\<^sub>0'=h\<^sub>0", insert map_le_conv, auto intro: exI[where x=Map.empty])


subsection \<open>Map disjunction and restriction\<close>

lemma map_disj_comp [simp]:
  "h\<^sub>0 \<bottom> h\<^sub>1 |` (UNIV - dom h\<^sub>0)"
  by (force simp: map_disj_def)

lemma restrict_map_disj:
  "S \<inter> T = {} \<Longrightarrow> h |` S \<bottom> h |` T"
  by (auto simp: map_disj_def restrict_map_def dom_def)

lemma map_disj_restrict_dom [simp]:
  "h\<^sub>0 \<bottom> h\<^sub>1 |` (dom h\<^sub>1 - dom h\<^sub>0)"
  by (force simp: map_disj_def)

lemma restrict_map_disj_dom_empty:
  "h \<bottom> h' \<Longrightarrow> h |` dom h' = Map.empty"
  by (fastforce simp: map_disj_def restrict_map_def)

lemma restrict_map_univ_disj_eq:
  "h \<bottom> h' \<Longrightarrow> h |` (UNIV - dom h') = h"
  by (rule ext, auto simp: map_disj_def restrict_map_def)

lemma restrict_map_disj_dom:
  "h\<^sub>0 \<bottom> h\<^sub>1 \<Longrightarrow> h |` dom h\<^sub>0 \<bottom> h |` dom h\<^sub>1"
  by (auto simp: map_disj_def restrict_map_def dom_def)

lemma map_add_restrict_dom_left:
  "h \<bottom> h' \<Longrightarrow> (h ++ h') |` dom h = h"
  by (rule ext, auto simp: restrict_map_def map_add_def dom_def map_disj_def
                     split: option.splits)

lemma restrict_map_disj_left:
  "h\<^sub>0 \<bottom> h\<^sub>1 \<Longrightarrow> h\<^sub>0 |` S \<bottom> h\<^sub>1"
  by (auto simp: map_disj_def)

lemma restrict_map_disj_right:
  "h\<^sub>0 \<bottom> h\<^sub>1 \<Longrightarrow> h\<^sub>0 \<bottom> h\<^sub>1 |` S"
  by (auto simp: map_disj_def)

lemmas restrict_map_disj_both = restrict_map_disj_right restrict_map_disj_left

lemma map_dom_disj_restrict_right:
  "h\<^sub>0 \<bottom> h\<^sub>1 \<Longrightarrow> (h\<^sub>0 ++ h\<^sub>0') |` dom h\<^sub>1 = h\<^sub>0' |` dom h\<^sub>1"
  by (simp add: map_add_restrict restrict_map_empty map_disj_def)

lemma restrict_map_on_disj:
  "h\<^sub>0' \<bottom> h\<^sub>1 \<Longrightarrow> h\<^sub>0 |` dom h\<^sub>0' \<bottom> h\<^sub>1"
  unfolding map_disj_def by auto

lemma restrict_map_on_disj':
  "h\<^sub>0 \<bottom> h\<^sub>1 \<Longrightarrow> h\<^sub>0 \<bottom> h\<^sub>1 |` S"
  by (auto simp: map_disj_def map_add_def)

lemma map_le_sub_dom:
  "\<lbrakk> h\<^sub>0 ++ h\<^sub>1 \<subseteq>\<^sub>m h ; h\<^sub>0 \<bottom> h\<^sub>1 \<rbrakk> \<Longrightarrow> h\<^sub>0 \<subseteq>\<^sub>m h |` (dom h - dom h\<^sub>1)"
  by (rule map_le_override_bothD, subst map_le_dom_restrict_sub_add)
     (auto elim: map_add_le_mapE simp: map_ac_simps)

lemma map_submap_break:
  "\<lbrakk> h \<subseteq>\<^sub>m h' \<rbrakk> \<Longrightarrow> h' = (h' |` (UNIV - dom h)) ++ h"
  by (fastforce split: option.splits
                simp: map_le_restrict restrict_map_def map_le_def map_add_def dom_def)

lemma map_add_disj_restrict_both:
  "\<lbrakk> h\<^sub>0 \<bottom> h\<^sub>1; S \<inter> S' = {}; T \<inter> T' = {} \<rbrakk>
   \<Longrightarrow> (h\<^sub>0 |` S) ++ (h\<^sub>1 |` T) \<bottom> (h\<^sub>0 |` S') ++ (h\<^sub>1 |` T')"
  by (auto simp: map_ac_simps intro!: restrict_map_disj_both restrict_map_disj)

end
