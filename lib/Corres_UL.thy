(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Corres_UL
imports
  Crunch_Instances_NonDet
  Monads.WPEx
  Monads.WPFix
  HaskellLemmaBucket
begin

text \<open>Definition of correspondence\<close>

definition
  corres_underlying :: "(('s \<times> 't) set) \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow>
                        ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow> bool)
           \<Rightarrow> ('s, 'a) nondet_monad \<Rightarrow> ('t, 'b) nondet_monad \<Rightarrow> bool"
where
 "corres_underlying srel nf nf' rrel G G' \<equiv> \<lambda>m m'.
      \<forall>(s, s') \<in> srel. G s \<and> G' s' \<longrightarrow>
           (nf \<longrightarrow> \<not> snd (m s)) \<longrightarrow>
           (\<forall>(r', t') \<in> fst (m' s'). \<exists>(r, t) \<in> fst (m s). (t, t') \<in> srel \<and> rrel r r') \<and>
           (nf' \<longrightarrow> \<not> snd (m' s'))"

text \<open>Base case facts about correspondence\<close>

lemma corres_underlyingI:
  assumes rv: "\<And>s t rv' t'. \<lbrakk>(s, t) \<in> R; P s; P' t; (rv', t') \<in> fst (c t)\<rbrakk>
                            \<Longrightarrow> \<exists>(rv, s') \<in> fst (a s). (s', t') \<in> R \<and> r rv rv'"
  and     nf: "\<And>s t. \<lbrakk>(s, t) \<in> R; P s; P' t; nf'\<rbrakk> \<Longrightarrow> \<not> snd (c t)"
  shows  "corres_underlying R nf nf' r P P' a c"
  unfolding corres_underlying_def using rv nf by (auto simp: split_def)

lemma corres_underlyingE:
  assumes cul: "corres_underlying R nf nf' r P P' a c"
  and     xin: "(s, t) \<in> R" "P s" "P' t" "(rv', t') \<in> fst (c t)"
  and      rl: "\<And>s' rv. \<lbrakk>nf' \<longrightarrow> \<not> snd (c t); (rv, s') \<in> fst (a s); (s', t') \<in> R; r rv rv'\<rbrakk> \<Longrightarrow> Q"
  and      nf: "nf \<longrightarrow> \<not> snd (a s)"
  shows   "Q"
  using cul xin nf
  unfolding corres_underlying_def by (fastforce simp: split_def intro: rl)

lemma corres_underlyingD:
  "\<lbrakk> corres_underlying R nf nf' rs P P' f f'; (s,s') \<in> R; P s; P' s'; nf \<longrightarrow> \<not> snd (f s) \<rbrakk>
  \<Longrightarrow> (\<forall>(r',t')\<in>fst (f' s'). \<exists>(r,t)\<in>fst (f s). (t, t') \<in> R \<and> rs r r') \<and> (nf' \<longrightarrow> \<not> snd (f' s'))"
  by (fastforce simp: corres_underlying_def)

lemma corres_underlyingD2:
  "\<lbrakk> corres_underlying R nf nf' rs P P' f f'; (s,s') \<in> R; P s; P' s'; (r',t')\<in>fst (f' s'); nf \<longrightarrow> \<not> snd (f s) \<rbrakk>
  \<Longrightarrow> \<exists>(r,t)\<in>fst (f s). (t, t') \<in> R \<and> rs r r'"
  by (fastforce dest: corres_underlyingD)

lemma propagate_no_fail:
  "\<lbrakk> corres_underlying S nf True R P P' f f';
        no_fail P f; \<forall>s'. P' s' \<longrightarrow> (\<exists>s. P s \<and> (s,s') \<in> S) \<rbrakk>
  \<Longrightarrow> no_fail P' f'"
  apply (clarsimp simp: corres_underlying_def no_fail_def)
  apply (erule allE, erule (1) impE)
  apply clarsimp
  apply (drule (1) bspec, clarsimp)
  done

lemma corres_underlying_serial:
  "\<lbrakk> corres_underlying S False True rrel G G' m m'; empty_fail m' \<rbrakk> \<Longrightarrow>
     \<forall>s. (\<exists>s'. (s,s') \<in> S \<and> G s \<and> G' s') \<longrightarrow> fst (m s) \<noteq> {}"
  apply (clarsimp simp: corres_underlying_def empty_fail_def)
  apply (drule_tac x="(s, s')" in bspec, simp)
  apply (drule_tac x=s' in spec)
  apply auto
  done

lemma corres_singleton:
 "corres_underlying sr nf nf' r P P' (\<lambda>s. ({(R s, S s)},x)) (\<lambda>s. ({(R' s, S' s)},False))
  = (\<forall>s s'. P s \<and> P' s' \<and> (s, s') \<in> sr \<and> (nf \<longrightarrow> \<not> x)
          \<longrightarrow> ((S s, S' s') \<in> sr \<and> r (R s) (R' s')))"
  by (auto simp: corres_underlying_def)

(* Lemmas that should not be [simp] inside automated corres methods.
   Shared between Corres_Method and CorresK_Method. *)
named_theorems corres_no_simp

(* Safe terminal corres rules that instantiate return relation and guards.
   Shared between Corres_Method and CorresK_Method. *)
named_theorems corres

(* Terminal corres rules that instantiate return relation and guards and that are safe if side
   conditions case be solved immediately. Used in Corres_Method. *)
named_theorems corres_term

lemma corres_return[simp, corres_no_simp]:
  "corres_underlying sr nf nf' r P P' (return a) (return b) =
   ((\<exists>s s'. P s \<and> P' s' \<and> (s, s') \<in> sr) \<longrightarrow> r a b)"
  by (simp add: return_def corres_singleton)

lemma corres_get[simp, corres_no_simp]:
 "corres_underlying sr nf nf' r P P' get get = (\<forall> s s'. (s, s') \<in> sr \<and> P s \<and> P' s' \<longrightarrow> r s s')"
  by (fastforce simp: get_def corres_singleton)

lemma corres_gets[simp, corres_no_simp]:
 "corres_underlying sr nf nf' r P P' (gets a) (gets b) =
  (\<forall> s s'. P s \<and> P' s' \<and> (s, s') \<in> sr \<longrightarrow> r (a s) (b s'))"
  by (simp add: simpler_gets_def corres_singleton)

lemma corres_gets_return:
  "corres_underlying sr nf nf' r P P' (gets f) (return v)
   = (\<forall>s s'. ((s, s') \<in> sr \<and> P s \<and> P' s') \<longrightarrow> r (f s) v)"
  by (fastforce simp: corres_underlying_def gets_def get_def return_def bind_def)

text \<open>A safer non-rewrite version of @{thm corres_gets_return} \<close>
lemma corres_gets_return_trivial:
  "(\<And>s s'. \<lbrakk>(s, s') \<in> sr; P s; P' s'\<rbrakk> \<Longrightarrow> r (f s) v)
   \<Longrightarrow> corres_underlying sr nf nf' r P P' (gets f) (return v)"
  by (fastforce simp: corres_gets_return)

lemma corres_throwError[simp, corres_no_simp]:
  "corres_underlying sr nf nf' r P P' (throwError a) (throwError b) =
   ((\<exists>s s'. P s \<and> P' s' \<and> (s, s') \<in> sr) \<longrightarrow> r (Inl a) (Inl b))"
  by (simp add: throwError_def)

lemma corres_no_failI_base:
  assumes f: "nf \<Longrightarrow> no_fail P f"
  assumes f': "nf' \<Longrightarrow> no_fail P' f'"
  assumes corres: "\<forall>(s, s') \<in> S. P s \<and> P' s' \<longrightarrow>
                     (\<forall>(r', t') \<in> fst (f' s'). \<exists>(r, t) \<in> fst (f s). (t, t') \<in> S \<and> R r r')"
  shows "corres_underlying S nf nf' R P P' f f'"
  using assms by (simp add: corres_underlying_def no_fail_def)

(* This lemma gets the shorter name because many existing proofs want nf=False *)
lemma corres_no_failI:
  assumes f': "nf' \<Longrightarrow> no_fail P' f'"
  assumes corres: "\<forall>(s, s') \<in> S. P s \<and> P' s' \<longrightarrow>
                     (\<forall>(r', t') \<in> fst (f' s'). \<exists>(r, t) \<in> fst (f s). (t, t') \<in> S \<and> R r r')"
  shows "corres_underlying S False nf' R P P' f f'"
  using assms by (simp add: corres_underlying_def no_fail_def)

text \<open>Congruence rules for the correspondence functions.\<close>

(* Rewrite everywhere, with full context. Use when there are no schematic variables. *)
lemma corres_cong:
  assumes "\<And>s. P s = P' s"
  assumes "\<And>s s'. \<lbrakk> (s,s') \<in> sr; P' s \<rbrakk> \<Longrightarrow> Q s' = Q' s'"
  assumes "\<And>s s'. \<lbrakk> (s,s') \<in> sr; P' s; Q' s' \<rbrakk> \<Longrightarrow> f s = f' s"
  assumes "\<And>s s'. \<lbrakk> (s,s') \<in> sr; P' s; Q' s' \<rbrakk>  \<Longrightarrow> g s' = g' s'"
  assumes "\<And>x y s t s' t'. \<lbrakk> P' s; Q' t; (s', t') \<in> sr;
                             (x, s') \<in> fst (f' s); (y, t') \<in> fst (g' t) \<rbrakk> \<Longrightarrow> r x y = r' x y"
  shows   "corres_underlying sr nf nf' r P Q f g = corres_underlying sr nf nf' r' P' Q' f' g'"
  by (force simp: corres_underlying_def assms split_def)

(* Do not rewrite return relation or guards, but do rewrite monads under guard context.
   This should be the default, because it protects potential schematics in return relation
   and guards. *)
lemmas corres_weak_cong = corres_cong[OF refl refl _ _ refl]

(* Even more restrictive: only rewrite monads, no additional context. Occasionally useful *)
lemma corres_weaker_cong:
  assumes "f = f'"
  assumes "g = g'"
  shows   "corres_underlying sr nf nf' r P Q f g = corres_underlying sr nf nf' r P Q f' g'"
  by (simp add: assms cong: corres_cong)

(* Rewrite only the return relation, with context. Occasionally useful: *)
lemmas corres_rel_cong = corres_cong[OF refl refl refl refl]

(* Rewrite only the guards, with the state relation as context. Use when guards are not schematic. *)
lemmas corres_guard_cong = corres_cong[OF _ _ refl refl refl]

bundle corres_default_cong = corres_weak_cong[cong]
bundle corres_cong = corres_cong[cong]
bundle corres_no_cong = corres_cong[cong del]

(* How to use these: *)
experiment
begin

lemma
  assumes cross_rule: "\<And>s s'. \<lbrakk> (s,s') \<in> sr; Q s \<rbrakk> \<Longrightarrow> Q' s'"
  shows "corres_underlying sr nf nf' r (K P and Q) (Q' and K P) (assert P) (do get; assert P od)"
  including corres_no_cong (* current default *)
  apply simp (* simplifies K, but nothing else *)
  including corres_cong
  apply simp (* turns asserts into returns, simplifies pred_and, removes P from rhs guard *)
  apply (simp add: cross_rule) (* turns concrete guard into True *)
  oops

schematic_goal
  "\<And>x y z. \<lbrakk> x = Suc z; y = 0 \<rbrakk> \<Longrightarrow>
   corres_underlying sr nf nf' (?r x y) (\<lambda>s. P z) (?Q x y) (assert (P z)) g"
  including corres_default_cong
  apply simp (* Turns assert into return, but does not touch schematics *)
  including corres_no_cong
  apply simp (* substitutes into schematic params, messy *)
  oops

(* Mixing schematic guards with non-schematic guards only works if the non-schematic guard
   is in the right form already. It explicitly does not get rewritten by the cong rule: *)
schematic_goal
  "\<And>x y z. \<lbrakk> x = Suc z; y = 0 \<rbrakk> \<Longrightarrow>
   corres_underlying sr nf nf' (?r x y) (K P) (?Q x y) (assert P) (do assert P; g od)"
  including corres_default_cong
  apply simp (* Only rewrite K_bind, because (K P) does not get rewritten
                before it can be applied to (assert P) *)
  (* You can make specific variants on the fly. Replace all bits that should not be rewritten
     with refl like this: *)
  apply (simp cong: corres_cong[OF _ refl _ _ refl]) (* Does not touch concrete guard and
                                                        return relation, rewrites the rest *)
  (* Note that the last refl (for return relation) is important -- without it the rule does
     nothing, probably because it would instantiate something *)
  oops

(* Mixing schematics within one guard will ignore that guard for rewriting: *)
schematic_goal
  "corres_underlying sr nf nf' (?r x y) (\<lambda>s. P \<and> ?P') (?Q x y) (assert P) g"
  including corres_default_cong
  apply simp (* Does nothing visible, because ?P' might get instantiated if used as a rewrite rule *)
  oops

end

text \<open>The guard weakening rule\<close>

named_theorems corres_pre
(* Introduce schematic corres guards; fail if already schematic *)
method corres_pre0 = WP_Pre.pre_tac corres_pre
(* Optionally introduce schematic corres guards *)
method corres_pre = corres_pre0?

lemma stronger_corres_guard_imp[corres_pre]:
  assumes x: "corres_underlying sr nf nf' r Q Q' f g"
  assumes y: "\<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> sr \<rbrakk> \<Longrightarrow> Q s"
  assumes z: "\<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> sr \<rbrakk> \<Longrightarrow> Q' s'"
  shows      "corres_underlying sr nf nf' r P P' f g"
  using x by (auto simp: y z corres_underlying_def)

lemma corres_guard_imp:
  assumes x: "corres_underlying sr nf nf' r Q Q' f g"
  assumes y: "\<And>s. P s \<Longrightarrow> Q s" "\<And>s. P' s \<Longrightarrow> Q' s"
  shows      "corres_underlying sr nf nf' r P P' f g"
  apply corres_pre
    apply (rule x)
   apply (simp add: y)+
  done

lemma corres_guard_imp2:
  "\<lbrakk>corres_underlying sr nf nf' r Q P' f g; \<And>s. P s \<Longrightarrow> Q s\<rbrakk>
   \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  by corres_pre
(* FIXME: names\<dots> (cf. corres_guard2_imp below) *)
lemmas corres_guard1_imp = corres_guard_imp2

lemma corres_guard2_imp:
  "\<lbrakk>corres_underlying sr nf nf' r P Q' f g; \<And>s. P' s \<Longrightarrow> Q' s\<rbrakk>
   \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  by corres_pre

named_theorems corres_rrel_pre
(* Introduce schematic return relation, fail if already schematic *)
method corres_rrel_pre = WP_Pre.pre_tac corres_rrel_pre

lemma corres_rel_imp[corres_rrel_pre]:
  assumes x: "corres_underlying sr nf nf' r' P P' f g"
  assumes y: "\<And>x y. r' x y \<Longrightarrow> r x y"
  shows      "corres_underlying sr nf nf' r P P' f g"
  apply (insert x)
  apply (simp add: corres_underlying_def)
  apply clarsimp
  apply (drule (1) bspec, clarsimp)
  apply (drule (1) bspec, clarsimp)
  apply (blast intro: y)
  done

text \<open>Splitting rules for correspondence of composite monads\<close>

lemma corres_underlying_split:
  assumes ac: "corres_underlying sr nf nf' r' P P' a c"
  assumes bd: "\<And>rv rv'. r' rv rv' \<Longrightarrow>
                        corres_underlying sr nf nf' r (Q rv) (Q' rv') (b rv) (d rv')"
  assumes valid: "\<lbrace>P\<rbrace> a \<lbrace>Q\<rbrace>" "\<lbrace>P'\<rbrace> c \<lbrace>Q'\<rbrace>"
  shows "corres_underlying sr nf nf' r P P' (a >>= (\<lambda>rv. b rv)) (c >>= (\<lambda>rv'. d rv'))"
  using ac bd valid
  apply (clarsimp simp: corres_underlying_def bind_def)
  apply (clarsimp simp: Bex_def Ball_def valid_def)
  apply meson
  done

text \<open>Derivative splitting rules\<close>

lemma corres_split:
  assumes x: "corres_underlying sr nf nf' r' P P' a c"
  assumes y: "\<And>rv rv'. r' rv rv' \<Longrightarrow> corres_underlying sr nf nf' r (R rv) (R' rv') (b rv) (d rv')"
  assumes    "\<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace>" "\<lbrace>Q'\<rbrace> c \<lbrace>R'\<rbrace>"
  shows      "corres_underlying sr nf nf' r (P and Q) (P' and Q') (a >>= (\<lambda>rv. b rv)) (c >>= (\<lambda>rv'. d rv'))"
  using assms
  apply -
  apply (rule corres_underlying_split)
     apply (rule corres_guard_imp, rule x, simp_all)
    apply (erule y)
   apply (rule hoare_weaken_pre, assumption)
   apply simp
  apply (rule hoare_weaken_pre, assumption)
  apply simp
  done

lemma corres_split_forwards:
  assumes ac: "corres_underlying sr nf nf' r' P P' a c"
  assumes valid: "\<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace>" "\<lbrace>Q'\<rbrace> c \<lbrace>R'\<rbrace>"
  assumes bd: "\<And>rv rv'. r' rv rv' \<Longrightarrow>
                        corres_underlying sr nf nf' r (R rv) (R' rv') (b rv) (d rv')"
  shows "corres_underlying sr nf nf' r (P and Q) (P' and Q') (a >>= (\<lambda>rv. b rv)) (c >>= (\<lambda>rv'. d rv'))"
  using assms
  apply -
  apply (rule corres_split)
     apply fastforce+
  done

lemmas corres_split_forwards' =
  corres_split_forwards[where P=P and Q=P and P'=P' and Q'=P' and R=Q and R'=Q' for P P' Q Q', simplified]

primrec
  rel_sum_comb :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool)
                     \<Rightarrow> ('a + 'c \<Rightarrow> 'b + 'd \<Rightarrow> bool)" (infixl "\<oplus>" 95)
where
  "(f \<oplus> g) (Inr x) y = (\<exists>y'. y = Inr y' \<and> (g x y'))"
| "(f \<oplus> g) (Inl x) y = (\<exists>y'. y = Inl y' \<and> (f x y'))"

lemma rel_sum_comb_r2[simp]:
  "(f \<oplus> g) x (Inr y) = (\<exists>x'. x = Inr x' \<and> g x' y)"
  apply (case_tac x, simp_all)
  done

lemma rel_sum_comb_l2[simp]:
  "(f \<oplus> g) x (Inl y) = (\<exists>x'. x = Inl x' \<and> f x' y)"
  apply (case_tac x, simp_all)
  done

lemma corres_splitEE:
  assumes    "corres_underlying sr nf nf' (f \<oplus> r') P P' a c"
  assumes y: "\<And>rv rv'. r' rv rv'
              \<Longrightarrow> corres_underlying sr nf nf' (f \<oplus> r) (R rv) (R' rv') (b rv) (d rv')"
  assumes x: "\<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace>,\<lbrace>\<top>\<top>\<rbrace>" "\<lbrace>Q'\<rbrace> c \<lbrace>R'\<rbrace>,\<lbrace>\<top>\<top>\<rbrace>"
  shows      "corres_underlying sr nf nf' (f \<oplus> r) (P and Q) (P' and Q') (a >>=E (\<lambda>rv. b rv)) (c >>=E (\<lambda>rv'. d rv'))"
  using assms
  apply (unfold bindE_def validE_def)
  apply (erule corres_split)
    defer
    apply assumption+
  apply (case_tac rv)
   apply (clarsimp simp: lift_def y)+
  done

lemma corres_splitEE_prod:
  assumes x: "corres_underlying sr nf nf' (f \<oplus> r') P P' a c"
  assumes y: "\<And>x y x' y'. r' (x, y) (x', y')
              \<Longrightarrow> corres_underlying sr nf nf' (f \<oplus> r) (R x y) (R' x' y') (b x y) (d x' y')"
  assumes z: "\<lbrace>Q\<rbrace> a \<lbrace>\<lambda>(x, y). R x y \<rbrace>,\<lbrace>\<top>\<top>\<rbrace>" "\<lbrace>Q'\<rbrace> c \<lbrace>\<lambda>(x, y). R' x y\<rbrace>,\<lbrace>\<top>\<top>\<rbrace>"
  shows      "corres_underlying sr nf nf' (f \<oplus> r) (P and Q) (P' and Q') (a >>=E (\<lambda>(x, y). b x y)) (c >>=E (\<lambda>(x, y). d x y))"
  using assms
  apply (unfold bindE_def validE_def)
  apply (rule corres_split[rotated 2], assumption+)
  apply (fastforce simp: lift_def y split: sum.splits)
  done

lemma corres_split_handle:
  assumes    "corres_underlying sr nf nf' (f' \<oplus> r) P P' a c"
  assumes y: "\<And>ft ft'. f' ft ft'
              \<Longrightarrow> corres_underlying sr nf nf' (f \<oplus> r) (E ft) (E' ft') (b ft) (d ft')"
  assumes x: "\<lbrace>Q\<rbrace> a \<lbrace>\<top>\<top>\<rbrace>,\<lbrace>E\<rbrace>" "\<lbrace>Q'\<rbrace> c \<lbrace>\<top>\<top>\<rbrace>,\<lbrace>E'\<rbrace>"
  shows      "corres_underlying sr nf nf' (f \<oplus> r) (P and Q) (P' and Q') (a <handle> (\<lambda>ft. b ft)) (c <handle> (\<lambda>ft'. d ft'))"
  using assms
  apply (simp add: handleE_def handleE'_def validE_def)
  apply (erule corres_split)
    defer
    apply assumption+
  apply (case_tac v, simp_all, safe, simp_all add: y)
  done

lemma corres_split_catch:
  assumes x: "corres_underlying sr nf nf' (f \<oplus> r) P P' a c"
  assumes y: "\<And>ft ft'. f ft ft' \<Longrightarrow> corres_underlying sr nf nf' r (E ft) (E' ft') (b ft) (d ft')"
  assumes z: "\<lbrace>Q\<rbrace> a \<lbrace>\<top>\<top>\<rbrace>,\<lbrace>E\<rbrace>" "\<lbrace>Q'\<rbrace> c \<lbrace>\<top>\<top>\<rbrace>,\<lbrace>E'\<rbrace>"
  shows      "corres_underlying sr nf nf' r (P and Q) (P' and Q') (a <catch> (\<lambda>ft. b ft)) (c <catch> (\<lambda>ft'. d ft'))"
  apply (simp add: catch_def)
  apply (rule corres_split[OF x, where R="case_sum E \<top>\<top>" and R'="case_sum E' \<top>\<top>"])
    apply (case_tac x)
     apply (clarsimp simp: y)
    apply clarsimp
   apply (insert z)
   apply (simp add: validE_def valid_def split_def split: sum.splits)+
  done

lemma corres_split_eqr:
  assumes x: "corres_underlying sr nf nf' (=) P P' a c"
  assumes y: "\<And>rv. corres_underlying sr nf nf' r (R rv) (R' rv) (b rv) (d rv)"
  assumes z: "\<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace>" "\<lbrace>Q'\<rbrace> c \<lbrace>R'\<rbrace>"
  shows      "corres_underlying sr nf nf' r (P and Q) (P' and Q') (a >>= (\<lambda>rv. b rv)) (c >>= d)"
  apply (rule corres_split[OF x _ z])
  apply (simp add: y)
  done

definition
 "dc \<equiv> \<lambda>rv rv'. True"

lemma dc_simp[simp]: "dc a b"
  by (simp add: dc_def)

lemma dc_o_simp1[simp]: "dc \<circ> f = dc"
  by (simp add: dc_def o_def)

lemma dc_o_simp2[simp]: "dc x \<circ> f = dc x"
  by (simp add: dc_def o_def)

lemma unit_dc_is_eq:
  "(dc::unit\<Rightarrow>_\<Rightarrow>_) = (=)"
  by (fastforce simp: dc_def)

lemma corres_split_nor:
  "\<lbrakk> corres_underlying sr nf nf' dc P P' a c; corres_underlying sr nf nf' r R R' b d;
     \<lbrace>Q\<rbrace> a \<lbrace>\<lambda>x. R\<rbrace>; \<lbrace>Q'\<rbrace> c \<lbrace>\<lambda>x. R'\<rbrace> \<rbrakk>
  \<Longrightarrow> corres_underlying sr nf nf' r (P and Q) (P' and Q') (a >>= (\<lambda>rv. b)) (c >>= (\<lambda>rv. d))"
  apply (rule corres_split, assumption+)
  done

lemma corres_split_norE:
  "\<lbrakk> corres_underlying sr nf nf' (f \<oplus> dc) P P' a c; corres_underlying sr nf nf' (f \<oplus> r) R R' b d;
     \<lbrace>Q\<rbrace> a \<lbrace>\<lambda>x. R\<rbrace>, \<lbrace>\<top>\<top>\<rbrace>; \<lbrace>Q'\<rbrace> c \<lbrace>\<lambda>x. R'\<rbrace>,\<lbrace>\<top>\<top>\<rbrace> \<rbrakk>
  \<Longrightarrow> corres_underlying sr nf nf' (f \<oplus> r) (P and Q) (P' and Q') (a >>=E (\<lambda>rv. b)) (c >>=E (\<lambda>rv. d))"
  apply (rule corres_splitEE, assumption+)
  done

lemma corres_split_eqrE:
  assumes z: "corres_underlying sr nf nf' (f \<oplus> (=)) P P' a c"
  assumes y: "\<And>rv. corres_underlying sr nf nf' (f \<oplus> r) (R rv) (R' rv) (b rv) (d rv)"
  assumes x: "\<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace>,\<lbrace>\<top>\<top>\<rbrace>" "\<lbrace>Q'\<rbrace> c \<lbrace>R'\<rbrace>,\<lbrace>\<top>\<top>\<rbrace>"
  shows      "corres_underlying sr nf nf' (f \<oplus> r) (P and Q) (P' and Q') (a >>=E (\<lambda>rv. b rv)) (c >>=E d)"
  apply (rule corres_splitEE[OF z _ x])
  apply (simp add: y)
  done

lemma corres_split_mapr:
  assumes y: "corres_underlying sr nf nf' ((=) \<circ> f) P P' a c"
  assumes x: "\<And>rv. corres_underlying sr nf nf' r (R rv) (R' (f rv)) (b rv) (d (f rv))"
  assumes z: "\<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace>" "\<lbrace>Q'\<rbrace> c \<lbrace>R'\<rbrace>"
  shows      "corres_underlying sr nf nf' r (P and Q) (P' and Q') (a >>= (\<lambda>rv. b rv)) (c >>= d)"
  apply (rule corres_split[OF y _ z])
  apply simp
  apply (simp add: x)
  done

lemma corres_split_maprE:
  assumes z: "corres_underlying sr nf nf' (r' \<oplus> ((=) \<circ> f)) P P' a c"
  assumes y: "\<And>rv. corres_underlying sr nf nf' (r' \<oplus> r) (R rv) (R' (f rv)) (b rv) (d (f rv))"
  assumes x: "\<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace>,\<lbrace>\<top>\<top>\<rbrace>" "\<lbrace>Q'\<rbrace> c \<lbrace>R'\<rbrace>,\<lbrace>\<top>\<top>\<rbrace>"
  shows      "corres_underlying sr nf nf' (r' \<oplus> r) (P and Q) (P' and Q') (a >>=E (\<lambda>rv. b rv)) (c >>=E d)"
  apply (rule corres_splitEE[OF z _ x])
  apply simp
  apply (simp add: y)
  done

text \<open>Some rules for walking correspondence into basic constructs\<close>

lemma corres_if:
  "\<lbrakk> G = G'; corres_underlying sr nf nf' r P P' a c; corres_underlying sr nf nf' r Q Q' b d \<rbrakk>
    \<Longrightarrow> corres_underlying sr nf nf' r
                (if G then P else Q) (if G' then P' else Q')
                (if G then a else b) (if G' then c else d)"
  by simp

lemma corres_whenE:
  "\<lbrakk> G = G'; corres_underlying sr nf nf' (fr \<oplus> r) P P' f g; r () () \<rbrakk>
     \<Longrightarrow> corres_underlying sr nf nf' (fr \<oplus> r) (\<lambda>s. G \<longrightarrow> P s) (\<lambda>s. G' \<longrightarrow> P' s) (whenE G f) (whenE G' g)"
  by (simp add: whenE_def returnOk_def)

lemmas corres_if2 = corres_if[unfolded if_apply_def2]
lemmas corres_when =
    corres_if2[where b="return ()" and d="return ()"
                and Q="\<top>" and Q'="\<top>" and r=dc, simplified,
                folded when_def]

lemma corres_if_r:
  "\<lbrakk> corres_underlying sr nf nf' r P P' a c; corres_underlying sr nf nf' r P Q' a d \<rbrakk>
   \<Longrightarrow> corres_underlying sr nf nf' r (P) (if G' then P' else Q')
                                     (a) (if G' then c  else d)"
  by (simp)

lemma corres_if3:
 "\<lbrakk> G = G';
    G \<Longrightarrow> corres_underlying sr nf nf' r P P' a c;
    \<not> G' \<Longrightarrow> corres_underlying sr nf nf' r Q Q' b d \<rbrakk>
  \<Longrightarrow> corres_underlying sr nf nf' r (if G then P else Q) (if G' then P' else Q')
                                    (if G then a else b) (if G' then c else d)"
  by simp

lemma corres_if_strong:
  "\<lbrakk>\<And>s s'. \<lbrakk>(s, s') \<in> sr; R s; R' s'\<rbrakk> \<Longrightarrow> G = G';
    \<lbrakk>G; G'\<rbrakk> \<Longrightarrow> corres_underlying sr nf nf' r P P' a c;
    \<lbrakk>\<not> G; \<not> G'\<rbrakk> \<Longrightarrow> corres_underlying sr nf nf' r Q Q' b d \<rbrakk>
   \<Longrightarrow> corres_underlying sr nf nf' r
         (R and (if G then P else Q)) (R' and (if G' then P' else Q'))
         (if G then a else b) (if G' then c else d)"
  by (fastforce simp: corres_underlying_def)

lemmas corres_if_strong' =
  corres_if_strong[where R=R and P=R and Q=R for R,
                   where R'=R' and P'=R' and Q'=R' for R', simplified]

text \<open>Some equivalences about liftM and other useful simps\<close>

(* These rules are declared [simp], which in hindsight was not a good decision, because they
   change the return relation which often is schematic when these rules apply in the goal.
   In those circumstances it is usually safer to unfold liftM_def and proceed with the resulting
   substituted term.

   (We leave the [simp] attribute here, because too many proofs now depend on it)
*)
lemma corres_liftM_simp[simp]:
  "corres_underlying sr nf nf' r P P' (liftM t f) g =
   corres_underlying sr nf nf' (r \<circ> t) P P' f g"
  by (fastforce simp add: corres_underlying_def in_liftM)

lemma corres_liftM2_simp[simp]:
  "corres_underlying sr nf nf' r P P' f (liftM t g) =
   corres_underlying sr nf nf' (\<lambda>x. r x \<circ> t) P P' f g"
  by (fastforce simp add: corres_underlying_def in_liftM)

lemma corres_liftE_rel_sum[simp]:
 "corres_underlying sr nf nf' (f \<oplus> r) P P' (liftE m) (liftE m') =
  corres_underlying sr nf nf' r P P' m m'"
  by (simp add: liftE_liftM o_def)

lemmas corres_liftE_lift = corres_liftE_rel_sum[THEN iffD2]

text \<open>Support for proving correspondence to noop with hoare triples\<close>

lemma corres_noop:
  assumes P: "\<And>s. P s \<Longrightarrow> \<lbrace>\<lambda>s'. (s, s') \<in> sr \<and> P' s'\<rbrace> f \<lbrace>\<lambda>rv s'. (s, s') \<in> sr \<and> r x rv\<rbrace>"
  assumes nf': "\<And>s. \<lbrakk> P s; nf' \<rbrakk> \<Longrightarrow> no_fail (\<lambda>s'. (s, s') \<in> sr \<and> P' s') f"
  shows "corres_underlying sr nf nf' r P P' (return x) f"
  apply (simp add: corres_underlying_def return_def)
  apply clarsimp
  apply (frule P)
  apply (insert nf')
  apply (clarsimp simp: valid_def no_fail_def)
  done

lemma corres_noopE:
  assumes P: "\<And>s. P s \<Longrightarrow> \<lbrace>\<lambda>s'. (s, s') \<in> sr \<and> P' s'\<rbrace> f \<lbrace>\<lambda>rv s'. (s, s') \<in> sr \<and> r x rv\<rbrace>,\<lbrace>\<lambda>r s. False\<rbrace>"
  assumes nf': "\<And>s. \<lbrakk> P s; nf' \<rbrakk> \<Longrightarrow> no_fail (\<lambda>s'. (s, s') \<in> sr \<and> P' s') f"
  shows "corres_underlying sr nf nf' (fr \<oplus> r) P P' (returnOk x) f"
proof -
  have Q: "\<And>P f Q E. \<lbrace>P\<rbrace>f\<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r s. case_sum (\<lambda>e. E e s) (\<lambda>r. Q r s) r\<rbrace>"
   by (simp add: validE_def)
  thus ?thesis
  apply (simp add: returnOk_def)
  apply (rule corres_noop)
   apply (rule hoare_post_imp)
    defer
    apply (rule Q)
    apply (rule P)
    apply assumption
   apply (erule(1) nf')
  apply (simp split: sum.splits)
  done
qed

(* this could be stronger in the no_fail part *)
lemma corres_noop2:
  assumes x: "\<And>s. P s  \<Longrightarrow> \<lbrace>(=) s\<rbrace> f \<exists>\<lbrace>\<lambda>r. (=) s\<rbrace>"
  assumes y: "\<And>s. P' s \<Longrightarrow> \<lbrace>(=) s\<rbrace> g \<lbrace>\<lambda>r. (=) s\<rbrace>"
  assumes z: "nf' \<Longrightarrow> no_fail P f" "nf' \<Longrightarrow> no_fail P' g"
  shows      "corres_underlying sr nf nf' dc P P' f g"
  apply (clarsimp simp: corres_underlying_def)
  apply (rule conjI)
   apply clarsimp
   apply (rule use_exs_valid)
    apply (rule exs_hoare_post_imp)
     prefer 2
     apply (rule x)
     apply assumption
    apply simp_all
   apply (subgoal_tac "ba = b")
    apply simp
   apply (rule sym)
   apply (rule use_valid[OF _ y], assumption+)
   apply simp
  apply (insert z)
  apply (clarsimp simp: no_fail_def)
  done

text \<open>Support for dividing correspondence along
        logical boundaries\<close>

lemma corres_disj_division:
  "\<lbrakk> P \<or> Q; P \<Longrightarrow> corres_underlying sr nf nf' r R S x y; Q \<Longrightarrow> corres_underlying sr nf nf' r T U x y \<rbrakk>
     \<Longrightarrow> corres_underlying sr nf nf' r (\<lambda>s. (P \<longrightarrow> R s) \<and> (Q \<longrightarrow> T s)) (\<lambda>s. (P \<longrightarrow> S s) \<and> (Q \<longrightarrow> U s)) x y"
  by (safe; corres_pre, simp+)

lemma corres_weaker_disj_division:
  "\<lbrakk> P \<or> Q; P \<Longrightarrow> corres_underlying sr nf nf' r R S x y; Q \<Longrightarrow> corres_underlying sr nf nf' r T U x y \<rbrakk>
     \<Longrightarrow> corres_underlying sr nf nf' r (R and T) (S and U) x y"
  by (corres_pre, rule corres_disj_division, simp+)

lemma corres_symmetric_bool_cases:
  "\<lbrakk> P = P'; \<lbrakk> P; P' \<rbrakk> \<Longrightarrow> corres_underlying srel nf nf' r Q Q' f g;
        \<lbrakk> \<not> P; \<not> P' \<rbrakk> \<Longrightarrow> corres_underlying srel nf nf' r R R' f g \<rbrakk>
      \<Longrightarrow> corres_underlying srel nf nf' r (\<lambda>s. (P \<longrightarrow> Q s) \<and> (\<not> P \<longrightarrow> R s))
                                          (\<lambda>s. (P' \<longrightarrow> Q' s) \<and> (\<not> P' \<longrightarrow> R' s))
                                          f g"
  by (cases P, simp_all)

text \<open>Support for symbolically executing into the guards
        and manipulating them\<close>

lemma corres_symb_exec_l:
  assumes z: "\<And>rv. corres_underlying sr nf nf' r (Q rv) P' (x rv) y"
  assumes x: "\<And>s. P s \<Longrightarrow> \<lbrace>(=) s\<rbrace> m \<exists>\<lbrace>\<lambda>r. (=) s\<rbrace>"
  assumes y: "\<lbrace>P\<rbrace> m \<lbrace>Q\<rbrace>"
  assumes nf: "nf' \<Longrightarrow> no_fail P m"
  shows      "corres_underlying sr nf nf' r P P' (m >>= (\<lambda>rv. x rv)) y"
  apply corres_pre
    apply (subst gets_bind_ign[symmetric], rule corres_split[OF _ z])
      apply (rule corres_noop2)
         apply (erule x)
        apply (rule gets_wp)
       apply (erule nf)
      apply (rule no_fail_gets)
     apply (rule y)
    apply (rule gets_wp)
   apply simp+
  done

lemma corres_symb_exec_r:
  assumes z: "\<And>rv. corres_underlying sr nf nf' r P (Q' rv) x (y rv)"
  assumes y: "\<lbrace>P'\<rbrace> m \<lbrace>Q'\<rbrace>"
  assumes x: "\<And>s. P' s \<Longrightarrow> \<lbrace>(=) s\<rbrace> m \<lbrace>\<lambda>r. (=) s\<rbrace>"
  assumes nf: "nf' \<Longrightarrow> no_fail P' m"
  shows      "corres_underlying sr nf nf' r P P' x (m >>= (\<lambda>rv. y rv))"
  apply corres_pre
    apply (subst gets_bind_ign[symmetric], rule corres_split[OF _ z])
      apply (rule corres_noop2)
         apply (simp add: simpler_gets_def exs_valid_def)
        apply (erule x)
       apply (rule no_fail_gets)
      apply (erule nf)
     apply (rule gets_wp)
    apply (rule y)
   apply simp+
  done

lemma corres_symb_exec_r_conj:
  assumes z: "\<And>rv. corres_underlying sr nf nf' r Q (R' rv) x (y rv)"
  assumes y: "\<lbrace>Q'\<rbrace> m \<lbrace>R'\<rbrace>"
  assumes x: "\<And>s. \<lbrace>\<lambda>s'. (s, s') \<in> sr \<and> P' s'\<rbrace> m \<lbrace>\<lambda>rv s'. (s, s') \<in> sr\<rbrace>"
  assumes nf: "\<And>s. nf' \<Longrightarrow> no_fail (\<lambda>s'. (s, s') \<in> sr \<and> P' s') m"
  shows      "corres_underlying sr nf nf' r Q (P' and Q') x (m >>= (\<lambda>rv. y rv))"
proof -
  have P: "corres_underlying sr nf nf' dc \<top> P' (return undefined) m"
    apply (rule corres_noop)
     apply (simp add: x)
    apply (erule nf)
    done
  show ?thesis
  apply corres_pre
    apply (subst return_bind[symmetric],
             rule corres_split [OF P])
      apply (rule z)
     apply wp
    apply (rule y)
   apply simp+
  done
qed

lemma corres_bind_return_r:
  "corres_underlying S nf nf' (\<lambda>x y. r x (h y)) P Q f g \<Longrightarrow>
   corres_underlying S nf nf' r P Q f (do x \<leftarrow> g; return (h x) od)"
  by (fastforce simp: corres_underlying_def bind_def return_def)

lemma corres_underlying_symb_exec_l:
  "\<lbrakk> corres_underlying sr nf nf' dc P P' f (return ()); \<And>rv. corres_underlying sr nf nf' r (Q rv) P' (g rv) h;
     \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<rbrakk>
    \<Longrightarrow> corres_underlying sr nf nf' r P P' (f >>= g) h"
  apply (drule corres_underlying_split)
     apply assumption+
   apply (rule return_wp)
  apply clarsimp
  done

text \<open>Inserting assumptions to be proved later\<close>

lemma corres_req:
  assumes x: "\<And>s s'. \<lbrakk> (s, s') \<in> sr; P s; P' s' \<rbrakk> \<Longrightarrow> F"
  assumes y: "F \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  shows      "corres_underlying sr nf nf' r P P' f g"
  apply (cases "F")
   apply (rule y)
   apply assumption
  apply (simp add: corres_underlying_def)
  apply clarsimp
  apply (subgoal_tac "F")
   apply simp
  apply (rule x, assumption+)
  done

(* Insert assumption to be proved later, on the left-hand (abstract) side *)
lemma corres_gen_asm:
  assumes x: "F \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  shows "corres_underlying sr nf nf' r (P and (\<lambda>s. F)) P' f g"
  apply (rule corres_req[where F=F])
   apply simp
  apply (rule corres_guard_imp [OF x])
    apply simp+
  done

(* Insert assumption to be proved later, on the right-hand (concrete) side *)
lemma corres_gen_asm2:
  assumes x: "F \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  shows "corres_underlying sr nf nf' r P (P' and (\<lambda>s. F)) f g"
  apply (rule corres_req[where F=F])
   apply simp
  apply (rule corres_guard_imp [OF x])
    apply simp+
  done

lemma corres_trivial:
 "corres_underlying sr nf nf' r \<top> \<top> f g \<Longrightarrow> corres_underlying sr nf nf' r \<top> \<top> f g"
  by assumption

lemma corres_underlying_trivial[corres]:
  "\<lbrakk> nf' \<Longrightarrow> no_fail P' f \<rbrakk> \<Longrightarrow> corres_underlying Id nf nf' (=) \<top> P' f f"
  by (auto simp add: corres_underlying_def Id_def no_fail_def)

(* Instance of corres_underlying_trivial for unit type with dc instead of (=) as return relation,
   for nicer return relation instantiation. *)
lemma corres_underlying_trivial_dc[corres]:
  "(nf' \<Longrightarrow> no_fail P' f) \<Longrightarrow> corres_underlying Id nf nf' dc (\<lambda>_. True) P' f f"
  for f :: "('s, unit) nondet_monad"
  by (fastforce intro: corres_underlying_trivial corres_rrel_pre)

lemma corres_assume_pre:
  assumes R: "\<And>s s'. \<lbrakk> P s; Q s'; (s,s') \<in> sr \<rbrakk> \<Longrightarrow> corres_underlying sr nf nf' r P Q f g"
  shows "corres_underlying sr nf nf' r P Q f g"
  apply (clarsimp simp add: corres_underlying_def)
  apply (frule (2) R)
  apply (clarsimp simp add: corres_underlying_def)
  apply blast
  done

lemma corres_initial_splitE:
"\<lbrakk> corres_underlying sr nf nf' (f \<oplus> r') P P' a c;
   \<And>rv rv'. r' rv rv' \<Longrightarrow> corres_underlying sr nf nf' (f \<oplus> r) (Q rv) (Q' rv') (b rv) (d rv');
   \<lbrace>P\<rbrace> a \<lbrace>Q\<rbrace>, \<lbrace>\<lambda>r s. True\<rbrace>;
   \<lbrace>P'\<rbrace> c \<lbrace>Q'\<rbrace>, \<lbrace>\<lambda>r s. True\<rbrace>\<rbrakk>
\<Longrightarrow> corres_underlying sr nf nf' (f \<oplus> r) P P' (a >>=E b) (c >>=E d)"
  apply corres_pre
    apply (erule corres_splitEE)
      apply fastforce+
  done

lemma corres_assert_assume:
  "\<lbrakk> P' \<Longrightarrow> corres_underlying sr nf nf' r P Q f (g ()); \<And>s. Q s \<Longrightarrow> P' \<rbrakk> \<Longrightarrow>
  corres_underlying sr nf nf' r P Q f (assert P' >>= g)"
  by (auto simp: bind_def assert_def fail_def return_def
                 corres_underlying_def)

lemma corres_assert_assume_l:
  "corres_underlying sr nf nf' rrel P Q (f ()) g
  \<Longrightarrow> corres_underlying sr nf nf' rrel (P and (\<lambda>s. P')) Q (assert P' >>= f) g"
  by (force simp: corres_underlying_def assert_def return_def bind_def fail_def)

lemma corres_assert_gen_asm_cross:
  "\<lbrakk> \<And>s s'. \<lbrakk>(s, s') \<in> sr; P' s; Q' s'\<rbrakk> \<Longrightarrow> A;
     A \<Longrightarrow> corres_underlying sr nf nf' r P Q f (g ()) \<rbrakk>
  \<Longrightarrow> corres_underlying sr nf nf' r (P and P') (Q and Q') f (assert A >>= g)"
  by (metis corres_assert_assume corres_assume_pre corres_weaker_disj_division)

lemma corres_state_assert:
  "corres_underlying sr nf nf' rr P Q f (g ()) \<Longrightarrow>
   (\<And>s. Q s \<Longrightarrow> R s) \<Longrightarrow>
   corres_underlying sr nf nf' rr P Q f (state_assert R >>= g)"
  by (clarsimp simp: corres_underlying_def state_assert_def get_def assert_def
                     return_def bind_def)

lemma corres_stateAssert_assume:
  "\<lbrakk> corres_underlying sr nf nf' r P Q f (g ()); \<And>s. Q s \<Longrightarrow> P' s \<rbrakk> \<Longrightarrow>
   corres_underlying sr nf nf' r P Q f (stateAssert P' [] >>= g)"
  apply (clarsimp simp: bind_assoc stateAssert_def)
  apply (rule corres_symb_exec_r [OF _ get_sp])
    apply (rule corres_assert_assume)
     apply (rule corres_assume_pre)
     apply (erule corres_guard_imp, clarsimp+)
   apply (wp | rule no_fail_pre)+
  done

lemma corres_stateAssert_implied:
  "\<lbrakk> corres_underlying sr nf nf' r P Q f (g ());
     \<And>s s'. \<lbrakk> (s, s') \<in> sr; P s; P' s; Q s' \<rbrakk> \<Longrightarrow> Q' s' \<rbrakk>
   \<Longrightarrow> corres_underlying sr nf nf' r (P and P') Q f (stateAssert Q' [] >>= g)"
  apply (clarsimp simp: bind_assoc stateAssert_def)
  apply (rule corres_symb_exec_r [OF _ get_sp])
    apply (rule corres_assume_pre)
    apply (rule corres_assert_assume)
     apply (erule corres_guard_imp, clarsimp+)
   apply (wp | rule no_fail_pre)+
  done

lemmas corres_stateAssert_ignore =
  corres_stateAssert_implied[where P=P and P'=P for P, simplified, rotated]

lemma corres_stateAssert_r:
  "corres_underlying sr nf nf' r P Q f (g ()) \<Longrightarrow>
   corres_underlying sr nf nf' r P (Q and P') f (stateAssert P' [] >>= g)"
  apply (clarsimp simp: bind_assoc stateAssert_def)
  apply (rule corres_symb_exec_r [OF _ get_sp])
    apply (rule corres_assert_assume)
     apply (rule corres_assume_pre)
     apply (erule corres_guard_imp, clarsimp+)
   apply (wp | rule no_fail_pre)+
  done

lemma corres_assert:
  "corres_underlying sr nf nf' dc (%_. P) (%_. Q) (assert P) (assert Q)"
  by (clarsimp simp add: corres_underlying_def return_def)

lemma corres_split2:
  assumes corr: "corres_underlying sr nf nf' (\<lambda>(a, b).\<lambda>(a', b'). r a a' b b') P P'
                        (do a \<leftarrow> F; b \<leftarrow> G; return (a, b) od)
                        (do a' \<leftarrow> F'; b' \<leftarrow> G'; return (a', b') od)"
  and     corr': "\<And>a a' b b'. \<lbrakk> r a a' b b'\<rbrakk>
                     \<Longrightarrow> corres_underlying sr nf nf' r1 (P1 a b) (P1' a' b') (H a b) (H' a' b')"
  and       h1: "\<lbrace>P\<rbrace> do fx \<leftarrow> F; gx \<leftarrow> G; return (fx, gx) od \<lbrace>\<lambda>rv. P1 (fst rv) (snd rv)\<rbrace>"
  and       h2: "\<lbrace>P'\<rbrace> do fx \<leftarrow> F'; gx \<leftarrow> G'; return (fx, gx) od \<lbrace>\<lambda>rv. P1' (fst rv) (snd rv)\<rbrace>"
  shows "corres_underlying sr nf nf' r1 P P'
                (do a \<leftarrow> F; b \<leftarrow> G; H a b od)
                (do a' \<leftarrow> F'; b' \<leftarrow> G'; H' a' b' od)"
proof -
  have "corres_underlying sr nf nf' r1 P P'
               (do a \<leftarrow> F; b \<leftarrow> G; rv \<leftarrow> return (a, b); H (fst rv) (snd rv) od)
               (do a' \<leftarrow> F'; b' \<leftarrow> G'; rv' \<leftarrow> return (a', b'); H' (fst rv') (snd rv') od)"
     by (rule corres_underlying_split [OF corr corr', simplified bind_assoc, OF _ h1 h2])
   (simp add: split_beta split_def)

  thus ?thesis by simp
qed


lemma corres_split3:
  assumes corr: "corres_underlying sr nf nf' (\<lambda>(a, b, c).\<lambda>(a', b', c'). r a a' b b' c c') P P'
                        (do a \<leftarrow> A; b \<leftarrow> B a; c \<leftarrow> C a b; return (a, b, c) od)
                        (do a' \<leftarrow> A'; b' \<leftarrow> B' a'; c' \<leftarrow> C' a' b'; return (a', b', c') od)"
  and     corr': "\<And>a a' b b' c c'. \<lbrakk> r a a' b b' c c'\<rbrakk>
                     \<Longrightarrow> corres_underlying sr nf nf' r1 (P1 a b c) (P1' a' b' c') (H a b c) (H' a' b' c')"
  and       h1: "\<lbrace>P\<rbrace>
                    do a \<leftarrow> A; b \<leftarrow> B a; c \<leftarrow> C a b; return (a, b, c) od
                 \<lbrace>\<lambda>(a, b, c). P1 a b c\<rbrace>"
  and       h2: "\<lbrace>P'\<rbrace>
                    do a' \<leftarrow> A'; b' \<leftarrow> B' a'; c' \<leftarrow> C' a' b'; return (a', b', c') od
                 \<lbrace>\<lambda>(a', b', c'). P1' a' b' c'\<rbrace>"
  shows "corres_underlying sr nf nf' r1 P P'
                (do a \<leftarrow> A; b \<leftarrow> B a; c \<leftarrow> C a b; H a b c od)
                (do a' \<leftarrow> A'; b' \<leftarrow> B' a'; c' \<leftarrow> C' a' b'; H' a' b' c' od)"
proof -
  have "corres_underlying sr nf nf' r1 P P'
               (do a \<leftarrow> A; b \<leftarrow> B a; c \<leftarrow> C a b; rv \<leftarrow> return (a, b, c);
                          H (fst rv) (fst (snd rv)) (snd (snd rv)) od)
               (do a' \<leftarrow> A'; b' \<leftarrow> B' a'; c' \<leftarrow> C' a' b'; rv \<leftarrow> return (a', b', c');
                          H' (fst rv) (fst (snd rv)) (snd (snd rv)) od)" using h1 h2
    by - (rule corres_underlying_split [OF corr corr', simplified bind_assoc ],
      simp_all add: split_beta split_def)

  thus ?thesis by simp
qed

(* A little broken --- see above *)
lemma corres_split4:
  assumes corr: "corres_underlying sr nf nf' (\<lambda>(a, b, c, d).\<lambda>(a', b', c', d'). r a a' b b' c c' d d') P P'
                        (do a \<leftarrow> A; b \<leftarrow> B; c \<leftarrow> C; d \<leftarrow> D; return (a, b, c, d) od)
                        (do a' \<leftarrow> A'; b' \<leftarrow> B'; c' \<leftarrow> C'; d' \<leftarrow> D'; return (a', b', c', d') od)"
  and     corr': "\<And>a a' b b' c c' d d'. \<lbrakk> r a a' b b' c c' d d'\<rbrakk>
                     \<Longrightarrow> corres_underlying sr nf nf' r1 (P1 a b c d) (P1' a' b' c' d')
                                  (H a b c d) (H' a' b' c' d')"
  and       h1: "\<lbrace>P\<rbrace>
                    do a \<leftarrow> A; b \<leftarrow> B; c \<leftarrow> C; d \<leftarrow> D; return (a, b, c, d) od
                 \<lbrace>\<lambda>(a, b, c, d). P1 a b c d\<rbrace>"
  and       h2: "\<lbrace>P'\<rbrace>
                    do a' \<leftarrow> A'; b' \<leftarrow> B'; c' \<leftarrow> C'; d' \<leftarrow> D'; return (a', b', c', d') od
                 \<lbrace>\<lambda>(a', b', c', d'). P1' a' b' c' d'\<rbrace>"
  shows "corres_underlying sr nf nf' r1 P P'
                (do a \<leftarrow> A; b \<leftarrow> B; c \<leftarrow> C; d \<leftarrow> D; H a b c d od)
                (do a' \<leftarrow> A'; b' \<leftarrow> B'; c' \<leftarrow> C'; d' \<leftarrow> D'; H' a' b' c' d' od)"
proof -
  have "corres_underlying sr nf nf' r1 P P'
               (do a \<leftarrow> A; b \<leftarrow> B; c \<leftarrow> C; d \<leftarrow> D; rv \<leftarrow> return (a, b, c, d);
                   H (fst rv) (fst (snd rv)) (fst (snd (snd rv))) (snd (snd (snd rv))) od)
               (do a' \<leftarrow> A'; b' \<leftarrow> B'; c' \<leftarrow> C'; d' \<leftarrow> D'; rv \<leftarrow> return (a', b', c', d');
                   H' (fst rv) (fst (snd rv)) (fst (snd (snd rv))) (snd (snd (snd rv))) od)"
    using h1 h2
    by - (rule corres_underlying_split [OF corr corr', simplified bind_assoc],
    simp_all add: split_beta split_def)

  thus ?thesis by simp
qed

(* for instantiations *)
lemma corres_inst: "corres_underlying sr nf nf' r P P' f g \<Longrightarrow> corres_underlying sr nf nf' r P P' f g" .

lemma corres_assert_opt_assume:
  assumes "\<And>x. P' = Some x \<Longrightarrow> corres_underlying sr nf nf' r P Q f (g x)"
  assumes "\<And>s. Q s \<Longrightarrow> P' \<noteq> None"
  shows "corres_underlying sr nf nf' r P Q f (assert_opt P' >>= g)" using assms
  by (auto simp: bind_def assert_opt_def assert_def fail_def return_def
                 corres_underlying_def split: option.splits)

lemma corres_assert_opt[corres]:
  "r x x' \<Longrightarrow>
  corres_underlying sr nf nf' (\<lambda>x x'. r (Some x) x') (\<lambda>s. x \<noteq> None) \<top> (assert_opt x) (return x')"
  unfolding corres_underlying_def
  by (clarsimp simp: assert_opt_def return_def split: option.splits)

lemma assert_opt_assert_corres[corres]:
  "(x = None) = (x' = None) \<Longrightarrow>
   corres_underlying sr nf nf' (\<lambda>y _. x = Some y) (K (x \<noteq> None)) \<top>
                     (assert_opt x) (assert (\<exists>y. x' = Some y))"
  by (simp add: corres_underlying_def assert_opt_def return_def split: option.splits)

lemma corres_assert_opt_l:
  assumes "\<And>x. P' = Some x \<Longrightarrow> corres_underlying sr nf nf' r (P x) Q (f x) g"
  shows "corres_underlying sr nf nf' r (\<lambda>s. \<exists>x. P' = Some x \<and> P x s) Q (assert_opt P' >>= f) g"
  using assms
  by (auto simp: bind_def assert_opt_def assert_def fail_def return_def corres_underlying_def
           split: option.splits)

lemma corres_gets_the_gets:
  "corres_underlying sr False nf' r P P' (gets_the f) f' \<Longrightarrow>
   corres_underlying sr nf nf' (\<lambda>x x'. x \<noteq> None \<and> r (the x) x') P P' (gets f) f'"
  apply (simp add: gets_the_def bind_def simpler_gets_def assert_opt_def)
  apply (fastforce simp: corres_underlying_def in_monad split: option.splits)
  done

text \<open>Support for proving correspondance by decomposing the state relation\<close>

lemma corres_underlying_decomposition:
  assumes x: "corres_underlying {(s, s'). P s s'} nf nf' r Pr Pr' f g"
      and y: "\<And>s'. \<lbrace>R s'\<rbrace> f \<lbrace>\<lambda>rv s. Q s s'\<rbrace>"
      and z: "\<And>s. \<lbrace>P s and Q s and K (Pr s) and Pr'\<rbrace> g \<lbrace>\<lambda>rv s'. R s' s\<rbrace>"
  shows      "corres_underlying {(s, s'). P s s' \<and> Q s s'} nf nf' r Pr Pr' f g"
  using x apply (clarsimp simp: corres_underlying_def)
  apply (elim allE, drule(1) mp, clarsimp)
  apply (drule(1) bspec)
  apply clarsimp
  apply (rule rev_bexI, assumption)
  apply simp
  apply (erule use_valid [OF _ y])
  apply (erule use_valid [OF _ z])
  apply simp
  done



lemma corres_stronger_no_failI:
  assumes f': "nf' \<Longrightarrow> no_fail (\<lambda>s'. \<exists>s. P s \<and> (s,s') \<in> S \<and> P' s')  f'"
  assumes corres: "\<forall>(s, s') \<in> S. P s \<and> P' s' \<longrightarrow>
                     (\<forall>(r', t') \<in> fst (f' s'). \<exists>(r, t) \<in> fst (f s). (t, t') \<in> S \<and> R r r')"
  shows "corres_underlying S nf nf' R P P' f f'"
  using assms
  apply (simp add: corres_underlying_def no_fail_def)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply blast
  apply clarsimp
  apply blast
  done

lemma corres_fail:
  assumes no_fail: "\<And>s s'. \<lbrakk> (s,s') \<in> sr; P s; P' s'; nf' \<rbrakk> \<Longrightarrow> False"
  shows "corres_underlying sr nf nf' R P P' f fail"
  using no_fail
  by (auto simp add: corres_underlying_def fail_def)

lemma corres_returnOk:
  "(\<And>s s'. \<lbrakk> (s,s') \<in> sr; P s; P' s' \<rbrakk> \<Longrightarrow> r x y) \<Longrightarrow>
  corres_underlying sr nf nf' (r' \<oplus> r) P P' (returnOk x) (returnOk y)"
  apply (rule corres_noopE)
   apply wp
   apply clarsimp
  apply wp
  done

lemma corres_returnOkTT:
  "r x y \<Longrightarrow> corres_underlying sr nf nf' (r' \<oplus> r) \<top> \<top> (returnOk x) (returnOk y)"
  by (simp add: corres_returnOk)

lemma corres_throwErrorTT:
  "r x y \<Longrightarrow> corres_underlying sr nf nf' (r \<oplus> r') \<top> \<top> (throwError x) (throwError y)"
  by simp

lemma corres_False [simp, corres_no_simp]:
  "corres_underlying sr nf nf' r P \<bottom> f f'"
  by (simp add: corres_underlying_def)

lemma corres_liftME[simp]:
  "corres_underlying sr nf nf' (f \<oplus> r) P P' (liftME fn m) m'
   = corres_underlying sr nf nf' (f \<oplus> (r \<circ> fn)) P P' m m'"
  apply (simp add: liftME_liftM)
  apply (rule corres_cong [OF refl refl refl refl])
  apply (case_tac x, simp_all)
  done

lemma corres_liftME2[simp]:
  "corres_underlying sr nf nf' (f \<oplus> r) P P' m (liftME fn m')
   = corres_underlying sr nf nf' (f \<oplus> (\<lambda>x. r x \<circ> fn)) P P' m m'"
  apply (simp add: liftME_liftM)
  apply (rule corres_cong [OF refl refl refl refl])
  apply (case_tac y, simp_all)
  done

lemma corres_assertE_assume:
  "\<lbrakk>\<And>s. P s \<longrightarrow> P'; \<And>s'. Q s' \<longrightarrow> Q'\<rbrakk> \<Longrightarrow>
   corres_underlying sr nf nf' (f \<oplus> (=)) P Q (assertE P') (assertE Q')"
  apply (simp add: corres_underlying_def assertE_def returnOk_def
                   fail_def return_def)
  by blast

definition
  rel_prod :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'c \<Rightarrow> 'b \<times> 'd \<Rightarrow> bool)"
  (infix "\<otimes>" 97)
where
  "rel_prod \<equiv> \<lambda>f g (a,b) (c,d). f a c \<and> g b d"

lemma rel_prod_apply [simp]:
  "(f \<otimes> g) (a,b) (c,d) = (f a c \<and> g b d)"
  by (simp add: rel_prod_def)

lemma mapME_x_corres_inv:
  assumes x: "\<And>x. corres_underlying sr nf nf' (f \<oplus> dc) (P x) (P' x) (m x) (m' x)"
  assumes y: "\<And>x P. \<lbrace>P\<rbrace> m x \<lbrace>\<lambda>x. P\<rbrace>,-" "\<And>x P'. \<lbrace>P'\<rbrace> m' x \<lbrace>\<lambda>x. P'\<rbrace>,-"
  assumes z: "xs = ys"
  shows      "corres_underlying sr nf nf' (f \<oplus> dc) (\<lambda>s. \<forall>x \<in> set xs. P x s) (\<lambda>s. \<forall>y \<in> set ys. P' y s)
                              (mapME_x m xs) (mapME_x m' ys)"
  unfolding z
proof (induct ys)
  case Nil
  show ?case
    by (simp add: mapME_x_def sequenceE_x_def returnOk_def)
next
  case (Cons z zs)
    from Cons have IH:
      "corres_underlying sr nf nf' (f \<oplus> dc) (\<lambda>s. \<forall>x\<in>set zs. P x s) (\<lambda>s. \<forall>y\<in>set zs. P' y s)
                       (mapME_x m zs) (mapME_x m' zs)" .
  show ?case
    apply (simp add: mapME_x_def sequenceE_x_def)
    apply (fold mapME_x_def sequenceE_x_def dc_def)
    apply corres_pre
      apply (rule corres_splitEE)
         apply (rule x)
        apply (rule IH)
       apply (fold validE_R_def)
       apply (rule y)+
     apply simp+
    done
qed

lemma select_corres_eq:
  "corres_underlying sr nf nf' (=) \<top> \<top> (select UNIV) (select UNIV)"
  by (simp add: corres_underlying_def select_def)

lemma corres_cases:
  "\<lbrakk> R \<Longrightarrow> corres_underlying sr nf nf' r P P' f g; \<not>R \<Longrightarrow> corres_underlying sr nf nf' r Q Q' f g \<rbrakk>
  \<Longrightarrow> corres_underlying sr nf nf' r (P and Q) (P' and Q') f g"
  by (simp add: corres_underlying_def) blast

lemma corres_cases':
  "\<lbrakk> R \<Longrightarrow> corres_underlying sr nf nf' r P P' f g; \<not>R \<Longrightarrow> corres_underlying sr nf nf' r Q Q' f g \<rbrakk>
  \<Longrightarrow> corres_underlying sr nf nf' r (\<lambda>s. (R \<longrightarrow> P s) \<and> (\<not>R \<longrightarrow> Q s))
                                   (\<lambda>s. (R \<longrightarrow> P' s) \<and> (\<not>R \<longrightarrow> Q' s)) f g"
  by (cases R; simp)

lemma corres_alternate1:
  "corres_underlying sr nf nf' r P P' a c \<Longrightarrow> corres_underlying sr nf nf' r P P' (a \<sqinter> b) c"
  apply (simp add: corres_underlying_def alternative_def)
  apply clarsimp
  apply (drule (1) bspec, clarsimp)+
  apply (rule rev_bexI)
   apply (rule UnI1)
   apply assumption
  apply simp
  done

lemma corres_alternate2:
  "corres_underlying sr nf nf' r P P' b c \<Longrightarrow> corres_underlying sr nf nf' r P P' (a \<sqinter> b) c"
  apply (simp add: corres_underlying_def alternative_def)
  apply clarsimp
  apply (drule (1) bspec, clarsimp)+
  apply (rule rev_bexI)
   apply (rule UnI2)
   apply assumption
  apply simp
  done

lemma corres_False':
  "corres_underlying sr nf nf' r \<bottom> P' f g"
  by (simp add: corres_underlying_def)

lemma corres_symb_exec_l_Ex:
  assumes x: "\<And>rv. corres_underlying sr nf nf' r (Q rv) P' (g rv) h"
  shows      "corres_underlying sr nf nf' r (\<lambda>s. \<exists>rv. Q rv s \<and> (rv, s) \<in> fst (f s)) P'
                       (do rv \<leftarrow> f; g rv od) h"
  apply (clarsimp simp add: corres_underlying_def)
  apply (cut_tac rv=rv in x)
  apply (clarsimp simp add: corres_underlying_def)
  apply (drule(1) bspec, clarsimp)
  apply (case_tac nf)
   apply (clarsimp simp: bind_def')
   apply blast
  apply clarsimp
  apply (drule(1) bspec, clarsimp)
  apply (clarsimp simp: bind_def | erule rev_bexI)+
  done

lemma corres_symb_exec_r_All:
  assumes nf: "\<And>rv. nf' \<Longrightarrow> no_fail (Q' rv) g"
  assumes x: "\<And>rv. corres_underlying sr nf nf' r P (Q' rv) f (h rv)"
  shows      "corres_underlying sr nf nf' r P (\<lambda>s. (\<forall>p \<in> fst (g s). snd p = s \<and> Q' (fst p) s) \<and> (\<exists>rv. Q' rv s))
                       f (do rv \<leftarrow> g; h rv od)"
  apply (clarsimp simp add: corres_underlying_def bind_def)
  apply (rule conjI)
   apply clarsimp
   apply (cut_tac rv=aa in x)
   apply (clarsimp simp add: corres_underlying_def bind_def)
   apply (drule(1) bspec, clarsimp)+
  apply (insert nf)
  apply (clarsimp simp: no_fail_def)
  apply (erule (1) my_BallE)
  apply (cut_tac rv="aa" in x)
  apply (clarsimp simp add: corres_underlying_def bind_def)
  apply (drule(1) bspec, clarsimp)+
  done

lemma corres_split_bind_case_sum:
  assumes x: "corres_underlying sr nf nf' (lr \<oplus> rr) P P' a d"
  assumes y: "\<And>rv rv'. lr rv rv' \<Longrightarrow> corres_underlying sr nf nf' r (R rv) (R' rv') (b rv) (e rv')"
  assumes z: "\<And>rv rv'. rr rv rv' \<Longrightarrow> corres_underlying sr nf nf' r (S rv) (S' rv') (c rv) (f rv')"
  assumes w: "\<lbrace>Q\<rbrace> a \<lbrace>S\<rbrace>,\<lbrace>R\<rbrace>" "\<lbrace>Q'\<rbrace> d \<lbrace>S'\<rbrace>,\<lbrace>R'\<rbrace>"
  shows "corres_underlying sr nf nf' r (P and Q) (P' and Q')
            (a >>= (\<lambda>rv. case_sum b c rv)) (d >>= (\<lambda>rv'. case_sum e f rv'))"
  apply (rule corres_split [OF x])
    defer
    apply (insert w)[2]
    apply (simp add: validE_def)+
  apply (case_tac rv)
   apply (clarsimp simp: y)
  apply (clarsimp simp: z)
  done

lemma whenE_throwError_corres_initial:
  assumes P: "frel f f'"
  assumes Q: "P = P'"
  assumes R: "\<not> P \<Longrightarrow> corres_underlying sr nf nf' (frel \<oplus> rvr) Q Q' m m'"
  shows      "corres_underlying sr nf nf' (frel \<oplus> rvr) Q Q'
                     (whenE P  (throwError f ) >>=E (\<lambda>_. m ))
                     (whenE P' (throwError f') >>=E (\<lambda>_. m'))"
  unfolding whenE_def
  apply (cases P)
   apply (simp add: P Q)
  apply (simp add: Q)
  apply (rule R)
  apply (simp add: Q)
  done

lemma whenE_throwError_corres:
  assumes P: "frel f f'"
  assumes Q: "P = P'"
  assumes R: "\<not> P \<Longrightarrow> corres_underlying sr nf nf' (frel \<oplus> rvr) Q Q' m m'"
  shows      "corres_underlying sr nf nf' (frel \<oplus> rvr) (\<lambda>s. \<not> P \<longrightarrow> Q s) (\<lambda>s. \<not> P' \<longrightarrow> Q' s)
                     (whenE P  (throwError f ) >>=E (\<lambda>_. m ))
                     (whenE P' (throwError f') >>=E (\<lambda>_. m'))"
  apply (rule whenE_throwError_corres_initial)
  apply (simp_all add: P Q R)
  done

lemma corres_move_asm:
  "\<lbrakk> corres_underlying sr nf nf' r P  Q f g;
      \<And>s s'. \<lbrakk>(s,s') \<in> sr; P s; P' s'\<rbrakk> \<Longrightarrow> Q s'\<rbrakk>
    \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  by (fastforce simp: corres_underlying_def)

lemmas corres_cross_over_guard = corres_move_asm[rotated]

lemma corres_cross_add_guard:
  "\<lbrakk>\<And>s s'. \<lbrakk>(s,s') \<in> sr; P s; P' s'\<rbrakk> \<Longrightarrow> Q' s';
    corres_underlying sr nf nf' r P (P' and Q') f g\<rbrakk>
   \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  by (fastforce simp: corres_underlying_def)

lemma corres_cross_add_abs_guard:
  "\<lbrakk>\<And>s s'. \<lbrakk>(s,s') \<in> sr; P s; P' s'\<rbrakk> \<Longrightarrow> Q s;
    corres_underlying sr nf nf' r (P and Q)  P' f g\<rbrakk>
   \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  by (fastforce simp: corres_underlying_def)

lemma corres_either_alternate:
  "\<lbrakk> corres_underlying sr nf nf' r P Pa' a c; corres_underlying sr nf nf' r P Pb' b c \<rbrakk>
   \<Longrightarrow> corres_underlying sr nf nf' r P (Pa' or Pb') (a \<sqinter> b) c"
  apply (simp add: corres_underlying_def alternative_def)
  apply clarsimp
  apply (drule (1) bspec, clarsimp)+
  apply (erule disjE, clarsimp)
   apply (drule(1) bspec, clarsimp)
   apply (rule rev_bexI)
    apply (erule UnI1)
   apply simp
  apply (clarsimp, drule(1) bspec, clarsimp)
  apply (rule rev_bexI)
   apply (erule UnI2)
  apply simp
  done

lemma corres_either_alternate2:
  "\<lbrakk> corres_underlying sr nf nf' r P R a c; corres_underlying sr nf nf' r Q R b c \<rbrakk>
   \<Longrightarrow> corres_underlying sr nf nf' r (P or Q) R (a \<sqinter> b) c"
  apply (simp add: corres_underlying_def alternative_def)
  apply clarsimp
  apply (drule (1) bspec, clarsimp)+
   apply (erule disjE)
   apply clarsimp
   apply (drule(1) bspec, clarsimp)
   apply (rule rev_bexI)
    apply (erule UnI1)
   apply simp
   apply clarsimp
  apply (drule(1) bspec, clarsimp)
  apply (rule rev_bexI)
   apply (erule UnI2)
  apply simp
  done

lemma option_corres:
  assumes None: "\<lbrakk> x = None; x' = None \<rbrakk> \<Longrightarrow> corres_underlying sr nf nf' r P P' (A None) (C None)"
  assumes Some: "\<And>z z'. \<lbrakk> x = Some z; x' = Some z' \<rbrakk> \<Longrightarrow>
             corres_underlying sr nf nf' r (Q z) (Q' z') (A (Some z)) (C (Some z'))"
  assumes None_eq: "(x = None) = (x' = None)"
  shows "corres_underlying sr nf nf' r (\<lambda>s. (x = None \<longrightarrow> P s) \<and> (\<forall>z. x = Some z \<longrightarrow> Q z s))
                  (\<lambda>s. (x' = None \<longrightarrow> P' s) \<and> (\<forall>z. x' = Some z \<longrightarrow> Q' z s))
                  (A x) (C x')"
  apply (cases x; cases x'; simp add: assms)
   apply (simp add: None flip: None_eq)
  apply (simp flip: None_eq)
  done


lemma corres_bind_return:
 "corres_underlying sr nf nf' r P P' (f >>= return) g \<Longrightarrow>
  corres_underlying sr nf nf' r P P' f g"
  by (simp add: corres_underlying_def)

lemma corres_bind_return2:
  "corres_underlying sr nf nf' r P P' f (g >>= return) \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  by simp

lemma corres_stateAssert_implied2:
  assumes c: "corres_underlying sr nf nf' r P Q f g"
  assumes sr: "\<And>s s'. \<lbrakk>(s, s') \<in> sr; R s; R' s'\<rbrakk> \<Longrightarrow> Q' s'"
  assumes f: "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. R\<rbrace>"
  assumes g: "\<lbrace>Q\<rbrace> g \<lbrace>\<lambda>_. R'\<rbrace>"
  shows "corres_underlying sr nf nf' dc P Q f (g >>= (\<lambda>_. stateAssert Q' []))"
  apply (subst bind_return[symmetric])
  apply corres_pre
    apply (rule corres_split)
       apply (rule c)
      apply (clarsimp simp: corres_underlying_def return_def
                            stateAssert_def bind_def get_def assert_def
                            fail_def)
      apply (drule (2) sr)
      apply simp
     apply (rule f)
    apply (rule g)
   apply simp
  apply simp
  done

lemma corres_stateAssert_add_assertion:
  "\<lbrakk> corres_underlying sr nf nf' r P (Q and Q') f (g ());
     \<And>s s'. \<lbrakk> (s, s') \<in> sr; P s; Q s' \<rbrakk> \<Longrightarrow> Q' s' \<rbrakk>
   \<Longrightarrow> corres_underlying sr nf nf' r P Q f (stateAssert Q' [] >>= g)"
  apply (clarsimp simp: bind_assoc stateAssert_def)
  apply (rule corres_symb_exec_r [OF _ get_sp])
    apply (rule corres_assume_pre)
    apply (rule corres_assert_assume)
     apply (erule corres_guard_imp, clarsimp+)
   apply (wp | rule no_fail_pre)+
  done

lemma corres_add_noop_lhs:
  "corres_underlying sr nf nf' r P P' (return () >>= (\<lambda>_. f)) g
      \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  by simp

lemma corres_add_noop_lhs2:
  "corres_underlying sr nf nf' r P P' (f >>= (\<lambda>_. return ())) g
      \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  by simp

lemmas corres_split_noop_rhs
  = corres_split_nor[THEN corres_add_noop_lhs, OF _ _ return_wp]

lemmas corres_split_noop_rhs2
  = corres_split_nor[THEN corres_add_noop_lhs2]

lemmas corres_split_dc = corres_split[where r'=dc, simplified]

lemma corres_add_noop_rhs:
  "corres_underlying sr nf nf' r P P' f (do _ \<leftarrow> return (); g od)
   \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  by simp

lemma corres_add_noop_rhs2:
  "corres_underlying sr nf nf' r P P' f (do _ \<leftarrow> g; return () od)
   \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  by simp

lemma isLeft_case_sum:
  "isLeft v \<Longrightarrow> (case v of Inl v' \<Rightarrow> f v' | Inr v' \<Rightarrow> g v') = f (theLeft v)"
  by (clarsimp split: sum.splits)

lemma corres_symb_exec_catch_r:
  "\<lbrakk> \<And>rv. corres_underlying sr nf nf' r P (Q' rv) f (h rv);
        \<lbrace>P'\<rbrace> g \<lbrace>\<bottom>\<bottom>\<rbrace>, \<lbrace>Q'\<rbrace>; \<And>s. \<lbrace>(=) s\<rbrace> g \<lbrace>\<lambda>r. (=) s\<rbrace>; nf' \<Longrightarrow> no_fail P' g \<rbrakk>
      \<Longrightarrow> corres_underlying sr nf nf' r P P' f (g <catch> h)"
  apply (simp add: catch_def)
  apply (rule corres_symb_exec_r, simp_all)
   apply (rule_tac F="isLeft x" in corres_gen_asm2)
   apply (simp add: isLeft_case_sum)
   apply assumption
  apply (simp add: validE_def)
  apply (erule hoare_chain, simp_all)[1]
  apply (simp split: sum.split_asm)
  done

lemma corres_returnTT:
  "r a b \<Longrightarrow> corres_underlying sr nf nf' r \<top> \<top> (return a) (return b)"
  by simp

lemmas corres_return_eq_same = corres_returnTT[of "(=)"]

lemmas corres_discard_r =
  corres_symb_exec_r [where P'=P' and Q'="\<lambda>_. P'" for P', simplified]

lemma corres_assert_gen_asm:
  "\<lbrakk> F \<Longrightarrow> corres_underlying sr nf nf' r P Q f (g ()) \<rbrakk>
   \<Longrightarrow> corres_underlying sr nf nf' r (P and (\<lambda>_. F)) Q f (assert F >>= g)"
  by (simp add: corres_gen_asm)

lemma corres_assert_gen_asm_l:
  "\<lbrakk> F \<Longrightarrow> corres_underlying sr nf nf' r P Q (f ()) g \<rbrakk>
   \<Longrightarrow> corres_underlying sr nf nf' r (P and (\<lambda>_. F)) Q (assert F >>= f) g"
  by (simp add: corres_gen_asm)

lemma corres_assert_gen_asm2:
  "\<lbrakk> F \<Longrightarrow> corres_underlying sr nf nf' r P Q f (g ()) \<rbrakk>
   \<Longrightarrow> corres_underlying sr nf nf' r P (Q and (\<lambda>_. F)) f (assert F >>= g)"
  by (simp add: corres_gen_asm2)

lemma corres_assert_gen_asm_l2:
  "\<lbrakk> F \<Longrightarrow> corres_underlying sr nf nf' r P Q (f ()) g \<rbrakk>
   \<Longrightarrow> corres_underlying sr nf nf' r P (Q and (\<lambda>_. F)) (assert F >>= f) g"
  by (simp add: corres_gen_asm2)

lemma corres_add_guard:
  "\<lbrakk>\<And>s s'. \<lbrakk>Q s; Q' s'; (s, s') \<in> sr\<rbrakk> \<Longrightarrow> P s \<and> P' s';
    corres_underlying sr nf nf' r (Q and P) (Q' and P') f g\<rbrakk> \<Longrightarrow>
    corres_underlying sr nf nf' r Q Q' f g"
  by (auto simp: corres_underlying_def)

lemma corres_stateAssert_r_cross:
  assumes A: "\<forall>s s'. (s, s') \<in> sr \<longrightarrow> P' s \<longrightarrow> Q' s' \<longrightarrow> A s'"
  assumes C: "corres_underlying sr nf nf' r P Q f (g ())"
  shows
  "corres_underlying sr nf nf' r (P and P') (Q and Q') f (stateAssert A [] >>= g)"
  apply (clarsimp simp: bind_assoc stateAssert_def)
  apply corres_pre
    apply (rule corres_symb_exec_r)
       apply (rule corres_assert_gen_asm2, rule C)
      apply wpsimp+
  apply (simp add: A)
  done

(* safer non-rewrite version of corres_gets *)
lemma corres_gets_trivial:
  "\<lbrakk>\<And>s s'. (s,s') \<in> sr \<Longrightarrow> f s = f' s' \<rbrakk>
   \<Longrightarrow> corres_underlying sr nf nf' (=) \<top> \<top> (gets f) (gets f')"
  unfolding corres_underlying_def gets_def get_def return_def bind_def
  by clarsimp

(* When we are ignoring failure on the concrete side, fail does refine fail *)
lemma corres_underlying_fail_fail:
  "corres_underlying rf_sr nf False r \<top> \<top> fail fail"
  by (simp add: corres_underlying_def fail_def)

(* assert refinement when concrete failure is ignored *)
lemma corres_underlying_assert_assert:
  "Q' = Q \<Longrightarrow> corres_underlying rf_sr nf False dc \<top> \<top> (assert Q) (assert Q')"
  by (simp add: assert_def corres_underlying_fail_fail)

(* stateAssert refinement when concrete failure is ignored *)
lemma corres_underlying_stateAssert_stateAssert:
  assumes "\<And>s s'. \<lbrakk> (s,s') \<in> rf_sr; P s; P' s' \<rbrakk> \<Longrightarrow> Q' s' = Q s"
  shows "corres_underlying rf_sr nf False dc P P' (stateAssert Q []) (stateAssert Q' [])"
  by (auto simp: stateAssert_def get_def Nondet_Monad.bind_def corres_underlying_def
                 assert_def return_def fail_def assms)

(* We can ignore a stateAssert in the middle of a computation even if we don't ignore abstract
   failure if we have separately proved no_fail for the entire computation *)
lemma corres_stateAssert_no_fail:
  "\<lbrakk> no_fail P (do v \<leftarrow> g; _ \<leftarrow> stateAssert X []; h v od);
     corres_underlying S False nf' r P Q (do v \<leftarrow> g; h v od) f \<rbrakk> \<Longrightarrow>
   corres_underlying S False nf' r P Q (do v \<leftarrow> g; _ \<leftarrow> stateAssert X []; h v od) f"
  apply (simp add: corres_underlying_def stateAssert_def get_def assert_def return_def no_fail_def fail_def cong: if_cong)
  apply (clarsimp simp: split_def Nondet_Monad.bind_def split: if_splits)
  apply (erule allE, erule (1) impE)
  apply (drule (1) bspec, clarsimp)+
  done

(* We can switch to the corres framework that is allowed to assume non-failure of the abstract
   side when we have already proved that the abstract side doesn't fail *)
lemma corres_no_fail_nf:
  "\<lbrakk> no_fail P f; corres_underlying S True nf' r P Q f g \<rbrakk> \<Longrightarrow>
   corres_underlying S False nf' r P Q f g"
  by (simp add: corres_underlying_def no_fail_def)

text \<open>Some setup of specialised methods.\<close>

lemma (in strengthen_implementation) wpfix_strengthen_corres_guard_imp:
  "(\<And>s. st (\<not> F) (\<longrightarrow>) (P s) (Q s))
    \<Longrightarrow> (\<And>s. st (\<not> F) (\<longrightarrow>) (P' s) (Q' s))
    \<Longrightarrow> st F (\<longrightarrow>)
        (corres_underlying sr nf nf' r P P' f g)
        (corres_underlying sr nf nf' r Q Q' f g)"
  by (cases F; auto elim: corres_guard_imp)

lemmas wpfix_strengthen_corres_guard_imp[wp_fix_strgs]
    = strengthen_implementation.wpfix_strengthen_corres_guard_imp

lemma corres_name_pre:
  "\<lbrakk> \<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> sr \<rbrakk>
                 \<Longrightarrow> corres_underlying sr nf nf' r ((=) s) ((=) s') f g \<rbrakk>
        \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  apply (simp add: corres_underlying_def split_def
                   Ball_def)
  apply blast
  done

lemma corres_return_trivial:
  "corres_underlying srel nf' nf dc \<top> \<top> (return a) (return b)"
  by (simp add: corres_underlying_def return_def)

lemma mapME_x_corres_same_xs:
  assumes x: "\<And>x. x \<in> set xs
      \<Longrightarrow> corres_underlying sr nf nf' (f \<oplus> dc) (P x) (P' x) (m x) (m' x)"
  assumes y: "\<And>x. x \<in> set xs \<Longrightarrow> \<lbrace>\<lambda>s. \<forall>y \<in> set xs. P y s\<rbrace> m x \<lbrace>\<lambda>_ s. \<forall>y \<in> set xs. P y s\<rbrace>,-"
             "\<And>x. x \<in> set xs \<Longrightarrow> \<lbrace>\<lambda>s. \<forall>y \<in> set xs. P' y s\<rbrace> m' x \<lbrace>\<lambda>_ s. \<forall>y \<in> set xs. P' y s\<rbrace>,-"
  assumes z: "xs = ys"
  shows      "corres_underlying sr nf nf' (f \<oplus> dc) (\<lambda>s. \<forall>x \<in> set xs. P x s) (\<lambda>s. \<forall>y \<in> set ys. P' y s)
                              (mapME_x m xs) (mapME_x m' ys)"
  apply (subgoal_tac "set ys \<subseteq> set xs
        \<Longrightarrow> corres_underlying sr nf nf' (f \<oplus> dc) (\<lambda>s. \<forall>x \<in> set xs. P x s) (\<lambda>s. \<forall>y \<in> set xs. P' y s)
                              (mapME_x m ys) (mapME_x m' ys)")
   apply (simp add: z)
proof (induct ys)
  case Nil
  show ?case
    by (simp add: mapME_x_def sequenceE_x_def returnOk_def)
next
  case (Cons z zs)
    from Cons have IH:
      "corres_underlying sr nf nf' (f \<oplus> dc) (\<lambda>s. \<forall>x\<in>set xs. P x s) (\<lambda>s. \<forall>y\<in>set xs. P' y s)
                       (mapME_x m zs) (mapME_x m' zs)"
      by (simp add: dc_def)
    from Cons have in_set:
      "z \<in> set xs" "set zs \<subseteq> set xs" by auto
  thus ?case
    apply (simp add: mapME_x_def sequenceE_x_def)
    apply (fold mapME_x_def sequenceE_x_def dc_def)
    apply (rule corres_guard_imp)
      apply (rule corres_splitEE)
         apply (rule x, simp)
        apply (rule IH)
       apply (wp y | simp)+
    done
qed

end
