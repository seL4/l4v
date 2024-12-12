(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Contributions by:
 *   2012 Lars Noschinski <noschinl@in.tum.de>
 *     Option monad while loop formalisation.
 *)

chapter \<open>State Projections and Reader Option Monad\<close>

theory Reader_Option_Monad
  imports
    Monad_Lib
    Fun_Pred_Syntax
    Less_Monad_Syntax
begin

section \<open>Projections\<close>

type_synonym ('s,'a) lookup = "'s \<Rightarrow> 'a option"

text \<open>Similar to @{const map_option} but the second function returns @{text option} as well\<close>
definition opt_map :: "('s,'a) lookup \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> ('s,'b) lookup" (infixl "|>" 54) where
  "f |> g \<equiv> \<lambda>s. case f s of None \<Rightarrow> None | Some x \<Rightarrow> g x"

abbreviation opt_map_Some :: "('s \<rightharpoonup> 'a) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 's \<rightharpoonup> 'b" (infixl "||>" 54) where
  "f ||> g \<equiv> f |> (\<lambda>s. Some (g s))"

lemmas opt_map_Some_def = opt_map_def

definition map_set :: "('a \<Rightarrow> 'b set option) \<Rightarrow> 'a \<Rightarrow> 'b set" where
  "map_set f \<equiv> case_option {} id \<circ> f"

definition opt_pred :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a option) \<Rightarrow> ('b \<Rightarrow> bool)" (infixl "|<" 55) where
  "P |< proj \<equiv> (\<lambda>x. case_option False P (proj x))"


subsection \<open>Lemmas for @{const opt_map}\<close>

lemma opt_map_cong[fundef_cong]:
  "\<lbrakk> f = f'; \<And>v s. f s = Some v \<Longrightarrow> g v = g' v\<rbrakk> \<Longrightarrow> f |> g = f' |> g'"
  by (rule ext) (simp add: opt_map_def split: option.splits)

lemma in_opt_map_eq:
  "((f |> g) s = Some v) = (\<exists>v'. f s = Some v' \<and> g v' = Some v)"
  by (simp add: opt_map_def split: option.splits)

lemma in_opt_map_None_eq:
  "((f |> g) s = None) = (f s = None \<or> (\<exists>v. f s = Some v \<and> g v = None))"
  by (simp add: opt_map_def split: option.splits)

lemma opt_mapE:
  "\<lbrakk> (f |> g) s = Some v; \<And>v'. \<lbrakk>f s = Some v'; g v' = Some v \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto simp: in_opt_map_eq)

lemma opt_map_red:
  "f x = Some y \<Longrightarrow> (f |> g) x = g y"
  by (clarsimp simp: opt_map_def)

lemma opt_map_left_None:
  "f x = None \<Longrightarrow> (f |> g) x = None"
  by (clarsimp simp: opt_map_def)

lemma opt_map_assoc:
  "f |> (g |> h) = f |> g |> h"
  by (fastforce simp: opt_map_def split: option.splits)

lemma opt_map_if_l:
  "(if P then f else f') |> g = (if P then f |> g else f' |> g)"
  by (auto simp: opt_map_def)

lemma opt_map_if_r:
  "f |> (if P then g else g') = (if P then f |> g else f |> g')"
  by (auto simp: opt_map_def)

lemma opt_map_upd_None:
  "f(x := None) |> g = (f |> g)(x := None)"
  by (auto simp: opt_map_def)

lemma opt_map_upd_Some:
  "f(x \<mapsto> v) |> g = (f |> g)(x := g v)"
  by (auto simp: opt_map_def)

lemma opt_map_Some_upd_Some:
  "f(x \<mapsto> v) ||> g = (f ||> g)(x \<mapsto> g v)"
  by (simp add: opt_map_upd_Some)

lemmas opt_map_upd[simp] = opt_map_upd_None opt_map_upd_Some opt_map_Some_upd_Some

lemma opt_map_upd_triv:
  "t k = Some x \<Longrightarrow> (t |> f)(k := f x) = t |> f"
  by (rule ext) (clarsimp simp add: opt_map_red)

lemma opt_map_Some_upd_triv:
  "t k = Some x \<Longrightarrow> (t ||> f)(k \<mapsto> f x) = t ||> f"
  by (rule ext) (clarsimp simp add: opt_map_red)

lemma opt_map_upd_triv_None:
  "t k = None \<Longrightarrow> (t |> f)(k := None) = t |> f"
  by (rule ext) (clarsimp simp add: opt_map_def)

lemmas opt_map_upd_triv_simps = opt_map_upd_triv opt_map_Some_upd_triv opt_map_upd_triv_None

lemma opt_map_foldr_upd:
  "foldr (\<lambda>p kh. kh(p := new)) ptrs f |> g
   = foldr (\<lambda>p kh. kh(p := (case new of Some x \<Rightarrow> g x | _ \<Rightarrow> None))) ptrs (f |> g)"
  by (induct ptrs arbitrary: new; clarsimp split: option.splits)

lemma opt_map_Some_foldr_upd:
  "foldr (\<lambda>p kh. kh(p := new)) ptrs f ||> g
   = foldr (\<lambda>p kh. kh(p := map_option g new)) ptrs (f ||> g)"
  by (induct ptrs arbitrary: new; clarsimp simp: map_option_case split: option.splits)

lemmas opt_map_foldr_upd_simps = opt_map_foldr_upd opt_map_Some_foldr_upd

lemma opt_map_Some_comp[simp]:
  "f ||> g ||> h = f ||> h o g"
  by (fastforce simp: opt_map_def split: option.split)

lemma opt_map_fold_l:
  "(id |> g) (f x) = (f |> g) x"
  by (clarsimp simp: opt_map_def)

(* LHS is the same as (f ||> id) *)
lemma opt_map_Some_id_r[simp]:
  "f |> Some = f"
  by (fastforce simp: opt_map_def split: option.split)

lemma opt_map_Some_id_l[simp]:
  "Some |> f = f"
  by (clarsimp simp: opt_map_def split: option.split)

lemma opt_map_zero_l[simp]:
  "Map.empty |> g = Map.empty"
  by (clarsimp simp: opt_map_def)

lemma opt_map_zero_r[simp]:
  "f |> Map.empty = Map.empty"
  by (fastforce simp: opt_map_def split: option.split)

lemma opt_map_Some_eta_fold:
  "f |> (\<lambda>x. Some (g x)) = f ||> g"
  by (simp add: o_def)

lemma case_opt_map_distrib:
  "(\<lambda>s. case_option None g (f s)) |> h = (\<lambda>s. case_option None (g |> h) (f s))"
  by (fastforce simp: opt_map_def split: option.splits)

lemma opt_map_apply_left_eq:
  "f s = f s' \<Longrightarrow> (f |> g) s = (f |> g) s'"
  by (simp add: opt_map_def)

declare None_upd_eq[simp]

(* None_upd_eq[simp] so that this pattern is by simp. Hopefully not too much slowdown. *)
lemma "\<lbrakk> (f |> g) x = None; g v = None \<rbrakk> \<Longrightarrow> f(x \<mapsto> v) |> g = f |> g"
  by simp

subsection \<open>Lemmas for @{const opt_pred}\<close>

lemma opt_pred_conj:
  "((P |< hp) p \<and> (Q |< hp) p) = ((P and Q) |< hp) p"
  by (fastforce simp: pred_conj_def opt_pred_def split: option.splits)

lemma opt_pred_disj:
  "((P |< hp) p \<or> (Q |< hp) p) = ((P or Q) |< hp) p"
  by (fastforce simp: pred_disj_def opt_pred_def split: option.splits)

lemma in_opt_pred:
  "(P |< f) p = (\<exists>v. f p = Some v \<and> P v)"
  by (auto simp: opt_pred_def split: option.splits)

lemmas opt_predD = in_opt_pred[THEN iffD1]

lemma opt_predE:
  "\<lbrakk>(P |< proj) x; \<And>y. \<lbrakk>proj x = Some y; P y\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (blast dest: opt_predD)

lemma opt_pred_unfold_map:
  "P |< (f |> g) = P |< g |< f"
  by (fastforce simp: opt_map_def in_opt_pred split: option.splits)

lemma opt_pred_unfold_proj:
  "P |< (f ||> g) = P o g |< f"
  by (clarsimp simp: opt_map_def opt_pred_def split: option.splits)

lemma opt_pred_proj_upd_eq[simp]:
  "(P |< proj (p \<mapsto> v)) p = P v"
  by (simp add: in_opt_pred)


section \<open>The Reader Option Monad\<close>

definition obind :: "('s,'a) lookup \<Rightarrow> ('a \<Rightarrow> ('s,'b) lookup) \<Rightarrow> ('s,'b) lookup" (infixl "|>>" 53)
  where
  "f |>> g \<equiv> \<lambda>s. case f s of None \<Rightarrow> None | Some x \<Rightarrow> g x s"

(* Enable "do { .. }" syntax *)
adhoc_overloading
  Monad_Syntax.bind obind

definition ofail :: "('s, 'a) lookup" where
  "ofail = K None"

definition oreturn :: "'a \<Rightarrow> ('s, 'a) lookup" where
  "oreturn = K o Some"

definition oassert :: "bool \<Rightarrow> ('s, unit) lookup" where
  "oassert P \<equiv> if P then oreturn () else ofail"

definition oassert_opt :: "'a option \<Rightarrow> ('s, 'a) lookup" where
  "oassert_opt r \<equiv> case r of None \<Rightarrow> ofail | Some x \<Rightarrow> oreturn x"

definition ostate_assert :: "('s \<Rightarrow> bool) \<Rightarrow> ('s, unit) lookup" where
  "ostate_assert P \<equiv> do { s \<leftarrow> Some; oassert (P s)}"

definition oapply :: "'a \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> 'b option" where
  "oapply x \<equiv> \<lambda>s. s x"

definition oapply2 :: "'a \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c option) \<Rightarrow> 'c option" where
  "oapply2 x y \<equiv> \<lambda>s. s x y"

definition oliftM :: "('a \<Rightarrow> 'b) \<Rightarrow> ('s,'a) lookup \<Rightarrow> ('s,'b) lookup" where
  "oliftM f m \<equiv> do { x \<leftarrow> m; oreturn (f x) }"

definition ounless :: "bool \<Rightarrow> ('s, unit) lookup \<Rightarrow> ('s, unit) lookup" where
  "ounless P f \<equiv> if P then oreturn () else f"

definition owhen :: "bool \<Rightarrow> ('s, unit) lookup \<Rightarrow> ('s, unit) lookup" where
  "owhen P f \<equiv> if P then f else oreturn ()"

(* Reader monad interface: *)
abbreviation (input) ask :: "('s, 's) lookup" where
  "ask \<equiv> Some"

definition asks :: "('s \<Rightarrow> 'a) \<Rightarrow> ('s, 'a) lookup" where
  "asks f = do { v <- ask; oreturn (f v) }"

abbreviation ogets :: "('s \<Rightarrow> 'a) \<Rightarrow> ('s, 'a) lookup" where
  "ogets \<equiv> asks"

text \<open>
  Integration with exception monad.
  Corresponding bindE would be analogous to lifting in @{text Nondet_Monad}.\<close>

definition
  "oreturnOk x = K (Some (Inr x))"

definition
  "othrow e = K (Some (Inl e))"

definition
  "oguard G \<equiv> \<lambda>s. if G s then Some () else None"

definition
  "ocondition c L R \<equiv> \<lambda>s. if c s then L s else R s"

definition
  "oskip \<equiv> oreturn ()"

lemma ogets_def:
  "ogets f = (\<lambda>s. Some (f s))"
  by (clarsimp simp: asks_def obind_def oreturn_def)

lemmas omonad_defs = ofail_def oreturn_def oassert_def oassert_opt_def ogets_def ounless_def
                     owhen_def


subsection \<open>Monad laws\<close>

lemma oreturn_bind[simp]:
  "(oreturn x |>> f) = f x"
  by (auto simp add: oreturn_def obind_def)

lemma obind_return[simp]:
  "(m |>> oreturn) = m"
  by (auto simp add: oreturn_def obind_def split: option.splits)

lemma obind_assoc:
  "(m |>> f) |>> g  =  m |>> (\<lambda>x. f x |>> g)"
  by (auto simp add: oreturn_def obind_def split: option.splits)


subsection \<open>Binding and fail\<close>

lemma obind_fail [simp]:
  "f |>> (\<lambda>_. ofail) = ofail"
  by (auto simp add: ofail_def obind_def split: option.splits)

lemma ofail_bind [simp]:
  "ofail |>> m = ofail"
  by (auto simp add: ofail_def obind_def split: option.splits)


subsection \<open>Function package setup\<close>

lemma opt_bind_cong[fundef_cong]:
  "\<lbrakk> f = f'; \<And>v s. f' s = Some v \<Longrightarrow> g v s = g' v s \<rbrakk> \<Longrightarrow> f |>> g = f' |>> g'"
  by (rule ext) (simp add: obind_def split: option.splits)

lemma opt_bind_cong_apply[fundef_cong]:
  "\<lbrakk> f s = f' s; \<And>v. f' s = Some v \<Longrightarrow> g v s = g' v s \<rbrakk> \<Longrightarrow> (f |>> g) s = (f' |>> g') s"
  by (simp add: obind_def split: option.splits)

lemma oassert_bind_cong[fundef_cong]:
  "\<lbrakk> P = P'; P' \<Longrightarrow> m = m' \<rbrakk> \<Longrightarrow> oassert P |>> m = oassert P' |>> m'"
  by (auto simp: oassert_def)

lemma oassert_bind_cong_apply[fundef_cong]:
  "\<lbrakk> P = P'; P' \<Longrightarrow> m () s = m' () s \<rbrakk> \<Longrightarrow> (oassert P |>> m) s = (oassert P' |>> m') s"
  by (auto simp: oassert_def)

lemma oreturn_bind_cong[fundef_cong]:
  "\<lbrakk> x = x'; m x' = m' x' \<rbrakk> \<Longrightarrow> oreturn x |>> m = oreturn x' |>> m'"
  by simp

lemma oreturn_bind_cong_apply[fundef_cong]:
  "\<lbrakk> x = x'; m x' s = m' x' s \<rbrakk> \<Longrightarrow> (oreturn x |>> m) s = (oreturn x' |>> m') s"
  by simp

lemma oreturn_bind_cong2[fundef_cong]:
  "\<lbrakk> x = x'; m x' = m' x' \<rbrakk> \<Longrightarrow> (oreturn $ x) |>> m = (oreturn $ x') |>> m'"
  by simp

lemma oreturn_bind_cong2_apply[fundef_cong]:
  "\<lbrakk> x = x'; m x' s = m' x' s \<rbrakk> \<Longrightarrow> ((oreturn $ x) |>> m) s = ((oreturn $ x') |>> m') s"
  by simp

lemma ocondition_cong[fundef_cong]:
"\<lbrakk>c = c'; \<And>s. c' s \<Longrightarrow> l s = l' s; \<And>s. \<not>c' s \<Longrightarrow> r s = r' s\<rbrakk>
  \<Longrightarrow> ocondition c l r = ocondition c' l' r'"
  by (auto simp: ocondition_def)


subsection \<open>Decomposition\<close>

lemma ocondition_K_true[simp]:
  "ocondition (\<lambda>_. True) T F = T"
  by (simp add: ocondition_def)

lemma ocondition_K_false[simp]:
  "ocondition (\<lambda>_. False) T F = F"
  by (simp add: ocondition_def)

lemma ocondition_False:
    "\<lbrakk> \<And>s. \<not> P s \<rbrakk> \<Longrightarrow> ocondition P L R = R"
  by (rule ext, clarsimp simp: ocondition_def)

lemma ocondition_True:
    "\<lbrakk> \<And>s. P s \<rbrakk> \<Longrightarrow> ocondition P L R = L"
  by (rule ext, clarsimp simp: ocondition_def)

lemma in_oreturn [simp]:
  "(oreturn x s = Some v) = (v = x)"
  by (auto simp: oreturn_def)

lemma oreturn_None[simp]:
  "\<not> oreturn x s = None"
  by (simp add: oreturn_def)

lemma oreturnE:
  "\<lbrakk>oreturn x s = Some v; v = x \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by simp

lemma in_ofail[simp]:
  "ofail s \<noteq> Some v"
  by (auto simp: ofail_def)

lemma ofailE:
  "ofail s = Some v \<Longrightarrow> P"
  by simp

lemma in_oassert_eq[simp]:
  "(oassert P s = Some v) = P"
  by (simp add: oassert_def)

lemma oassert_True[simp]:
  "oassert True = oreturn ()"
  by (simp add: oassert_def)

lemma oassert_False[simp]:
  "oassert False = ofail"
  by (simp add: oassert_def)

lemma oassertE:
  "\<lbrakk> oassert P s = Some v; P \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by simp

lemma in_obind_eq:
  "((f |>> g) s = Some v) = (\<exists>v'. f s = Some v' \<and> g v' s = Some v)"
  by (simp add: obind_def split: option.splits)

lemma obind_None_eq:
  "((f |>> g) s = None) = (f s = None \<or> (\<exists>v. f s = Some v \<and> g v s = None))"
  by (simp add: obind_def split: option.split)

lemma obind_eqI:
  "\<lbrakk> f s = f s' ; \<And>x. f s = Some x \<Longrightarrow> g x s = g' x s' \<rbrakk> \<Longrightarrow> obind f g s = obind f g' s'"
  by (simp add: obind_def split: option.splits)

(* full form of obind_eqI; the second equality makes more sense flipped here, as we end up
   with "f s = Some x ; f s' = f s" preventing "Some x = ..." *)
lemma obind_eqI_full:
  "\<lbrakk> f s = f s' ; \<And>x. \<lbrakk> f s = Some x; f s' = f s \<rbrakk> \<Longrightarrow> g x s = g' x s' \<rbrakk>
   \<Longrightarrow> obind f g s = obind f g' s'"
  by (drule sym[where s="f s"]) (* prevent looping *)
     (clarsimp simp: obind_def split: option.splits)

lemma obindE:
  "\<lbrakk> (f |>> g) s = Some v; \<And>v'. \<lbrakk>f s = Some v'; g v' s = Some v\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (auto simp: in_obind_eq)

lemma in_othrow_eq[simp]:
  "(othrow e s = Some v) = (v = Inl e)"
  by (auto simp: othrow_def)

lemma othrowE:
  "\<lbrakk>othrow e s = Some v; v = Inl e \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by simp

lemma in_oreturnOk_eq[simp]:
  "(oreturnOk x s = Some v) = (v = Inr x)"
  by (auto simp: oreturnOk_def)

lemma oreturnOkE:
  "\<lbrakk>oreturnOk x s = Some v; v = Inr x \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by simp

lemmas omonadE[elim!] = obindE oreturnE ofailE othrowE oreturnOkE oassertE

lemma in_opt_map_Some_eq:
  "((f ||> g) x = Some y) = (\<exists>v. f x = Some v \<and> g v = y)"
  by (simp add: in_opt_map_eq)

lemma in_opt_map_Some_None_eq[simp]:
  "((f ||> g) x = None) = (f x = None)"
  by (simp add: opt_map_def split: option.splits)

lemma oreturn_comp[simp]:
  "oreturn x \<circ> f = oreturn x"
  by (simp add: oreturn_def o_def)

lemma ofail_comp[simp]:
  "ofail \<circ> f = ofail"
  by (auto simp: ofail_def)

lemma oassert_comp[simp]:
  "oassert P \<circ> f = oassert P"
  by (simp add: oassert_def)

lemma fail_apply[simp]:
  "ofail s = None"
  by (simp add: ofail_def)

lemma oassert_apply[simp]:
  "oassert P s = (if P then Some () else None)"
  by (simp add: oassert_def)

lemma oreturn_apply[simp]:
  "oreturn x s = Some x"
  by simp

lemma oapply_apply[simp]:
  "oapply x s = s x"
  by (simp add: oapply_def)

lemma oapply2_apply[simp]:
  "oapply2 x y s = s x y"
  by (simp add: oapply2_def)

lemma obind_comp_dist:
  "obind f g o h = obind (f o h) (\<lambda>x. g x o h)"
  by (auto simp: obind_def split: option.splits)

lemma if_comp_dist:
  "(if P then f else g) o h = (if P then f o h else g o h)"
  by auto

lemma obindK_is_opt_map:
  "f \<bind> (\<lambda>x. K $ g x) = f |> g"
  by (simp add: obind_def opt_map_def)

lemmas in_omonad = bind_eq_Some_conv in_obind_eq in_opt_map_eq in_opt_pred Let_def


section \<open>"While" loops over option monad.\<close>

text \<open>
  This is an inductive definition of a while loop over the plain option monad
  (without passing through a state)
\<close>

inductive_set option_while' :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a option) \<Rightarrow> 'a option rel" for C B where
    final: "\<not> C r \<Longrightarrow> (Some r, Some r) \<in> option_while' C B"
  | fail: "\<lbrakk> C r; B r = None \<rbrakk> \<Longrightarrow> (Some r, None) \<in> option_while' C B"
  | step: "\<lbrakk> C r;  B r = Some r'; (Some r', sr'') \<in> option_while' C B \<rbrakk>
           \<Longrightarrow> (Some r, sr'') \<in> option_while' C B"

definition
  "option_while C B r \<equiv>
    (if (\<exists>s. (Some r, s) \<in> option_while' C B) then
      (THE s. (Some r, s) \<in> option_while' C B) else None)"

lemma option_while'_inj:
  assumes "(s,s') \<in> option_while' C B" "(s, s'') \<in> option_while' C B"
  shows "s' = s''"
  using assms
  by (induct rule: option_while'.induct) (auto elim: option_while'.cases)

lemma option_while'_inj_step:
  "\<lbrakk> C s; B s = Some s'; (Some s, t) \<in> option_while' C B ; (Some s', t') \<in> option_while' C B \<rbrakk>
   \<Longrightarrow> t = t'"
  by (metis option_while'.step option_while'_inj)

lemma option_while'_THE:
  assumes "(Some r, sr') \<in> option_while' C B"
  shows "(THE s. (Some r, s) \<in> option_while' C B) = sr'"
  using assms by (blast dest: option_while'_inj)

lemma option_while_simps:
  "\<not> C s \<Longrightarrow> option_while C B s = Some s"
  "C s \<Longrightarrow> B s = None \<Longrightarrow> option_while C B s = None"
  "C s \<Longrightarrow> B s = Some s' \<Longrightarrow> option_while C B s = option_while C B s'"
  "(Some s, ss') \<in> option_while' C B \<Longrightarrow> option_while C B s = ss'"
  using option_while'_inj_step[of C s B s']
  by (auto simp: option_while_def option_while'_THE
           intro: option_while'.intros
           dest: option_while'_inj
           elim: option_while'.cases)

lemma option_while_rule:
  assumes "option_while C B s = Some s'"
  assumes "I s"
  assumes istep: "\<And>s s'. C s \<Longrightarrow> I s \<Longrightarrow> B s = Some s' \<Longrightarrow> I s'"
  shows "I s' \<and> \<not> C s'"
proof -
  { fix ss ss' assume "(ss, ss') \<in> option_while' C B" "ss = Some s" "ss' = Some s'"
    then have ?thesis using \<open>I s\<close>
      by (induct arbitrary: s) (auto intro: istep) }
  then show ?thesis using assms(1)
    by (auto simp: option_while_def option_while'_THE split: if_split_asm)
qed

lemma option_while'_term:
  assumes "I r"
  assumes "wf M"
  assumes step_less: "\<And>r r'. \<lbrakk>I r; C r; B r = Some r'\<rbrakk> \<Longrightarrow> (r',r) \<in> M"
  assumes step_I: "\<And>r r'. \<lbrakk>I r; C r; B r = Some r'\<rbrakk> \<Longrightarrow> I r'"
  obtains sr' where "(Some r, sr') \<in> option_while' C B"
  apply atomize_elim
  using assms(2,1)
proof induct
  case (less r)
  show ?case
  proof (cases "C r" "B r" rule: bool.exhaust[case_product option.exhaust])
    case (True_Some r')
    then have "(r',r) \<in> M" "I r'"
      by (auto intro: less step_less step_I)
    then obtain sr' where "(Some r', sr') \<in> option_while' C B"
      by atomize_elim (rule less)
    then have "(Some r, sr') \<in> option_while' C B"
      using True_Some by (auto intro: option_while'.intros)
    then show ?thesis ..
  qed (auto intro: option_while'.intros)
qed

lemma option_while_rule':
  assumes "option_while C B s = ss'"
  assumes "wf M"
  assumes "I (Some s)"
  assumes less: "\<And>s s'. C s \<Longrightarrow> I (Some s) \<Longrightarrow> B s = Some s' \<Longrightarrow> (s', s) \<in> M"
  assumes step: "\<And>s s'. C s \<Longrightarrow> I (Some s) \<Longrightarrow> B s = Some s' \<Longrightarrow> I (Some s')"
  assumes final: "\<And>s. C s \<Longrightarrow> I (Some s) \<Longrightarrow> B s = None \<Longrightarrow> I None"
  shows "I ss' \<and> (case ss' of Some s' \<Rightarrow> \<not> C s' | _ \<Rightarrow> True)"
proof -
  define ss where "ss \<equiv> Some s"
  obtain ss1' where "(Some s, ss1') \<in> option_while' C B"
    using assms(3,2,4,5) by (rule option_while'_term)
  then have *: "(ss, ss') \<in> option_while' C B" using \<open>option_while C B s = ss'\<close>
    by (auto simp: option_while_simps ss_def)
  show ?thesis
  proof (cases ss')
    case (Some s') with * ss_def show ?thesis using \<open>I _\<close>
      by (induct arbitrary:s) (auto intro: step)
  next
    case None with * ss_def show ?thesis using \<open>I _\<close>
      by (induct arbitrary:s) (auto intro: step final)
  qed
qed


section \<open>Lift @{term option_while} to the @{typ "('a,'s) lookup"} monad\<close>

definition owhile :: "('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> ('s,'a) lookup) \<Rightarrow> 'a \<Rightarrow> ('s,'a) lookup" where
 "owhile c b a \<equiv> \<lambda>s. option_while (\<lambda>a. c a s) (\<lambda>a. b a s) a"

lemma owhile_unroll:
  "owhile C B r = ocondition (C r) (B r |>> owhile C B) (oreturn r)"
  by (auto simp: ocondition_def obind_def oreturn_def owhile_def
                 option_while_simps
           split: option.split)

text \<open>Rule for terminating loops\<close>

lemma owhile_rule:
  assumes "I r s"
  assumes "wf M"
  assumes less: "\<And>r r'. \<lbrakk>I r s; C r s; B r s = Some r'\<rbrakk> \<Longrightarrow> (r',r) \<in> M"
  assumes step: "\<And>r r'. \<lbrakk>I r s; C r s; B r s = Some r'\<rbrakk> \<Longrightarrow> I r' s"
  assumes fail: "\<And>r. \<lbrakk>I r s; C r s; B r s = None\<rbrakk> \<Longrightarrow> Q None"
  assumes final: "\<And>r. \<lbrakk>I r s; \<not>C r s\<rbrakk> \<Longrightarrow> Q (Some r)"
  shows "Q (owhile C B r s)"
proof -
  let ?rs' = "owhile C B r s"
  have "(case ?rs' of Some r \<Rightarrow> I r s | _ \<Rightarrow> Q None)
      \<and> (case ?rs' of Some r' \<Rightarrow> \<not> C r' s | _ \<Rightarrow> True)"
    by (rule option_while_rule'[where B="\<lambda>r. B r s" and s=r, OF _ \<open>wf _\<close>])
       (auto simp: owhile_def intro: assms)
  then show ?thesis by (auto intro: final split: option.split_asm)
qed

end
