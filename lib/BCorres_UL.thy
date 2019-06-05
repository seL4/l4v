(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory BCorres_UL
imports
  "Monad_WP/NonDetMonadVCG"
  Crunch_Instances_NonDet
begin

definition s_bcorres_underlying where
  "s_bcorres_underlying t f g s \<equiv> (\<lambda>(x,y). (x, t y)) ` (fst (f s)) \<subseteq> (fst (g (t s)))"

definition bcorres_underlying where
  "bcorres_underlying t f g \<equiv> \<forall>s. s_bcorres_underlying t f g s"

lemma wpc_helper_bcorres:
  "bcorres_underlying t f g \<Longrightarrow>  wpc_helper (P, P') (Q, Q') (bcorres_underlying t f g)"
  by (simp add: wpc_helper_def)

lemma wpc_helper_s_bcorres:
  "s_bcorres_underlying t f g s \<Longrightarrow>  wpc_helper (P, P') (Q, Q') (s_bcorres_underlying t f g s)"
  by (simp add: wpc_helper_def)

wpc_setup "\<lambda>f. bcorres_underlying t f g" wpc_helper_bcorres
wpc_setup "\<lambda>f. s_bcorres_underlying t f g s" wpc_helper_bcorres

lemma s_bcorres_underlying_split[wp_split]:
  "(\<And>r s'. (r,s') \<in> fst (f s) \<Longrightarrow>  (s_bcorres_underlying t (g r) (g' r) s')) \<Longrightarrow>
   s_bcorres_underlying t f f' s \<Longrightarrow>
   s_bcorres_underlying t (f >>= g) (f' >>= g') s"
  by (clarsimp simp: s_bcorres_underlying_def bind_def) force

lemma bcorres_underlying_split[wp_split]:
  "(\<And>r. (bcorres_underlying t (g r) (g' r))) \<Longrightarrow>
   bcorres_underlying t f f' \<Longrightarrow>
   bcorres_underlying t (f >>= g) (f' >>= g')"
  by (simp add: bcorres_underlying_def s_bcorres_underlying_split)

lemma get_s_bcorres_underlying[wp]:
  "s_bcorres_underlying t (f s) (f' (t s)) s \<Longrightarrow> s_bcorres_underlying t (get >>= f) (get >>= f') s"
  by (simp add: gets_def s_bcorres_underlying_def get_def bind_def return_def)

lemma get_bcorres[wp]:
  "(\<And>x. bcorres_underlying t (f x) (f' (t x))) \<Longrightarrow> bcorres_underlying t (get >>= f) (get >>= f')"
  by (simp add: bcorres_underlying_def get_s_bcorres_underlying)

lemma gets_s_bcorres_underlying[wp]:
  "x' (t s) = x s \<Longrightarrow>  s_bcorres_underlying t (gets x) (gets x') s"
  by (simp add: s_bcorres_underlying_def gets_def get_def bind_def return_def)

lemma gets_bcorres_underlying[wp]:
  "(\<And>s. x' (t s) = x s) \<Longrightarrow> bcorres_underlying t (gets x) (gets x')"
  by (simp add: bcorres_underlying_def gets_s_bcorres_underlying)

lemma gets_map_bcorres_underlying[wp]:
  "(\<And>s. f' (t s) p = f s p) \<Longrightarrow> bcorres_underlying t (gets_map f p) (gets_map f' p)"
  by (simp add: gets_map_def bcorres_underlying_def s_bcorres_underlying_def simpler_gets_def
                bind_def assert_opt_def fail_def return_def
        split: option.splits)

lemma gets_bcorres_underlying':
  "(\<And>xa. bcorres_underlying t (f (x xa)) (f' (x' (t xa)))) \<Longrightarrow>
  bcorres_underlying t (gets x >>= f) (gets x' >>= f')"
  by (wpsimp simp: gets_def)

lemma assert_bcorres_underlying[wp]:
  "f = f' \<Longrightarrow> bcorres_underlying t (assert f) (assert f')"
  by (simp add: assert_def bcorres_underlying_def return_def s_bcorres_underlying_def fail_def)

lemma return_bcorres[wp]:
  "bcorres_underlying t (return x) (return x)"
  by (simp add:return_def bcorres_underlying_def s_bcorres_underlying_def)

lemma drop_sbcorres_underlying:
  "bcorres_underlying t f g \<Longrightarrow> s_bcorres_underlying t f g s"
  by (simp add: bcorres_underlying_def)

lemma use_sbcorres_underlying:
  "(\<And>s. s_bcorres_underlying t f g s) \<Longrightarrow> bcorres_underlying t f g"
  by (simp add: bcorres_underlying_def)

lemma bcorres_underlying_throwError[wp]:
  "bcorres_underlying t (throwError a) (throwError a)"
  by (wpsimp simp: throwError_def)

lemma s_bcorres_underlying_splitE[wp_split]:
  "(\<And>r s'. (Inr r,s') \<in> fst (f s) \<Longrightarrow> s_bcorres_underlying t (g r) (g' r) s') \<Longrightarrow>
   s_bcorres_underlying t f f' s \<Longrightarrow>
   s_bcorres_underlying t (f >>=E g) (f' >>=E g') s"
  by (wpsimp simp: bindE_def lift_def split: sum.splits | rule conjI drop_sbcorres_underlying)+

lemma get_s_bcorres_underlyingE[wp]:
  "s_bcorres_underlying t (f s) (f' (t s)) s \<Longrightarrow>
   s_bcorres_underlying t (liftE get >>=E f) (liftE get >>=E f') s"
  by (simp add: gets_def s_bcorres_underlying_def get_def bindE_def bind_def return_def liftE_def lift_def)

lemma bcorres_underlying_splitE[wp_split]:
  "(\<And>r. bcorres_underlying t (g r) (g' r)) \<Longrightarrow>
   bcorres_underlying t f f' \<Longrightarrow>
   bcorres_underlying t (f >>=E g) (f' >>=E g')"
  by (simp add: bcorres_underlying_def s_bcorres_underlying_splitE)

lemmas return_s_bcorres_underlying[wp] = drop_sbcorres_underlying[OF return_bcorres]

lemma liftE_s_bcorres_underlying[wp]:
  "s_bcorres_underlying t f f' s \<Longrightarrow> s_bcorres_underlying t (liftE f) (liftE f') s"
  by (wpsimp simp: liftE_def)

lemma liftE_bcorres_underlying[wp]:
  "bcorres_underlying t f f' \<Longrightarrow>  bcorres_underlying t (liftE f) (liftE f')"
  by (simp add: bcorres_underlying_def liftE_s_bcorres_underlying)

lemma returnOk_bcorres_underlying[wp]:
  "bcorres_underlying t (returnOk x) (returnOk x)"
  by (wpsimp simp: returnOk_def)

lemma whenE_s_bcorres_underlying[wp]:
  "\<lbrakk> \<lbrakk>P = P'; P\<rbrakk> \<Longrightarrow> s_bcorres_underlying t f f' s; P = P' \<rbrakk> \<Longrightarrow>
   s_bcorres_underlying t (whenE P f) (whenE P' f') s"
  by (wpsimp simp: whenE_def|rule drop_sbcorres_underlying)+

lemma select_s_bcorres_underlying[wp]:
  "A \<subseteq> B \<Longrightarrow> s_bcorres_underlying t (select A) (select B) s"
  by (simp add: s_bcorres_underlying_def select_def image_def) blast

lemma fail_s_bcorres_underlying[wp]:
  "s_bcorres_underlying t fail fail s"
  by (simp add: s_bcorres_underlying_def fail_def)

lemma fail_bcorres_underlying[wp]:
  "bcorres_underlying t fail fail"
  by (simp add: bcorres_underlying_def fail_s_bcorres_underlying)

lemma assertE_bcorres_underlying[wp]:
  "bcorres_underlying t (assertE P) (assertE P)"
  by (wpsimp simp: assertE_def returnOk_def|rule conjI)+

lemmas assertE_s_bcorres_underlying[wp] = drop_sbcorres_underlying[OF assertE_bcorres_underlying]

lemma when_s_bcorres_underlying[wp]:
  "(P \<Longrightarrow> s_bcorres_underlying t f f' s) \<Longrightarrow> s_bcorres_underlying t (when P f) (when P f') s"
  by (simp add: return_s_bcorres_underlying when_def)

lemma when_bcorres_underlying[wp]:
  "(P \<Longrightarrow> bcorres_underlying t f f') \<Longrightarrow> bcorres_underlying t (when P f) (when P f')"
  by (simp add: bcorres_underlying_def when_s_bcorres_underlying)

lemma put_bcorres_underlying[wp]:
  "t f = f' \<Longrightarrow> bcorres_underlying t (put f) (put f')"
  by (simp add: bcorres_underlying_def s_bcorres_underlying_def put_def)

lemma modify_bcorres_underlying[wp]:
  "(\<And>x. t (f x) = f' (t x)) \<Longrightarrow> bcorres_underlying t (modify f) (modify f')"
  by (wpsimp simp: modify_def)

lemma liftM_bcorres_underlying[wp]:
  "bcorres_underlying t m m' \<Longrightarrow> bcorres_underlying t (liftM f m) (liftM f m')"
  by (wpsimp simp: liftM_def)

lemma sequence_x_bcorres_underlying[wp]:
  "(\<And>x. bcorres_underlying t (f x) (f' x)) \<Longrightarrow>
   bcorres_underlying t (sequence_x (map f xs)) (sequence_x (map f' xs))"
  by (induct xs; wpsimp simp: sequence_x_def)

lemma sequence_bcorres_underlying[wp]:
  "(\<And>x. bcorres_underlying t (f x) (f' x)) \<Longrightarrow>
   bcorres_underlying t (sequence (map f xs)) (sequence (map f' xs))"
  by (induct xs; wpsimp simp: sequence_def)

lemma mapM_x_bcorres_underlying[wp]:
  "(\<And>x. bcorres_underlying t (f x) (f' x)) \<Longrightarrow> bcorres_underlying t (mapM_x f xs) (mapM_x f' xs)"
  by (wpsimp simp: mapM_x_def)

lemma mapM_bcorres_underlying[wp]:
  "(\<And>x. bcorres_underlying t (f x) (f' x)) \<Longrightarrow> bcorres_underlying t (mapM f xs) (mapM f' xs)"
  by (simp add: mapM_def | wp)+

lemma gets_s_bcorres_underlyingE':
  "s_bcorres_underlying t (f (x s)) (f' (x' (t s))) s \<Longrightarrow>
   s_bcorres_underlying t (liftE (gets x) >>=E f) (liftE (gets x') >>=E f') s"
  by (simp add: gets_def liftE_def lift_def bindE_def) wp

lemma bcorres_underlying_filterM[wp]:
  "(\<And>x. bcorres_underlying t (a x) (a' x)) \<Longrightarrow> bcorres_underlying t (filterM a b) (filterM a' b)"
  by (induct b; wpsimp simp: filterM_def)

lemma option_rec_bcorres_underlying[wp_split]:
  "(\<And>x y. bcorres_underlying t (g x y) (g' x y)) \<Longrightarrow>
   (\<And>x. bcorres_underlying t (f x) (f' x)) \<Longrightarrow>
   bcorres_underlying t (rec_option f g a b) (rec_option f' g' a b)"
  by (cases a, simp+)

lemma bcorres_underlying_mapME[wp]:
  "(\<And>x. bcorres_underlying t (f x) (f' x)) \<Longrightarrow> bcorres_underlying t (mapME f r) (mapME f' r)"
  by (induct r; wpsimp simp: mapME_def sequenceE_def)

lemma handle2_bcorres_underlying[wp]:
  "bcorres_underlying t f f' \<Longrightarrow>
   (\<And>x. bcorres_underlying t (g x) (g' x)) \<Longrightarrow>
   bcorres_underlying t (f <handle2> g) (f' <handle2> g')"
  by (wpsimp simp: handleE'_def)

lemma liftME_bcorres_underlying[wp]:
  "bcorres_underlying t f f' \<Longrightarrow> bcorres_underlying t (liftME a f) (liftME a f')"
  by (wpsimp simp: liftME_def)

lemma zipWithM_x_bcorres[wp]:
  "(\<And>x y. bcorres_underlying t (f x y) (f' x y) ) \<Longrightarrow>
   bcorres_underlying t (zipWithM_x f xs ys) (zipWithM_x f' xs ys)"
  by (wpsimp simp: zipWithM_x_def zipWith_def split_def)

lemma mapME_x_bcorres_underlying[wp]:
  "(\<And>x. bcorres_underlying t (f x) (f' x)) \<Longrightarrow> bcorres_underlying t (mapME_x f xs) (mapME_x f' xs)"
  by (induct xs; wpsimp simp: mapME_x_def sequenceE_x_def)

lemma liftE_bind_bcorres[wp]:
  "bcorres_underlying t (f >>= g) (f' >>= g') \<Longrightarrow>
   bcorres_underlying t (liftE f >>=E g) (liftE f' >>=E g')"
  by (simp add: gets_def bcorres_underlying_def s_bcorres_underlying_def get_def bind_def return_def
                split_def liftE_def bindE_def lift_def)

lemma select_f_bcorres[wp]: "bcorres_underlying t (select_f f) (select_f f)"
  by (fastforce simp: select_f_def bcorres_underlying_def s_bcorres_underlying_def)

lemma bcorres_underlying_if[wp]:
  "(b \<Longrightarrow> bcorres_underlying t f f') \<Longrightarrow>
   (\<not>b \<Longrightarrow> bcorres_underlying t g g') \<Longrightarrow>
   bcorres_underlying t (if b then f else g) (if b then f' else g')"
  by (case_tac b; simp)

lemma assert_opt_bcorres_underlying[wp]:
  "bcorres_underlying t (assert_opt f) (assert_opt f)"
  by (wpsimp simp: assert_opt_def)

lemma unlessb_corres_underlying[wp]:
  "bcorres_underlying t f f' \<Longrightarrow> bcorres_underlying t (unless a f) (unless a f')"
  by (wpsimp simp: unless_def)

lemma select_bcorres_underlying[wp]:
  "A \<subseteq> B \<Longrightarrow> bcorres_underlying t (select A) (select B)"
  by (fastforce simp: bcorres_underlying_def select_def s_bcorres_underlying_def)

lemma catch_bcorres[wp]:
  "bcorres_underlying t f f' \<Longrightarrow>
   (\<And>x. bcorres_underlying t (g x) (g' x)) \<Longrightarrow>
   bcorres_underlying t (f <catch> g) (f' <catch> g')"
  unfolding catch_def by wpsimp

lemma whenE_bcorres_underlying[wp]:
  "\<lbrakk> \<lbrakk>P = P'; P\<rbrakk> \<Longrightarrow> bcorres_underlying t f f'; P = P' \<rbrakk> \<Longrightarrow>
  bcorres_underlying t (whenE P f) (whenE P' f')"
  unfolding whenE_def by wpsimp

lemma unlessE_bcorres[wp]:
  "bcorres_underlying t f f' \<Longrightarrow> bcorres_underlying t (unlessE P f) (unlessE P f')"
  by (wpsimp simp: unlessE_def)

lemma alternative_bcorres[wp]:
  "\<lbrakk> bcorres_underlying t f f';  bcorres_underlying t g g' \<rbrakk> \<Longrightarrow>
  bcorres_underlying t (f \<sqinter> g) (f' \<sqinter> g')"
  by (fastforce simp: alternative_def bcorres_underlying_def s_bcorres_underlying_def)

lemma gets_the_bcorres_underlying[wp]:
  "(\<And>s. f' (t s) = f s) \<Longrightarrow> bcorres_underlying t (gets_the f) (gets_the f')"
  by (wpsimp simp: gets_the_def)

ML \<open>
structure CrunchBCorresInstance : CrunchInstance =
struct
  val name = "bcorres";
  type extra = term;
  val eq_extra = ae_conv;
  fun parse_extra ctxt extra
        = case extra of
             "" => error "bcorres needs truncate function"
             | e =>(Syntax.parse_term ctxt "%_. True", Syntax.parse_term ctxt e);
  val has_preconds = false;
  fun mk_term _ body extra =
    (Syntax.parse_term @{context} "bcorres_underlying") $ extra $ body $ body;
  fun dest_term (Const (@{const_name "bcorres_underlying"}, _) $ extra $ body $ _)
        = SOME (Term.dummy, body, extra)
    | dest_term _ = NONE;
  fun put_precond _ ((v as Const (@{const_name "bcorres_underlying"}, _)) $ extra $ body $ body')
        = v $ extra $ body $ body'
    | put_precond _ _ = error "put_precond: not an bcorres term";
  val pre_thms = [];
  val wpc_tactic = WeakestPreCases.wp_cases_tac @{thms wpc_processors};
  val magic = Syntax.parse_term @{context}
    "\<lambda>mapp_lambda_ignore. bcorres_underlying t_free_ignore mapp_lambda_ignore g_free_ignore";
  val get_monad_state_type = get_nondet_monad_state_type;
end;

structure CrunchBCorres : CRUNCH = Crunch(CrunchBCorresInstance);
\<close>

setup \<open>
  add_crunch_instance "bcorres" (CrunchBCorres.crunch_x, CrunchBCorres.crunch_ignore_add_del)
\<close>

end
