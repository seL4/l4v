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
  Crunch
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

lemma s_bcorres_underlying_split[wp_split]: "(\<And>r s'. (r,s') \<in> fst (f s) \<Longrightarrow>  (s_bcorres_underlying t (g r) (g' r) s')) \<Longrightarrow>  s_bcorres_underlying t f f' s \<Longrightarrow>  s_bcorres_underlying t (f >>= g) (f' >>= g') s"
  apply (simp add: s_bcorres_underlying_def)
  apply clarsimp
  apply (simp add: bind_def split_def)
  apply (simp add: split_def image_def)
  apply force
   done

lemma bcorres_underlying_split[wp_split]: "(\<And>r. (bcorres_underlying t (g r) (g' r))) \<Longrightarrow> bcorres_underlying t f f' \<Longrightarrow>  bcorres_underlying t (f >>= g) (f' >>= g')"
  apply (simp add: bcorres_underlying_def s_bcorres_underlying_split)
  done

lemma get_s_bcorres_underlying[wp]: "s_bcorres_underlying t (f s) (f' (t s)) s  \<Longrightarrow> s_bcorres_underlying t (get >>= f) (get >>= f') s"
  apply (simp add: gets_def s_bcorres_underlying_def get_def bind_def return_def)
  done

lemma get_bcorres[wp]: "(\<And>x. bcorres_underlying t (f x) (f' (t x)))  \<Longrightarrow> bcorres_underlying t (get >>= f) (get >>= f')"
  apply (simp add: bcorres_underlying_def get_s_bcorres_underlying)
  done

lemma gets_s_bcorres_underlying[wp]: "x' (t s) = x s \<Longrightarrow>  s_bcorres_underlying t (gets x) (gets x') s"
  apply (simp add: s_bcorres_underlying_def gets_def get_def bind_def return_def)
  done

lemma gets_bcorres_underlying[wp]: "(\<And>s. x' (t s) = x s) \<Longrightarrow> bcorres_underlying t (gets x) (gets x')"
  apply (simp add: bcorres_underlying_def gets_s_bcorres_underlying)
  done


lemma gets_bcorres_underlying': "(\<And>xa. bcorres_underlying t (f (x xa)) (f' (x' (t xa)))) \<Longrightarrow> bcorres_underlying t (gets x >>= f) (gets x' >>= f')"
  apply (simp add: gets_def)
  apply wp
  apply simp
  done

lemma assert_bcorres_underlying[wp]: "f = f' \<Longrightarrow>  bcorres_underlying t (assert f) (assert f')"
  apply (simp add: assert_def bcorres_underlying_def return_def s_bcorres_underlying_def fail_def)
  done

lemma return_bcorres[wp]: "bcorres_underlying t (return x) (return x)"
  apply (simp add:return_def bcorres_underlying_def s_bcorres_underlying_def)
  done

lemma drop_sbcorres_underlying: "bcorres_underlying t f g \<Longrightarrow> s_bcorres_underlying t f g s"
  apply (simp add: bcorres_underlying_def)
  done

lemma use_sbcorres_underlying: "(\<And>s. s_bcorres_underlying t f g s) \<Longrightarrow>  bcorres_underlying t f g"
  apply (simp add: bcorres_underlying_def)
  done

lemma bcorres_underlying_throwError[wp]: "bcorres_underlying t (throwError a) (throwError a)"
  apply (simp add: throwError_def)
  apply wp
  done


lemma s_bcorres_underlying_splitE[wp_split]: "(\<And>r s'. (Inr r,s') \<in> fst (f s)  \<Longrightarrow>  (s_bcorres_underlying t (g r) (g' r) s')) \<Longrightarrow>  s_bcorres_underlying t f f' s \<Longrightarrow> s_bcorres_underlying t (f >>=E g) (f' >>=E g') s"
  apply (simp add: bindE_def)
  apply (wp | simp)+
  apply (simp add: lift_def)
  apply (case_tac r)
  apply simp
  apply (rule drop_sbcorres_underlying)
  apply (wp | simp)+
  done


lemma get_s_bcorres_underlyingE[wp]: "s_bcorres_underlying t (f s) (f' (t s)) s \<Longrightarrow> s_bcorres_underlying t ( liftE (get) >>=E f) ( liftE (get) >>=E f') s"
  apply (simp add: gets_def s_bcorres_underlying_def get_def bindE_def bind_def return_def liftE_def lift_def)
  done


lemma bcorres_underlying_splitE[wp_split]: "(\<And>r. (bcorres_underlying t (g r) (g' r))) \<Longrightarrow>  bcorres_underlying t f f' \<Longrightarrow>  bcorres_underlying t (f >>=E g) (f' >>=E g')"
  apply (simp add: bcorres_underlying_def s_bcorres_underlying_splitE)
  done

lemmas return_s_bcorres_underlying[wp] = drop_sbcorres_underlying[OF return_bcorres]

lemma liftE_s_bcorres_underlying[wp]: "s_bcorres_underlying t f f' s \<Longrightarrow>  s_bcorres_underlying t (liftE f) (liftE f') s"
  apply (simp add: liftE_def)
  apply (wp | simp)+
  done

lemma liftE_bcorres_underlying[wp]: "bcorres_underlying t f f' \<Longrightarrow>  bcorres_underlying t (liftE f) (liftE f')"
  apply (simp add: bcorres_underlying_def liftE_s_bcorres_underlying)
  done

lemma returnOk_bcorres_underlying[wp]: "bcorres_underlying t (returnOk x) (returnOk x)"
  apply (simp add: returnOk_def)
  apply wp
  done

lemma whenE_s_bcorres_underlying[wp]: "(P = P' \<Longrightarrow> P \<Longrightarrow> s_bcorres_underlying t f f' s) \<Longrightarrow> P = P'  \<Longrightarrow> s_bcorres_underlying t (whenE P f) (whenE P' f') s"
  apply (clarsimp simp add: whenE_def)
  apply (rule drop_sbcorres_underlying)
  apply wp
  done

lemma select_s_bcorres_underlying[wp]: "A \<subseteq> B \<Longrightarrow>  s_bcorres_underlying t (select A) (select B) s"
  apply (simp add: s_bcorres_underlying_def select_def image_def)
  apply blast
  done

lemma fail_s_bcorres_underlying[wp]: "s_bcorres_underlying t fail fail s"
  apply (simp add: s_bcorres_underlying_def fail_def)
  done

lemma fail_bcorres_underlying[wp]: "bcorres_underlying t fail fail"
  apply (simp add: bcorres_underlying_def fail_s_bcorres_underlying)
  done

lemma assertE_bcorres_underlying[wp]: "bcorres_underlying t (assertE P) (assertE P)"
  apply (clarsimp simp add: assertE_def returnOk_def)
  apply (intro impI conjI; wp)
  done

lemmas assertE_s_bcorres_underlying[wp] = drop_sbcorres_underlying[OF assertE_bcorres_underlying]

lemma when_s_bcorres_underlying[wp]:
  "(P \<Longrightarrow> s_bcorres_underlying t f f' s) \<Longrightarrow> s_bcorres_underlying t (when P f) (when P f') s"
  by (simp add: return_s_bcorres_underlying when_def)

lemma when_bcorres_underlying[wp]:
  "(P \<Longrightarrow> bcorres_underlying t f f') \<Longrightarrow> bcorres_underlying t (when P f) (when P f')"
  by (simp add: bcorres_underlying_def when_s_bcorres_underlying)

lemma put_bcorres_underlying[wp]:
  "t f = f' \<Longrightarrow>  bcorres_underlying t (put f) (put f')" 
  apply (simp add: bcorres_underlying_def s_bcorres_underlying_def put_def)
  done

lemma modify_bcorres_underlying[wp]: "(\<And>x. t (f x) = f' (t x)) \<Longrightarrow> bcorres_underlying t (modify f) (modify f')"
  apply (simp add: modify_def)
  apply wp
  apply simp
  done

lemma liftM_bcorres_underlying[wp]:
  "bcorres_underlying t m m' \<Longrightarrow> bcorres_underlying t (liftM f m) (liftM f m')"
  apply (simp add: liftM_def)
  apply (wp | simp)+
  done

lemma sequence_x_bcorres_underlying[wp]:
  "(\<And>x. bcorres_underlying t (f x) (f' x)) \<Longrightarrow>
    bcorres_underlying t (sequence_x (map f xs)) (sequence_x (map f' xs))"
  apply (induct xs)
    apply (simp add: sequence_x_def | wp)+
  done


lemma sequence_bcorres_underlying[wp]:
  "(\<And>x. bcorres_underlying t (f x) (f' x)) \<Longrightarrow>
    bcorres_underlying t (sequence (map f xs)) (sequence (map f' xs))"
  apply (induct xs)
    apply (simp add: sequence_def | wp)+
  done

lemma mapM_x_bcorres_underlying[wp]:
  "(\<And>x. bcorres_underlying t (f x) (f' x)) \<Longrightarrow> bcorres_underlying t (mapM_x f xs) (mapM_x f' xs)"
  apply (simp add: mapM_x_def | wp)+
  done

lemma mapM_bcorres_underlying[wp]:
  "(\<And>x. bcorres_underlying t (f x) (f' x)) \<Longrightarrow> bcorres_underlying t (mapM f xs) (mapM f' xs)"
  by (simp add: mapM_def | wp)+
 
lemma gets_s_bcorres_underlyingE': "s_bcorres_underlying t (f (x s)) (f' (x' (t s))) s \<Longrightarrow> s_bcorres_underlying t (liftE (gets x) >>=E f) (liftE (gets x') >>=E f') s"
  by (simp add: gets_def liftE_def lift_def bindE_def) wp

lemma bcorres_underlying_filterM[wp]:
  "(\<And>x. bcorres_underlying t (a x) (a' x)) \<Longrightarrow> bcorres_underlying t (filterM a b) (filterM a' b)"
  apply (induct b)
   apply (simp add: filterM_def)
   apply (wp | simp)+
  done

lemma option_rec_bcorres_underlying[wp_split]:
  "(\<And>x y. bcorres_underlying t (g x y) (g' x y)) \<Longrightarrow> (\<And>x. bcorres_underlying t (f x) (f' x))
    \<Longrightarrow> bcorres_underlying t (rec_option f g a b) (rec_option f' g' a b)"
  by (cases a,simp+)

lemma bcorres_underlying_mapME[wp]: "(\<And>x. bcorres_underlying t (f x) (f' x)) \<Longrightarrow>  bcorres_underlying t (mapME f r) (mapME f' r)"
  apply (induct r)
   apply (simp add: mapME_def sequenceE_def | wp)+
  done

lemma handle2_bcorres_underlying[wp]: "bcorres_underlying t f f' \<Longrightarrow>  (\<And>x. bcorres_underlying t (g x) (g' x)) \<Longrightarrow>  bcorres_underlying t (f <handle2> g) (f' <handle2> g')"
  apply (simp add: handleE'_def)
  apply (wp | wpc | simp)+
  done

lemma liftME_bcorres_underlying[wp]: "bcorres_underlying t f f' \<Longrightarrow> bcorres_underlying t (liftME a f) (liftME a f')"
  apply (simp add: liftME_def)
  apply (wp | simp)+
  done

lemma zipWithM_x_bcorres[wp]: "(\<And>x y. bcorres_underlying t (f x y) (f' x y) ) \<Longrightarrow>  bcorres_underlying t (zipWithM_x f xs ys) (zipWithM_x f' xs ys)"
  apply (simp add: zipWithM_x_def)
  apply (simp add: zipWith_def split_def)
  apply (wp | simp)+
  done

lemma mapME_x_bcorres_underlying[wp]: "(\<And>x. bcorres_underlying t (f x) (f' x)) \<Longrightarrow> bcorres_underlying t (mapME_x f xs) (mapME_x f' xs)"
  apply (induct xs)
  apply (wp | simp add: mapME_x_def sequenceE_x_def)+
  done

ML {*
structure CrunchBCorresInstance : CrunchInstance =
struct
  type extra = term;
  val eq_extra = ae_conv;
  val name = "bcorres";
  val has_preconds = false;
  fun mk_term _ body extra =
    (Syntax.parse_term @{context} "bcorres_underlying") $ extra $ body $ body;
  fun get_precond (Const (@{const_name "bcorres_underlying"}, _) $ _ $ _ $ _ ) = Term.dummy
    | get_precond _ = error "get_precond: not an bcorres term";
  fun put_precond _ ((v as Const (@{const_name "bcorres_underlying"}, _)) $ extra $ body $ body')
        = v $ extra $ body $ body'
    | put_precond _ _ = error "put_precond: not an bcorres term";
  fun dest_term (Const (@{const_name "bcorres_underlying"}, _) $ extra $ body $ _)
      = SOME (Term.dummy, body, extra)
    | dest_term _ = NONE
  val pre_thms = [];
  val wpc_tactic = WeakestPreCases.wp_cases_tac @{thms wpc_processors};
  fun parse_extra ctxt extra
        = case extra of
             "" => error "bcorres needs truncate function"
             | e =>(Syntax.parse_term ctxt "%_. True", Syntax.parse_term ctxt e);
  val magic = Syntax.parse_term @{context}
    "\<lambda>mapp_lambda_ignore. bcorres_underlying t_free_ignore mapp_lambda_ignore g_free_ignore"
end;

structure CrunchBCorres : CRUNCH = Crunch(CrunchBCorresInstance);
*}

setup {*
  add_crunch_instance "bcorres" (CrunchBCorres.crunch_x, CrunchBCorres.crunch_ignore_add_del)
*}

end
