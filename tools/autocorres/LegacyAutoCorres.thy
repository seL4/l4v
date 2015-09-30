(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory LegacyAutoCorres

imports AutoCorres "../../lib/clib/Corres_UL_C"

begin

text {* This theory adds some legacy support to the autocorres framework. It allows
the use of autocorres in single ccorres_underlying goals without performing an
autocorres translation on the entire program base. *}

lemma fst_c_with_gets_xf:
  "fst ((doE _ \<leftarrow> c'; liftE (gets xf) odE) s)
    = (\<lambda>(rv, s). (case rv of Inr _ \<Rightarrow> Inr (xf s) | Inl v \<Rightarrow> Inl v, s)) ` fst (c' s)"
  by (auto simp: in_bindE image_def in_monad split: sum.splits,
      auto elim: rev_bexI)

lemma ccorres_underlying_L1corres:
  "L1corres Gamma c' c
    \<Longrightarrow> corres_underlying sr True ((\<lambda>_ _. False) \<oplus> r) P (\<lambda>s. s \<in> P')
         (liftE a) (doE c'; liftE (gets xf) odE)
    \<Longrightarrow> ccorres_underlying sr Gamma r xf arrel axf P P' [] a c"
  apply (clarsimp simp: L1corres_def ccorres_underlying_def corres_underlying_def
                        ball_cong[OF fst_c_with_gets_xf refl])
  apply (drule(1) bspec, clarsimp simp: in_monad snd_bindE)
  apply (drule spec, drule(1) mp)
  apply (erule exec_handlers.cases, simp_all)
   apply (erule exec_handlers.cases, simp_all)
   apply fastforce
  apply clarsimp
  apply (drule spec, drule(1) mp)
  apply (clarsimp split: xstate.split_asm)
  apply (fastforce simp: unif_rrel_def in_monad)
  done

lemma corres_underlying_L2corres:
  "L2corres gs ret_xf ex_xf P c' c
    \<Longrightarrow> corres_underlying gs_sr
            True (ftr \<oplus> r) Q Q' a c'
    \<Longrightarrow> corres_underlying {(s, s'). (s, gs s') \<in> gs_sr}
            True (ftr \<oplus> r)
            Q (\<lambda>s. P s \<and> Q' (gs s))
        a (doE c; liftE (gets ret_xf) odE)"
  apply (clarsimp simp: corres_underlying_def L2corres_def corresXF_def
                        ball_cong[OF fst_c_with_gets_xf refl]
                        snd_bindE snd_liftE snd_gets)
  apply (drule(1) bspec, clarsimp)
  apply (drule spec, drule mp, erule conjI, simp)
  apply clarsimp
  apply (fastforce split: sum.splits)
  done

text {* This rule allows three autocorres-generated theorems to be
used to initialise a ccorres_underlying proof. *}
lemma ccorres_underlying_autocorres:
  "L1corres Gamma c' c
     \<Longrightarrow> (\<And>s. L2corres gs ret_xf ex_xf (L2P s) c'' c')
     \<Longrightarrow> c'' \<equiv> c'''
     \<Longrightarrow> \<forall>s. s \<in> P' \<longrightarrow> L2P s s
     \<Longrightarrow> \<forall>s. xf s = xf_fudge (ret_xf s)
     \<Longrightarrow> \<forall>s s'. (s, s') \<in> sr = gs_sr s (gs s')
     \<Longrightarrow> corres_underlying {(s, s'). gs_sr s s'}
            True ((\<lambda>_ (_ :: unit). False) \<oplus> (\<lambda>rv rv'. r rv (xf_fudge rv'))) Q Q' (liftE a) c'''
     \<Longrightarrow> \<forall>s s'. P s \<and> s' \<in> P' \<and> (s, s') \<in> sr \<longrightarrow> Q s \<and> Q' (gs s')
     \<Longrightarrow> ccorres_underlying sr Gamma r xf arrel axf P P' [] a c"
  apply (erule ccorres_underlying_L1corres)
  apply (subst corres_underlying_def, clarsimp)
  apply (drule corres_underlying_L2corres[rotated], assumption)
  apply (clarsimp simp: corres_underlying_def ball_cong[OF fst_c_with_gets_xf refl]
                        snd_bindE snd_liftE snd_gets)
  apply (rename_tac s s')
  apply (drule spec, drule spec, drule_tac P="gs_sr s (gs s')" in mp, assumption)
  apply (drule mp, blast, clarsimp)
  apply (drule(1) bspec)+
  apply (auto split: sum.splits)
  done

text {* Since any functions called in the function body won't be translated,
we have to fake in some wrappers that call back to Simpl semantics. *}
definition
  "wrap_simpl_call Gamma proc
    = do s \<leftarrow> get;
         assert (Gamma \<turnstile> Call proc \<down> Normal s);
         xs \<leftarrow> select {t. Gamma\<turnstile> \<langle>Call proc,Normal s\<rangle> \<Rightarrow> t};
         case xs of Normal s \<Rightarrow> liftE (put s)
        | Abrupt s \<Rightarrow> do put s; throwError () od
        | Fault (ft :: strictc_errortype) \<Rightarrow> fail | _ \<Rightarrow> fail
    od"

lemma L1corres_trivial:
  "L1corres Gamma (wrap_simpl_call Gamma proc) (Call proc)"
  apply (clarsimp simp: L1corres_def wrap_simpl_call_def in_monad
                        exec_get assert_def)
  apply (case_tac t, simp_all add: in_monad in_select)
     apply (auto simp: in_monad snd_bind select_def)
  done

definition
  "wrap_l2 args arg_fn gs ret_xf l1body
    = do cur_gs \<leftarrow> get;
        s \<leftarrow> select {s. gs s = cur_gs \<and> arg_fn s = args};
        (rv, s') \<leftarrow> select_f (l1body s);
        put (gs s');
        case rv of Inl _ \<Rightarrow> fail
            | Inr _ \<Rightarrow> return (Inr (ret_xf s') :: (unit + _))
    od"

lemma L2corres_trivial:
  "L2corres gs ret_xf ex_xf (\<lambda>s. arg_fn s = args)
    (wrap_l2 args arg_fn gs ret_xf f) f"
  apply (clarsimp simp: L2corres_def corresXF_def wrap_l2_def
                 split: sum.split)
  apply (clarsimp simp: snd_bind in_monad exec_get select_def)
  apply (clarsimp simp: select_f_def snd_bind put_def split: sum.split_asm)
  apply (fastforce simp: return_def)
  done

definition
  "wrap_l1l2 arg_fn gs ret_xf Gamma proc args
    = wrap_l2 args arg_fn gs ret_xf (wrap_simpl_call Gamma proc)"

lemma L1L2corres_trivial:
  "L2corres gs ret_xf ex_xf (\<lambda>s. arg_fn s = args)
    (wrap_l1l2 arg_fn gs ret_xf Gamma proc args)
    (wrap_simpl_call Gamma proc)"
  by (simp add: wrap_l1l2_def L2corres_trivial)

definition
  "wrap_l1l2ts arg_fn gs ret_xf Gamma proc args
    = liftM (\<lambda>rv. case rv of Inr v \<Rightarrow> v)
        (wrap_l1l2 arg_fn gs ret_xf Gamma proc args)"

lemma type_strengthen_wrapper_trivial[ts_rule nondet]:
  "L2_call (wrap_l1l2 arg_fn gs ret_xf Gamma proc args)
    = liftE (wrap_l1l2ts arg_fn gs ret_xf Gamma proc args)"
  apply (simp add: wrap_l1l2ts_def wrap_l1l2_def liftE_def liftM_def
                   wrap_l2_def bind_assoc L2_defs L2_call_def
                   handleE'_def bindE_bind_linearise)
  apply (rule ext)
  apply (simp add: exec_gets exec_get)
  apply (rule bind_apply_cong[OF refl])+
  apply (clarsimp simp: bind_assoc returnOk_def in_monad split: sum.splits)
  done

ML_file "legacy.ML"

end
