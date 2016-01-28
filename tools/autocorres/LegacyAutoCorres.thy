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

ML_file "legacy.ML"

end
