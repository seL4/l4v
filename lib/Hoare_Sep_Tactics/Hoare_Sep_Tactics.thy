(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Hoare_Sep_Tactics
imports
  "../Monad_WP/NonDetMonadVCG"
  "../sep_algebra/Sep_Algebra_L4v"
begin

(* FIXME: needs cleanup *)

lemma hoare_eq_pre:  " \<lbrakk> \<And>s. P s = G s; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>G\<rbrace> f \<lbrace>Q\<rbrace>"
  by (erule hoare_pre_subst [rotated], auto)

lemma hoare_eq_preE:  " \<lbrakk> \<And>s. P s = G s; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>G\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  apply (rule hoare_weaken_preE)
   apply (assumption)
  apply (clarsimp)
  done

lemma hoare_eq_preE_R:  " \<lbrakk> \<And>s. P s = G s; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,-\<rbrakk> \<Longrightarrow> \<lbrace>G\<rbrace> f \<lbrace>Q\<rbrace>,-"
  apply (clarsimp simp: validE_R_def)
   apply (erule hoare_eq_preE)
  apply (clarsimp)
  done

lemma hoare_eq_post: " \<lbrakk> \<And>rv s. Q rv s = G rv s; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>G\<rbrace>"
  by (rule hoare_strengthen_post, assumption, clarsimp)

lemma hoare_eq_postE: " \<lbrakk> \<And>rv s. Q rv s = G rv s; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>G\<rbrace>, \<lbrace>E\<rbrace>"
  by (metis (full_types) hoare_post_impErr')

lemma hoare_eq_postE_R: " \<lbrakk> \<And>rv s. Q rv s = G rv s; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, -\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>G\<rbrace>, -"
  by (metis hoare_post_imp_R)

ML {*
val sep_select_post_method =  sep_select_generic_method false [@{thm hoare_eq_post},
                                                               @{thm hoare_eq_postE},
                                                               @{thm hoare_eq_postE_R}]
val sep_select_pre_method  =  sep_select_generic_method false [@{thm hoare_eq_pre},
                                                               @{thm hoare_eq_preE},
                                                               @{thm hoare_eq_preE_R}]
*}

method_setup sep_select_pre = {*

Scan.lift (Scan.repeat Parse.int) >> sep_select_pre_method

*}

method_setup sep_select_post = {*

Scan.lift (Scan.repeat Parse.int) >> sep_select_post_method

*}

lemma strong_sep_impl_sep_wp:
    "\<And>sep_lift.
     (\<And>R. \<lbrace>(\<lambda>s. (P \<and>* R) (sep_lift s) )\<rbrace> f \<lbrace>\<lambda>_. (\<lambda>s. (Q \<and>* R) (sep_lift s))\<rbrace>) \<Longrightarrow>
     \<lbrace>(\<lambda>s. ( P \<and>* (Q \<longrightarrow>* R) ) (sep_lift s))\<rbrace> f \<lbrace>\<lambda>_. (\<lambda>s.(R) (sep_lift s))\<rbrace>"
 apply (atomize)
 apply (erule_tac x="(Q \<longrightarrow>* R)" in allE)
 apply (rule hoare_strengthen_post)
 apply (assumption)
 apply (sep_mp)
 apply (sep_solve)
done

lemma extract_exists: "((\<lambda>s. \<exists>x. (P x) s) \<and>* R) s \<Longrightarrow> \<exists>x. (P x \<and>*  R) s"
  apply (clarsimp simp: sep_conj_def, fastforce)
done

lemma extract_all: "((\<lambda>s. \<forall>x. (P x) s) \<and>* R) s \<Longrightarrow> \<forall>x. (P x \<and>*  R) s"
  apply (clarsimp simp: sep_conj_def, fastforce)
done

schematic_goal strong_sep_impl_sep_wp':
    "\<And>sep_lift.
     (\<And>R. \<lbrace>(\<lambda>s. (P \<and>* R) (sep_lift s) )\<rbrace> f \<lbrace>\<lambda>rv. (\<lambda>s. (Q rv \<and>* R) (sep_lift s))\<rbrace>) \<Longrightarrow>
     \<lbrace>(\<lambda>s. ( P \<and>* (?f Q R)) (sep_lift s))\<rbrace> f \<lbrace>\<lambda>rv s . R rv (sep_lift s)\<rbrace>"
 apply (atomize)
 apply (erule_tac x="(\<lambda>s. \<forall>x. (Q x \<longrightarrow>* R x) s)" in allE)
 apply (rule hoare_strengthen_post)
 apply (assumption)
 apply (sep_drule (direct)  extract_all)
 apply (erule_tac x=r in allE)
 apply (sep_solve)
done

thm strong_sep_impl_sep_wp'

lemma strong_sep_impl_sep_wp'':
    "\<And>sep_lift.
     (\<And>R. \<lbrace>(\<lambda>s. (P \<and>* R x) (sep_lift s) )\<rbrace> f \<lbrace>\<lambda>rv. (\<lambda>s. (Q rv \<and>* R rv) (sep_lift s))\<rbrace>) \<Longrightarrow>
     \<lbrace>(\<lambda>s. ( P \<and>* (Q x \<longrightarrow>* R x)) (sep_lift s))\<rbrace> f \<lbrace>\<lambda>rv s . R rv (sep_lift s)\<rbrace>"
 apply (atomize)
 apply (erule_tac x="(\<lambda>x. (Q x \<longrightarrow>* R x))" in allE)
 apply (rule hoare_strengthen_post)
 apply (assumption)
 apply (sep_solve)
done


lemma auto_wp:"\<lbrace>P \<rbrace> f \<lbrace>Q \<rbrace> \<Longrightarrow> \<lbrace>\<lambda>s.  P s \<and> (\<forall>s x. Q x s \<longrightarrow> R x s)\<rbrace> f \<lbrace>R\<rbrace>"
by (clarsimp simp: valid_def split:prod.splits)

lemma strong_sep_impl_sep_wpE:
"\<And>sep_lift. (\<And>R. \<lbrace>(\<lambda>s. (P \<and>* R) (sep_lift s)) \<rbrace> f \<lbrace>\<lambda>_ s. (Q \<and>* R) (sep_lift s)\<rbrace>, \<lbrace>E\<rbrace>) \<Longrightarrow>
                  \<lbrace>(\<lambda>s. ( P \<and>* (Q \<longrightarrow>* R)) (sep_lift s))\<rbrace> f \<lbrace>\<lambda>_ s. R (sep_lift s)\<rbrace>, \<lbrace>E\<rbrace>"
 apply (atomize)
  apply (erule_tac x="(Q \<longrightarrow>* R)" in allE)
  apply (simp add: valid_def split_def validE_def)
  apply (rule allI)
  apply (rule impI)
  apply (erule_tac x=s in allE)
  apply (erule impE)
   apply (sep_cancel)+
  apply (rule ballI)
  apply (erule_tac x="x" in ballE)
   apply (clarsimp split: sum.splits)
  apply (sep_solve)
  apply (clarsimp split: sum.splits)
done

lemma strong_sep_impl_sep_wp_side:
 "\<And>sep_lift.
  (\<And>R. \<lbrace>(\<lambda>s. (P \<and>* R) (sep_lift s)) and K (P')\<rbrace> f \<lbrace>\<lambda>_ s. (Q \<and>* R) (sep_lift s)\<rbrace>) \<Longrightarrow> P' \<Longrightarrow>
  \<lbrace>(\<lambda>s. (P \<and>* (Q \<longrightarrow>* R)) (sep_lift s)) \<rbrace> f \<lbrace>\<lambda>_ s. R (sep_lift s)\<rbrace>"
 apply (atomize)
  apply (erule_tac x="(\<lambda>s. (Q \<longrightarrow>* R) s)" in allE)
  apply (rule hoare_chain)
    apply (assumption)
   apply (clarsimp)
  apply (clarsimp)+
  apply (sep_solve)
  done

lemma strong_sep_impl_sep_wp_side':
 "\<And>sep_lift.
  (\<And>R. \<lbrace>(\<lambda>s. (P \<and>* R) (sep_lift s)) and K (P')\<rbrace> f \<lbrace>\<lambda>_ s. (Q \<and>* R) (sep_lift s)\<rbrace>) \<Longrightarrow>
  \<lbrace>(\<lambda>s. ((P \<and>* (Q \<longrightarrow>* R)) and K (P')) (sep_lift s)) \<rbrace> f \<lbrace>\<lambda>_ s. R (sep_lift s)\<rbrace>"
 apply (atomize)
 apply (erule_tac x="(\<lambda>s. (Q \<longrightarrow>* R) s)" in allE)
 apply (rule hoare_chain)
 apply (assumption)
 apply (clarsimp)+
 apply (sep_solve)
done

lemma strong_sep_impl_sep_wp_side'':
 "\<And>sep_lift.
  (\<And>R. \<lbrace>(\<lambda>s. ((P \<and>* R) and K P')  (sep_lift s))\<rbrace> f \<lbrace>\<lambda>_ s. (Q \<and>* R) (sep_lift s)\<rbrace>) \<Longrightarrow>
  \<lbrace>(\<lambda>s. ((P \<and>* (Q \<longrightarrow>* R)) and K (P')) (sep_lift s)) \<rbrace> f \<lbrace>\<lambda>_ s. R (sep_lift s)\<rbrace>"
 apply (atomize)
 apply (erule_tac x="(\<lambda>s. (Q \<longrightarrow>* R) s)" in allE)
 apply (rule hoare_chain)
 apply (assumption)
 apply (clarsimp)+
 apply (sep_solve)
done

lemma strong_sep_impl_sep_wp_sideE:
  "\<And>sep_lift.
  (\<And>R. \<lbrace>(\<lambda>s. (P \<and>* R) (sep_lift s)) and K (P')\<rbrace> f \<lbrace>\<lambda>_ s. (Q \<and>* R) (sep_lift s)\<rbrace>, \<lbrace>E\<rbrace>) \<Longrightarrow> P' \<Longrightarrow>
  \<lbrace>(\<lambda>s. (P \<and>* (Q \<longrightarrow>* R)) (sep_lift s)) \<rbrace> f \<lbrace>\<lambda>_ s. R (sep_lift s)\<rbrace>, \<lbrace>E\<rbrace>"
 apply (atomize)
  apply (erule_tac x="(Q \<longrightarrow>* R)" in allE)
  apply (rule hoare_chainE)
     apply (assumption)
    apply (clarsimp)
   apply (sep_solve)+
  done

lemma strong_sep_impl_sep_wp_sideE':
"\<And>sep_lift.
(\<And>R. \<lbrace>(\<lambda>s. (P \<and>* R) (sep_lift s))  and K (P')\<rbrace> f \<lbrace>\<lambda>_ s. (Q \<and>* R) (sep_lift s)\<rbrace>, \<lbrace>E\<rbrace>) \<Longrightarrow>
     \<lbrace>(\<lambda>s. ((P \<and>* (Q \<longrightarrow>* R)) and K (P')) (sep_lift s))\<rbrace> f \<lbrace>\<lambda>_ s. R (sep_lift s)\<rbrace>, \<lbrace>E\<rbrace>"
 apply (atomize)
  apply (erule_tac x="(Q \<longrightarrow>* R)" in allE)
  apply (rule hoare_chainE)
     apply (assumption)
    apply (clarsimp)
   apply (sep_solve)+
  done


lemma strong_sep_impl_sep_wp_rv:
    "\<And>sep_lift.
     (\<And>R. \<lbrace>(\<lambda>s. (P \<and>* R) (sep_lift s) )\<rbrace> f \<lbrace>\<lambda>x. (\<lambda>s. (Q x \<and>* R) (sep_lift s))\<rbrace>) \<Longrightarrow>
     \<lbrace>(\<lambda>s. ( P \<and>* (\<lambda>s. \<forall>x. (Q x  \<longrightarrow>* R x) s ))(sep_lift s))\<rbrace> f \<lbrace>\<lambda>rv s . (R rv) (sep_lift s)\<rbrace>"
 apply (rule hoare_chain, assumption)
 apply (sep_solve)
 apply (sep_select_asm 2, erule sep_conj_sep_impl2)
 apply (fastforce)
done

lemma strong_sep_impl_sep_wp_rv':
    "\<And>sep_lift.
     (\<And>R. \<lbrace>(\<lambda>s. ((P \<and>* R) and K(p')) (sep_lift s) )\<rbrace> f \<lbrace>\<lambda>x. (\<lambda>s. (Q x \<and>* R) (sep_lift s))\<rbrace>) \<Longrightarrow>
     \<lbrace>(\<lambda>s. (( P \<and>* (\<lambda>s. \<forall>x. (Q x  \<longrightarrow>* R x) s )) and K(p') )(sep_lift s))\<rbrace> f \<lbrace>\<lambda>rv s . (R rv) (sep_lift s)\<rbrace>"
  apply (rule hoare_chain, assumption)
 apply (sep_solve)
 apply (sep_select_asm 2, erule sep_conj_sep_impl2)
 apply (fastforce)
done

lemma strong_sep_impl_sep_wp_rv'':
    "\<And>sep_lift.
     (\<And>R. \<lbrace>(\<lambda>s. ((P \<and>* R)) (sep_lift s) )\<rbrace> f \<lbrace>\<lambda>x. (\<lambda>s. ((Q x \<and>* R) and K (p'' x)) (sep_lift s))\<rbrace>) \<Longrightarrow>
     \<lbrace>(\<lambda>s. (( P \<and>* (\<lambda>s. \<forall>x. p'' x \<longrightarrow> (Q x  \<longrightarrow>* R x) s )))(sep_lift s))\<rbrace> f \<lbrace>\<lambda>rv s . (R rv) (sep_lift s)\<rbrace>"
apply (rule hoare_chain, assumption)
 apply (sep_solve)
 apply (clarsimp)
 apply (sep_select_asm 2, erule sep_conj_sep_impl2)
 apply (fastforce)
done


lemma strong_sep_impl_sep_wp_rv''':
    "\<And>sep_lift.
     (\<And>R. \<lbrace>(\<lambda>s. ((P \<and>* R) and K(p')) (sep_lift s) )\<rbrace> f \<lbrace>\<lambda>x. (\<lambda>s. ((Q x \<and>* R) and K (p'' x)) (sep_lift s))\<rbrace>) \<Longrightarrow>
     \<lbrace>(\<lambda>s. (( P \<and>* (\<lambda>s. \<forall>x. p'' x \<longrightarrow> (Q x  \<longrightarrow>* R x) s )) and K(p') )(sep_lift s))\<rbrace> f \<lbrace>\<lambda>rv s . (R rv) (sep_lift s)\<rbrace>"
apply (rule hoare_chain, assumption)
 apply (sep_solve)
 apply (clarsimp)
 apply (sep_select_asm 2, erule sep_conj_sep_impl2)
 apply (fastforce)
done

lemma strong_sep_impl_sep_wp_rv_ex_post:
    "\<And>sep_lift.
     (\<And>R. \<lbrace>\<lambda>s. ((P \<and>* R) and K(p')) (sep_lift s)\<rbrace> f \<lbrace>\<lambda>x s. \<exists>t. ((Q x t  \<and>* R) and K (p'' x t)) (sep_lift s)\<rbrace>) \<Longrightarrow>
      \<lbrace>\<lambda>s.  (( P \<and>* (\<lambda>s. (\<forall>x t.  p'' x t \<longrightarrow> (Q x t  \<longrightarrow>* R x t) (s )))) and K(p') ) (sep_lift s) \<rbrace> f \<lbrace>\<lambda>rv s . \<exists>t. (R rv t) (sep_lift s) \<rbrace>"
  apply (rule hoare_chain, assumption)+
apply (clarsimp)
  apply (sep_cancel)
  apply (clarsimp simp: sep_conj_def sep_impl_def)
by (metis (full_types) sep_add_commute sep_disj_commute)

lemma strong_sep_impl_sep_wp_rv_ex_pre_post:
  "\<And>sep_lift.
   (\<And>R. \<lbrace>\<lambda>s. \<exists>t'. ((P t' \<and>* R) and K(p' t')) (sep_lift s)\<rbrace> f \<lbrace>\<lambda>x s. \<exists>t. ((Q x t  \<and>* R) and K (p'' x t)) (sep_lift s)\<rbrace>) \<Longrightarrow>

   \<lbrace>\<lambda>s. \<exists>t'. (( P t' \<and>* (\<lambda>s. (\<forall>x t.  p'' x t \<longrightarrow> (Q x t  \<longrightarrow>* R x t) (s )))) and K(p' t') ) (sep_lift s) \<rbrace>
   f
   \<lbrace>\<lambda>rv s . \<exists>t. (R rv t) (sep_lift s) \<rbrace>"
  apply (rule hoare_chain, assumption)+
   apply (clarsimp)
   apply (rule_tac x=t' in exI, simp)
  apply (clarsimp simp: sep_conj_def sep_impl_def)
  by (metis (full_types) sep_add_commute sep_disj_commute)

ML {*
local
  val simpset = simpset_of (
      put_simpset HOL_basic_ss @{context}
        addsimps [(sym OF [@{thm sep_conj_assoc}])])
  fun simp ctxt thm = simplify (put_simpset simpset ctxt) thm
  fun attrib thm ctxt thm' =
    (thm OF [simp (ctxt) thm'])
    |> Goal.norm_result ctxt
  fun wp_add_attrib thm (ctxt, thm') = WeakestPre.gen_att ( WeakestPre.add_rule o (attrib thm (Context.proof_of ctxt))) (ctxt, thm')
  fun first_working (f::fs) x  = f x
                       handle THM _ => first_working (fs) x
  fun wp_add_attrib' f (ctxt, thm') = WeakestPre.gen_att ( WeakestPre.add_rule o (f (Context.proof_of ctxt))) (ctxt, thm')
in
val sep_magic_wand        = Thm.rule_attribute [] (attrib @{thm strong_sep_impl_sep_wp} o Context.proof_of)
val sep_magic_wandE       = Thm.rule_attribute [] (attrib @{thm strong_sep_impl_sep_wpE} o Context.proof_of)
val sep_magic_wand_side   = Thm.rule_attribute [] (attrib @{thm strong_sep_impl_sep_wp_side} o Context.proof_of )
val sep_magic_wand_side'  = Thm.rule_attribute [] (attrib @{thm strong_sep_impl_sep_wp_side'} o Context.proof_of )
val sep_magic_wand_sideE  = Thm.rule_attribute [] (attrib @{thm strong_sep_impl_sep_wp_sideE} o Context.proof_of)
val sep_magic_wand_sideE' = Thm.rule_attribute [] (attrib @{thm strong_sep_impl_sep_wp_sideE'}o Context.proof_of)

fun sep_wandise_helper ctxt =
                  first_working [attrib @{thm strong_sep_impl_sep_wp} ctxt,
                                 attrib @{thm strong_sep_impl_sep_wpE} ctxt,
                                 attrib @{thm strong_sep_impl_sep_wp_side''} ctxt,
                                 attrib @{thm strong_sep_impl_sep_wp_rv'''} ctxt,
                                 attrib @{thm strong_sep_impl_sep_wp_rv_ex_post} ctxt,
                                 attrib @{thm strong_sep_impl_sep_wp_rv_ex_pre_post} ctxt,
                                 attrib @{thm strong_sep_impl_sep_wp_side'} ctxt,
                                 attrib @{thm strong_sep_impl_sep_wp_sideE'} ctxt,
                                 attrib @{thm strong_sep_impl_sep_wp_rv} ctxt,
                                 attrib @{thm strong_sep_impl_sep_wp'} ctxt,
                                 attrib @{thm strong_sep_impl_sep_wp_rv''} ctxt]

val sep_wandise = Thm.rule_attribute [] ((fn ctxt => (
                  first_working [attrib @{thm strong_sep_impl_sep_wp} ctxt,
                                 attrib @{thm strong_sep_impl_sep_wpE} ctxt,
                                 attrib @{thm strong_sep_impl_sep_wp_side''} ctxt,
                                 attrib @{thm strong_sep_impl_sep_wp_rv'''} ctxt,
                                 attrib @{thm strong_sep_impl_sep_wp_rv_ex_post} ctxt,
                                 attrib @{thm strong_sep_impl_sep_wp_rv_ex_pre_post} ctxt,
                                 attrib @{thm strong_sep_impl_sep_wp_side'} ctxt,
                                 attrib @{thm strong_sep_impl_sep_wp_rv''} ctxt,
                                 attrib @{thm strong_sep_impl_sep_wp_sideE'} ctxt])) o Context.proof_of )


fun composeOption f g x = case g x of (SOME v, SOME h) => f (v,h) | _ => (NONE , NONE)

fun wp_modifiers extras_ref =
 [Args.add -- Args.colon >> K (I, fn att => (WeakestPre.add_extra_rule (#2 att) extras_ref; WeakestPre.wp_add att)),
  Args.del -- Args.colon >> K (I, WeakestPre.wp_del),
  Args.$$$ "sep_wp" -- Args.colon >> (K (I, fn att => (WeakestPre.add_extra_rule (#2 att) extras_ref; wp_add_attrib' sep_wandise_helper att))),
  Args.$$$ "sep_wand" -- Args.colon >> (K (I, fn att => (WeakestPre.add_extra_rule (#2 att) extras_ref; wp_add_attrib @{thm strong_sep_impl_sep_wp} att))),
  Args.$$$ "sep_wandE" -- Args.colon >> (K (I, fn att => (WeakestPre.add_extra_rule (#2 att) extras_ref; wp_add_attrib @{thm strong_sep_impl_sep_wpE} att ))),
  Args.$$$ "sep_wand_side" -- Args.colon >> (K (I, fn att => (WeakestPre.add_extra_rule (#2 att) extras_ref; wp_add_attrib @{thm strong_sep_impl_sep_wp_side} att ))),
  Args.$$$ "sep_wand_side'" -- Args.colon >> (K (I, fn att => (WeakestPre.add_extra_rule (#2 att) extras_ref; wp_add_attrib @{thm strong_sep_impl_sep_wp_side} att ))),
  Args.$$$ "sep_wand_sideE" -- Args.colon >> (K (I, fn att => (WeakestPre.add_extra_rule (#2 att) extras_ref; wp_add_attrib @{thm strong_sep_impl_sep_wp_sideE} att ))),
  Args.$$$ "sep_wand_sideE'" -- Args.colon >> (K (I, fn att => (WeakestPre.add_extra_rule (#2 att) extras_ref; wp_add_attrib @{thm strong_sep_impl_sep_wp_sideE'} att ))),
  Args.$$$ "comb" -- Args.colon >> K (I, fn att => (WeakestPre.add_extra_rule (#2 att) extras_ref; WeakestPre.combs_add att)),
  Args.$$$ "comb" -- Args.add -- Args.colon >> K (I, fn att => (WeakestPre.add_extra_rule (#2 att) extras_ref; WeakestPre.combs_add att)),
  Args.$$$ "comb" -- Args.del -- Args.colon >> K (I, WeakestPre.combs_del),
  Args.$$$ "only" -- Args.colon
    >> K (Context.proof_map (WeakestPre.WPData.map WeakestPre.clear_rules), fn att =>
                               (WeakestPre.add_extra_rule (#2 att) extras_ref; WeakestPre.wp_add att))];

fun apply_rules_args trace xs =
  let val extras_ref = Unsynchronized.ref [] : thm list Unsynchronized.ref;
  in
    WeakestPre.if_colon
    (WeakestPre.sections (wp_modifiers extras_ref) >>
      K (fn ctxt => SIMPLE_METHOD (WeakestPre.apply_rules_tac trace ctxt [] extras_ref)))
    (Attrib.thms >> curry (fn (extras, ctxt) =>
      Method.SIMPLE_METHOD (
        WeakestPre.apply_rules_tac trace ctxt extras extras_ref
      )
    ))
  end xs;

fun apply_once_args trace xs =
  let val extras_ref = Unsynchronized.ref [] : thm list Unsynchronized.ref;
  in
    WeakestPre.if_colon
    (WeakestPre.sections (wp_modifiers extras_ref) >>
      K (fn ctxt => SIMPLE_METHOD (WeakestPre.apply_once_tac trace ctxt [] extras_ref)))
    (Attrib.thms >> curry (fn (extras, ctxt) =>
      Method.SIMPLE_METHOD (
        WeakestPre.apply_once_tac trace ctxt extras extras_ref
      )
    ))
  end xs;

end;
*}

attribute_setup sep_wand_side_wp =  {* Scan.succeed sep_magic_wand_side *}
attribute_setup sep_wand_side_wp' =  {* Scan.succeed sep_magic_wand_side' *}
attribute_setup sep_wand_wp = {* Scan.succeed sep_magic_wand *}
attribute_setup sep_wand_wpE =  {* Scan.succeed sep_magic_wandE *}
attribute_setup sep_wand_side_wpE = {* Scan.succeed sep_magic_wand_sideE *}
attribute_setup sep_wand_side_wpE' = {* Scan.succeed sep_magic_wand_sideE' *}
attribute_setup sep_wandise = {* Scan.succeed sep_wandise *}

method_setup wp = {* apply_rules_args false *}
  "applies weakest precondition rules"

lemma boxsolve: "P s \<Longrightarrow> (\<box> \<and>* (\<box> \<longrightarrow>* P)) s"
  apply (clarsimp)
  apply (sep_solve)
done


ML {*
   fun J f x = f x
               handle _ => x   (* FIXME! exceptions *)

   fun sep_wp thms ctxt  =
   let
     val thms' = map (sep_wandise_helper ctxt |> J) thms;
     val wp = WeakestPre.apply_once_tac false ctxt thms'  (Unsynchronized.ref [] : thm list Unsynchronized.ref)
     val sep_impi = (REPEAT_ALL_NEW  (sep_match_trivial_tac ctxt)) THEN' assume_tac ctxt
     val schemsolve = sep_rule_tac (eresolve0_tac [@{thm boxsolve}]) ctxt
     val hoare_post = (resolve0_tac [(rotate_prems ~1 @{thm hoare_strengthen_post})])
   in
     K wp THEN' (TRY o sep_flatten ctxt) THEN' (TRY o (hoare_post THEN' (schemsolve ORELSE' sep_impi))) THEN'
     (TRY o (sep_match_trivial_tac ctxt |> REPEAT_ALL_NEW)) THEN'
     (TRY o sep_flatten ctxt)
   end
*}

method_setup sep_wp = {*
  Attrib.thms >> (fn thms => fn ctxt => Method.SIMPLE_METHOD' (sep_wp thms ctxt))
*}

end
