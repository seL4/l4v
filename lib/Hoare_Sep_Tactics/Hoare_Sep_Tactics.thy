(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Hoare_Sep_Tactics
imports
  Monads.Nondet_VCG
  Sep_Algebra.Sep_Algebra_L4v
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

ML \<open>
val sep_select_post_method =  sep_select_generic_method false [@{thm hoare_eq_post},
                                                               @{thm hoare_eq_postE},
                                                               @{thm hoare_eq_postE_R}]
val sep_select_pre_method  =  sep_select_generic_method false [@{thm hoare_eq_pre},
                                                               @{thm hoare_eq_preE},
                                                               @{thm hoare_eq_preE_R}]
\<close>

method_setup sep_select_pre = \<open>

Scan.lift (Scan.repeat Parse.int) >> sep_select_pre_method

\<close>

method_setup sep_select_post = \<open>

Scan.lift (Scan.repeat Parse.int) >> sep_select_post_method

\<close>

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
  apply (erule hoare_strengthen_post)
  apply (rename_tac rv s)
  apply (sep_drule (direct)  extract_all)
  apply (erule_tac x=rv in allE)
  apply (sep_solve)
  done

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

ML \<open>
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

val wp_modifiers =
 [Args.add -- Args.colon >> K (I, WeakestPre.wp_add),
  Args.del -- Args.colon >> K (I, WeakestPre.wp_del),
  Args.$$$ "sep_wp" -- Args.colon >> K (I, wp_add_attrib' sep_wandise_helper),
  Args.$$$ "sep_wand" -- Args.colon >> K (I, wp_add_attrib @{thm strong_sep_impl_sep_wp}),
  Args.$$$ "sep_wandE" -- Args.colon >> K (I, wp_add_attrib @{thm strong_sep_impl_sep_wpE}),
  Args.$$$ "sep_wand_side" -- Args.colon >> K (I, wp_add_attrib @{thm strong_sep_impl_sep_wp_side}),
  Args.$$$ "sep_wand_side'" -- Args.colon >> K (I, wp_add_attrib @{thm strong_sep_impl_sep_wp_side}),
  Args.$$$ "sep_wand_sideE" -- Args.colon >> K (I, wp_add_attrib @{thm strong_sep_impl_sep_wp_sideE}),
  Args.$$$ "sep_wand_sideE'" -- Args.colon >> K (I, wp_add_attrib @{thm strong_sep_impl_sep_wp_sideE'}),
  Args.$$$ "comb" -- Args.colon >> K (I, WeakestPre.combs_add),
  Args.$$$ "comb" -- Args.add -- Args.colon >> K (I, WeakestPre.combs_add),
  Args.$$$ "comb" -- Args.del -- Args.colon >> K (I, WeakestPre.combs_del),
  Args.$$$ "only" -- Args.colon
    >> K (Context.proof_map (WeakestPre.WPData.map WeakestPre.clear_rules), (WeakestPre.wp_add))];

fun apply_wp_args xs =
  let fun apply_tac once = if once then WeakestPre.apply_once_tac else WeakestPre.apply_rules_tac;
  in
    Scan.lift (WeakestPre.modes ["trace", "once"])
      --| WeakestPre.if_colon (WeakestPre.sections wp_modifiers >> flat) WeakestPre.add_section
    >> curry (fn ([trace, once], ctxt) => SIMPLE_METHOD (apply_tac once trace ctxt []))
  end xs;

end;
\<close>

attribute_setup sep_wand_side_wp =  \<open>Scan.succeed sep_magic_wand_side\<close>
attribute_setup sep_wand_side_wp' =  \<open>Scan.succeed sep_magic_wand_side'\<close>
attribute_setup sep_wand_wp = \<open>Scan.succeed sep_magic_wand\<close>
attribute_setup sep_wand_wpE =  \<open>Scan.succeed sep_magic_wandE\<close>
attribute_setup sep_wand_side_wpE = \<open>Scan.succeed sep_magic_wand_sideE\<close>
attribute_setup sep_wand_side_wpE' = \<open>Scan.succeed sep_magic_wand_sideE'\<close>
attribute_setup sep_wandise = \<open>Scan.succeed sep_wandise\<close>

method_setup wp = \<open>apply_wp_args\<close>
  "applies weakest precondition rules"

lemma boxsolve: "P s \<Longrightarrow> (\<box> \<and>* (\<box> \<longrightarrow>* P)) s"
  apply (clarsimp)
  apply (sep_solve)
done


ML \<open>
   fun J f x = f x
               handle _ => x   (* FIXME! exceptions *)

   fun sep_wp thms ctxt  =
   let
     val thms' = map (sep_wandise_helper ctxt |> J) thms;
     val wp = WeakestPre.apply_rules_tac_n false ctxt thms'
     val sep_impi = (REPEAT_ALL_NEW  (sep_match_trivial_tac ctxt)) THEN' assume_tac ctxt
     val schemsolve = sep_rule_tac (eresolve0_tac [@{thm boxsolve}]) ctxt
     val hoare_post = (resolve0_tac [(rotate_prems ~1 @{thm hoare_strengthen_post})])
     val wp_pre_tac = SELECT_GOAL (NO_CONTEXT_TACTIC ctxt
                      (Method_Closure.apply_method ctxt @{method wp_pre} [] [] [] ctxt []))
   in
     (wp THEN' (TRY o sep_flatten ctxt) THEN' (TRY o (hoare_post THEN' (schemsolve ORELSE' sep_impi))) THEN'
     (TRY o (sep_match_trivial_tac ctxt |> REPEAT_ALL_NEW)) THEN'
     (TRY o sep_flatten ctxt)) ORELSE' (CHANGED o wp_pre_tac)
   end
\<close>

method_setup sep_wp = \<open>
  Attrib.thms >> (fn thms => fn ctxt => Method.SIMPLE_METHOD' (sep_wp thms ctxt))
\<close>



lemma shift_inside_left:
  "\<lbrace>\<lambda>s. (P \<and>* R) (sep_lift s) \<and> A\<rbrace> f \<lbrace>R'\<rbrace> \<longleftrightarrow> \<lbrace>\<lambda>s. ((P and K A) \<and>* R) (sep_lift s)\<rbrace> f \<lbrace>R'\<rbrace>"
  apply (clarsimp simp: pred_conj_def conj_commute)
  done

lemma shift_inside_right:
  "\<lbrace>\<lambda>s. A \<and> (P \<and>* R) (sep_lift s)\<rbrace> f \<lbrace>R'\<rbrace> \<longleftrightarrow> \<lbrace>\<lambda>s. ((P and K A) \<and>* R) (sep_lift s)\<rbrace> f \<lbrace>R'\<rbrace>"
  apply (clarsimp simp: pred_conj_def conj_commute)
  done

(* FIXME: Make nicer alias for doing this *)
lemmas sep_wp_simp = pred_conj_def K_def shift_inside_left shift_inside_right sep_conj_assoc[symmetric]

lemma sep_hoare_fold_mapM_x:
  "(\<And>R x. x \<in> set xs \<Longrightarrow> \<lbrace>\<lambda>s. (P x \<and>* R) (sep_lift s)\<rbrace> f x \<lbrace>\<lambda>_ s. (Q x \<and>* R) (sep_lift s)\<rbrace>)
    \<Longrightarrow> \<lbrace>\<lambda>s. (sep_fold P Q R xs) (sep_lift s)\<rbrace> mapM_x f xs \<lbrace>\<lambda>_ s. R (sep_lift s)\<rbrace>"
  apply (clarsimp simp: sep_fold_def)
  apply (induct xs arbitrary: R)
   apply (clarsimp simp: mapM_x_def sequence_x_def)+
  apply wp
    apply assumption+
   apply atomize
   apply (erule allE)
   apply (erule allE)
   apply (erule_tac x=a in allE)
   apply clarsimp
   apply (rule hoare_chain)
     apply assumption+
   apply (sep_erule (direct) sep_mp)
  apply clarsimp
  done

end
