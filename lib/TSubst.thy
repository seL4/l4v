(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*
 * Term subst method: substitution with a given term as the equation.
 * The equation will be added as a subgoal.
 * See example at the end of this file.
 *)

theory TSubst
imports
  Main
begin

method_setup tsubst = \<open>
  Scan.lift (Args.mode "asm" --
             Scan.optional (Args.parens (Scan.repeat Parse.nat)) [0] --
             Parse.term)
   >> (fn ((asm,occs),t) => (fn ctxt =>
  Method.SIMPLE_METHOD (Subgoal.FOCUS_PARAMS (fn focus => (fn thm =>
  let
    (* This code used to use Thm.certify_inst in 2014, which was removed.
       The following is just a best guess for what it did. *)
    fun certify_inst ctxt (typ_insts, term_insts) =
          (typ_insts
           |> map (fn (tvar, inst) =>
                  (Thm.ctyp_of ctxt (TVar tvar),
                   Thm.ctyp_of ctxt inst)),
           term_insts
           |> map (fn (var, inst) =>
                  (Thm.cterm_of ctxt (Var var),
                   Thm.cterm_of ctxt inst)))

    val ctxt' = #context focus

    val ((_, schematic_terms), ctxt2) =
      Variable.import_inst true [(#concl focus) |> Thm.term_of] ctxt'
      |>> certify_inst ctxt'

    val ctxt3 = fold (fn (t,t') => Variable.bind_term (Thm.term_of t |> Term.dest_Var |> fst, (t' |> Thm.term_of))) schematic_terms ctxt2


    val athm = Syntax.read_term ctxt3 t
          |> Object_Logic.ensure_propT ctxt'
          |> Thm.cterm_of ctxt'
          |> Thm.trivial

    val thm' = Thm.instantiate ([], map (apfst (Thm.term_of #> dest_Var)) schematic_terms) thm

  in
    (if asm then EqSubst.eqsubst_asm_tac else EqSubst.eqsubst_tac)
      ctxt3 occs [athm] 1 thm'
      |> Seq.map (singleton (Variable.export ctxt3 ctxt'))
     end)) ctxt 1)))
  \<close> "subst, with term instead of theorem as equation"

schematic_goal
  assumes a: "\<And>x y. P x \<Longrightarrow> P y"
  fixes x :: 'b
  shows "\<And>x ::'a :: type. ?Q x \<Longrightarrow> P x \<and> ?Q x"
  apply (tsubst (asm) "?Q x = (P x \<and> P x)")
   apply (rule refl)
  apply (tsubst "P x = P y",simp add:a)+
  apply (tsubst (2) "P y = P x", simp add:a)
  apply (clarsimp simp: a)
  done

end
