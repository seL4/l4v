(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory TSubst (* FIXME: bitrotted *)
imports Main
begin


method_setup tsubst = 
  {* Scan.lift (Args.mode "asm" -- Scan.optional (Args.parens (Scan.repeat Parse.nat)) [0] -- Parse.term) >> (fn ((asm,occs),t) => (fn ctxt => 
  Method.SIMPLE_METHOD (Subgoal.FOCUS_PARAMS (fn focus => (fn thm =>
  let
    val ctxt' = #context focus
    val thy = Proof_Context.theory_of ctxt'

    val ((_, schematic_terms), ctxt2) =
      Variable.import_inst true [(#concl focus) |> Thm.term_of] ctxt'
      |>> Thm.certify_inst thy
     
    val ctxt3 = fold (fn (t,t') => Variable.bind_term (Thm.term_of t |> Term.dest_Var |> fst,SOME (t' |> Thm.term_of))) schematic_terms ctxt2


    val athm = Syntax.read_term ctxt3 t
          |> Object_Logic.ensure_propT thy
          |> Thm.cterm_of thy
          |> Thm.trivial

    val thm' = Thm.instantiate ([],schematic_terms) thm
         
  in
    (if asm then EqSubst.eqsubst_asm_tac else EqSubst.eqsubst_tac) 
      ctxt3 occs [athm] 1 thm'
      |> Seq.map (singleton (Variable.export ctxt3 ctxt'))
     end)) ctxt 1))) *}

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
