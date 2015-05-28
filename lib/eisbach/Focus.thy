(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Focus
imports Method_Definition
keywords "focus" "unfocus":: prf_script
begin

ML {*fun freeze ctxt thm =
  let
 
    val (schematics, ctxt3) =
      Variable.import_inst true ([prop_of thm]) ctxt
      |>> Thm.certify_inst (Thm.theory_of_thm thm);

    val frozen_prop = Thm.instantiate schematics thm;
  in
    (frozen_prop,(schematics,ctxt3)) end;*}

ML {* 

fun focus use_asms state =
  let
    val _ = Proof.assert_backward state
    val thy = Proof.theory_of state;
    val cert = Thm.cterm_of thy;
    
    val {goal = goal, context = ctxt} = Proof.simple_goal state

    val (focus,focused_goal) = Subgoal2.gen_focus (true,true,use_asms,true) ctxt 1 goal
               
    
    val result_ref = Synchronized.var "goal var" (Drule.dummy_thm)
                          
    fun do_retrofit result =
    let
      val result' = 
        Subgoal2.retrofit' ctxt focus use_asms true 1 result goal
        |> Seq.hd
        
       val _ = Synchronized.change result_ref (K (result'))
     in
      Goal.protect 0 (Conjunction.intr (Drule.mk_term (Thm.cprop_of result')) result') end;
    

          
    val goal = Var (("guess", 0), propT);
    
    fun put_thm tac = Method.Basic (K (RAW_METHOD (K (Seq.single o tac))))
    
    val before_qed = SOME (put_thm do_retrofit)
        
    (*FIXME: Proof.local_goal is smashing flex-flex pairs between before_qed and after_qed,
    so we need to stash it statefully to avoid losing this information.
    It's unclear whether this will break in batch processing.*)
    
    
    fun after_qed [[_, _]] _ =  
    let
      val res = Synchronized.value result_ref
    in
      state
      |> Proof.refine (put_thm (K res)) |> Seq.hd end;
    
    val concl = 
      let 
        val concl = (Logic.unprotect (concl_of focused_goal))
      in
        the_default concl (try HOLogic.dest_Trueprop concl) end
  in
    Proof.begin_notepad (#context focus)
    |> Proof.local_goal (K (K ())) (K I) (pair o rpair I)
      "subgoal" before_qed after_qed [(Thm.empty_binding, [Logic.mk_term goal, goal])]
    |> Proof.put_thms false ("focus_prems",SOME (Assumption.all_prems_of (#context focus)))
    |> Proof.bind_terms [(("concl",0),SOME (Thm.term_of (#concl focus)))]
    |> Proof.refine (Method.primitive_text (K focused_goal)) |> Seq.hd
   
  end;
  
val _ =
  Outer_Syntax.command @{command_keyword "focus"} "focus subgoal"
    ((Scan.optional (Args.parens (Args.$$$ "no_asm") >> K false) true) >> 
      (fn mode => Toplevel.print o Toplevel.proofs (Seq.make_results o Seq.single o focus mode)));

(* Needed because "done" is prematurely terminating the parsing of the proof in batch mode *)
(* Note that "qed" is still necessary to unfocus if we went into structured proof mode,
   so this is not a total solution *)
val _ =
  Outer_Syntax.command @{command_keyword "unfocus"} "done proof"
    (Scan.succeed Isar_Cmd.done_proof);
  
  *}  

  

end
