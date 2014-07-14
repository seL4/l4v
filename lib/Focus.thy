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
imports Main
keywords "focus" :: prf_script
begin


ML {* 

fun push_asms_to_concl ctxt nasms thm =
let
  val cert = Thm.cterm_of (Proof_Context.theory_of ctxt)  
  val all_prems = Drule.strip_imp_prems (cprop_of thm)  
  val asms = take nasms all_prems
 
  val B_names = map (fn i => "B" ^ Int.toString i) (1 upto (length all_prems - nasms))
  
  val (C :: Bs,ctxt') = ctxt
  |> Proof_Context.add_fixes (map (fn n => (Binding.name n,SOME propT,NoSyn)) ("C" :: B_names))
  |>> map (cert o Free o rpair propT)
  
  val concl =  Drule.list_implies (asms @ Bs,Drule.protect C)
  val my_thm = Goal.init concl

  val new_thm = my_thm
  |> Thm.elim_implies (Goal.conclude (Thm.assume (Drule.protect concl)))
  |> Goal.conclude
  |> fold (Thm.elim_implies o Thm.assume)  (asms @ Bs)
  |> Goal.conclude
  |> Drule.implies_intr_list asms
  |> Goal.protect
  |> Drule.implies_intr_list Bs
  |> Drule.implies_intr_list [Drule.protect concl]
  |> singleton (Variable.export ctxt' ctxt)  
  
  val composed = new_thm OF [Goal.protect thm]
  
 in
   composed end

   
fun focus use_asms state =
  let
    val _ = Proof.assert_backward state
    val thy = Proof.theory_of state;
    val cert = Thm.cterm_of thy;
    
    val {goal = goal, context = ctxt} = Proof.simple_goal state

    val (focus,focused_goal) = Subgoal.focus ctxt 1 goal
    
    val focused_goal' = if use_asms then focused_goal
    |> Method.insert_tac (#prems focus) 1
    |> Seq.hd
    else focused_goal
    
    fun fix_result ctxt result = result
    |> Drule.implies_intr_list (#asms focus)
    |> push_asms_to_concl ctxt (length (#asms focus))
       
    fun retrofit new_ctxt result = 
      let
        val result' = (use_asms ? (fix_result new_ctxt)) result
        val asms = if use_asms then [] else (#asms focus)
        val res = Subgoal.retrofit (#context focus) ctxt (#params focus) asms 1 result' goal
      in
        res
        |> Seq.hd end
    
    fun do_retrofit ctxt th =
      let
        val res = (retrofit ctxt th)
      in
        Goal.protect (Conjunction.intr (Drule.mk_term (Thm.cprop_of res)) res) end;

    val goal = Var (("guess", 0), propT);
      
    val before_qed = SOME (Method.Basic (fn ctxt => (SIMPLE_METHOD (PRIMITIVE (do_retrofit ctxt)))))
        
    fun after_qed [[_, res]] _ =  state
    |> Proof.refine (Method.primitive_text (K res)) |> Seq.hd
    
    val concl = 
      let 
        val concl = (Logic.unprotect (concl_of focused_goal'))
      in
        the_default concl (try HOLogic.dest_Trueprop concl) end
  in
    Proof.begin_notepad (#context focus)
    |> Proof.local_goal (K (K ())) (K I) (pair o rpair I)
      "subgoal" before_qed after_qed [(Thm.empty_binding, [Logic.mk_term goal, goal])]
    |> Proof.put_thms false (Auto_Bind.assmsN,SOME (Assumption.all_prems_of (#context focus)))
    |> Proof.bind_terms [(("concl",0),SOME concl)]
    |> Proof.refine (Method.primitive_text (K focused_goal')) |> Seq.hd
  end;
  
val _ =
  Outer_Syntax.command @{command_spec "focus"} "focus subgoal"
    ((Scan.optional (Args.parens (Args.$$$ "no_asm") >> K false) true) >> 
      (fn mode => Toplevel.print o Toplevel.proofs (Seq.make_results o Seq.single o focus mode)));     
  
  *}  
  
schematic_lemma test: "\<And>x. Q x \<and> ?P x\<Longrightarrow> ?P x \<and> Q x"
  focus
    thm assms
    apply (rule conjE)
  done
  apply assumption
  focus (no_asm)
    thm assms
    term ?concl
    apply (rule conjI)
    apply (rule assms)
    apply (rule assms)
  done
done
