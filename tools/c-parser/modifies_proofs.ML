(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

signature MODIFIES_PROOFS =
sig

  type csenv = ProgramAnalysis.csenv
  val gen_modify_body : theory -> typ -> term -> term ->
                        ProgramAnalysis.modify_var list -> term
  (* [gen_modify_body thy ty s0 s vs]
     ty is the Isabelle type of the state
     s0 is an Isabelle var standing for the initial state
     s is an Isabelle var standing for the final state
     vs is the list of variables allowed to be modified.

     The "global exception" variable will automatically be added to the
     list of variables as something that can be modified.
  *)


  val gen_modify_goal : theory -> typ list -> term -> string ->
                        ProgramAnalysis.modify_var list -> term
  (* [gen_modify_goal thy tys tm fname vs]
     tys is the three types that are parameters to all HoarePackage constants
     tm is the \<Gamma> that houses the lookup table from fn names to bodies
     fname is the name of the function being called
     vs is the list of variables allowed to be modified.

     The "global exception" variable will automatically be added to the
     goal as something that can be modified.
  *)

  val gen_modify_goalstring : csenv -> string -> string list -> string

  val modifies_vcg_tactic : local_theory -> int -> tactic
  val modifies_tactic : thm -> local_theory -> tactic

  val prove_all_modifies_goals_local : csenv -> (string -> bool) -> typ list ->
                                       local_theory -> local_theory

  val prove_all_modifies_goals : theory -> csenv -> (string -> bool) ->
                                 typ list -> string -> theory
   (* string is the name of the locale where the theorems about Gamma live *)

  val sorry_modifies_proofs : bool ref

  val calculate_modifies_proofs : bool Config.T
end

structure Modifies_Proofs : MODIFIES_PROOFS =
struct

open TermsTypes
type csenv = ProgramAnalysis.csenv

val sorry_modifies_proofs = ref false

(* Config item to determine if "modifies" thms should be generated. *)
val (calculate_modifies_proofs, calculate_modifies_proofs_setup) =
    Attrib.config_bool (Binding.name "calculate_modifies_proofs") (K true)
val _ = Context.>> (Context.map_theory calculate_modifies_proofs_setup)

fun gen_modify_goalstring csenv fname modstrings = let
  fun foldthis (vname, vset) =
      case MSymTab.lookup (ProgramAnalysis.get_addressed csenv) (MString.mk vname) of
        NONE => Binaryset.add(vset, vname)
      | SOME _ => Binaryset.add(vset, NameGeneration.global_heap)
  val vset = List.foldl foldthis (Binaryset.empty String.compare) modstrings
in
    "\<forall>\<sigma>. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} Call "^
    fname ^ "_'proc " ^
    "{t. t may_only_modify_globals \<sigma> in [" ^
    commas (Binaryset.listItems vset) ^ "]}"
end

fun mvar_to_string mv = let
  open ProgramAnalysis
in
  case mv of
    TheHeap => NameGeneration.global_heap
  | M vi => MString.dest (get_mname vi)
  | PhantomState => NameGeneration.phantom_state_name
  | GhostState => NameGeneration.ghost_state_name
end

fun gen_modify_body thy state_ty sigma t mvars = let
  val vars = map mvar_to_string mvars
  val vars = rev (sort_strings vars)
  val glob_ty =
      case state_ty of
          Type(@{type_name "StateSpace.state.state_ext"}, [g, _]) => g
        | _ => raise TYPE ("state_ty has unexpected form", [state_ty], [])
  val globals_name = @{const_name "globals"}
  val globals_t = Const(globals_name, state_ty --> glob_ty)
  val base_t = globals_t $ sigma
  fun gettypes v = let
    val vn = HoarePackage.varname v
    val qvn = "globals." ^ vn
    val fullvar_name = Sign.intern_const thy qvn
    val varaccessor_ty =
        valOf (Sign.const_type thy fullvar_name)
        handle Option => raise Fail ("Couldn't get type for constant "^
                                     fullvar_name)
    val (_, var_ty) = dom_rng varaccessor_ty
  in
    (vn, fullvar_name, var_ty)
  end
  val vartypes = map gettypes vars
  fun mk_update((var_name, fullvarname, var_ty), acc) = let
    val var_v = Free(var_name, var_ty)
    val updfn = mk_abs(Free("_", var_ty), var_v)
    val updator = Const(suffix Record.updateN fullvarname,
                        (var_ty --> var_ty) --> (glob_ty --> glob_ty))
  in
    updator $ updfn $ acc
  end
  val updated_t = List.foldr mk_update base_t vartypes
  val globals_tt = globals_t $ t
  val meq_t = Const(HoarePackage.modeqN, glob_ty --> glob_ty --> bool) $
              globals_tt $ updated_t
  fun mk_mex ((var_name, _, var_ty), base) = let
    val abs_t = mk_abs(Free(var_name, var_ty), base)
  in
    Const(HoarePackage.modexN, (var_ty --> bool) --> bool) $
    abs_t
  end
in
  List.foldl mk_mex meq_t vartypes
end

fun gen_modify_goal_pair thy tyargs gamma fname mvars = let
  val state_ty = hd tyargs
  val name_ty = List.nth(tyargs, 1)
  val com_ty = mk_com_ty tyargs
  val stateset_ty = mk_set_type state_ty
  val error_ty = List.nth(tyargs, 2)
  val sigma = Free("\<sigma>", state_ty)
  val t = Free("t", state_ty)

  val theta_element_ty =
      list_mk_prod_ty [stateset_ty, name_ty, stateset_ty, stateset_ty]
  val theta_ty = mk_set_type theta_element_ty
  val hoarep_t =
      Const(@{const_name "hoarep"},
            (name_ty --> mk_option_ty com_ty) -->
            theta_ty -->
            mk_set_type error_ty -->
            stateset_ty -->
            com_ty -->
            stateset_ty -->
            stateset_ty -->
            bool)
  val theta_t = mk_empty theta_element_ty
  val faults_t = mk_UNIV error_ty
  val pre_t = list_mk_set state_ty [sigma]
  val prog_t = Const(@{const_name "Language.com.Call"},
                     name_ty --> mk_com_ty tyargs) $
               Const(Sign.intern_const
                         thy
                         (fname ^ HoarePackage.proc_deco),
                     name_ty)
  (* post_t is the complicated Collect term *)
  val post_t = let
    val mexxed_t = gen_modify_body thy state_ty sigma t mvars
  in
    mk_collect_t state_ty $ mk_abs(t, mexxed_t)
  end
  val abr_t = mk_empty state_ty
  val goal_t = hoarep_t $ gamma $ theta_t $ faults_t $ pre_t $ prog_t $ post_t $ abr_t
in
  (mk_abs(sigma, post_t), mk_forall(sigma, goal_t))
end

fun gen_modify_goal thy tyargs gamma fname mvars = let
  val (_, goal) = gen_modify_goal_pair thy tyargs gamma fname mvars
in
  goal
end

fun munge_tactic ctxt goal msgf tac = let
  fun tacticfn {prems = _,context} st =
      if !sorry_modifies_proofs then
         Skip_Proof.cheat_tac ctxt 1 st
      else
         tac context st
  fun tacticmsg st t = case Seq.pull (tacticfn st t) of
      NONE => Seq.empty
    | SOME (t, _) => (msgf (); Seq.single t)
in
  Goal.prove_future ctxt [] [] (TermsTypes.mk_prop goal) tacticmsg
end

fun modifies_vcg_tactic ctxt i t = let
  val timer = Timer.startCPUTimer ()
  val tac = HoarePackage.vcg_tac "_modifies" "false" [] ctxt i
  val res = Seq.list_of (DETERM tac t)
  val {usr, sys} = Timer.checkCPUTimer timer
in
  Feedback.informStr (0, "modifies vcg-time:" ^ Time.fmt 2 (Time.+ (usr, sys)));
  Seq.of_list res
end

fun modifies_tactic mod_inv_prop ctxt = let
  val mip_intros = [mod_inv_prop] RL @{thms modifies_inv_intros}
  val gsurj = Proof_Context.get_thm ctxt "globals.surjective"
  val geqs = map (fn t => [gsurj, gsurj] MRS t) @{thms asm_store_eq_helper}
  val gsp = Proof_Context.get_thms ctxt "globals.splits"
in
  EVERY [
    HoarePackage.hoare_rule_tac ctxt @{thms HoarePartial.ProcNoRec1} 1,
    REPEAT_ALL_NEW (resolve_tac ctxt (@{thms allI} @ mip_intros)) 1,
    ALLGOALS (modifies_vcg_tactic ctxt),
    ALLGOALS (clarsimp_tac ctxt),
    ALLGOALS (TRY o resolve_tac ctxt @{thms asm_spec_enabled}),
    ALLGOALS (clarsimp_tac
                (ctxt addSEs @{thms asm_specE state_eqE} addsimps (gsp @ @{thms state.splits}))),
    ALLGOALS (clarsimp_tac (ctxt addsimps geqs)),
    ALLGOALS (TRY o REPEAT_ALL_NEW (resolve_tac ctxt [exI])),
    ALLGOALS (asm_full_simp_tac ctxt)
  ]
end

fun get_mod_inv_prop ctxt post_abs mod_inv_props = let
  fun prove_mod_inv_prop () = let
    val mi_prop_ty = fastype_of post_abs --> HOLogic.boolT
    fun mi_goal prop = HOLogic.mk_Trueprop (Const (prop, mi_prop_ty) $ post_abs)
    fun mi_prop_tac _ = let
      val globals_equality = Proof_Context.get_thm ctxt "globals.equality"
      fun mi_refl_tac _ =
        simp_tac (clear_simpset ctxt addsimps @{thms modifies_inv_refl_def mex_def meq_def}) 1 THEN
        resolve_tac ctxt @{thms allI} 1 THEN
        resolve_tac ctxt @{thms CollectI} 1 THEN
        TRY (REPEAT_ALL_NEW (resolve_tac ctxt @{thms exI}) 1) THEN
        resolve_tac ctxt [globals_equality] 1 THEN
        ALLGOALS (simp_tac (clear_simpset ctxt addsimprocs [Record.simproc]))
      fun mi_incl_tac _ =
        simp_tac (clear_simpset ctxt addsimps @{thms modifies_inv_incl_def mex_def meq_def}) 1 THEN
        resolve_tac ctxt @{thms allI} 1 THEN
        resolve_tac ctxt @{thms allI} 1 THEN
        resolve_tac ctxt @{thms impI} 1 THEN
        resolve_tac ctxt @{thms Collect_mono} 1 THEN
        TRY (REPEAT_ALL_NEW (resolve_tac ctxt @{thms ex_mono}) 1) THEN
        eresolve_tac ctxt @{thms CollectE} 1 THEN
        TRY (REPEAT_ALL_NEW (eresolve_tac ctxt @{thms exE}) 1) THEN
        clarsimp_tac ctxt 1
      val mi_refl = Goal.prove ctxt [] [] (mi_goal @{const_name modifies_inv_refl}) mi_refl_tac
      val mi_incl = Goal.prove ctxt [] [] (mi_goal @{const_name modifies_inv_incl}) mi_incl_tac
    in
      REPEAT_ALL_NEW (resolve_tac ctxt (mi_refl :: mi_incl :: @{thms modifies_inv_prop})) 1
    end
    val mi_prop = Goal.prove_future ctxt [] [] (mi_goal @{const_name modifies_inv_prop}) mi_prop_tac
  in
    (mi_prop, Termtab.update (post_abs, mi_prop) mod_inv_props)
  end
in
  case Termtab.lookup mod_inv_props post_abs of
      SOME mi_prop => (mi_prop, mod_inv_props)
    | NONE => prove_mod_inv_prop ()
end

fun prove_all_modifies_goals_local csenv includeP tyargs lthy = let
  open ProgramAnalysis
  val _ = Feedback.informStr (0, "Proving automatically calculated modifies proofs")
  val globs_all_addressed = Config.get lthy CalculateState.globals_all_addressed
  val _ = Feedback.informStr (0, "Globals_all_addressed mode = " ^ Bool.toString globs_all_addressed)
  (* first enter the locale where \<Gamma> exists, and where all the
     mappings from function name to function body exist *)
  val lconsts = Proof_Context.consts_of lthy
  val gamma_nm = Consts.intern lconsts "\<Gamma>"
  val gamma_t = Syntax.check_term lthy (Const(gamma_nm, dummyT))
  val {callgraph,callers} = compute_callgraphs csenv

  fun do_one (fname, (failedsofar, mod_inv_props, lthy)) = let
      val _ = Feedback.informStr (0, "Beginning modifies proof for singleton " ^ fname)
      val timer = Timer.startCPUTimer ()

      fun modifies_msg msg () = let
          val {usr, sys} = Timer.checkCPUTimer timer
        in
          Feedback.informStr (0, "modifies:" ^ fname ^ ":" ^
                   Time.fmt 2 (Time.+ (usr, sys)) ^ "s:" ^ msg)
        end;
    in
      case get_modifies csenv fname of
        NONE => (modifies_msg "can't do modifies proof" ();
                 (Binaryset.add(failedsofar,fname), mod_inv_props, lthy))
      | SOME mods => let
          val mvlist = Binaryset.listItems mods
          val mvlist =
              (* map globals to "TheHeap" if globals_all_addressed is true*)
              if globs_all_addressed then map (fn M _ => TheHeap | x => x) mvlist
              else mvlist
          val calls = case Symtab.lookup callgraph fname of
                        NONE => Binaryset.empty String.compare
                      | SOME s => s
          val i = Binaryset.intersection(calls, failedsofar)
        in
          if Binaryset.isEmpty i then let
              val thy = Proof_Context.theory_of lthy
              val (post_abs, goal) = gen_modify_goal_pair thy tyargs gamma_t fname mvlist
              val (mod_inv_prop, mod_inv_props') = get_mod_inv_prop lthy post_abs mod_inv_props
              val th = munge_tactic lthy goal (modifies_msg "completed") (modifies_tactic mod_inv_prop)
              val (_, lthy) = Local_Theory.note ((Binding.name (fname ^ "_modifies"), []), [th]) lthy
            in
              (failedsofar, mod_inv_props', lthy)
            end
          else let
              val example = valOf (Binaryset.find (fn _ => true) i)
              val _ = modifies_msg
                          ("not attempted, as it calls a function ("
                           ^ example ^ ") that has failed")
            in
              (Binaryset.add(failedsofar, fname), mod_inv_props, lthy)
            end
        end
    end
  exception NoMods of string Binaryset.set
  fun do_recgroup (fnlist, (failedsofar, mod_inv_props, lthy)) = let
    val n = length fnlist (* >= 1 *)
    val rec_thm = HoarePackage.gen_proc_rec lthy HoarePackage.Partial n
    val mods = valOf (get_modifies csenv (hd fnlist))
        handle Option => (Feedback.informStr (0, "No modifies info for "^hd fnlist);
                          raise NoMods (Binaryset.addList(failedsofar, fnlist)))
    val mvlist = Binaryset.listItems mods
    fun gen_modgoal (fname : string) : term = let
      val calls = case Symtab.lookup callgraph fname of
                    NONE => raise Fail (fname ^ " part of clique, but \
                                                \doesn't call anything??")
                  | SOME s => s
      val i = Binaryset.intersection(calls, failedsofar)
    in
      if Binaryset.isEmpty i then
        gen_modify_goal (Proof_Context.theory_of lthy) tyargs
                        gamma_t fname mvlist
      else let
          val example = valOf (Binaryset.find (fn _ => true) i)
          val _ = Feedback.informStr (0, "Not attempting modifies proof for "^fname^
                           " (or its recursive component) as it calls a\
                           \ function ("^example^") that has failed")
        in
          raise NoMods (Binaryset.addList(failedsofar, fnlist))
        end
    end
    val nway_goal = list_mk_conj (map gen_modgoal fnlist)
    fun tac ctxt =
        HoarePackage.hoare_rule_tac ctxt [rec_thm] 1 THEN
        ALLGOALS (HoarePackage.vcg_tac "_modifies" "false" [] ctxt)
  in
    let
      val pnm = "Modifies proof for recursive clique " ^ commas fnlist
      val _ = Feedback.informStr (0, pnm ^ " commencing.")
      fun msg () = Feedback.informStr (0, pnm ^ " completed.")
      val nway_thm = munge_tactic lthy nway_goal msg tac
      val nway_thms = HOLogic.conj_elims lthy nway_thm
      val _ = length nway_thms = length fnlist orelse
              raise Fail "CONJUNCTS nway_thm and fnlist don't match up!"
      fun note_it (nm, th, lthy) =
          (Feedback.informStr (0, "Modifies rule for "^nm^" extracted");
           #2 (Local_Theory.note ((Binding.name (nm ^ "_modifies"), []),
                                  [th])
                                 lthy))
      val noted = ListPair.foldl note_it lthy (fnlist, nway_thms)
    in
      (failedsofar, mod_inv_props, noted)
    end
  end handle NoMods newset => (newset, mod_inv_props, lthy)


  fun do_scc (args as (fnlist, acc)) =
      case fnlist of
        [fname] =>
          if includeP fname then
            if not (is_recursivefn csenv fname) then
              do_one(fname, acc)
            else do_recgroup args
          else acc
      | (fname::_) => if includeP fname then do_recgroup args
                      else acc
      | _ => raise Fail "SCC with empty list!"

  fun lift f fnm = case Symtab.lookup f fnm of
                     NONE => []
                   | SOME s => Binaryset.listItems s
  val sorted_fnames =
      Topo_Sort.topo_sort { cmp = String.compare,
                            graph = lift callgraph,
                            converse = lift callers}
                          (get_functions csenv)
  val acc_init = (Binaryset.empty String.compare, Termtab.empty, lthy)
  val (_, _, lthy) = List.foldl do_scc acc_init sorted_fnames
in
  lthy
end

fun prove_all_modifies_goals thy csenv includeP tyargs globloc =
  if Config.get_global thy calculate_modifies_proofs then
    let
      val lthy = Named_Target.init globloc thy
    in
      lthy
        |> prove_all_modifies_goals_local csenv includeP tyargs
        |> Local_Theory.reset
        |> Local_Theory.exit_global
    end
  else
    thy

end (* struct *)
