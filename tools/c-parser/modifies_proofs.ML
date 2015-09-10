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


fun gen_modify_goal thy tyargs gamma fname mvars = let
  val state_ty = hd tyargs
  val name_ty = List.nth(tyargs, 1)
  val com_ty = mk_com_ty tyargs
  val stateset_ty = mk_set_type state_ty
  val error_ty = List.nth(tyargs, 2)
  val sigma = Free("\<sigma>", state_ty)
  val t = Free("t", state_ty)

  val arg1_element_ty =
      list_mk_prod_ty [stateset_ty, name_ty, stateset_ty, stateset_ty]
  val arg1_ty = mk_set_type arg1_element_ty
  val hoarep_t =
      Const(@{const_name "hoarep"},
            (name_ty --> mk_option_ty com_ty) -->
            arg1_ty -->
            mk_set_type error_ty -->
            stateset_ty -->
            com_ty -->
            stateset_ty -->
            stateset_ty -->
            bool)
  val arg1_t = mk_empty arg1_element_ty
  val arg2_t = mk_UNIV error_ty
  val arg3_t = list_mk_set state_ty [sigma]
  val arg4_t = Const(@{const_name "Language.com.Call"},
                     name_ty --> mk_com_ty tyargs) $
               Const(Sign.intern_const
                         thy
                         (fname ^ HoarePackage.proc_deco),
                     name_ty)
  (* arg5 is the complicated Collect term *)
  val arg5_t = let
    val mexxed_t = gen_modify_body thy state_ty sigma t mvars
  in
    mk_collect_t state_ty $ mk_abs(t, mexxed_t)
  end
  val arg6_t = mk_empty state_ty
in
  mk_forall(sigma,
            hoarep_t $ gamma $ arg1_t $ arg2_t $ arg3_t $ arg4_t $
                     arg5_t $ arg6_t)
end

fun munge_tactic ctxt goal tac = let
  fun tacticfn {prems = _,context} st =
      if !sorry_modifies_proofs then
         Skip_Proof.cheat_tac ctxt 1 st
      else
         tac context st
in
  Goal.prove_future ctxt [] [] (TermsTypes.mk_prop goal) tacticfn
end

fun prove_all_modifies_goals_local csenv includeP tyargs lthy = let
  open ProgramAnalysis
  val _ = tracing "Proving automatically calculated modifies proofs"
  val globs_all_addressed = Config.get lthy CalculateState.globals_all_addressed
  val _ = tracing ("Globals_all_addressed mode = " ^ Bool.toString globs_all_addressed)
  (* first enter the locale where \<Gamma> exists, and where all the
     mappings from function name to function body exist *)
  val lconsts = Proof_Context.consts_of lthy
  val gamma_nm = Consts.intern lconsts "\<Gamma>"
  val gamma_t = Syntax.check_term lthy (Const(gamma_nm, dummyT))
  val {callgraph,callers} = compute_callgraphs csenv

  fun do_one (fname, (failedsofar, lthy)) = let
      val timer = Timer.startCPUTimer ()

      fun modifies_msg msg = let
          val {usr, sys} = Timer.checkCPUTimer timer
        in
          tracing ("modifies:" ^ fname ^ ":" ^
                   Int.toString (Time.toSeconds usr + Time.toSeconds sys) ^
                   "s:" ^ msg)
        end;
    in
      case get_modifies csenv fname of
        NONE => (modifies_msg "can't do modifies proof";
                 (Binaryset.add(failedsofar,fname), lthy))
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
              val goal = gen_modify_goal thy tyargs gamma_t fname mvlist
              fun tac ctxt = let
                val geq = Proof_Context.get_thm ctxt "globals.equality"
              in
                HoarePackage.vcg_tac "_modifies" "false" [] ctxt 1 THEN
                ALLGOALS (REPEAT_ALL_NEW (resolve_tac ctxt [exI, geq])) THEN
                ALLGOALS (asm_full_simp_tac ctxt)
              end
            in
              let
                val th = munge_tactic lthy goal tac
                val (_, lthy) =
                      Local_Theory.note
                          ((Binding.name (fname ^ "_modifies"), []), [th])
                          lthy
              in
                (failedsofar, lthy) before
                modifies_msg "successful"
              end
            end
          else let
              val example = valOf (Binaryset.find (fn _ => true) i)
              val _ = modifies_msg
                          ("not attempted, as it calls a function ("
                           ^ example ^ ") that has failed")
            in
              (Binaryset.add(failedsofar, fname), lthy)
            end
        end
    end
  exception NoMods of string Binaryset.set
  fun do_recgroup (fnlist, (failedsofar, lthy)) = let
    val n = length fnlist (* >= 1 *)
    val rec_thm = HoarePackage.gen_proc_rec lthy HoarePackage.Partial n
    val mods = valOf (get_modifies csenv (hd fnlist))
        handle Option => (tracing ("No modifies info for "^hd fnlist);
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
          val _ = tracing ("Not attempting modifies proof for "^fname^
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
      val nway_thm = munge_tactic lthy nway_goal tac
      val nway_thms = HOLogic.conj_elims lthy nway_thm
      val _ = length nway_thms = length fnlist orelse
              raise Fail "CONJUNCTS nway_thm and fnlist don't match up!"
      fun note_it (nm, th, lthy) =
          (tracing ("Modifies proof for "^nm^" successful");
           #2 (Local_Theory.note ((Binding.name (nm ^ "_modifies"), []),
                                  [th])
                                 lthy))
      val noted = ListPair.foldl note_it lthy (fnlist, nway_thms)
    in
      (failedsofar, noted)
    end
  end handle NoMods newset => (newset, lthy)


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
  val (_, lthy) =
      List.foldl do_scc (Binaryset.empty String.compare, lthy) sorted_fnames
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
        |> Local_Theory.restore
        |> Local_Theory.exit_global
    end
  else
    thy

end (* struct *)
