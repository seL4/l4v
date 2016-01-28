(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

structure AutoCorresLegacy = struct

fun mk_l1corres_trivial_thm fn_info ctxt fn_name = let
    val info = Symtab.lookup (FunctionInfo.get_functions fn_info) fn_name
        |> the
    val const = #const info
    val impl_thm = Proof_Context.get_thm ctxt (fn_name ^ "_impl")
    val gamma = safe_mk_meta_eq impl_thm |> Thm.concl_of |> Logic.dest_equals
        |> fst |> (fn (f $ _) => f | t => raise TERM ("gamma", [t]))
    val thm = @{thm L1corres_call_simpl}
        WHERE [("proc", Thm.cterm_of ctxt const), ("Gamma", Thm.cterm_of ctxt gamma)]
    val body = SimplConv.get_body_of_l1corres_thm thm
    val term = Abs ("measure", @{typ nat}, body)
  in (term, thm) end

fun get_ext_l1corres_thm prog_info fn_info ctxt fn_name = let
    val callees = FunctionInfo.get_function_callees fn_info fn_name
    fun fake_callee nm = let
        val (term, thm) = mk_l1corres_trivial_thm fn_info ctxt nm
      in (nm, (false, term, thm)) end
    val callee_tab = Symtab.make (map fake_callee callees)
  in SimplConv.get_l1corres_thm prog_info fn_info ctxt true false fn_name
    callee_tab @{term "ameasure :: nat"} |> fst
  end

fun mk_l2corres_trivial_thm fn_info ctxt gs fn_name = let
    val info = Symtab.lookup (FunctionInfo.get_functions fn_info) fn_name
        |> the
    val const = #const info
    val args = #args info
    val impl_thm = Proof_Context.get_thm ctxt (fn_name ^ "_impl")
    val gamma = safe_mk_meta_eq impl_thm |> Thm.concl_of |> Logic.dest_equals
        |> fst |> (fn (f $ _) => f | t => raise TERM ("gamma", [t]))
    val (sT, gsT) = case strip_type (fastype_of gs) of
        ([sT], gsT) => (sT, gsT) | _ => raise TERM ("mk_l2corres_trivial_thm", [gs])
    val ex_xf = Abs ("s", sT, HOLogic.unit)

    fun set_domain_type (Const (s, T)) = Const (s, sT --> range_type T)
      | set_domain_type t = raise TERM ("set_domain_type", [t])
    val params = Symtab.lookup (#proc_info (Hoare.get_data ctxt))
      (fn_name ^ "_'proc") |> the |> #params
      |> map (apsnd (Proof_Context.read_const {proper=true, strict=true} ctxt #> set_domain_type))
    val arg_accs = filter (fn p => fst p = HoarePackage.In) params |> map snd
    val ret_accs = filter (fn p => fst p = HoarePackage.Out) params |> map snd

    val arg_xf = Abs ("s", sT, HOLogic.mk_tuple (map (fn t => t $ Bound 0) arg_accs))
    val ret_xf = Abs ("s", sT, HOLogic.mk_tuple (map (fn t => t $ Bound 0) ret_accs))
    val arg_frees = map (fn (s, T) => Var ((s, 0), T)) args
    val arg_v = HOLogic.mk_tuple arg_frees

    val thm = @{thm L2corres_L2_call_simpl}
        WHERE (map (apsnd (Thm.cterm_of ctxt))
            [("proc", const), ("Gamma", gamma), ("ex_xf", ex_xf), ("gs", gs),
             ("ret_xf", ret_xf), ("arg_fn", arg_xf), ("args", arg_v)])
    val body = LocalVarExtract.get_body_of_thm ctxt thm
    val term = fold_rev Term.lambda (@{term "ameasure :: nat"} :: arg_frees) body
  in (term, thm) end

fun get_ext_l2corres_thm prog_info fn_info ctxt gs fn_name l1_body = let
    val callees = FunctionInfo.get_function_callees fn_info fn_name
    fun fake_callee nm = let
        val (term, thm) = mk_l2corres_trivial_thm fn_info ctxt gs nm
      in (nm, (false, term, thm)) end
    val callee_tab = Symtab.make (map fake_callee callees)
    val args = Symtab.lookup (FunctionInfo.get_functions fn_info) fn_name
        |> the |> #args
    val (thm, _) = LocalVarExtract.get_l2corres_thm ctxt prog_info fn_info true false fn_name
        callee_tab (map Free args) l1_body @{thm refl}
    val body = LocalVarExtract.get_body_of_thm ctxt thm
  in (body, Drule.generalize ([], map fst args) thm) end

fun get_ext_type_strengthen_thm ctxt prog_info fn_info fn_name body = let
    val rules = Monad_Types.get_ordered_rules ["nondet"] (Context.Proof @{context})
        |> hd
    val res = TypeStrengthen.perform_lift_and_polish ctxt prog_info fn_info rules true
        ((@{thm refl} WHERE [("t", Thm.cterm_of ctxt body)]) |> mk_meta_eq)
        fn_name
    val args = Symtab.lookup (FunctionInfo.get_functions fn_info) fn_name
        |> the |> #args
  in case res of SOME (thm, _) => Drule.generalize ([], map fst args) thm
    | NONE => raise TERM ("get_ext_type_strengthen_thm: NONE", [])
  end

fun dest_ccorres_underlying_call t = case strip_comb t |> apsnd List.rev
  of (Const (@{const_name ccorres_underlying}, _),
    ((Const (@{const_name com.Call}, _) $ proc) :: _)) => proc
  | _ => raise TERM ("dest_ccorres_underlying_call", [t])

fun tac prog_info fn_info globals ctxt = SUBGOAL (fn (t, i) => let
    val proc = dest_ccorres_underlying_call (HOLogic.dest_Trueprop
        (Logic.strip_assums_concl t))
    val fn_name = FunctionInfo.get_function_from_const fn_info proc
        |> the |> #name
    val l1corres = get_ext_l1corres_thm prog_info fn_info ctxt fn_name
    val l2corres = get_ext_l2corres_thm prog_info fn_info ctxt
        globals fn_name (SimplConv.get_body_of_l1corres_thm l1corres)
    val ts = get_ext_type_strengthen_thm ctxt prog_info fn_info
        fn_name (fst l2corres)
  in rtac @{thm ccorres_underlying_autocorres} 
    THEN' rtac l1corres THEN' rtac (snd l2corres) THEN' rtac ts end i)

fun method prog_info fn_info globals
    = Scan.succeed (fn ctxt => Method.SIMPLE_METHOD (tac
        prog_info fn_info globals ctxt 1))

end