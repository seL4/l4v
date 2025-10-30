(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

structure CtacImpl =
struct

exception TACTIC of string;

(* FIXME: avoid refs *)
val time_ctac = ref false

type trace_opts = {
     trace_this : bool,
     trace_simp : bool,
     trace_ceqv : bool,
     trace_xpres : bool
}

val default_trace_opts : trace_opts = {trace_this = false, trace_simp = false, trace_ceqv = false, trace_xpres = false}
val all_trace_opts : trace_opts     = {trace_this = true, trace_simp = true, trace_ceqv = true, trace_xpres = true}
fun set_ceqv_trace_opts {trace_this, ...} = {trace_this = trace_this, trace_simp = true, trace_ceqv = true, trace_xpres = true}

fun tracet b s ctxt =
    if b
    then SUBGOAL (fn (p, _) =>
                let
                    val _ = tracing (s ^ Syntax.string_of_term ctxt p)
                in
                    no_tac
                end)
    else (fn _ => no_tac)


fun wrap_accum f i xq =
    Seq.make (fn () =>
             (case f i (fn () => Seq.pull xq) of
                  (_, NONE) => NONE
                | (i', SOME (x, xq')) => SOME (x, wrap_accum f i' xq')));

fun prim_trace_tac' b depth s ctxt t n thm = let
    val depth_str = "[" ^ Int.toString depth ^ "] "
    val _ = tracet b (depth_str ^ s ^ ":\n") ctxt n thm
    fun wrapper i f = case f () of
                          NONE => let val _ = if b then tracing (depth_str ^ s ^ " FAIL") else ()
                                  in (i, NONE) end
                        | SOME (x, xq) => let val _ = if b then tracing (depth_str ^ s ^ " (" ^ Int.toString i ^ ")") else ()
                                          in (i + 1, SOME (x, xq)) end
    val res = t n thm
in
    wrap_accum wrapper 0 res
end;

fun prim_trace_tac b depth s ctxt t thm = prim_trace_tac' b depth s ctxt (fn _ => t) 1 thm

(* Presumably you want to be careful with this ... don't use it when the results
 are inifinite, for example *)
fun nres_trace_tac ctxt s t thm = let
    val r    = t thm
    fun p1 (t, s) = s ^ "  ALT:\n" ^ Thm.string_of_thm ctxt t ^ "\n"
    val _    = tracing (foldl p1 s (Seq.list_of r))
in
    r
end;

fun nres_trace_tac' ctxt s t n thm = nres_trace_tac ctxt s (t n) thm

structure ctac_rules = Generic_Data
(struct
    type T = thm list
    val empty = []
    val merge = Thm.merge_thms;
end);

structure ctac_pre = Generic_Data
(struct
    type T = thm list
    val empty = []
    val merge = Thm.merge_thms;
end);

structure ctac_post = Generic_Data
(struct
    type T = thm list
    val empty = []
    val merge = Thm.merge_thms;
end);

val ctac_add = Thm.declaration_attribute
                    (fn thm =>
                        (ctac_rules.map (Thm.add_thm thm)));

val ctac_del = Thm.declaration_attribute
                    (fn thm =>
                        (ctac_rules.map (Thm.del_thm thm)));

val ctac_clear = ctac_rules.map (fn _ => [])

val ctac_pre_add = Thm.declaration_attribute
                    (fn thm =>
                        (ctac_pre.map (Thm.add_thm thm)));

val ctac_pre_del = Thm.declaration_attribute
                    (fn thm =>
                        (ctac_pre.map (Thm.del_thm thm)));

val ctac_pre_clear = ctac_pre.map (fn _ => [])

val ctac_post_add = Thm.declaration_attribute
                    (fn thm =>
                        (ctac_post.map (Thm.add_thm thm)));

val ctac_post_del = Thm.declaration_attribute
                    (fn thm =>
                        (ctac_post.map (Thm.del_thm thm)));

val ceqv_simpl_sequence_pair = Attrib.config_bool
    @{binding ceqv_simpl_sequence} (K false)
fun ceqv_simpl_seq ctxt = Config.get ctxt (fst ceqv_simpl_sequence_pair)

val setup =
  Attrib.setup @{binding "corres"} (Attrib.add_del ctac_add ctac_del)
    "correspondence rules"
  #> Attrib.setup @{binding "ccorres_pre"}
    (Attrib.add_del ctac_pre_add ctac_pre_del)
    "correspondence preprocessing rules"
  #> Attrib.setup @{binding "corres_post"}
    (Attrib.add_del ctac_post_add ctac_post_del)
    "correspondence postprocessing rules"
  #> snd ceqv_simpl_sequence_pair;

(* tacticals *)

fun REPEAT_DETERM' t n = REPEAT_DETERM (t n)

fun TRY' t = t ORELSE' (fn _ => all_tac)

(* Then all new with the first being distinguished --- this is
 * complex because we want to execute ftac _first_, then the new goals. *)
infix 1 THEN_ALL_NEW_DIST_FIRST;
fun (tac1 THEN_ALL_NEW_DIST_FIRST (ftac, tac2)) n st =
    st |> (tac1 n THEN (fn st' => (ftac n THEN (fn st'' =>
                                                   Seq.INTERVAL tac2
                                                                (n + Thm.nprems_of st'' - Thm.nprems_of st' + 1)
                                                                (n + (Thm.nprems_of st'' - Thm.nprems_of st)) st'')) st'));

(* Collapses a list down to THEN_ELSE (_, _ THEN_ELSE (_, ...)) *)
fun FIRST_COMMIT' tacs n =
    foldr (fn ((t, match), nomatch) => t n THEN_ELSE (match n, nomatch)) no_tac tacs

(* Return the name of the extraction function and its return type. *)
fun xfu_to_xf s = unsuffix "_update" s

fun update_to_xf s tp =
    (* tp should be (a -> a) -> cstate -> cstate *)
    (unsuffix "_update" s, domain_type (domain_type tp))

val cstate = @{typ "cstate"};

fun xf_to_update (s, tp) =
    (s ^ "_update", (tp --> tp) --> cstate --> cstate)

(* tacticals *)

fun SOLVE' tac n = SELECT_GOAL (SOLVE (tac 1)) n;

(* call stuff *)
fun call_name (Const ("Language.call", _) $ _ $ (Const (f, _)) $ _ $ _) = f
  | call_name t = raise TERM ("call_name: expecting Language.call", [t]);

(* ccorres stuff *)
type ccorres = {
     strel : term,
     gamma : term,
     rrel  : term,
     xf    : term,
     absg  : term,
     concg : term,
     ehs   : term,
     abs   : term,
     conc  : term
}

fun is_ccorres c =
    case head_of c of
        Const x => fst x = "Corres_UL_C.ccorres_underlying"
      | _       => false

fun dest_ccorres (lhs $ strel $ gamma $ vrrel $ vxf $ vg $ vg' $ vhs $ va $ vc)
  = if is_ccorres lhs then
        { strel = strel, gamma = gamma, rrel = vrrel,
          xf = vxf, absg = vg, concg = vg', ehs = vhs, abs = va, conc = vc }
    else
        raise TERM ("Expected head to be ccorres", [lhs])
  | dest_ccorres t = raise TERM ("Expected fully applied ccorres", [t]);

fun extract_seq_lhs (Const ("Language.com.Seq", _) $ a $ _) = SOME a
  | extract_seq_lhs _ = NONE;

val xfdc = let
    val (xf, tp) = dest_Const @{term "xfdc"}
in
    (xf, range_type tp)
end;

(* Cases we care about (xf_update is top level xf):
 * xf_update (foo_update v)
 * xf_update (\<lambda>x. foo_update v (g x))
 *
 * Note the first doesn't really work with this framework
 *)

fun field_update_to_xfru_maybe xf t = let

    val xf_occurs = member (op =) (Term.add_const_names t []) xf

    fun doit (Const (c, tp))
      = if (String.isSuffix "_update" c) then SOME ((c, tp), xf_occurs) else NONE
      | doit (Abs (_, _, c)) = doit c
      | doit (c $ _)         = doit c
      | doit _               = NONE
in
    doit t
end;

fun extract_basic_xf
        (Const ("Language.com.Basic", _) $ (Abs (_, _, (Const (c, tp) $ body $ _))))
  = let
      val xf_tp = update_to_xf c tp
  in
      (SOME xf_tp, field_update_to_xfru_maybe (fst xf_tp) body)
  end
  | extract_basic_xf (Const ("Language.com.Basic", _) $ (Const (c, tp) $ body))
  = let
      val xf_tp = update_to_xf c tp
  in
      (SOME xf_tp, field_update_to_xfru_maybe (fst xf_tp) body)
  end
  (* In the unknown case, return xfdc *)
  | extract_basic_xf _ = (NONE, NONE)
(*  | extract_basic_xf t = raise TERM ("extract_basic_xf", [t]) *)

(* Not used at the moment *)

fun nothrows (Const ("Language.com.Skip", _)) = true
  | nothrows (Const ("Language.com.Basic", _) $ _) = true
  | nothrows (Const ("Language.com.Spec", _) $ _) = true
  | nothrows (Const ("Language.com.Seq", _) $ a $ b) =
    nothrows a andalso nothrows b
  | nothrows (Const ("Language.com.Cond", _) $ _ $ a $ b) =
    nothrows a andalso nothrows b
  | nothrows (Const ("Language.com.While", _) $ _ $ a) =  nothrows a
  | nothrows (Const ("Language.com.Call", _) $ _) =  true
  | nothrows (Const ("Language.com.DynCom", _) $ (Abs (_, _, c))) = nothrows c
  | nothrows (Const ("Language.com.Guard", _) $ _ $ _ $ b) = nothrows b
  | nothrows (Const ("Language.com.Throw", _)) = false
  | nothrows (Const ("Language.com.Catch", _) $ a $ b) =
    nothrows a orelse nothrows b
  | nothrows (Const ("Language.call", _) $ _ $ _ $ _ $ (Abs (_, _, (Abs (_, _, c)))))
    = nothrows c
  | nothrows _ = false (* who knows *)

fun extract_iscall c =
    let
        fun f (Const ("Language.call", _)) = true
          | f _ = false
    in
        f (head_of c)
    end;

fun ceqv_thms ctxt = Proof_Context.get_thms ctxt "ceqv_rules";
fun xpres_thms ctxt = Proof_Context.get_thms ctxt "xpres_rules";

fun my_thm ctxt name = Proof_Context.get_thm ctxt name
fun my_thms ctxt name = Proof_Context.get_thm ctxt name

fun my_simp_tac trace depth ctxt n =
    prim_trace_tac' (#trace_simp trace) depth "my_simp_tac" ctxt (SOLVE' (asm_full_simp_tac ctxt)) n

fun xpres_tac trace depth ctxt n = let
    fun rest_tac n = (resolve_tac ctxt @{thms "match_xpres"} n)
                         THEN_ELSE
                         (xpres_tac trace (depth + 1) ctxt n, my_simp_tac trace (depth + 1) ctxt n)
in
    prim_trace_tac' (#trace_xpres trace) depth "XP" ctxt ((fn n => DETERM (resolve_tac ctxt (xpres_thms ctxt) n)) THEN_ALL_NEW rest_tac) n
end;

fun FOCUS_PREMS_ctxt tac = Subgoal.FOCUS_PREMS (fn focus => tac (#context focus) (#prems focus))

fun corres_ceqv_tac trace depth ctxt n = let
    val depth' = depth + 1

    (* This ugliness is so we can do this very quickly --- the
    simplifier was just taking too long. It seems that the refl rule
    produces multiple results, hence the DETERM *)
    fun tac ctxt [p] = (rewrite_goals_tac ctxt [p RS @{thm "eq_reflection"}])
                      THEN ((DETERM (resolve_tac ctxt [refl] 1)))
      | tac _    _   = let val _ = tracing "WARNING: ceqv non-singleton case" in no_tac end;
    val my_eq_tac = prim_trace_tac' (#trace_ceqv trace) depth' "CEQV xfI" ctxt (FOCUS_PREMS_ctxt tac ctxt)

    (* This ugliness makes back-tracking more efficient, I hope *)
    val rest_tac = FIRST_COMMIT' [(resolve_tac ctxt @{thms "match_ceqv"}, corres_ceqv_tac trace depth' ctxt),
                                  (resolve_tac ctxt @{thms "match_xpres"}, xpres_tac trace depth' ctxt),
                                  (resolve_tac ctxt @{thms "rewrite_xfI"}, my_eq_tac),
                                  (fn _ => all_tac, my_simp_tac trace depth' ctxt)]
in
    prim_trace_tac' (#trace_this trace) depth "CEQV" ctxt (resolve_tac ctxt (ceqv_thms ctxt) THEN_ALL_NEW rest_tac) n
end;

fun corres_solve_ceqv_old (trace : trace_opts) (depth : int) ctxt =
    EVERY' [REPEAT_DETERM' (Rule_Insts.thin_tac ctxt "_" []),
            SOLVE' (corres_ceqv_tac trace depth ctxt)]

val ceqv_xpres_ceqvI = @{thm ceqv_xpres_ceqvD};
val ceqv_xpres_rules = @{thms ceqv_xpres_rules};
val ceqv_xpres_FalseI = @{thm ceqv_xpres_FalseI};
val ceqv_xpres_rewrite_basic_left_cong = @{thm ceqv_xpres_rewrite_basic_left_cong};
val ceqv_xpres_rewrite_basic_refl = @{thm ceqv_xpres_rewrite_basic_refl};
val ceqv_xpres_basic_preserves_TrueI = @{thm ceqv_xpres_basic_preserves_TrueI};
val ceqv_xpres_basic_preserves_FalseI = @{thm ceqv_xpres_basic_preserves_FalseI};
val ceqv_xpres_lvar_nondet_init_TrueI = @{thm ceqv_xpres_lvar_nondet_init_TrueI};
val ceqv_xpres_lvar_nondet_init_FalseI = @{thm ceqv_xpres_lvar_nondet_init_FalseI};
val ceqv_xpres_rewrite_set_rules = @{thms ceqv_xpres_rewrite_set_rules};
val xpres_eq_If_rules = @{thms xpres_eq_If_rules};

val cinit_lift_thms = (@{thm ccorres_save_pre_UNIV_Int}
                       , @{thm ccorres_save_pre_lift1}
                       , @{thm ccorres_save_pre_lift1_save_global}
                       , @{thm ccorres_save_pre_init_lift2})

val clift_thms = (@{thm ccorres_introduce_UNIV_Int_when_needed}
                  , @{thm ccorres_tmp_lift1}
                  , @{thm ccorres_tmp_lift1_global}
                  , @{thm ccorres_tmp_lift2})

val apply_ceqv_xpres_rules_trace = ref @{term True};

fun apply_ceqv_xpres_rules1 ctxt rules _ n = DETERM
  (resolve_tac ctxt rules n
     ORELSE (SUBGOAL (fn (t, n) =>
          (warning ("apply_ceqv_xpres_rules: no rule applied"
                     ^ " - see CtacImpl.apply_ceqv_xpres_rules_trace");
             apply_ceqv_xpres_rules_trace := t;
             resolve_tac ctxt [ceqv_xpres_FalseI] n)) n));

fun apply_ceqv_xpres_rules ctxt = let
    val seq = ceqv_simpl_seq ctxt
    val ex_rules = if seq then [@{thm ceqv_xpres_While_simpl_sequence}]
        else []
  in apply_ceqv_xpres_rules1 ctxt (ex_rules @ ceqv_xpres_rules) end

fun addcongs thms ss = foldl (uncurry Simplifier.add_cong) ss thms
fun delsplits thms ss = foldl (uncurry Splitter.del_split) ss thms

fun solve_ceqv_xpres_rewrite_basic ctxt n = DETERM
  (safe_simp_tac (addcongs [ceqv_xpres_rewrite_basic_left_cong] (put_simpset HOL_basic_ss ctxt)) n
      THEN resolve_tac ctxt [ceqv_xpres_rewrite_basic_refl] n);

fun solve_ceqv_xpres_basic_preserves ctxt (t, n) = let
    val true_tac = resolve_tac ctxt [ceqv_xpres_basic_preserves_TrueI] n
                   THEN SOLVE' (clarsimp_tac ctxt) n
    fun false_tac st = let
        val t_concl = Envir.beta_eta_contract (Logic.strip_assums_concl t)
        val (context, xf) = case t_concl of
            @{term_pat "Trueprop (ceqv_xpres_basic_preserves ?context ?xf _ _ _ _)"} => (context, xf)
          | _ => (@{term unknown}, @{term unknown})
        val _ = tracing ("failed to show preservation for variable: " ^ Syntax.string_of_term ctxt xf
                         ^ "\nin context: " ^ Syntax.string_of_term ctxt context)
      in resolve_tac ctxt [ceqv_xpres_basic_preserves_FalseI] n st end
  in DETERM (true_tac ORELSE false_tac) end;

fun ceqv_xpres_call_tac ctxt (t, n) = let
    val t_concl = Envir.beta_eta_contract (Logic.strip_assums_concl t);
    fun f_name () = case t_concl of
        @{term Trueprop} $ (@{term_pat "ceqv_xpres_call _ _ _"} $ Const p $ _ $ _ $ _ $ _ $ _ $ _ $ _ $ _) => fst p
      | _ => raise TERM ("unexpected conclusion", [t_concl]);
    fun modifies_thm () = f_name ()
        |> Long_Name.base_name
        |> unsuffix Hoare.proc_deco
        |> suffix "_modifies"
        |> my_thm ctxt
        |> Local_Defs.unfold ctxt @{thms mex_def meq_def};
    fun ceqv_xpres_call_modifies () =
        resolve_tac ctxt [modifies_thm ()] 1 @{thm ceq_xpres_call_hoarep} |> Seq.hd;
    fun ceqv_xpres_call_default s =
        (warning ("ceqv_xpres_call_tac: " ^ s); @{thm ceqv_xpres_call});
    (* FIXME: does something like this already exist? *)
    fun string_of_terms ts =
        if null ts then "" else (List.foldl (fn (t,s) => s ^ Syntax.string_of_term ctxt t ^ "\n") ":\n" ts)
    val ceqv_xpres_callI = ceqv_xpres_call_modifies ()
        handle ERROR s => ceqv_xpres_call_default s
        handle TERM (s, t) => ceqv_xpres_call_default (s ^ string_of_terms t)
        handle Option => ceqv_xpres_call_default "ceqv_xpres_call_modifies";
  in resolve_tac ctxt [ceqv_xpres_callI] n end;

fun solve_ceqv_xpres_lvar ctxt n = DETERM
  ((resolve_tac ctxt [ceqv_xpres_lvar_nondet_init_TrueI] n
       THEN SOLVE' (safe_simp_tac ctxt) n)
     ORELSE resolve_tac ctxt [ceqv_xpres_lvar_nondet_init_FalseI] n);

fun abstract_upds ctxt t = let
    val sT = domain_type (fastype_of t)
    fun inner (upd $ _ $ t) = upd :: inner t
      | inner (Bound 0) = []
      | inner t = raise TERM ("strip_upds", [t])
    val upds = inner (betapply (t, Bound 0)) |> List.rev
    val xs = map (dest_Const #> snd #> domain_type
            #> curry (op -->) sT #> pair "x") upds
        |> Variable.variant_names ctxt |> map Free
    val upd = Abs ("s", sT, fold (fn (u, x) => fn s => u $ (x $ Bound 0) $ s)
        (upds ~~ xs) (Bound 0))
  in (upd, xs) end

fun ceqv_restore_args_tac ctxt = SUBGOAL (fn (t, n) => case
        Envir.beta_eta_contract (Logic.strip_assums_concl t)
    of @{term Trueprop}
        $ (Const (@{const_name ceqv_xpres_call_restore_args}, _) $ i $ f $ _)
      => let
      val cnames = Term.add_const_names f []
      val (f, xs) = abstract_upds ctxt f
      val sT = domain_type (fastype_of f)

      val proc = dest_Const i |> fst |> Long_Name.base_name
      val pinfo = Hoare.get_data ctxt |> #proc_info
      val params = Symtab.lookup pinfo proc |> the |> #params
          |> filter (fn (v, _, _) => v = HoarePackage.In)
      val new_upds = map (#2 #> suffix Record.updateN #> Syntax.read_term ctxt
              #> dest_Const #> fst) params
          |> filter_out (member (op =) cnames)

      fun add_upd upd f = let
        val updC = Syntax.parse_term ctxt upd
        val accC = Syntax.parse_term ctxt (unsuffix Record.updateN upd)
      in Abs ("s", sT, updC $ Abs ("x", dummyT, accC $ Bound 1)
            $ (f $ Bound 0)) end
      val g = fold add_upd new_upds f |> Syntax.check_term ctxt |> Thm.cterm_of ctxt
      val thm = infer_instantiate ctxt [(("f",0), Thm.cterm_of ctxt f),
              (("g",0), g)]
          @{thm ceqv_xpres_call_restore_argsI}
          |> Drule.generalize (Names.empty, Names.make_set (map (dest_Free #> fst) xs))
    in resolve_tac ctxt [thm] n THEN simp_tac ctxt n end
  | _ => raise TERM("ceqv_restore_args_tac", [t]))

fun xpres_abnormal_tac ctxt =
    resolve_tac ctxt @{thms xpres_abnormal_rules}
    ORELSE' resolve_tac ctxt @{thms xpres_abnormal_trivial}

fun ceqv2_consts_and_tacs ctxt = map (apfst (fst o dest_Const)) [
  (@{term ceqv_xpres}, apply_ceqv_xpres_rules ctxt),
  (@{term ceqv_xpres_rewrite_basic}, solve_ceqv_xpres_rewrite_basic),
  (@{term ceqv_xpres_rewrite_set}, K (resolve_tac ctxt ceqv_xpres_rewrite_set_rules)),
  (@{term ceqv_xpres_basic_preserves}, SUBGOAL o solve_ceqv_xpres_basic_preserves),
  (@{term ceqv_xpres_lvar_nondet_init}, solve_ceqv_xpres_lvar),
  (@{term ceqv_xpres_call_restore_args}, ceqv_restore_args_tac),
  (@{term ceqv_xpres_call}, SUBGOAL o ceqv_xpres_call_tac),
  (@{term xpres_eq_If}, K (resolve_tac ctxt xpres_eq_If_rules)),
  (@{term xpres_abnormal}, K (xpres_abnormal_tac ctxt))
];

fun ceqv2_all_tacs ctxt = SUBGOAL (fn (t, n) =>
  case head_of (HOLogic.dest_Trueprop (Logic.strip_assums_concl t)) of
    Const (s, T) => (case (filter (fn v => fst v = s) (ceqv2_consts_and_tacs ctxt)) of
        (v :: _) => (snd v) ctxt n
      | [] => raise TERM ("ceqv2_all_tacs: unknown head const " ^ s, [Const (s, T), t]))
  | _ => raise TERM ("ceqv2_all_tacs: unknown form", [t]));

fun ceqv2_tac ctxt n = let
in
  resolve_tac ctxt [ceqv_xpres_ceqvI] n THEN
    SELECT_GOAL (REPEAT_DETERM (eresolve_tac ctxt [thin_rl] 1)
       THEN REPEAT_DETERM (ceqv2_all_tacs ctxt 1)) n
end;

fun corres_solve_ceqv (_ (*trace*) : trace_opts) (_ (*depth*) : int) = ceqv2_tac;

fun rename_fresh_tac nm i thm = let
    (* FIXME: proper name context handling *)
    val frees = Name.make_context (Term.add_free_names (Thm.prop_of thm) [])
in
    rename_tac [#1 (Name.variant nm frees)] i thm
end;

fun corres_pre_lift_tac lift_thms trace depth ctxt xf =
  prim_trace_tac' (#trace_this trace) depth ("PRE_LIFT_TAC " ^ xf) ctxt
  let val (univ_thm, lift1_local_thm, lift1_global_thm, lift2_thm) = lift_thms
      val base_xf = Long_Name.base_name xf;
      val var_name = (unsuffix "_'" base_xf handle Fail _ => "rv");
      fun inst lift xf = Rule_Insts.res_inst_tac ctxt [((("xf'", 0), Position.none), xf)] [] lift;
  in EVERY' [TRY o resolve_tac ctxt [univ_thm],
             inst lift1_local_thm xf ORELSE' inst lift1_global_thm xf,
             rename_fresh_tac var_name,
             resolve_tac ctxt [lift2_thm],
             corres_solve_ceqv trace depth ctxt]
  end;

fun extract_lhs_xf (ct as (Const ("Language.com.Basic", _) $ _)) = extract_basic_xf ct
  | extract_lhs_xf (Const ("Language.call", _) $ _ $ _ $ _ $ (Abs (_, _, (Abs (_, _, c)))))
    = extract_basic_xf c
  | extract_lhs_xf _ = (NONE, NONE) (* raise TERM ("extract_lhs_xf", [t]) *)

fun Call_name (Const ("Language.com.Call", _) $ (Const (name, _))) = name
  | Call_name t = raise TERM ("Call_name", [t])

(* eta bites us here *)
fun isBindE t =
    case head_of t of
        (Const ("NonDetMonad.bindE", _)) => true
      | (Abs (_, _, c))                  => isBindE c
      | _                                => false

fun is_call t =
    case head_of t of
        (Const ("Language.call", _)) => true
      | _                            => false

fun extract_Seq (Const ("Language.com.Seq", _) $ a $ b) = (a, b)
  | extract_Seq t = raise TERM ("extract_Seq", [t])

val concl_dest_ccorres = dest_ccorres o HOLogic.dest_Trueprop o Logic.strip_assums_concl
val first_prem_dest_ccorres = dest_ccorres o HOLogic.dest_Trueprop o hd o Thm.prems_of

fun xf_of_thm_prem corr = let
    (* Extract the name of the extraction function.
     * The xf can be either a variable or a liftxf *)
    val major_cc = first_prem_dest_ccorres corr
    val xf_name  = case (#xf major_cc) of
                       Var ((x, _), _) => x
                     | _ $ Var ((x, _), _) => x
                     | _ => raise TERM ("Expecting an extraction function", [#xf major_cc])
in
    xf_name
end;

val guard_is_UNIVI  = @{thms "guard_is_UNIVI"}

fun ccorres_cleanup_rest (trace : trace_opts)
                         (depth : int)
                         (ctxt : Proof.context)
                         (n : int) = let
    val match_ceqv      = Proof_Context.get_thms ctxt "match_ceqv"
    val my_clarsimp_tac = prim_trace_tac' (#trace_this trace) depth "my_clarsimp_tac" ctxt (SOLVE' (clarsimp_tac ctxt))
in
    (FIRST_COMMIT' [(resolve_tac ctxt match_ceqv, corres_solve_ceqv trace depth ctxt),
                    (resolve_tac ctxt guard_is_UNIVI, fn _ => all_tac), (* maybe we should try simp? *)
                    (fn _ => all_tac, my_clarsimp_tac)]) n
end;


fun ccorres_norename_cleanup (trace : trace_opts)
                             (depth : int)
                             (ctxt : Proof.context)
                             (n : int) = let
    val match_cc        = Proof_Context.get_thms ctxt "match_ccorres"
in
    prim_trace_tac (#trace_this trace) depth "CLEANUP (no rename)" ctxt
                   (resolve_tac ctxt match_cc n
                    THEN_ELSE (all_tac, ccorres_cleanup_rest trace (depth + 1) ctxt n))
end;

fun ccorres_rename_cleanup trace depth xf ctxt n = let
    val match_cc  = Proof_Context.get_thms ctxt "match_ccorres"

    val base_xf   = Long_Name.base_name xf
    val var_name  = (unsuffix "_'" base_xf handle Fail _ => base_xf)
in
    prim_trace_tac (#trace_this trace) depth "CLEANUP" ctxt
                   (resolve_tac ctxt match_cc n
                    THEN_ELSE (rename_fresh_tac var_name n,
                               ccorres_cleanup_rest trace (depth + 1) ctxt n))
end;

fun abstract_record_xf_if_required trace depth ctxt xf o_xfr = let
    (* Used to abstract out record variables *)
    val abstract_thm   = Proof_Context.get_thm ctxt "ccorres_abstract"
in
    case o_xfr of
        SOME (_, true) => prim_trace_tac' (#trace_this trace) depth "ccorres_abstract" ctxt
                                          (Rule_Insts.res_inst_tac ctxt [((("xf'", 0), Position.none), xf)] [] abstract_thm
                                           THEN_ALL_NEW ccorres_rename_cleanup trace (depth + 1) xf ctxt)
      | _              => fn _ => all_tac
end;

(* Returns (is concrete, xf, o_xfr) where xf and o_xfr have been sanitised to remove globals *)
fun normalise_xf (o_xf, o_xfru) =
    case o_xf of
        NONE                     => (false, xfdc, NONE)
      | SOME (xf_tp as (xf, _)) => if (Long_Name.base_name xf) = "globals" then (false, xfdc, NONE) else (true, xf_tp, o_xfru)

(* Options *)

type ctac_opts = {
     trace : trace_opts,          (* debug or not *)
     use_simp : bool,             (* use simplifier or not *)
     vcg_suffix : string,         (* suffix for vcg rule --- "" for use vcg, "_novcg" otherwise *)
     c_lines : int                (* Number of lines of C to use (# times ccorres_rhs_assoc2 + 1) *)
}

val default_ctac_opts : ctac_opts = { trace = default_trace_opts, use_simp = true, vcg_suffix = "", c_lines = 1 }

fun ctac_opts_trace_update new_trace {trace, use_simp, vcg_suffix, c_lines} =
    {trace = new_trace trace, use_simp = use_simp, vcg_suffix = vcg_suffix, c_lines = c_lines}

fun ctac_opts_simp_update new_use_simp {trace, use_simp, vcg_suffix, c_lines} =
    {trace = trace, use_simp = new_use_simp use_simp, vcg_suffix = vcg_suffix, c_lines = c_lines}

fun ctac_opts_vcg_update new_vcg_suffix {trace, use_simp, vcg_suffix, c_lines} =
    {trace = trace, use_simp = use_simp, vcg_suffix = new_vcg_suffix vcg_suffix, c_lines = c_lines}

fun ctac_opts_c_lines_update new_c_lines {trace, use_simp, vcg_suffix, c_lines} =
    {trace = trace, use_simp = use_simp, vcg_suffix = vcg_suffix, c_lines = new_c_lines c_lines}

type csymbr_opts = {
     trace : trace_opts          (* debug or not *)
}

val default_csymbr_opts : csymbr_opts = { trace = default_trace_opts }

fun csymbr_opts_trace_update new_trace {trace} = {trace = new_trace trace}

type ceqv_opts = {
     trace : trace_opts          (* debug or not *)
}

val default_ceqv_opts : ceqv_opts = { trace = default_trace_opts }

fun ceqv_opts_trace_update new_trace {trace} = {trace = new_trace trace}

(* These are the filters used to determine which assumptions we substitute *)
fun substp_is_var_eq (Const ("op =", _) $ Var (_, _) $ _) = true
  | substp_is_var_eq _ = false

fun substp_is_eq (Const ("op =", _) $ _ $ _) = true
  | substp_is_eq _ = false

fun substp_never _ = false

type cinit_opts = {
     subst_asms : term -> bool,  (* subst assumptions or not *)
     ignore_call : bool,         (* use call_ignore_cong or not *)
     ccorres_rewrite : bool,     (* perform ccorres_rewrite or not *)
     trace : trace_opts          (* debug or not *)
}

val default_cinit_opts : cinit_opts =
    {trace = default_trace_opts, subst_asms = substp_is_eq, ccorres_rewrite = true, ignore_call = true}

fun cinit_opts_subst_update new_subst_asms {subst_asms, ignore_call, ccorres_rewrite, trace} =
    {subst_asms = new_subst_asms subst_asms, ignore_call = ignore_call, ccorres_rewrite = ccorres_rewrite, trace = trace}

fun cinit_opts_call_update new_ignore_call {subst_asms, ignore_call, ccorres_rewrite, trace} =
    {subst_asms = subst_asms, ignore_call = new_ignore_call ignore_call, ccorres_rewrite = ccorres_rewrite, trace = trace}

fun cinit_opts_ccorres_rewrite_update new_ccorres_rewrite {subst_asms, ignore_call, ccorres_rewrite, trace} =
    {subst_asms = subst_asms, ignore_call = ignore_call, ccorres_rewrite = new_ccorres_rewrite ccorres_rewrite, trace = trace}

fun cinit_opts_trace_update new_trace {subst_asms, ignore_call, ccorres_rewrite, trace} =
    {subst_asms = subst_asms, ignore_call = ignore_call, ccorres_rewrite = ccorres_rewrite, trace = new_trace trace}

fun ccorres_doit (opts : ctac_opts)
                 (depth : int)
                 (ctxt : Proof.context)
                 (lhs : term)
                 (record_splits : thm list)
                 (call_splits : thm list)
                 (non_call_splits : thm list) : int -> tactic =
    let
        val trace     = #trace opts
        val depth'    = depth + 1

        (* Theorems *)
        val skips     = Proof_Context.get_thms ctxt "ctac_skips"
        val splits    = call_splits @ non_call_splits

        val thms      = ctac_rules.get (Context.Proof ctxt);

        (* xf stuff *)
        val (xf_is_concrete, (xf, _), o_xfru) = normalise_xf (extract_lhs_xf lhs)

        val _ = if isSome o_xfru andalso not xf_is_concrete
                then raise TACTIC ("BUG: not xf_is_concrete && isSome o_xfru")
                else ()

        val xfN   = "xf'"
        val xfrN  = "xfr"
        val xfruN  = "xfru"

        (* We try to instantiate the xf if possible:

         * - if we are doing a call, we always need an xf.  If the one
         *   we detected was globals (or we didn't detect one), we
         *   use xfdc --- this means that ceqv_xfdc will fire as well

         * - if we are looking at a record, we need to instantiate the
         *   lot.  If we detected globals, then we treat it as a non-record case.

         * - otherwise we instantiate the xf if it was a concrete value.
         *)
        val split_tac = case o_xfru of
                            SOME ((xfru, _), _) => let
                                val insts = [(((xfN, 0), Position.none), xf),
                                             (((xfrN, 0), Position.none), xfu_to_xf xfru),
                                             (((xfruN, 0), Position.none), xfru)]
                            in
                                prim_trace_tac' (#trace_this trace) depth "SPLIT (record)" ctxt
                                                (FIRST' (map (Rule_Insts.res_inst_tac ctxt insts []) record_splits))
                            end
                          | NONE => if xf_is_concrete orelse is_call lhs
                                    then
                                        prim_trace_tac' (#trace_this trace) depth "SPLIT (concrete/call)" ctxt
                                                        (FIRST' (map (Rule_Insts.res_inst_tac ctxt [(((xfN, 0), Position.none), xf)] []) splits))
                                    else
                                        prim_trace_tac' (#trace_this trace) depth "SPLIT (other)" ctxt
                                                        (resolve_tac ctxt non_call_splits)

        val cctac_simp = if (#use_simp opts) then my_simp_tac trace (depth' + 1) ctxt else (fn _ => all_tac);

        val cctac   = prim_trace_tac' (#trace_this trace) depth' "CCTAC" ctxt
                                      ((resolve_tac ctxt thms) THEN_ALL_NEW cctac_simp)

        (* solve the remaining subgoals *)
        val resttac = (resolve_tac ctxt skips) (* Ignore any valids etc. *)
                          ORELSE'
                          ccorres_rename_cleanup trace depth' xf ctxt
    in
        (abstract_record_xf_if_required trace depth ctxt xf o_xfru)
            THEN'
            (split_tac THEN_ALL_NEW_DIST_FIRST (cctac, resttac))
    end;

fun corres_split_tac opts ctxt =
    SUBGOAL (fn (prem, i) =>
                let
                    val trace          = #trace opts
                    val cc             = concl_dest_ccorres prem;
                    val (lhs, _)     = extract_Seq (#conc cc)
                    val vcg_suffix     = #vcg_suffix opts
                    val record_splits     = Proof_Context.get_thms ctxt ("ctac_splits_record" ^ vcg_suffix)
                    val call_splits       = Proof_Context.get_thms ctxt ("ctac_splits_call" ^ vcg_suffix)
                    val non_call_splits   = Proof_Context.get_thms ctxt ("ctac_splits_non_call" ^ vcg_suffix)

                in
                    prim_trace_tac' (#trace_this trace) 0 "SPLIT" ctxt
                                    (ccorres_doit opts 1 ctxt lhs record_splits call_splits non_call_splits) i
                end);

(* We ignore vcg options here *)
fun corres_nosplit_tac opts ctxt =
    SUBGOAL (fn (prem, i) =>
                let
                    val trace          = #trace opts
                    val cc             = concl_dest_ccorres prem;
                    val lhs            = #conc cc
                    val record_splits     = Proof_Context.get_thms ctxt "ctac_nosplit_record"
                    val call_splits       = Proof_Context.get_thms ctxt "ctac_nosplit_call"
                    val non_call_splits   = Proof_Context.get_thms ctxt "ctac_nosplit_non_call"
                in
                    prim_trace_tac' (#trace_this trace) 0 "NOSPLIT" ctxt
                                    (ccorres_doit opts 1 ctxt lhs record_splits call_splits non_call_splits) i
                end);

fun corres_ctac opts ctxt n = let
  val ctxt = Context_Position.set_visible false ctxt
  val match_seq = Proof_Context.get_thms ctxt "match_ccorres_Seq";
  val rhs_assoc2 = Proof_Context.get_thms ctxt "ccorres_rhs_assoc2";
  val ctac_pre_rules = ctac_pre.get (Context.Proof ctxt);
  val ctac_post_rules = ctac_post.get (Context.Proof ctxt);
in
    (* Apply as many pre rules as possible *)
    (REPEAT_DETERM (resolve_tac ctxt ctac_pre_rules n))
        THEN (REPEAT_DETERM_N (#c_lines opts - 1) (resolve_tac ctxt rhs_assoc2 n))
        THEN
        (resolve_tac ctxt match_seq n
         THEN_ELSE (corres_split_tac opts ctxt n,
                    corres_nosplit_tac opts ctxt n))
        THEN REPEAT_DETERM (resolve_tac ctxt ctac_post_rules n)
end;


(* We get multiple unifiers because of the P in ccorres_lift_rhs,
 * so we need to pick any that matches.  Unfortunately, only one of these
 * is type correct, so we can't just use unification, as we then get an
 * exception :( *)

fun instantiate_xf_type ctxt tp which thms = let
    val ctp = Thm.ctyp_of ctxt tp
    fun inst_type_vars thm = let
        val (Const ("Pure.all", _) $ Abs (_, tpv, _)) = nth (Thm.prems_of thm) which
    in
        Thm.instantiate (TVars.make [(dest_TVar tpv, ctp)], Vars.empty) thm
    end;
in
    map inst_type_vars thms
end handle Bind => raise TACTIC ("Exception Bind in instantiate_xf_type: check order of assumptions to rhss lemmas in Corres_C and function corres_symb_rhs_tac");

fun corres_symb_rhs_exec_tac (trace : trace_opts)
                             (depth : int)
                             (ctxt : Proof.context)
                             (lhs : term)
                             (insts : ((indexname * Position.T) * string) list)
                             (lift_rhss : thm list)
                             (xf : string)
                             (n : int) (* Ugh. This makes the function sufficiently lazy *)
                             (t : thm) : thm Seq.seq = let
    val depth'     = depth + 1

    val proc_name  = (Long_Name.base_name o unsuffix "_'proc" o call_name) lhs

    (* You would think this exists in hoare_package.  I can't find it ... *)
    val proc_spec  = Proof_Context.get_thm ctxt (suffix "_spec" proc_name)
    val proc_mod   = Proof_Context.get_thm ctxt (suffix "_modifies" proc_name)

    val spec_rules = [proc_spec] RLN (3, lift_rhss)
    val rule       = case ([proc_mod] RLN (3, spec_rules)) of
                         [rule] => rule
                       | [] => raise THM ("corres_symb_rhs_exec_tac: No unifiers for " ^ proc_name,
                                             3, [proc_spec, proc_mod] @ [@{thm TrueI}] @ spec_rules @ [@{thm TrueI}] @ lift_rhss)
                       | xs  => raise THM ("corres_symb_rhs_exec_tac: Multiple unifiers for " ^ proc_name,
                                             3, [proc_spec, proc_mod] @ [@{thm TrueI}] @ spec_rules @ [@{thm TrueI}] @ lift_rhss
                                                 @[@{thm TrueI}] @ xs)
in
    prim_trace_tac' (#trace_this trace) depth ("CSYMBR (" ^ proc_name ^ ")") ctxt
                    (Rule_Insts.res_inst_tac ctxt insts [] rule
                     THEN_ALL_NEW ccorres_rename_cleanup trace depth' xf ctxt) n t
end; (* handle TERM  e => no_tac
            | ERROR e => no_tac *)

fun corres_trim_lvar_nondet_init_tac trace depth ctxt known_guard = let
    val match_seq = Proof_Context.get_thms ctxt "match_ccorres_Seq";

    fun tac (_, i) = let
              val remove_lvar_init = Proof_Context.get_thm ctxt
                                                    (if known_guard
                                                     then "ccorres_lift_rhs_remove_lvar_init"
                                                     else "ccorres_lift_rhs_remove_lvar_init_unknown_guard")
    in
              prim_trace_tac' (#trace_this trace) depth "LVAR_INIT" ctxt
                                          (resolve_tac ctxt [remove_lvar_init]
                                           THEN_ALL_NEW (ccorres_norename_cleanup trace depth ctxt)) i
    end;
in
    resolve_tac ctxt match_seq THEN' SUBGOAL tac
end;

fun corres_symb_rhs_tac (opts : ceqv_opts) ctxt =
let
    val ctxt      = Context_Position.set_visible false ctxt
    val trace     = #trace opts
    val depth     = 0
    val depth'    = depth + 1

    val match_seq = Proof_Context.get_thms ctxt "match_ccorres_Seq";
    fun tac (prem, i) = let
        (* Theorems *)
        val gen_asm    = Proof_Context.get_thms ctxt "ccorres_gen_asm2"
        (* Only simplify the rhs of the intersection in the concrete guard *)
        val cc_cong    = Proof_Context.get_thms ctxt "ccorres_special_Int_cong"
        (* Used to discriminate between call and Basic *)
        val match_call_Seq = Proof_Context.get_thms ctxt "match_ccorres_call_Seq"

        (* xf and friends *)
        val cc         = concl_dest_ccorres prem;
        val (lhs, _) = extract_Seq (#conc cc)
        val (_, (xf, tp), o_xfru) = normalise_xf (extract_lhs_xf lhs)

        val xfN   = "xf'" (* _should_ be OK here *)
        val xfrN  = "xfr"
        val xfruN  = "xfru"

        val inst_xf_tp   = instantiate_xf_type ctxt tp 1 (* xfxfr *)

        (* If we are in a record, return the appropriate thm names and the instantiation for xfr,
         * otherwise return those for the non-record case *)
        val (xfr_inst, inst_tp, record_suffix, new_xf_name)
          = case o_xfru of
                NONE   => ([],
                           inst_xf_tp,
                           "",
                           xf)
              | SOME ((xfru, tpru), _) => ([(((xfrN, 0), Position.none), xfu_to_xf xfru), (((xfruN, 0), Position.none), xfru)],
                                           inst_xf_tp o instantiate_xf_type ctxt (domain_type (domain_type tpru)) 4, (* xfrxfru *)
                                           "_record",
                                           xfu_to_xf xfru)

        val xf_inst   = [(((xfN, 0), Position.none), xf)]

        val ss        = addcongs cc_cong ctxt |> delsplits @{thms if_splits}

        val basic_thm = Proof_Context.get_thm ctxt ("ccorres_lift_rhs_Basic" ^ record_suffix)
        (* The Basic_record lemmas don't seem to require xfr and xfru to be instantiated *)
        val basic_tac =
            prim_trace_tac' (#trace_this trace) depth "CSYMBR (Basic)" ctxt
                            (Rule_Insts.res_inst_tac ctxt xf_inst [] basic_thm
                             THEN_ALL_NEW (ccorres_norename_cleanup trace depth' ctxt))

        val call_thms' = Proof_Context.get_thms ctxt ("ccorres_lift_rhss" ^ record_suffix)
        val call_thms = inst_tp call_thms'
        val _ = forall (fn (t, t') => Thm.concl_of t <> Thm.concl_of t') (call_thms ~~ call_thms')
            orelse raise THM ("corres_symb_rhs_tac: failed to inst_tp", 1, call_thms @ call_thms')
        val call_tac  = EVERY' [corres_symb_rhs_exec_tac trace depth ctxt lhs (xf_inst @ xfr_inst) call_thms new_xf_name,
                                (* Yes, simp should ignore assumptions -- this simplifies away the state dep. on i *)
                                    TRY' (simp_tac ss),
                                TRY' (resolve_tac ctxt gen_asm)]
    in
        (abstract_record_xf_if_required trace depth ctxt xf o_xfru i)
            THEN
            (*            prim_trace_tac trace_ctac "POST abstract:\n" ctxt *)
            ((resolve_tac ctxt match_call_Seq i) THEN_ELSE (call_tac i, basic_tac i))
    end;
in
    (resolve_tac ctxt match_seq THEN' SUBGOAL tac) ORELSE' (corres_trim_lvar_nondet_init_tac trace depth ctxt false)
end;

fun substutite_asm_eqs ctxt f = let
    val concl = HOLogic.dest_Trueprop o Thm.concl_of

    fun mk_meta_eq p = p RS @{thm "eq_reflection"}

    fun tac ctxt ps = rewrite_goals_tac ctxt (map mk_meta_eq (filter (f o concl) ps))
in
    FOCUS_PREMS_ctxt tac ctxt
end;

(* tactical which solves the current subgoal and all subsequent subgoals using the same tac --- like
   REPEAT_ALL_NEW but without the TRY *)
fun MY_REPEAT_ALL_NEW tac =
  tac THEN_ALL_NEW (fn i => MY_REPEAT_ALL_NEW tac i);

fun corres_pre_lift_tacs ctxt lift_thms pre_tac post_tac trace depth xfs =
    EVERY' (pre_tac :: rev (post_tac :: map (corres_pre_lift_tac lift_thms trace depth ctxt) xfs))

fun corres_pre_lift_tac_cinit ctxt =
    corres_pre_lift_tacs ctxt cinit_lift_thms
                         (resolve_tac ctxt [@{thm ccorres_save_pre_start}])
                         (REPEAT_ALL_NEW (resolve_tac ctxt @{thms ccorres_save_pre_finish}))

fun corres_boilerplate_tac opts unfold_haskell_p xfs ctxt = let
    val ctxt = Context_Position.set_visible false ctxt
    val trace = #trace opts
    val depth = 0
    val depth' = depth + 1

    fun tac (prem, i) = let
        (* xf and friends *)
        val cc         = concl_dest_ccorres prem;
        val conc_proc_name = (Long_Name.base_name o unsuffix "_'proc" o Call_name) (#conc cc)

        (* theorems *)
        val Call_thm = Proof_Context.get_thms ctxt "ccorres_Call"
        val boilerplace_simp_dels = Proof_Context.get_thms ctxt "ccorres_boilerplace_simp_dels"
        val ccorres_rhs_assoc = Proof_Context.get_thms ctxt "ccorres_rhs_assoc"
        val ccorres_guard_imp2 = Proof_Context.get_thms ctxt "ccorres_guard_imp2"
        val call_ignore_cong = @{thms "call_ignore_cong"}

        val ccorres_trim_redundant_throw = Proof_Context.get_thms ctxt "ccorres_trim_redundant_throw"
        val trim_redundant_throw_tac = resolve_tac ctxt ccorres_trim_redundant_throw
                                       THEN_ALL_NEW ccorres_norename_cleanup trace depth' ctxt

        val ccorres_trim_DontReach = Proof_Context.get_thms ctxt "ccorres_special_trim_guard_DontReach_pis"
        val pis_thms = Proof_Context.get_thms ctxt "push_in_stmt_rules"
        val trim_DontReach_tac = resolve_tac ctxt ccorres_trim_DontReach
                                 THEN' (SOLVE' (MY_REPEAT_ALL_NEW (resolve_tac ctxt pis_thms)))

        val conc_impl = Proof_Context.get_thm ctxt (conc_proc_name ^ "_impl")
        val conc_body = Proof_Context.get_thms ctxt (conc_proc_name ^ "_body_def")
        (* Unfold body def in the impl rule --- maybe get the parser to do this? *)
        val conc_impl' = Simplifier.rewrite_rule ctxt conc_body conc_impl

        val abs_unfold_tac =
            if unfold_haskell_p then let
                    val abs_proc_name = (Long_Name.base_name o fst o dest_Const o head_of) (#abs cc)
                    val abs_proc_def  = Proof_Context.get_thms ctxt (abs_proc_name ^ "_def")
                in
                    Simplifier.rewrite_goal_tac ctxt abs_proc_def
                end
            else
                (fn _ => all_tac)

        val ccorres_rewrite_tac = NO_CONTEXT_TACTIC ctxt
            (Method_Closure.apply_method ctxt @{method "ccorres_rewrite"} [] [] [] ctxt [])

        val ss = simpset_of (ctxt delsimps boilerplace_simp_dels |> addcongs
                 (if #ignore_call opts then call_ignore_cong else []))
    in
        prim_trace_tac' (#trace_this trace) depth "CINIT" ctxt
                        (EVERY' [
                         (* Unfold abstract side *)
                         abs_unfold_tac,
                         (* Get function body *)
                         resolve_tac ctxt Call_thm THEN' resolve_tac ctxt [conc_impl'],
                         (* Remove any superfluous return/Guard DontReach at the end *)
                         REPEAT_DETERM' (FIRST' [trim_redundant_throw_tac , trim_DontReach_tac]),
                         (* Fix associativity of ;; *)
                         REPEAT_DETERM' (resolve_tac ctxt ccorres_rhs_assoc),
                         (* Simplify bodies, ignoring parts of calls *)
                         TRY' (asm_full_simp_tac (put_simpset ss ctxt)),
                         (* Simplify, using ccorres_rewrite *)
                         TRY' (fn _ => if #ccorres_rewrite opts then ccorres_rewrite_tac else all_tac),
                         (* Lift any variables *)
                         corres_pre_lift_tac_cinit ctxt trace depth' xfs,
                         (* Substitute any lifted variable equalities.  The option is the predicate to use on assumptions *)
                         substutite_asm_eqs ctxt (#subst_asms opts),
                         (* Remove local variable initialisers *)
                         REPEAT_DETERM' (corres_trim_lvar_nondet_init_tac trace depth' ctxt true),
                         (* Do guard implication *)
                         resolve_tac ctxt ccorres_guard_imp2]) i
    end;
in
    SUBGOAL tac
end;

(* Exported tactics *)

val ccorresN = "ccorres"
val preN = "pre"
val onlyN = "only"
val liftoptN = "lift"

val trace_allN = "trace"        (* trace everything *)
val trace_ceqvN = "trace_ceqv"  (* trace ceqv, xpres, and simp *)

val use_simpN = "use_simp" (* default *)
val no_simpN = "no_simp"

val subst_asm_varsN = "subst_asm_vars"
val subst_asmN = "subst_asm" (* default *)
val no_subst_asmN = "no_subst_asm"

val ignore_callN = "ignore_call" (* default *)
val no_ignore_callN = "no_ignore_call"

val no_vcgN = "no_vcg"
val use_vcgN = "use_vcg" (* default *)

val c_linesN = "c_lines"

val ccorres_rewriteN = "ccorres_rewrite" (* default *)
val no_ccorres_rewriteN = "no_ccorres_rewrite"

val C_simpN = "C_simp"
val C_simpThm = @{named_theorems "C_simp"}

(* val auto_vcgN = "auto_vcg" *)

fun thm_mod_add_del_only name att_add att_del att_clear =
    [Args.$$$ name -- Scan.option Args.add -- Args.colon >> K (Method.modifier att_add @{here}),
     Args.$$$ name -- Args.del -- Args.colon >> K (Method.modifier att_del @{here}),
     Args.$$$ name -- Args.$$$ onlyN -- Args.colon >> K {init = Context.proof_map att_clear, attribute = att_add, pos = @{here}}]

val ctac_add_del_only =
    [Args.add -- Args.colon >> K (Method.modifier ctac_add @{here}),
     Args.del -- Args.colon >> K (Method.modifier ctac_del @{here}),
     Args.$$$ onlyN -- Args.colon >> K {init = Context.proof_map ctac_clear, attribute = ctac_add, pos = @{here}}]

val ctac_modifiers =
    Simplifier.simp_modifiers
    @ thm_mod_add_del_only ccorresN ctac_add ctac_del ctac_clear
    @ thm_mod_add_del_only preN ctac_pre_add ctac_pre_del ctac_pre_clear
    @ ctac_add_del_only

val csymbr_modifiers =
    Simplifier.simp_modifiers

val C_simp_add = Thm.declaration_attribute (Named_Theorems.add_thm C_simpThm)
val C_simp_del = Thm.declaration_attribute (Named_Theorems.del_thm C_simpThm)
val C_simp_clear = Named_Theorems.clear C_simpThm

val boilerplate_modifiers =
    Simplifier.simp_modifiers
    @ thm_mod_add_del_only C_simpN C_simp_add C_simp_del C_simp_clear

structure P = Parse;

val ctac_options =
    [Args.$$$ trace_allN >> K (ctac_opts_trace_update (K all_trace_opts)),
     Args.$$$ trace_ceqvN >> K (ctac_opts_trace_update set_ceqv_trace_opts),
     Args.$$$ use_simpN >> K (ctac_opts_simp_update (K true)),
     Args.$$$ no_simpN >> K (ctac_opts_simp_update (K false)),
     Args.$$$ use_vcgN >> K (ctac_opts_vcg_update (K "")),
     Args.$$$ no_vcgN >> K (ctac_opts_vcg_update (K "_novcg")),
     Args.$$$ c_linesN |-- P.nat >> (fn n => (ctac_opts_c_lines_update (K n)))
(*  , Args.$$$ auto_vcgN >> K (ctac_opts_vcg_update NONE) *)]

val csymbr_options =
    [Args.$$$ trace_allN >> K (csymbr_opts_trace_update (K all_trace_opts)),
     Args.$$$ trace_ceqvN >> K (csymbr_opts_trace_update set_ceqv_trace_opts)]

val cinit_options =
    [Args.$$$ subst_asmN >> K (cinit_opts_subst_update (K substp_is_eq)),
     Args.$$$ no_subst_asmN >> K (cinit_opts_subst_update (K substp_never)),
     Args.$$$ subst_asm_varsN >> K (cinit_opts_subst_update (K substp_is_var_eq)),
     Args.$$$ ignore_callN >> K (cinit_opts_call_update (K true)),
     Args.$$$ no_ignore_callN >> K (cinit_opts_call_update (K false)),
     Args.$$$ no_ccorres_rewriteN >> K (cinit_opts_ccorres_rewrite_update (K false)),
     Args.$$$ trace_allN >> K (cinit_opts_trace_update (K all_trace_opts)),
     Args.$$$ trace_ceqvN >> K (cinit_opts_trace_update set_ceqv_trace_opts)]

val ceqv_options =
    [Args.$$$ trace_allN >> K (ceqv_opts_trace_update (K all_trace_opts)),
     Args.$$$ trace_ceqvN >> K (ceqv_opts_trace_update set_ceqv_trace_opts)]

fun apply [] x = x
  | apply (f :: fs) x = apply fs (f x);

fun shorten_names mp =
    mp -- Shorten_Names.shorten_names_preserve_new >> MethodExtras.then_all_new

val corres_ctac_tactic = let
    fun tac upds ctxt
      = Method.SIMPLE_METHOD' (corres_ctac (apply upds default_ctac_opts) ctxt
                               THEN_ALL_NEW (fn _ => no_name_eta_tac ctxt));

    val option_args = Args.parens (P.list (Scan.first ctac_options))
    val opt_option_args = Scan.lift (Scan.optional option_args [])
in
    (opt_option_args --| Method.sections ctac_modifiers
      >> tac) |> shorten_names
end;

fun corres_pre_lift_tac_clift ctxt =
    corres_pre_lift_tacs ctxt clift_thms (fn _ => all_tac) (fn _ => all_tac)

fun corres_pre_abstract_args lift_fn =
    let
        fun tac (xfs : string list) (ctxt : Proof.context)
          = Method.SIMPLE_METHOD' (lift_fn ctxt default_trace_opts 0 xfs)
    in
        (Args.context |-- Scan.lift (Scan.repeat1 Args.name) >> tac)
        |> shorten_names
    end;

(* These differ only in the behaviour wrt the concrete guards --- the first abstracts the new variable, the second just drops it *)
val corres_abstract_args = corres_pre_abstract_args corres_pre_lift_tac_clift;
val corres_abstract_init_args = corres_pre_abstract_args corres_pre_lift_tac_cinit;

val corres_symb_rhs = let
    fun tac upds ctxt
      = Method.SIMPLE_METHOD' (corres_symb_rhs_tac (apply upds default_csymbr_opts) ctxt
                               THEN_ALL_NEW (fn _ => no_name_eta_tac ctxt));

    val option_args = Args.parens (P.list (Scan.first csymbr_options))
    val opt_option_args = Scan.lift (Scan.optional option_args [])
in
    (opt_option_args --| Method.sections csymbr_modifiers >> tac)
    |> shorten_names
end;

val corres_ceqv = let
    fun tac upds ctxt
      = Method.SIMPLE_METHOD' (corres_solve_ceqv (#trace (apply upds default_ceqv_opts)) 0 ctxt);

    val option_args = Args.parens (P.list (Scan.first ceqv_options))
    val opt_option_args = Scan.lift (Scan.optional option_args [])
in
    (opt_option_args --| Method.sections [] >> tac)
    |> shorten_names
end;

(* Does all the annoying boilerplate stuff at the start of a ccorres rule.
 * We should be able to get the xfs from the goal ... *)
fun corres_boilerplate unfold_haskell_p = let
    fun tac (upds, xfs : string list) ctxt
      = Method.SIMPLE_METHOD' (corres_boilerplate_tac (apply upds default_cinit_opts) unfold_haskell_p xfs ctxt
                               THEN_ALL_NEW (fn _ => no_name_eta_tac ctxt))

    val var_lift_args = Args.$$$ liftoptN |-- Args.colon |--
                             Scan.repeat (Scan.unless (Scan.first boilerplate_modifiers) Args.name)
    val option_args = Args.parens (P.list (Scan.first cinit_options))
    val opt_var_lift_args = Scan.lift (Scan.optional option_args [] -- Scan.optional var_lift_args [])
in
    (opt_var_lift_args --| Method.sections boilerplate_modifiers >> tac)
    |> shorten_names
end;

(* Debugging *)

val corres_print_xf = let
    fun tac (_ : Proof.context) (prem, _) = let
        val cc         = concl_dest_ccorres prem;
        val (lhs, _) = extract_Seq (#conc cc)
        val (is_concr, (xf, _), o_xfru)  = normalise_xf (extract_lhs_xf lhs)

        fun b_to_s b = if b then "true" else "false"

        val _ = tracing ("xf: " ^ xf ^ " (concrete: " ^ b_to_s is_concr ^ ")")
        val _ = case o_xfru of
                    NONE => tracing ("xfru: NONE")
                  | SOME ((xfru', _), b) => tracing ("xfru: " ^ xfru' ^ " (abstract required: " ^ b_to_s b ^ ")")
    in
        all_tac
    end;
    fun method ctxt = Method.SIMPLE_METHOD' (SUBGOAL (tac ctxt))
in
    Args.context >> K method
end;

end;
