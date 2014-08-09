(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

fun funkysplit [_,b,c] = [b,c]
        | funkysplit [_,c] = [c]
        | funkysplit l = l

fun real_base_name name = name |> Long_Name.explode |> funkysplit |> Long_Name.implode (*Handles locales properly-ish*)

fun handle_int exn func = if Exn.is_interrupt exn then reraise exn else func

val wp_sect = "wp";
val ignore_sect = "ignore";
val simp_sect = "simp";
val lift_sect = "lift";
val ignore_del_sect = "ignore_del";
val unfold_sect = "unfold";

fun read_const ctxt = Proof_Context.read_const {proper = true, strict = false} ctxt;

signature CrunchInstance =
sig
    type extra;
    val name : string;
    val has_preconds : bool;
    val mk_term : term -> term -> extra -> term;
    val get_precond : term -> term;
    val put_precond : term -> term -> term;
    val pre_thms : thm list;
    val wpc_tactic : Proof.context -> tactic;
    val parse_extra : Proof.context -> string -> term * extra;
    val magic : term;
end

signature CRUNCH =
sig
    type extra;
    (* Crunch configuration: theory, naming scheme, lifting rules, wp rules *)
    type crunch_cfg = {lthy: local_theory, prp_name: string, nmspce: string option, lifts: thm list,
        wps: (string * thm) list, igs: string list, simps: thm list, ig_dels: string list, unfolds: (string * thm) list};

    (* Crunch takes a configuration, a precondition, any extra information needed, a debug stack,
    a constant name, and a list of previously proven theorems, and returns a theorem for
    this constant and a list of new theorems (which may be empty if the result
    had already been proven). *)
    val crunch :
       crunch_cfg -> term -> extra -> string list -> string
         -> (string * thm) list ->  (thm option * (string * thm) list);

    val crunch_x : Args.src list -> string -> string -> (string * xstring) list
         -> string list -> local_theory -> local_theory;

    val crunch_ignore_add_del : string list -> string list -> theory -> theory
end

functor Crunch (Instance : CrunchInstance) =
struct

type extra = Instance.extra;

type crunch_cfg = {lthy: local_theory, prp_name: string, nmspce: string option, lifts: thm list,
    wps: (string * thm) list, igs: string list, simps: thm list, ig_dels: string list, unfolds: (string * thm) list};

structure CrunchIgnore = Generic_Data
(struct
    val name = "HOL/crunch/ignore/" ^ Instance.name
    type T = string list
    val empty = []
    val extend = I
    val merge = Library.merge (op =);
    fun print context names = 
        Pretty.writeln (Pretty.big_list "Constants to be ignored in crunch unfolding:"
                                        (map Pretty.str names)); 
end);

fun crunch_ignore_add thms thy =
  Context.theory_map (CrunchIgnore.map (curry (Library.merge (op =)) thms)) thy

fun crunch_ignore_del thms thy =
  Context.theory_map (CrunchIgnore.map (Library.subtract (op =) thms)) thy

fun crunch_ignore_add_del adds dels thy =
  thy |> crunch_ignore_add adds |> crunch_ignore_del dels

val def_sfx = "_def"; 
val induct_sfx = ".induct";
val simps_sfx = ".simps";
val param_name = "param_a";
val dummy_monad_name = "__dummy__";

fun def_of n = n ^ def_sfx;
fun induct_of n = n ^ induct_sfx;
fun simps_of n = n ^ simps_sfx;

fun num_args t = length (binder_types t) - 1;

fun real_const_from_name const nmspce lthy =
    let
      val qual::locale::nm::nil = Long_Name.explode const;
      val SOME some_nmspce = nmspce;
      val nm = Long_Name.implode (some_nmspce :: nm :: nil);
      val _ = read_const lthy nm;
     in
       nm
     end
     handle exn => handle_int exn const;


fun get_monad lthy f xs = if is_Const f then
    (* we need the type of the underlying constant to avoid polymorphic
       constants like If, case_option, K_bind being considered monadic *)
    let val T = dest_Const f |> fst |> read_const lthy |> type_of;

    fun is_product v (Type ("Product_Type.prod", [Type ("fun", [Type ("Product_Type.prod", [_,v']), Type ("HOL.bool",[])]), Type ("HOL.bool",[])])) = (v = v')
      | is_product v (Type ("Product_Type.prod", [Type ("Set.set", [Type ("Product_Type.prod", [_,v'])]), Type ("HOL.bool",[])])) = (v = v')
      | is_product _ _ = false;

    fun num_args (Type ("fun", [v,p])) n =
          if is_product v p then SOME n else num_args p (n + 1)
      | num_args _ _ = NONE
        
    in case num_args T 0 of NONE => []
      | SOME n => [list_comb (f, Library.take n (xs @ map Bound (1 upto n)))]
    end
  else [];

fun monads_of lthy t = case strip_comb t of
    (Const f, xs) => get_monad lthy (Const f) xs @ maps (monads_of lthy) xs
  | (Abs (_, _, t), []) => monads_of lthy t
  | (Abs a, xs) => monads_of lthy (betapplys (Abs a, xs))
  | (_, xs) => maps (monads_of lthy) xs;


val get_thm = Proof_Context.get_thm

val get_thms = Proof_Context.get_thms

fun maybe_thms thy name = get_thms thy name handle exn => handle_int exn []
fun thy_maybe_thms thy name = Global_Theory.get_thms thy name handle exn => handle_int exn []

fun add_thm thm atts name lthy =
  Local_Theory.notes [((Binding.name name, atts), [([thm], atts)])] lthy |> #2

fun get_thm_name_bluh (cfg: crunch_cfg) const_name
  = Long_Name.base_name const_name ^ "_" ^ (#prp_name cfg)

fun get_thm_name (cfg : crunch_cfg) const_name
  = if read_const (#lthy cfg) (Long_Name.base_name const_name)
         = read_const (#lthy cfg) const_name
      then Long_Name.base_name const_name ^ "_" ^ (#prp_name cfg)
      else space_implode "_" (space_explode "." const_name @ [#prp_name cfg])

fun get_stored cfg n = get_thm (#lthy cfg) (get_thm_name cfg n)

fun get_stored_bluh cfg n = 
  let val r = (maybe_thms (#lthy cfg) (get_thm_name cfg n)) @ (maybe_thms (#lthy cfg) (get_thm_name_bluh cfg n));
      in (case r of [] => error ("") | _ => (hd r))
  end

fun mapM _ [] y = y
  | mapM f (x::xs) y = mapM f xs (f x y)

fun dest_equals t = t |> Logic.dest_equals
  handle TERM _ => t |> HOLogic.dest_Trueprop |> HOLogic.dest_eq;

fun const_is_lhs const nmspce lthy def =
    let
      val (lhs, _) = def |> prop_of |> dest_equals;
      val (nm, _)  = dest_Const const;
      val (nm', _) = dest_Const (head_of lhs);
    in
      (real_const_from_name nm nmspce lthy) = (real_const_from_name nm' nmspce lthy)
    end handle TERM _ => false

fun deep_search_thms lthy defn const nmspce =
    let
      val thy  = Proof_Context.theory_of lthy
      val thys = thy :: Theory.ancestors_of thy;
      val filt = filter (const_is_lhs const nmspce lthy);
    
      fun search [] = error("not found: const: " ^ PolyML.makestring const ^ " defn: " ^ PolyML.makestring defn)
        | search (t::ts) = (case (filt (thy_maybe_thms t defn)) of
              [] => search ts
	    | thms => thms);
    in
      case filt (maybe_thms lthy defn) of
          [] => search thys
        | defs => defs
     end;

val unfold_get_params = @{thms Let_def return_bind returnOk_bindE
    K_bind_def split_def bind_assoc bindE_assoc
    trans[OF liftE_bindE return_bind]};

fun unfold lthy const triple nmspce =
    let
      val _ = tracing "unfold"
      val const_term = read_const lthy const;
      val const_defn = const |> Long_Name.base_name |> def_of;
      val const_def = deep_search_thms lthy const_defn const_term nmspce
                        |> hd |> Simpdata.safe_mk_meta_eq;
      val _ = Pretty.writeln (Pretty.block [Pretty.str ("const_def: " ^ PolyML.makestring const_defn), Display.pretty_thm lthy const_def])
      val trivial_rule = Thm.trivial triple
      val _ = Pretty.writeln (Pretty.block [Pretty.str "trivial_rule: ", Display.pretty_thm lthy trivial_rule])
      val unfold_rule = trivial_rule
        |> Simplifier.rewrite_goals_rule lthy [const_def];
      val _ = Pretty.writeln (Pretty.block [Pretty.str "unfold_rule: ", Display.pretty_thm lthy unfold_rule])
      val ms = unfold_rule
        |> Simplifier.rewrite_goals_rule lthy unfold_get_params
        |> prems_of |> maps (monads_of lthy);
    in if Thm.eq_thm_prop (trivial_rule, unfold_rule)
       then error ("Unfold rule generated for " ^ const ^ " does not apply")
       else (ms, unfold_rule) end

fun mk_apps t n m = 
    if n = 0 
    then t
    else mk_apps t (n-1) (m+1) $ Bound m

fun mk_abs t n =
    if n = 0
    then t
    else Abs ("_", dummyT, mk_abs t (n-1))

fun eq_cname (Const (s, _)) (Const (t, _)) = (s = t)
  | eq_cname _ _ = false

fun resolve_abbreviated lthy abbrev =
  let
      val (abbrevn,_) = dest_Const abbrev
      val origin = (head_of (snd ((Consts.the_abbreviation o Proof_Context.consts_of) lthy abbrevn)));
      val (originn,_) = dest_Const origin;
      val (_::_::_::nil) = Long_Name.explode originn;
    in origin end handle exn => handle_int exn abbrev

fun map_consts f = 
      let
         fun map_aux (Const a) = f (Const a)
           | map_aux (t $ u) = map_aux t $ map_aux u
           | map_aux x = x
      in map_aux end;

fun map_unvarifyT t = map_types Logic.unvarifyT_global t

fun induct_inst lthy const goal nmspce =
    let
      val _ = tracing "induct_inst"
      val base_const = Long_Name.base_name const;
      val _ = tracing ("base_const: " ^ PolyML.makestring base_const)
      val induct_thm = base_const |> induct_of |> get_thm lthy;
      val _ = tracing ("induct_thm: " ^ PolyML.makestring induct_thm)
      val const_term = read_const lthy const |> map_unvarifyT;
      val n = const_term |> fastype_of |> num_args;
      val t = mk_abs (Instance.magic $ mk_apps const_term n 0) n
              |> Syntax.check_term lthy |> Logic.varify_global |> cterm_of (Proof_Context.theory_of lthy);
      val P = Thm.concl_of induct_thm |> HOLogic.dest_Trueprop |> head_of |> cterm_of (Proof_Context.theory_of lthy);
      val trivial_rule = Thm.trivial goal;
      val induct_inst = Thm.instantiate ([], [(P, t)]) induct_thm
                        RS trivial_rule;
      val _ = tracing ("induct_inst" ^ Syntax.string_of_term lthy (Thm.prop_of induct_inst));
      val simp_thms = deep_search_thms lthy (base_const |> simps_of) const_term nmspce;
      val induct_inst_simplified = induct_inst
        |> Simplifier.rewrite_goals_rule lthy (map Simpdata.safe_mk_meta_eq simp_thms);
      val ms = maps (monads_of lthy) (prems_of induct_inst_simplified);
      val ms' = filter_out (eq_cname (resolve_abbreviated lthy const_term) o head_of) ms;
    in if Thm.eq_thm_prop (trivial_rule, induct_inst)
       then error ("Unfold rule generated for " ^ const ^ " does not apply")
       else (ms', induct_inst) end

fun unfold_data lthy constn goal nmspce nil = (
    induct_inst lthy constn goal nmspce handle exn => handle_int exn
    unfold lthy constn goal nmspce handle exn => handle_int exn
    error ("unfold_data: couldn't find defn or induct rule for " ^ constn))
  | unfold_data lthy constn goal _ [(_, thm)] =
    let
      val trivial_rule = Thm.trivial goal
      val unfold_rule = Simplifier.rewrite_goals_rule lthy [safe_mk_meta_eq thm] trivial_rule;
      val ms = unfold_rule
        |> Simplifier.rewrite_goals_rule lthy unfold_get_params
        |> prems_of |> maps (monads_of lthy);
    in if Thm.eq_thm_prop (trivial_rule, unfold_rule)
       then error ("Unfold rule given for " ^ constn ^ " does not apply")
       else (ms, unfold_rule) end
  | unfold_data _ constn _ _ _ = error ("Multiple unfolds are given for " ^ constn)



val split_if = @{thm "split_if"}

fun maybe_cheat_tac thm =
  if (Goal.skip_proofs_enabled ())
  then ALLGOALS (Skip_Proof.cheat_tac) thm
  else all_tac thm;

fun var_precond v =
  if Instance.has_preconds
  then Instance.put_precond (Var (("Precond", 0), Instance.get_precond v |> fastype_of)) v
  else v;

fun is_proof_of cfg const (name, _) =
  get_thm_name cfg const = name

fun get_inst_precond ctxt pre extra (mapply, goal) = let
    val thy = Proof_Context.theory_of ctxt;
    val (c, xs) = strip_comb mapply;
    fun replace_vars (t, n) =
      if exists_subterm (fn t => is_Bound t orelse is_Var t) t
        then Free ("ignore_me" ^ string_of_int n, dummyT)
      else t
    val ys = map replace_vars (xs ~~ (1 upto (length xs)));
    val goal2 = Instance.mk_term pre (list_comb (c, ys)) extra
      |> Syntax.check_term ctxt |> var_precond
      |> HOLogic.mk_Trueprop |> cterm_of thy;
    val spec = goal RS Thm.trivial goal2;
    val precond = concl_of spec |> HOLogic.dest_Trueprop |> Instance.get_precond;
  in SOME precond end
    (* in rare cases the tuple extracted from the naming scheme doesn't
       match what we were trying to prove, thus a THM exception from RS *)
  handle THM _ => NONE;

fun split_precond (Const (@{const_name pred_conj}, _) $ P $ Q)
    = split_precond P @ split_precond Q
  | split_precond (Abs (n, T, @{const "HOL.conj"} $ P $ Q))
    = maps (split_precond o Envir.eta_contract) [Abs (n, T, P), Abs (n, T, Q)]
  | split_precond t = [t];

val precond_implication_term
  = Syntax.parse_term @{context}
    "%P Q. (!! s. (P s ==> Q s))";

fun precond_needed lthy pre css pre' = let
    val imp = Syntax.check_term lthy (precond_implication_term $ pre $ pre');
  in Goal.prove lthy [] [] imp
       (fn prems => clarsimp_tac css 1); false end
     handle exn => handle_int exn true;

fun combine_preconds ctxt pre pres = let
    val pres' = maps (split_precond o Envir.beta_eta_contract) pres
      |> filter_out (exists_subterm (fn t => is_Var t orelse
            (is_Free t andalso
              is_prefix (op =) (String.explode "ignore_me")
                (String.explode (fst (dest_Free t))))))
      |> remove (op aconv) pre |> distinct (op aconv)
      |> filter (precond_needed ctxt pre ctxt);
    val T = fastype_of pre;
    val conj = Const (@{const_name pred_conj}, T --> T --> T)
  in case pres' of
      [] => pre
    | _ => let val precond = foldl1 (fn (a, b) => conj $ a $ b) pres'
        in if precond_needed ctxt precond ctxt pre then conj $ pre $ precond else precond end
  end;

(* the crunch function is designed to be foldable with this custom fold
   to crunch over a list of constants *)
fun funkyfold _ [] _ = ([], [])
  | funkyfold f (x :: xs) thms = let
    val (z, thms') = f x thms
    val (zs, thms'') = funkyfold f xs (thms' @ thms)
  in (z :: zs, thms' @ thms'') end

exception WrongType

fun make_goal const_term const pre extra lthy =
  let val nns = const_term |> fastype_of |> num_args |> 
                          Name.invent Name.context param_name; 
      val parse = Syntax.parse_term lthy;
      val check = Syntax.check_term lthy;
      val body = parse (String.concat (separate " " (const :: nns)));
  in check (Instance.mk_term pre body extra) end;

fun crunch cfg pre extra stack const' thms =
  let 
    val lthy = #lthy cfg;
    val const = real_const_from_name const' (#nmspce cfg) lthy;
    val empty_ref = Unsynchronized.ref [] : thm list Unsynchronized.ref (* FIXME: avoid refs *)
  in
    let
      val _ = "crunching constant: " ^ const |> tracing;
      val const_term = read_const lthy const;
      val real_const_term = resolve_abbreviated lthy const_term;
      val goal = make_goal const_term const pre extra lthy
                 handle exn => handle_int exn (raise WrongType);
      val goal_prop = HOLogic.mk_Trueprop goal;
    in
      let val v = find_first (is_proof_of cfg const) thms
      in (SOME (snd (the v)), []) end
      handle exn => handle_int exn
        (SOME (get_stored cfg const), [])
      handle exn => handle_int exn
      let val const_long_name = real_const_term |> dest_Const |> fst;
        val cgoal_prop = cterm_of (Proof_Context.theory_of lthy) goal_prop;
        val v = find_first (fn (s, t) => s = const_long_name andalso
                    (is_some o SINGLE (WeakestPre.apply_rules_tac_n false lthy [t] empty_ref 1)) (Goal.init cgoal_prop)) (#wps cfg)
      in (SOME (snd (the v)), []) end
      handle exn => handle_int exn
        let
          fun wp rules = WeakestPre.apply_rules_tac_n false lthy
                                           (map snd (thms @ #wps cfg) @ rules) empty_ref

          val lthy' = Variable.auto_fixes goal_prop lthy
          val (thm, thms')
                   = ( Goal.prove lthy' [] [] goal_prop (fn prems =>
                                  TRY (wp [] 1) THEN TRY (wp (#lifts cfg) 1))
                         |> singleton (Proof_Context.export lthy' lthy)
                     , [] )
          handle exn => handle_int exn
            let
              val lthy' = Variable.auto_fixes goal lthy;
              val cgoal = goal |> var_precond |> HOLogic.mk_Trueprop |> cterm_of (Proof_Context.theory_of lthy');
              val unfolds' = filter (fn (a, _) => a = const) (#unfolds cfg)
              val (ms, unfold_rule) = unfold_data lthy' const cgoal (#nmspce cfg) unfolds'
                |>> map (fn t => (real_const_from_name (fst (dest_Const (head_of t))) (#nmspce cfg) lthy', t))
                |>> subtract (fn (a, b) => a = (fst b))
                      (subtract (op =) (#ig_dels cfg) (#igs cfg @ CrunchIgnore.get (Context.Proof lthy')));
              val stack' = const :: stack;
              val _ = if (length stack' > 20) then
                         (tracing "Crunch call stack:";
                          map tracing (const::stack);
                          error("probably infinite loop")) else ();
              val (goals, thms') = funkyfold (crunch cfg pre extra stack') (map fst ms) thms;
              val goals' = map_filter I goals
              val lthy'' = lthy' addsimps ((#simps cfg) @ goals')
                  |> Splitter.del_split split_if

              fun collect_preconds pre =
                let val preconds = map_filter (fn (x, SOME y) => SOME (x, y) | (_, NONE) => NONE) (map snd ms ~~ goals) 
                                                    |> map_filter (get_inst_precond lthy'' pre extra);
                  val precond = combine_preconds lthy'' (Instance.get_precond goal) preconds;
                in Instance.put_precond precond goal |> HOLogic.mk_Trueprop end;
              val goal_prop2 = if Instance.has_preconds then collect_preconds pre else goal_prop;

              val lthy''' = Variable.auto_fixes goal_prop2 lthy''
              val _ = tracing ("attempting: " ^ Syntax.string_of_term lthy''' goal_prop2);
 
            in (Goal.prove lthy''' [] [] goal_prop2
                  ( (*DupSkip.goal_prove_wrapper *) (fn _ => 
                  rtac unfold_rule 1
                    THEN maybe_cheat_tac
                  THEN ALLGOALS (fn n =>
                    simp_tac lthy''' n
                    THEN
                    TRY (resolve_tac Instance.pre_thms n)
                    THEN
                    REPEAT_DETERM (
                      wp goals' n
                      ORELSE
                      CHANGED (clarsimp_tac lthy''' n) 
                      ORELSE
                      assume_tac n
                      ORELSE
                      Instance.wpc_tactic lthy'''
                      ORELSE
                      safe_tac lthy'''
                      ORELSE
                      CHANGED (simp_tac lthy''' n)
                  )))) |> singleton (Proof_Context.export lthy''' lthy)
                  handle e => 
                         (tracing "Crunch call stack:";
                          map tracing (const::stack);
                          raise e)
                , thms') end
        in (SOME thm, (get_thm_name cfg const, thm) :: thms') end
    end
    handle WrongType =>
      let val _ = tracing ("The constant " ^ const ^ " has the wrong type and is being ignored")
      in (NONE, []) end
  end 

(*Todo: Remember mapping from locales to theories*)
fun get_locale_origins full_const_names ctxt =
  let
    fun get_locale_origin abbrev = 
      let
        (*Check if the given const is an abbreviation*)
        val (origin,_) = dest_Const (head_of (snd ((Consts.the_abbreviation o Proof_Context.consts_of) ctxt abbrev)));
        (*Check that the origin can be broken into 3 parts (i.e. it is from a locale) *)
        val [_,_,_] = Long_Name.explode origin;
        (*Remember the theory for the abbreviation*)

        val [qual,nm] = Long_Name.explode abbrev                
      in SOME qual end handle exn => handle_int exn NONE
  in fold (curry (fn (abbrev,qual) => case (get_locale_origin abbrev) of
                                        SOME q => SOME q
                                      | NONE => NONE)) full_const_names NONE
  end
 
fun parse_unfold_pair unfold =
  let
    val parse_string = Scan.repeat (Scan.unless ($$ "," || $$ ")") (Scan.one Symbol.not_eof))
    val ((first, second), rem) = ($$ "(" |-- parse_string --| Scan.this_string ", " -- parse_string --| $$ ")") (Symbol.explode unfold)
      handle exn => handle_int exn error "Could not parse unfold data, expected: (const, thm)"
  in if rem = [] then (implode first, implode second)
    else error "Could not parse unfold data, expected: (const, thm)" end

fun crunch_x atts extra prp_name wpigs consts lthy =
    let 
        fun const_name const = dest_Const (read_const lthy const) |> #1
(*              handle exn => handle_int exn
                               strip_comb (Syntax.read_term ctxt const) |> tap (fn x => tracing (PolyML.makestring x)) |> #1 |> dest_Const |> #1;*)

        val wps' = wpigs |> filter (fn (s,_) => s = wp_sect) |> map #2

        val simps = wpigs |> filter (fn (s,_) => s = simp_sect) |> map #2 
                    |> maps (get_thms lthy)

        val igs = wpigs |> filter (fn (s,_) => s = ignore_sect) 
                        |> map (const_name o #2)

        val lifts = wpigs |> filter (fn (s,_) => s = lift_sect) |> map #2
                          |> maps (get_thms lthy)

        val ig_dels = wpigs |> filter (fn (s,_) => s = ignore_del_sect)
                            |> map (const_name o #2)

        fun read_unfold (first, second) = (const_name first, get_thm lthy second)

        val unfolds = wpigs |> filter (fn (s,_) => s = unfold_sect) |> map #2
                    |> map (read_unfold o parse_unfold_pair)

        fun mk_wp thm = 
           let val ms = prop_of thm |> monads_of lthy;
                val m = if length ms = 1 
                        then 
                            hd ms |> head_of |> dest_Const |> fst
                        else 
                            dummy_monad_name;
            in (m, thm) end;

        val wps = maps (get_thms lthy) wps' |> map mk_wp;
        val full_const_names = map const_name consts;
       
        val nmspce = get_locale_origins full_const_names lthy;
        val (pre', extra') = Instance.parse_extra lthy extra

        (* check that the given constants match the type of the given property*)
        val const_terms = map (read_const lthy) full_const_names;
        val _ = map (fn (const_term, const) => make_goal const_term const pre' extra' lthy)
                    (const_terms ~~ full_const_names)

        val (_, thms) = funkyfold (crunch {lthy = lthy, prp_name = prp_name, nmspce = nmspce, lifts = lifts,
              wps = wps, igs = igs, simps = simps, ig_dels = ig_dels, unfolds = unfolds} pre' extra' [])
            full_const_names [];

        val atts' = map (Attrib.check_src lthy) atts;

        val lthy' = fold (fn (name, thm) => add_thm thm atts' name) thms lthy;
    in
        Pretty.writeln
          (Pretty.big_list "proved:"
                           (map (fn (n,t) =>
                                    Pretty.block
                                      [Pretty.str (n ^ ": "),
                                       Syntax.pretty_term lthy (prop_of t)])
                                thms));
        lthy'
    end

end
(*
structure Crunch_Crunches : CRUNCH = Crunch;
*)
