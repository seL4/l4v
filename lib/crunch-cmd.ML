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
What is crunch? Crunch is for proving easily proved properties over various
functions within a (shallow monadic) specification. Suppose we have a toplevel
specification function f and some simple notion of correctness, P \<turnstile> f, which
we want to prove. However f is defined in terms of subfunctions g etc.
To prove P \<turnstile> f, we will first show many lemmas P \<turnstile> g, which crunch lets us
do easily.

As a first step, crunch must discover "cruch rules" which structure the proof.
For instance, if f is a constant with a definition, crunch may discover the
definition "f == f_body" and derive the crunch rule "P \<turnstile> f_body \<Longrightarrow> P \<turnstile> f".
A crunch rule will be used if all its premises are either proofs of the
same notion of correctness (P \<turnstile> ?f) or can be solved trivially by wp/simp.

The user can supply crunch rules with the rule: section or crunch_rule
attribute, which will be tried both as rewrites and
as introduction rules. Crunch also has a number of builtin strategies
for finding definitional rules in the context.

Once a crunch rule for P \<turnstile> f is found, crunch will recursively apply to
all monadic constants in all the premises. (The exploration terminates
where crunch rules can be found without premises.) Crunch will obtain
proofs e.g. P \<turnstile> g for all f's dependencies, then finally try to prove
P \<turnstile> f using the crunch rule, wp (with the given dependencies) and simp.
Additional wp and simp rules can also be given with the wp: and simp:
sections.

*)

(* Tracing debug. *)
val should_debug = Unsynchronized.ref false
fun debug_trace s =
  if (!should_debug) then
    tracing s
  else
    ()

fun funkysplit [_,b,c] = [b,c]
        | funkysplit [_,c] = [c]
        | funkysplit l = l

fun real_base_name name = name |> Long_Name.explode |> funkysplit |> Long_Name.implode (*Handles locales properly-ish*)

fun handle_int exn func = if Exn.is_interrupt exn then Exn.reraise exn else func

val wp_sect = "wp";
val wp_del_sect = "wp_del";
val ignore_sect = "ignore";
val ignore_del_sect = "ignore_del";
val simp_sect = "simp";
val simp_del_sect = "simp_del";
val rule_sect = "rule";
val rule_del_sect = "rule_del";

fun read_const ctxt = Proof_Context.read_const {proper = true, strict = false} ctxt;

fun gen_term_eq (f $ x, f' $ x') = gen_term_eq (f, f') andalso gen_term_eq (x, x')
  | gen_term_eq (Abs (_, _, t), Abs (_, _, t')) = gen_term_eq (t, t')
  | gen_term_eq (Const (nm, _), Const (nm', _)) = (nm = nm')
  | gen_term_eq (Free (nm, _), Free (nm', _)) = (nm = nm')
  | gen_term_eq (Var (nm, _), Var (nm', _)) = (nm = nm')
  | gen_term_eq (Bound i, Bound j) = (i = j)
  | gen_term_eq _ = false
fun ae_conv (t, t') = gen_term_eq
  (Envir.beta_eta_contract t, Envir.beta_eta_contract t')

signature CrunchInstance =
sig
    type extra;
    val name : string;
    val has_preconds : bool;
    val mk_term : term -> term -> extra -> term;
    val dest_term : term -> (term * term * extra) option;
    val get_precond : term -> term;
    val put_precond : term -> term -> term;
    val eq_extra : extra * extra -> bool;
    val pre_thms : thm list;
    val wpc_tactic : Proof.context -> tactic;
    val parse_extra : Proof.context -> string -> term * extra;
    val magic : term;
end

signature CRUNCH =
sig
    type extra;
    (* Crunch configuration: theory, naming scheme, lifting rules, wp rules *)
    type crunch_cfg = {ctxt: local_theory, prp_name: string, nmspce: string option,
        wps: (string * thm) list, igs: string list, simps: thm list, ig_dels: string list,
        rules: thm list};

    (* Crunch takes a configuration, a precondition, any extra information needed, a debug stack,
    a constant name, and a list of previously proven theorems, and returns a theorem for
    this constant and a list of new theorems (which may be empty if the result
    had already been proven). *)
    val crunch :
       crunch_cfg -> term -> extra -> string list -> string
         -> (string * thm) list ->  (thm option * (string * thm) list);

    val crunch_x : Token.src list -> string -> string -> (string * xstring) list
         -> string list -> local_theory -> local_theory;

    val crunch_ignore_add_del : string list -> string list -> theory -> theory

    val mism_term_trace : (term * extra) list Unsynchronized.ref
end

functor Crunch (Instance : CrunchInstance) =
struct

type extra = Instance.extra;

type crunch_cfg = {ctxt: local_theory, prp_name: string, nmspce: string option,
    wps: (string * thm) list, igs: string list, simps: thm list, ig_dels: string list,
    rules: thm list};

structure CrunchIgnore = Generic_Data
(struct
    type T = string list
    val empty = []
    val extend = I
    val merge = Library.merge (op =);
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

fun real_const_from_name const nmspce ctxt =
    let
      val qual::locale::nm::nil = Long_Name.explode const;
      val SOME some_nmspce = nmspce;
      val nm = Long_Name.implode (some_nmspce :: nm :: nil);
      val _ = read_const ctxt nm;
     in
       nm
     end
     handle exn => handle_int exn const;


fun get_monad ctxt f xs = if is_Const f then
    (* we need the type of the underlying constant to avoid polymorphic
       constants like If, case_option, K_bind being considered monadic *)
    let val T = dest_Const f |> fst |> read_const ctxt |> type_of;

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

fun monads_of ctxt t = case strip_comb t of
    (Const f, xs) => get_monad ctxt (Const f) xs @ maps (monads_of ctxt) xs
  | (Abs (_, _, t), []) => monads_of ctxt t
  | (Abs a, xs) => monads_of ctxt (betapplys (Abs a, xs))
  | (_, xs) => maps (monads_of ctxt) xs;


val get_thm = Proof_Context.get_thm

val get_thms = Proof_Context.get_thms

fun maybe_thms thy name = get_thms thy name handle ERROR _ => []
fun thy_maybe_thms thy name = Global_Theory.get_thms thy name handle ERROR _ => []

fun add_thm thm atts name ctxt =
  Local_Theory.notes [((Binding.name name, atts), [([thm], atts)])] ctxt |> #2

fun get_thm_name_bluh (cfg: crunch_cfg) const_name
  = Long_Name.base_name const_name ^ "_" ^ (#prp_name cfg)

fun get_thm_name (cfg : crunch_cfg) const_name
  = if read_const (#ctxt cfg) (Long_Name.base_name const_name)
         = read_const (#ctxt cfg) const_name
      then Long_Name.base_name const_name ^ "_" ^ (#prp_name cfg)
      else space_implode "_" (space_explode "." const_name @ [#prp_name cfg])

fun get_stored cfg n = get_thm (#ctxt cfg) (get_thm_name cfg n)

fun get_stored_bluh cfg n =
  let val r = (maybe_thms (#ctxt cfg) (get_thm_name cfg n)) @ (maybe_thms (#ctxt cfg) (get_thm_name_bluh cfg n));
      in (case r of [] => error ("") | _ => (hd r))
  end

fun mapM _ [] y = y
  | mapM f (x::xs) y = mapM f xs (f x y)

fun dest_equals t = t |> Logic.dest_equals
  handle TERM _ => t |> HOLogic.dest_Trueprop |> HOLogic.dest_eq;

fun const_is_lhs const nmspce ctxt def =
    let
      val (lhs, _) = def |> Thm.prop_of |> dest_equals;
      val (nm, _)  = dest_Const const;
      val (nm', _) = dest_Const (head_of lhs);
    in
      (real_const_from_name nm nmspce ctxt) = (real_const_from_name nm' nmspce ctxt)
    end handle TERM _ => false

fun deep_search_thms ctxt defn const nmspce =
    let
      val thy  = Proof_Context.theory_of ctxt
      val thys = thy :: Theory.ancestors_of thy;
      val filt = filter (const_is_lhs const nmspce ctxt);

      fun search [] = error("not found: const: " ^ @{make_string} const ^ " defn: " ^ @{make_string} defn)
        | search (t::ts) = (case (filt (thy_maybe_thms t defn)) of
              [] => search ts
	    | thms => thms);
    in
      case filt (maybe_thms ctxt defn) of
          [] => search thys
        | defs => defs
     end;

val unfold_get_params = @{thms Let_def return_bind returnOk_bindE
    K_bind_def split_def bind_assoc bindE_assoc
    trans[OF liftE_bindE return_bind]};

fun def_from_ctxt ctxt const =
  let
    val crunch_defs = Named_Theorems.get ctxt @{named_theorems crunch_def}
    val abs_def = Local_Defs.meta_rewrite_rule ctxt #> Drule.abs_def;
    fun do_filter thm =
    let
      val (Const (nm, _), _) = Logic.dest_equals (Thm.prop_of (abs_def thm));
    in nm = const end
  in
   case crunch_defs |> filter do_filter of
     [x] => [x]
   | [] => []
   | _ => raise Fail ("Multiple definitions declared for:" ^ const)
  end

fun unfold ctxt const triple nmspce =
    let
      val _ = debug_trace "unfold"
      val const_term = read_const ctxt const;
      val const_defn = const |> Long_Name.base_name |> def_of;
      val const_def = deep_search_thms ctxt const_defn const_term nmspce
                        |> hd |> Simpdata.safe_mk_meta_eq;
      val _ = Pretty.writeln (Pretty.block [Pretty.str ("const_def: " ^ @{make_string} const_defn), Thm.pretty_thm ctxt const_def])
      val trivial_rule = Thm.trivial triple
      val _ = Pretty.writeln (Pretty.block [Pretty.str "trivial_rule: ", Thm.pretty_thm ctxt trivial_rule])
      val unfold_rule = trivial_rule
        |> Simplifier.rewrite_goals_rule ctxt [const_def];
      val _ = Pretty.writeln (Pretty.block [Pretty.str "unfold_rule: ", Thm.pretty_thm ctxt unfold_rule])
      val ms = unfold_rule
        |> Simplifier.rewrite_goals_rule ctxt unfold_get_params
        |> Thm.prems_of |> maps (monads_of ctxt);
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

fun resolve_abbreviated ctxt abbrev =
  let
      val (abbrevn,_) = dest_Const abbrev
      val origin = (head_of (snd ((Consts.the_abbreviation o Proof_Context.consts_of) ctxt abbrevn)));
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

fun induct_inst ctxt const goal nmspce =
    let
      val _ = debug_trace "induct_inst"
      val base_const = Long_Name.base_name const;
      val _ = debug_trace ("base_const: " ^ @{make_string} base_const)
      val induct_thm = base_const |> induct_of |> get_thm ctxt;
      val _ = debug_trace ("induct_thm: " ^ @{make_string} induct_thm)
      val const_term = read_const ctxt const |> map_unvarifyT;
      val n = const_term |> fastype_of |> num_args;
      val t = mk_abs (Instance.magic $ mk_apps const_term n 0) n
              |> Syntax.check_term ctxt |> Logic.varify_global |> Thm.cterm_of ctxt;
      val P = Thm.concl_of induct_thm |> HOLogic.dest_Trueprop |> head_of |> Term.dest_Var;
      val trivial_rule = Thm.trivial goal;
      val induct_inst = Thm.instantiate ([], [(P, t)]) induct_thm
                        RS trivial_rule;
      val _ = debug_trace ("induct_inst" ^ Syntax.string_of_term ctxt (Thm.prop_of induct_inst));
      val simp_thms = deep_search_thms ctxt (base_const |> simps_of) const_term nmspce;
      val induct_inst_simplified = induct_inst
        |> Simplifier.rewrite_goals_rule ctxt (map Simpdata.safe_mk_meta_eq simp_thms);
      val ms = maps (monads_of ctxt) (Thm.prems_of induct_inst_simplified);
      val ms' = filter_out (eq_cname (resolve_abbreviated ctxt const_term) o head_of) ms;
    in if Thm.eq_thm_prop (trivial_rule, induct_inst)
       then error ("Unfold rule generated for " ^ const ^ " does not apply")
       else (ms', induct_inst) end

fun unfold_data ctxt constn goal nmspce nil = (
    induct_inst ctxt constn goal nmspce handle exn => handle_int exn
    unfold ctxt constn goal nmspce handle exn => handle_int exn
    error ("unfold_data: couldn't find defn or induct rule for " ^ constn))
  | unfold_data ctxt constn goal _ [(_, thm)] =
    let
      val trivial_rule = Thm.trivial goal
      val unfold_rule = Simplifier.rewrite_goals_rule ctxt [safe_mk_meta_eq thm] trivial_rule;
      val ms = unfold_rule
        |> Simplifier.rewrite_goals_rule ctxt unfold_get_params
        |> Thm.prems_of |> maps (monads_of ctxt);
    in if Thm.eq_thm_prop (trivial_rule, unfold_rule)
       then error ("Unfold rule given for " ^ constn ^ " does not apply")
       else (ms, unfold_rule) end
  | unfold_data _ constn _ _ _ = error ("Multiple unfolds are given for " ^ constn)



val split_if = @{thm "if_split"}

fun maybe_cheat_tac ctxt thm =
  if (Goal.skip_proofs_enabled ())
  then ALLGOALS (Skip_Proof.cheat_tac ctxt) thm
  else all_tac thm;

fun var_precond v =
  if Instance.has_preconds
  then Instance.put_precond (Var (("Precond", 0), Instance.get_precond v |> fastype_of)) v
  else v;

fun is_proof_of cfg const (name, _) =
  get_thm_name cfg const = name

fun get_inst_precond ctxt pre extra (mapply, goal) = let
    val (c, xs) = strip_comb mapply;
    fun replace_vars (t, n) =
      if exists_subterm (fn t => is_Bound t orelse is_Var t) t
        then Free ("ignore_me" ^ string_of_int n, dummyT)
      else t
    val ys = map replace_vars (xs ~~ (1 upto (length xs)));
    val goal2 = Instance.mk_term pre (list_comb (c, ys)) extra
      |> Syntax.check_term ctxt |> var_precond
      |> HOLogic.mk_Trueprop |> Thm.cterm_of ctxt;
    val spec = goal RS Thm.trivial goal2;
    val precond = Thm.concl_of spec |> HOLogic.dest_Trueprop |> Instance.get_precond;
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

fun precond_needed ctxt pre css pre' = let
    val imp = Syntax.check_term ctxt (precond_implication_term $ pre $ pre');
  in Goal.prove ctxt [] [] imp
       (fn _ => clarsimp_tac css 1); false end
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

fun make_goal const_term const pre extra ctxt =
  let val nns = const_term |> fastype_of |> num_args |>
                          Name.invent Name.context param_name;
      val parse = Syntax.parse_term ctxt;
      val check = Syntax.check_term ctxt;
      val body = parse (String.concat (separate " " (const :: nns)));
  in check (Instance.mk_term pre body extra) end;

fun seq_try_apply f x = Seq.map_filter (try f) (Seq.single x)

fun crunch_known_rule cfg const const_long_name thms goal_prop =
  let
    val thms_proof = Seq.filter (is_proof_of cfg const) (Seq.of_list thms)
    val stored = seq_try_apply (get_stored cfg) const
    val ctxt = #ctxt cfg
    val cgoal_in = Goal.init (Thm.cterm_of ctxt goal_prop)
    val empty_ref = Unsynchronized.ref []
    val wps = Seq.filter (fn (s, t) => s = const_long_name andalso
                    (is_some o SINGLE (WeakestPre.apply_rules_tac_n false ctxt [t] empty_ref 1)) cgoal_in)
           (Seq.of_list (#wps cfg))
    val seq = Seq.append (Seq.map snd thms_proof) (Seq.append stored (Seq.map snd wps))
  in Seq.pull seq |> Option.map fst end

val mism_term_trace = Unsynchronized.ref []

fun crunch_rule cfg const goal extra thms =
  let
    (* first option: produce a terminal rule via wp *)
    val ctxt = #ctxt cfg
    val empty_ref = Unsynchronized.ref []
    fun wp rules = WeakestPre.apply_rules_tac_n false ctxt
        (map snd (thms @ #wps cfg) @ rules) empty_ref
    val vgoal_prop = goal |> var_precond |> HOLogic.mk_Trueprop
    val goal_prop = goal |> HOLogic.mk_Trueprop
    val ctxt' = Variable.auto_fixes goal_prop
        (Variable.auto_fixes vgoal_prop ctxt)
    val wp_seq = seq_try_apply (Goal.prove ctxt' [] [] goal_prop) (fn _ =>
                                  TRY (wp [] 1))
      |> Seq.map (singleton (Proof_Context.export ctxt' ctxt))
      |> Seq.map (pair NONE)

    (* second option: apply a supplied rule *)
    val cgoal = vgoal_prop |> Thm.cterm_of ctxt

    val base_rule = Thm.trivial cgoal
    fun app_rew r t = Seq.single (Simplifier.rewrite_goals_rule ctxt [r] t)
      |> Seq.filter (fn t' => not (Thm.eq_thm_prop (t, t')))
    val supplied_seq = Seq.of_list (#rules cfg)
      |> Seq.maps (fn r => Seq.append
        (resolve_tac ctxt [r] 1 base_rule) (app_rew r base_rule))
      |> Seq.map (pair NONE)

    (* third option: builtins *)
    val unfolds' = (map (pair "") (def_from_ctxt ctxt const))
    val unf_seq = Seq.map (unfold_data ctxt' const cgoal (#nmspce cfg))
          (Seq.single unfolds')
      |> Seq.map (apfst SOME)

    val seq = foldr1 (uncurry Seq.append) [wp_seq, supplied_seq, unf_seq]

    fun fail_tac t _ _ = (writeln "discarding crunch rule, unsolved premise:";
      Syntax.pretty_term ctxt t |> Pretty.writeln;
      mism_term_trace := (t, extra) :: (! mism_term_trace);
      Seq.empty)
    val goal_extra = goal |> Instance.dest_term |> the |> #3
    val finalise = ALLGOALS (SUBGOAL (fn (t, i)
          => if try (Logic.strip_assums_concl #> HOLogic.dest_Trueprop
                #> Instance.dest_term #> the #> #3 #> curry Instance.eq_extra goal_extra)
            t = SOME true
          then all_tac
          else DETERM (((wp [] ORELSE' simp_tac ctxt) THEN_ALL_NEW fail_tac t) i)))

    val seq = Seq.maps (fn (ms, t) => Seq.map (pair ms) (finalise t)) seq

    val (ms, thm) = case Seq.pull seq of SOME ((ms, thm), _) => (ms, thm)
      | NONE => error ("could not find crunch rule for " ^ const)

    val _ = Pretty.writeln (Pretty.block
        [Pretty.str "crunch rule: ", Thm.pretty_thm ctxt thm])

    val ms = case ms of SOME ms => ms
        | NONE => Thm.prems_of thm |> maps (monads_of ctxt)
  in (ms, thm) end

fun crunch cfg pre extra stack const' thms =
  let
    val ctxt = #ctxt cfg |> Context_Position.set_visible false;
    val const = real_const_from_name const' (#nmspce cfg) ctxt;
    val empty_ref = Unsynchronized.ref [] : thm list Unsynchronized.ref (* FIXME: avoid refs *)
  in
    let
      val _ = "crunching constant: " ^ const |> writeln;
      val const_term = read_const ctxt const;
      val real_const_term = resolve_abbreviated ctxt const_term;
      val goal = make_goal const_term const pre extra ctxt
                 handle exn => handle_int exn (raise WrongType);
      val goal_prop = HOLogic.mk_Trueprop goal;
      val const_long_name = real_const_term |> dest_Const |> fst;
    in (* first check: has this constant already been done or supplied? *)
      case crunch_known_rule cfg const const_long_name thms goal_prop
        of SOME thm => (SOME thm, [])
          | NONE => let (* not already known, find a crunch rule. *)
          val (ms, rule) = crunch_rule cfg const goal extra thms
            (* and now crunch *)
          val ctxt' = Variable.auto_fixes goal ctxt;
          val ms = ms
            |> map (fn t => (real_const_from_name (fst (dest_Const (head_of t))) (#nmspce cfg) ctxt', t))
            |> subtract (fn (a, b) => a = (fst b))
                      (subtract (op =) (#ig_dels cfg) (#igs cfg @ CrunchIgnore.get (Context.Proof ctxt')))
            |> filter_out (fn (s, _) => s = const');
          val stack' = const :: stack;
          val _ = if (length stack' > 20) then
                     (writeln "Crunch call stack:";
                      map writeln (const::stack);
                      error("probably infinite loop")) else ();
          val (goals, thms') = funkyfold (crunch cfg pre extra stack') (map fst ms) thms;
          val goals' = map_filter I goals
          val ctxt'' = ctxt' addsimps ((#simps cfg) @ goals')
              |> Splitter.del_split split_if

          fun collect_preconds pre =
            let val preconds = map_filter (fn (x, SOME y) => SOME (x, y) | (_, NONE) => NONE) (map snd ms ~~ goals)
                                                    |> map_filter (get_inst_precond ctxt'' pre extra);
              val precond = combine_preconds ctxt'' (Instance.get_precond goal) preconds;
            in Instance.put_precond precond goal |> HOLogic.mk_Trueprop end;
          val goal_prop2 = if Instance.has_preconds then collect_preconds pre else goal_prop;

          val ctxt''' = ctxt'' |> Variable.auto_fixes goal_prop2
          val _ = writeln ("attempting: " ^ Syntax.string_of_term ctxt''' goal_prop2);

          fun wp rules = WeakestPre.apply_rules_tac_n false ctxt
              (map snd (thms @ #wps cfg) @ rules) empty_ref

          val thm = Goal.prove_future ctxt''' [] [] goal_prop2
              ( (*DupSkip.goal_prove_wrapper *) (fn _ =>
              resolve_tac ctxt''' [rule] 1
                THEN maybe_cheat_tac ctxt'''
              THEN ALLGOALS (fn n =>
                simp_tac ctxt''' n
                THEN
                TRY (resolve_tac ctxt''' Instance.pre_thms n)
                THEN
                REPEAT_DETERM (
                  wp goals' n
                  ORELSE
                  CHANGED (clarsimp_tac ctxt''' n)
                  ORELSE
                  assume_tac ctxt''' n
                  ORELSE
                  Instance.wpc_tactic ctxt'''
                  ORELSE
                  safe_tac ctxt'''
                  ORELSE
                  CHANGED (simp_tac ctxt''' n)
              )))) |> singleton (Proof_Context.export ctxt''' ctxt)
              handle e =>
                     (writeln "Crunch call stack:";
                      map writeln (const::stack);
                      raise e)
        in (SOME thm, (get_thm_name cfg const, thm) :: thms') end
    end
    handle WrongType =>
      let val _ = writeln ("The constant " ^ const ^ " has the wrong type and is being ignored")
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

fun crunch_x atts extra prp_name wpigs consts ctxt =
    let
        fun const_name const = dest_Const (read_const ctxt const) |> #1

        val wps' = wpigs |> filter (fn (s,_) => s = wp_sect) |> map #2

        val wp_dels' = wpigs |> filter (fn (s,_) => s = wp_del_sect) |> map #2

        val simps = wpigs |> filter (fn (s,_) => s = simp_sect) |> map #2
                    |> maps (get_thms ctxt)

        val simp_dels = wpigs |> filter (fn (s,_) => s = simp_del_sect) |> map #2
                    |> maps (get_thms ctxt)

        val igs = wpigs |> filter (fn (s,_) => s = ignore_sect)
                        |> map (const_name o #2)

        val rules = wpigs |> filter (fn (s,_) => s = rule_sect) |> map #2
                          |> maps (get_thms ctxt)
        val rules = rules @ Named_Theorems.get ctxt @{named_theorems crunch_rules}

        val ig_dels = wpigs |> filter (fn (s,_) => s = ignore_del_sect)
                            |> map (const_name o #2)

        fun mk_wp thm =
           let val ms = Thm.prop_of thm |> monads_of ctxt;
                val m = if length ms = 1
                        then
                            hd ms |> head_of |> dest_Const |> fst
                        else
                            dummy_monad_name;
            in (m, thm) end;

        val wps = maps (get_thms ctxt) wps' |> map mk_wp;
        val full_const_names = map const_name consts;

        val nmspce = get_locale_origins full_const_names ctxt;
        val (pre', extra') = Instance.parse_extra ctxt extra

        (* check that the given constants match the type of the given property*)
        val const_terms = map (read_const ctxt) full_const_names;
        val _ = map (fn (const_term, const) => make_goal const_term const pre' extra' ctxt)
                    (const_terms ~~ full_const_names)

        val wp_dels = maps (get_thms ctxt) wp_dels';
        val ctxt' = fold (fn thm => fn ctxt => Thm.proof_attributes [WeakestPre.wp_del] thm ctxt |> snd)
                          wp_dels ctxt;

        val ctxt'' = ctxt' delsimps simp_dels;

        val (_, thms) = funkyfold (crunch {ctxt = ctxt'', prp_name = prp_name, nmspce = nmspce,
              wps = wps, igs = igs, simps = simps, ig_dels = ig_dels, rules = rules} pre' extra' [])
            full_const_names [];

        val atts' = map (Attrib.check_src ctxt) atts;

        val ctxt''' = fold (fn (name, thm) => add_thm thm atts' name) thms ctxt;
    in
        Pretty.writeln
          (Pretty.big_list "proved:"
                           (map (fn (n,t) =>
                                    Pretty.block
                                      [Pretty.str (n ^ ": "),
                                       Syntax.pretty_term ctxt (Thm.prop_of t)])
                                thms));
        ctxt'''
    end

end
(*
structure Crunch_Crunches : CRUNCH = Crunch;
*)
