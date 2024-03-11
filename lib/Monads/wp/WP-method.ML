(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

signature WP =
sig
  type wp_rules = {trips: thm list * (theory -> term -> term),
    rules: (int * thm) Net.net * int * (int * thm) list,
    splits: thm list, combs: thm list, unsafe_rules: thm list};

  val debug_get: Proof.context -> wp_rules;

  val get_rules: Proof.context -> thm list -> wp_rules;

  val apply_rules_tac_n: bool -> Proof.context -> thm list -> int -> tactic;
  val apply_rules_tac: bool -> Proof.context -> thm list -> tactic;
  val apply_once_tac: bool -> Proof.context -> thm list -> tactic;
  val apply_wp_args: (Proof.context -> Method.method) context_parser;

  val setup: theory -> theory;

  val wp_add: Thm.attribute;
  val wp_del: Thm.attribute;
  val splits_add: Thm.attribute;
  val splits_del: Thm.attribute;
  val combs_add: Thm.attribute;
  val combs_del: Thm.attribute;
  val wp_unsafe_add: Thm.attribute;
  val wp_unsafe_del: Thm.attribute;
end;

structure WeakestPre =
struct

type wp_rules = {trips: thm list * (theory -> term -> term),
    rules: (int * thm) Net.net * int * (int * thm) list,
    splits: thm list, combs: thm list, unsafe_rules: thm list};

fun accum_last_occurence' [] _ = ([], Termtab.empty)
  | accum_last_occurence' ((t, v) :: ts) tt1 = let
      val tm = Thm.prop_of t;
      val tt2 = Termtab.insert_list (K false) (tm, v) tt1;
      val (ts', tt3) = accum_last_occurence' ts tt2;
  in case Termtab.lookup tt3 tm of
        NONE => ((t, Termtab.lookup_list tt2 tm)  :: ts',
                    Termtab.update (tm, ()) tt3)
      | SOME _ => (ts', tt3)
  end;

fun accum_last_occurence ts =
        fst (accum_last_occurence' ts Termtab.empty);

fun flat_last_occurence ts =
  map fst (accum_last_occurence (map (fn v => (v, ())) ts));

fun dest_rules (trips, _, others) =
  rev (order_list (Net.entries trips @ others));

fun get_key trip_conv t = let
    val t' = Thm.concl_of t |> trip_conv (Thm.theory_of_thm t)
        |> Envir.beta_eta_contract;
  in case t' of Const (@{const_name Trueprop}, _) $
      (Const (@{const_name triple_judgement}, _) $ _ $ f $ _) => SOME f
    | _ => NONE end;

fun add_rule_inner trip_conv t (trips, n, others) = (
  case get_key trip_conv t of
      SOME k => (Net.insert_term (K false)
                 (k, (n, t)) trips, n + 1, others)
    | _ => (trips, n + 1, (n, t) :: others)
  );

fun del_rule_inner trip_conv t (trips, n, others) =
    case get_key trip_conv t of
      SOME k => (Net.delete_term_safe (Thm.eq_thm_prop o apply2 snd)
                 (k, (n, t)) trips, n, others)
    | _ => (trips, n, remove (Thm.eq_thm_prop o apply2 snd) (n, t) others)

val no_rules = (Net.empty, 0, []);

fun mk_rules trip_conv rules = fold_rev (add_rule_inner trip_conv) rules no_rules;

fun mk_trip_conv trips thy = Pattern.rewrite_term thy
    (map (Thm.concl_of #> HOLogic.dest_Trueprop #> HOLogic.dest_eq) trips) []

fun rules_merge (wp_rules, wp_rules') = let
    val trips = Thm.merge_thms (fst (#trips wp_rules), fst (#trips wp_rules'));
    val trip_conv = mk_trip_conv trips
    val rules = flat_last_occurence (dest_rules (#rules wp_rules) @ dest_rules (#rules wp_rules'));
  in {trips = (trips, trip_conv),
        rules = mk_rules trip_conv rules,
        splits = Thm.merge_thms (#splits wp_rules, #splits wp_rules'),
        combs = Thm.merge_thms (#combs wp_rules, #combs wp_rules'),
        unsafe_rules = Thm.merge_thms (#unsafe_rules wp_rules, #unsafe_rules wp_rules')} end

structure WPData = Generic_Data
(struct
    type T = wp_rules;
    val empty = {trips = ([], K I), rules = no_rules,
      splits = [], combs = [], unsafe_rules = []};

    val merge = rules_merge;
end);

fun is_wp_rule ctxt thm =
let
  val ({rules, trips, ...}) = WPData.get (Context.Proof ctxt);
  val (triples, _, others) = rules;
  val trip_conv = (snd trips);
  val results = case get_key trip_conv thm of
    SOME k => Net.lookup triples (Net.key_of_term k)
  | NONE => others
in exists (fn (_, thm') => Thm.eq_thm_prop (thm, thm')) results end

fun add_rule rule rs =
    {trips = #trips rs,
      rules = add_rule_inner (snd (#trips rs)) rule (#rules rs),
      splits = #splits rs,
      combs = #combs rs,
      unsafe_rules = #unsafe_rules rs
    }

fun del_rule rule rs =
    {trips = #trips rs,
      rules = del_rule_inner (snd (#trips rs)) rule (#rules rs),
      splits = #splits rs,
      combs = #combs rs,
      unsafe_rules = #unsafe_rules rs
    }

fun add_trip rule (rs : wp_rules) = let
    val trips = Thm.add_thm rule (fst (#trips rs));
    val trip_conv = mk_trip_conv trips
  in {trips = (trips, trip_conv),
      rules = mk_rules trip_conv (dest_rules (#rules rs)),
      splits = #splits rs,
      combs = #combs rs,
      unsafe_rules = #unsafe_rules rs}
  end

fun del_trip rule (rs : wp_rules) = let
    val trips = Thm.del_thm rule (fst (#trips rs));
    val trip_conv = mk_trip_conv trips
  in {trips = (trips, trip_conv),
      rules = mk_rules trip_conv (dest_rules (#rules rs)),
      splits = #splits rs,
      combs = #combs rs,
      unsafe_rules = #unsafe_rules rs}
  end

fun add_split rule (rs : wp_rules) =
    {trips = #trips rs,
      rules = #rules rs,
      splits = Thm.add_thm rule (#splits rs),
      combs = #combs rs,
      unsafe_rules = #unsafe_rules rs}

fun add_comb rule (rs : wp_rules) =
    {trips = #trips rs, rules = #rules rs,
      splits = #splits rs, combs = Thm.add_thm rule (#combs rs),
      unsafe_rules = #unsafe_rules rs}

fun del_split rule rs =
    {trips = #trips rs, rules = #rules rs,
      splits = Thm.del_thm rule (#splits rs), combs = #combs rs,
      unsafe_rules = #unsafe_rules rs}

fun del_comb rule rs =
    {trips = #trips rs, rules = #rules rs,
      splits = #splits rs, combs = Thm.del_thm rule (#combs rs),
      unsafe_rules = #unsafe_rules rs}

fun add_unsafe_rule rule rs =
    {trips = #trips rs, rules = #rules rs,
      splits = #splits rs, combs = #combs rs,
      unsafe_rules = Thm.add_thm rule (#unsafe_rules rs)}

fun del_unsafe_rule rule rs =
    {trips = #trips rs, rules = #rules rs,
      splits = #splits rs, combs = #combs rs,
      unsafe_rules = Thm.del_thm rule (#unsafe_rules rs)}

fun gen_att m = Thm.declaration_attribute (fn thm => fn context => WPData.map (m thm) context);

val wp_add = gen_att add_rule;
val wp_del = gen_att del_rule;
val trip_add = gen_att add_trip;
val trip_del = gen_att del_trip;
val splits_add = gen_att add_split;
val splits_del = gen_att del_split;
val combs_add = gen_att add_comb;
val combs_del = gen_att del_comb;
val wp_unsafe_add = gen_att add_unsafe_rule;
val wp_unsafe_del = gen_att del_unsafe_rule;

val setup =
      Attrib.setup @{binding "wp"}
          (Attrib.add_del wp_add wp_del)
          "monadic weakest precondition rules"
      #> Attrib.setup @{binding "wp_trip"}
          (Attrib.add_del trip_add trip_del)
          "monadic triple conversion rules"
      #> Attrib.setup @{binding "wp_split"}
          (Attrib.add_del splits_add splits_del)
          "monadic split rules"
      #> Attrib.setup @{binding "wp_comb"}
          (Attrib.add_del combs_add combs_del)
          "monadic combination rules"
      #> Attrib.setup @{binding "wp_unsafe"}
          (Attrib.add_del wp_unsafe_add wp_unsafe_del)
          "unsafe monadic weakest precondition rules"

fun debug_get ctxt = WPData.get (Context.Proof ctxt);

fun get_rules ctxt extras = fold_rev add_rule extras (debug_get ctxt);

fun resolve_ruleset_tac' trace ctxt rs used_thms_ref n t =
  let
    val rtac = WP_Pre.rtac ctxt
    fun trace_rtac tag rule = WP_Pre.trace_rule trace ctxt used_thms_ref tag rtac rule
  in case
    Thm.cprem_of t n |> Thm.term_of |> snd (#trips rs) (Thm.theory_of_thm t)
        |> Envir.beta_eta_contract |> Logic.strip_assums_concl
     handle THM _ => @{const True}
  of Const (@{const_name Trueprop}, _) $
      (Const (@{const_name triple_judgement}, _) $ _ $ f $ _) =>
      let
        val rules = Net.unify_term (#1 (#rules rs)) f |> order_list |> rev;
        fun per_rule_combapp_tac rule combapp =
          let val insts_ref = Unsynchronized.ref (Trace_Schematic_Insts.empty_instantiations)
          in WP_Pre.trace_rule' trace ctxt
               (fn rule_insts => fn _ => insts_ref := rule_insts)
               rtac combapp
             THEN'
             WP_Pre.trace_rule' trace ctxt
               (fn rule_insts => fn _ =>
                  (WP_Pre.append_used_rule ctxt used_thms_ref "wp_comb" combapp (!insts_ref);
                   WP_Pre.append_used_rule ctxt used_thms_ref "wp" rule rule_insts))
               rtac rule
          end
        fun per_rule_tac rule =
          trace_rtac "wp" rule ORELSE'
          FIRST' (map (per_rule_combapp_tac rule) (#combs rs))
      in (FIRST' (map per_rule_tac rules) ORELSE'
          FIRST' (map (trace_rtac "wp_split") (#splits rs))) n t
      end
    | _ => FIRST' (map (trace_rtac "wp") (map snd (#3 (#rules rs))) @
                   map (trace_rtac "wp_split") (#splits rs)) n t
  end;

fun resolve_ruleset_tac trace ctxt rs used_thms_ref n =
  (Apply_Debug.break ctxt (SOME "wp")) THEN (resolve_ruleset_tac' trace ctxt rs used_thms_ref n)

fun warn_unsafe_rules unsafe_rules n ctxt t =
  let val used_thms_dummy = Unsynchronized.ref [] : (string * string * term) list Unsynchronized.ref;
      val ctxt' = (Config.put WP_Pre.wp_trace false ctxt |> Config.put WP_Pre.wp_trace_instantiation false)
      val useful_unsafe_rules =
          filter (fn rule =>
            (is_some o SINGLE (
              resolve_ruleset_tac false ctxt' (get_rules ctxt [rule]) used_thms_dummy n)) t)
            unsafe_rules
  in if not (null useful_unsafe_rules)
     then Pretty.list "Unsafe theorems that could be used: \n" ""
                      (map (ThmExtras.pretty_thm true ctxt) useful_unsafe_rules)
          |> Pretty.writeln
     else () end;

fun apply_rules_tac_n trace ctxt extras n =
let
  val trace' = trace orelse Config.get ctxt WP_Pre.wp_trace orelse Config.get ctxt WP_Pre.wp_trace_instantiation
  val used_thms_ref = Unsynchronized.ref [] : (string * string * term) list Unsynchronized.ref
  val rules = get_rules ctxt extras
  val wp_pre_tac = TRY (WP_Pre.pre_tac trace' ctxt
                                       (Named_Theorems.get ctxt \<^named_theorems>\<open>wp_pre\<close>)
                                       used_thms_ref 1)
  val wp_fix_tac = TRY (WPFix.both_tac ctxt 1)
  val cleanup_tac = TRY (REPEAT
                      (resolve_tac ctxt [@{thm TrueI}, @{thm conj_TrueI}, @{thm conj_TrueI2}] 1
                       ORELSE assume_tac ctxt 1))
  val steps_tac = (CHANGED (REPEAT_DETERM (resolve_ruleset_tac trace' ctxt rules used_thms_ref 1)))
                  THEN cleanup_tac
in
  SELECT_GOAL (
    (fn t => Seq.map (fn thm => (WP_Pre.trace_used_thms trace' ctxt used_thms_ref;
                                 used_thms_ref := []; thm))
                     ((wp_pre_tac THEN wp_fix_tac THEN steps_tac) t))
    THEN_ELSE
    (fn t => (warn_unsafe_rules (#unsafe_rules rules) 1 ctxt t; all_tac t),
     fn t => (warn_unsafe_rules (#unsafe_rules rules) 1 ctxt t; no_tac t))) n
end

fun apply_rules_tac trace ctxt extras = apply_rules_tac_n trace ctxt extras 1;

fun apply_once_tac trace ctxt extras t =
  let
    val trace' = trace orelse Config.get ctxt WP_Pre.wp_trace orelse Config.get ctxt WP_Pre.wp_trace_instantiation
    val used_thms_ref = Unsynchronized.ref [] : (string * string * term) list Unsynchronized.ref
    val rules = get_rules ctxt extras
  in Seq.map (fn thm => (WP_Pre.trace_used_thms trace' ctxt used_thms_ref; thm))
             (SELECT_GOAL (resolve_ruleset_tac trace' ctxt rules used_thms_ref 1) 1 t)
  end

fun clear_rules ({combs, rules, trips, splits, unsafe_rules}) =
  {combs=combs, rules=no_rules, trips=trips, splits=splits, unsafe_rules=unsafe_rules}

val wp_modifiers =
 [Args.add -- Args.colon >> K (I, wp_add),
  Args.del -- Args.colon >> K (I, wp_del),
  Args.$$$ "comb" -- Args.colon >> K (I, combs_add),
  Args.$$$ "comb" -- Args.add -- Args.colon >> K (I, combs_add),
  Args.$$$ "comb" -- Args.del -- Args.colon >> K (I, combs_del),
  Args.$$$ "only" -- Args.colon >> K (Context.proof_map (WPData.map clear_rules), wp_add)];

fun has_colon xs = exists (Token.keyword_with (curry (op =) ":")) xs;

fun if_colon scan1 scan2 xs = if has_colon (snd xs) then scan1 xs else scan2 xs;

(* FIXME: It would be nice if we could just use Method.sections, but to maintain
   compatability we require that the order of thms in each section is reversed. *)
fun thms ss = Scan.repeat (Scan.unless (Scan.lift (Scan.first ss)) Attrib.multi_thm) >> flat;
fun app (f, att) ths context = fold_map (Thm.apply_attribute att) ths (Context.map_proof f context);

fun section ss = Scan.depend (fn ctxt => (Scan.first ss -- Scan.pass ctxt (thms ss)) :|--
  (fn (m, thms) => Scan.succeed (swap (app m (rev thms) ctxt))));
fun sections ss = Scan.repeat (section ss);

val add_section = Scan.depend (fn ctxt => (Scan.pass ctxt Attrib.thms) :|--
  (fn thms => Scan.succeed (swap (app (I, wp_add) (rev thms) ctxt))));

fun modes ss =
  Scan.optional (Args.parens (Parse.list (Scan.first (map Args.$$$ ss)))
                 >> (fn strings => map (member (op =) strings) ss))
                (replicate (length ss) false);

fun apply_wp_args xs =
  let fun apply_tac once = if once then apply_once_tac else apply_rules_tac;
  in
    Scan.lift (modes ["trace", "once"])
      --| if_colon (sections wp_modifiers >> flat) add_section
    >> curry (fn ([trace, once], ctxt) => SIMPLE_METHOD (apply_tac once trace ctxt []))
  end xs;

end;

structure WeakestPreInst : WP = WeakestPre;
