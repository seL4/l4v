(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

signature WP =
sig
  type wp_rules = {trips: thm list * (theory -> term -> term),
    rules: (int * thm) Net.net * int * (int * thm) list,
    splits: thm list, combs: thm list, unsafe_rules: thm list};

  val debug_get: Proof.context -> wp_rules;

  val get_rules: Proof.context -> thm list -> wp_rules;

  val apply_rules_tac_n: bool -> Proof.context -> thm list -> thm list Unsynchronized.ref
                      -> int -> tactic;
  val apply_rules_tac: bool -> Proof.context -> thm list -> thm list Unsynchronized.ref
                    -> tactic;
  val apply_rules_args: bool -> (Proof.context -> Method.method) context_parser;

  val apply_once_tac: bool -> Proof.context -> thm list -> thm list Unsynchronized.ref
                   -> tactic;
  val apply_once_args: bool -> (Proof.context -> Method.method) context_parser;

  val setup: theory -> theory;
  val warn_unused: bool Config.T

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
    val extend = I;

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

fun append_used_rule rule used_rules = used_rules := !used_rules @ [rule]

fun add_extra_rule rule extra_rules = extra_rules := !extra_rules @ [rule]

fun resolve_ruleset_tac' ctxt rs used_rules_ref n t =
  let fun append_rule rule thm = Seq.map (fn thm => (append_used_rule rule used_rules_ref; thm)) thm;
  in case
    Thm.cprem_of t n |> Thm.term_of |> snd (#trips rs) (Thm.theory_of_thm t)
        |> Envir.beta_eta_contract |> Logic.strip_assums_concl
     handle THM _ => @{const True}
  of Const (@{const_name Trueprop}, _) $
      (Const (@{const_name triple_judgement}, _) $ _ $ f $ _) => let
        val ts = Net.unify_term (#1 (#rules rs)) f |> order_list |> rev;
        val combapps = Seq.maps (fn combapp => Seq.map
                                      (fn combapp' => (combapp, combapp')) (resolve_tac ctxt [combapp] n t))
                                (Seq.of_list (#combs rs)) |> Seq.list_of |> Seq.of_list;
        fun per_rule_tac t = (fn thm => append_rule t (resolve_tac ctxt [t] n thm)) ORELSE
                             (fn _ => Seq.maps (fn combapp => append_rule t
                                        (append_rule (#1 combapp) (resolve_tac ctxt [t] n (#2 combapp)))) combapps);
      in FIRST (map per_rule_tac ts) ORELSE
         FIRST (map (fn split => fn thm => append_rule split (resolve_tac ctxt [split] n thm)) (#splits rs)) end t
    | _ => FIRST (map (fn rule => fn thm => append_rule rule (resolve_tac ctxt [rule] n thm))
                      (map snd (#3 (#rules rs)) @ #splits rs)) t end;

fun resolve_ruleset_tac ctxt rs used_rules_ref n =
  (Apply_Debug.break ctxt (SOME "wp")) THEN (resolve_ruleset_tac' ctxt rs used_rules_ref n)

fun pretty_rule ctxt rule =
  Pretty.big_list (Thm.get_name_hint rule) [Thm.pretty_thm ctxt rule]
           |> Pretty.string_of;

fun trace_used_thms false _ _ = Seq.empty
  | trace_used_thms true used_rules ctxt =
      let val used_thms = !used_rules
      in map (fn rule => tracing (pretty_rule ctxt rule)) used_thms
        |> Seq.of_list end;

val warn_unused = Attrib.setup_config_bool @{binding wp_warn_unused} (K false);

fun warn_unused_thms ctxt thms extra_rules used_rules =
  if Config.get ctxt warn_unused
  then
    let val used_thms = map (fn rule => Thm.get_name_hint rule) (!used_rules)
        val unused_thms = map Thm.get_name_hint (!extra_rules @ thms) |> subtract (op =) used_thms
    in if not (null unused_thms)
       then "Unused theorems: " ^ commas_quote unused_thms |> warning
       else ()
    end
  else ()

fun warn_unsafe_thms unsafe_thms n ctxt t =
  let val used_rules = Unsynchronized.ref [] : thm list Unsynchronized.ref;
      val useful_unsafe_thms =
          filter (fn rule =>
            (is_some o SINGLE (
              resolve_ruleset_tac ctxt (get_rules ctxt [rule]) used_rules n)) t) unsafe_thms
      val unsafe_thm_names = map (fn rule => Thm.get_name_hint rule) useful_unsafe_thms
  in if not (null unsafe_thm_names)
     then "Unsafe theorems that could be used: " ^ commas_quote unsafe_thm_names |> warning
     else () end;

fun apply_rules_tac_n trace ctxt extras extras_ref n =
let
  val rules = get_rules ctxt extras;
  val used_rules = Unsynchronized.ref [] : thm list Unsynchronized.ref
  val wp_pre_tac = Method.NO_CONTEXT_TACTIC ctxt
                      (Method_Closure.apply_method ctxt @{method wp_pre} [] [] [] ctxt [])
  val wp_fix_tac = TRY (WPFix.both_tac ctxt 1)
  val cleanup_tac = TRY (REPEAT
                      (resolve_tac ctxt [@{thm TrueI}, @{thm conj_TrueI}, @{thm conj_TrueI2}] 1
                       ORELSE assume_tac ctxt 1))
  val steps_tac = (CHANGED (REPEAT_DETERM (resolve_ruleset_tac ctxt rules used_rules 1)))
                  THEN cleanup_tac
in
  SELECT_GOAL (
  (fn t => Seq.map (fn thm => (warn_unused_thms ctxt extras extras_ref used_rules;
                               trace_used_thms trace used_rules ctxt; thm))
    ((wp_pre_tac THEN wp_fix_tac THEN steps_tac) t)) THEN_ELSE
  (fn t => (warn_unsafe_thms (#unsafe_rules rules) 1 ctxt t; all_tac t),
  fn t => (warn_unsafe_thms (#unsafe_rules rules) 1 ctxt t; no_tac t))) n
end

fun apply_rules_tac trace ctxt extras extras_ref =
  apply_rules_tac_n trace ctxt extras extras_ref 1;

fun apply_once_tac trace ctxt extras extras_ref t =
  let
    val used_rules = Unsynchronized.ref [] : thm list Unsynchronized.ref;
  in Seq.map (fn thm => (warn_unused_thms ctxt extras extras_ref used_rules;
                         trace_used_thms trace used_rules ctxt; thm))
    (SELECT_GOAL (resolve_ruleset_tac ctxt (get_rules ctxt extras) used_rules 1) 1 t) end

fun clear_rules ({combs, rules, trips, splits, unsafe_rules}) =
  {combs=combs, rules=no_rules, trips=trips, splits=splits, unsafe_rules=unsafe_rules}

fun wp_modifiers extras_ref =
 [Args.add -- Args.colon >> K (I, fn att => (add_extra_rule (#2 att) extras_ref; wp_add att)),
  Args.del -- Args.colon >> K (I, wp_del),
  Args.$$$ "comb" -- Args.colon >> K (I, fn att => (add_extra_rule (#2 att) extras_ref; combs_add att)),
  Args.$$$ "comb" -- Args.add -- Args.colon >> K (I, fn att => (add_extra_rule (#2 att) extras_ref; combs_add att)),
  Args.$$$ "comb" -- Args.del -- Args.colon >> K (I, combs_del),
  Args.$$$ "only" -- Args.colon
    >> K (Context.proof_map (WPData.map clear_rules), fn att =>
                               (add_extra_rule (#2 att) extras_ref; wp_add att))];

fun has_colon xs = exists (Token.keyword_with (curry (op =) ":")) xs;

fun if_colon scan1 scan2 xs = if has_colon (snd xs) then scan1 xs else scan2 xs;

(* FIXME: It would be nice if we could just use Method.sections, but to maintain
   compatability we require that the order of thms in each section is reversed. *)
fun thms ss = Scan.repeat (Scan.unless (Scan.lift (Scan.first ss)) Attrib.multi_thm) >> flat;
fun app (f, att) ths context = fold_map (Thm.apply_attribute att) ths (Context.map_proof f context);

fun section ss = Scan.depend (fn context => (Scan.first ss -- Scan.pass context (thms ss)) :|--
  (fn (m, ths) => Scan.succeed (swap (app m (rev ths) context))));

fun sections ss = Scan.repeat (section ss);

fun apply_rules_args trace xs =
  let val extras_ref = Unsynchronized.ref [] : thm list Unsynchronized.ref;
  in
    if_colon
    (sections (wp_modifiers extras_ref) >>
      K (fn ctxt => SIMPLE_METHOD (apply_rules_tac trace ctxt [] extras_ref)))
    (Attrib.thms >> curry (fn (extras, ctxt) =>
      Method.SIMPLE_METHOD (
        apply_rules_tac trace ctxt extras extras_ref
      )
    ))
  end xs;

fun apply_once_args trace xs =
  let val extras_ref = Unsynchronized.ref [] : thm list Unsynchronized.ref;
  in
    if_colon
    (sections (wp_modifiers extras_ref) >>
      K (fn ctxt => SIMPLE_METHOD (apply_once_tac trace ctxt [] extras_ref)))
    (Attrib.thms >> curry (fn (extras, ctxt) =>
      Method.SIMPLE_METHOD (
        apply_once_tac trace ctxt extras extras_ref
      )
    ))
  end xs;

end;

structure WeakestPreInst : WP = WeakestPre;
