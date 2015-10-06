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
 * The top-level "autocorres" command.
 *)
structure AutoCorres =
struct

(*
 * Option parsing for the autocorres command.
 * The most general form of the command is
 *   autocorres [ no_heap_abs = FUNC_NAMES,
 *                force_heap_abs = FUNC_NAMES,
 *       (* or *) skip_heap_abs,
 *
 *                heap_abs_syntax,
 *
 *                unsigned_word_abs = FUNC_NAMES,
 *                no_signed_word_abs = FUNC_NAMES,
 *       (* or *) skip_word_abs,
 *
 *                ts_rules = RULE_NAMES,
 *                ts_force RULE_NAME = FUNC_NAMES,
 *                ts_force ... = ...,
 *
 *                lifted_globals_field_prefix = "STRING",
 *                lifted_globals_field_suffix = "STRING",
 *                function_name_prefix = "STRING",
 *                function_name_suffix = "STRING",
 *
 *                trace_heap_lift = FUNC_NAMES,
 *                trace_word_abs = FUNC_NAMES,
 *                trace_opt,
 *                no_opt,
 *                gen_word_heaps,
 *                statistics,
 *                keep_going
 *              ]
 *              "prog.c"
 *)

(*
 * Most fields are wrapped in option so that the parser can work out
 * whether they have been specified already.
 *
 * Additionally, everything is a reference as a hack around the fact
 * that SML doesn't have field-updater syntax. There are other ways to
 * work around this, but this is a light-weight solution.
 *)
type autocorres_options = {
  (* Do not lift heaps for these functions. *)
  no_heap_abs : string list option ref,

  (* Insist the the following functions should be lifted, even if our
   * heuristics claim it won't succeed. *)
  force_heap_abs : string list option ref,

  (* Skip heap lifting for the whole program. *)
  skip_heap_abs : bool option ref,

  (* Enable unsigned word abstraction for these functions. *)
  unsigned_word_abs : string list option ref,

  (* Disable signed word abstraction for these functions. *)
  no_signed_word_abs : string list option ref,

  (* Skip word abstraction for the whole program. *)
  skip_word_abs : bool option ref,

  (* Only lift to these monads. *)
  ts_rules : string list option ref,

  (* Force functions to be lifted to certain monads.
     The symtab is keyed on function name. *)
  ts_force : string Symtab.table ref,

  (* Create some funky syntax for heap operations. *)
  heap_abs_syntax: bool option ref,

  (* Allow set of functions to translated to be limited. *)
  scope: string list option ref,
  scope_depth: int option ref,

  (* Store detailed traces for conversions of the selected functions. *)
  trace_heap_lift : string list option ref,
  trace_word_abs : string list option ref,

  (* Disable L1Peephole, L2Peephole and L2Opt rules. *)
  no_opt : bool option ref,

  (* Trace simplification rules. Note that some simplification is performed even with no_opt set. *)
  trace_opt : bool option ref,

  (* Define word{8,16,32,64} heaps even if the program does not use them. *)
  gen_word_heaps : bool option ref,

  print_stats : bool option ref,

  keep_going : bool option ref,

  (* Change generated names for lifted_globals fields *)
  lifted_globals_field_prefix : string option ref,
  lifted_globals_field_suffix : string option ref,

  (* Change generated function names *)
  function_name_prefix : string option ref,
  function_name_suffix : string option ref
}

(* Get all that the given function depends on, up to "depth" functions deep. *)
fun get_function_deps get_callees roots depth =
let
  fun get_recursive_callees d root results =
    if d = 0 orelse Symset.contains results root then
      Symset.empty
    else
      fold (fn n => fn r => Symset.union (get_recursive_callees (d - 1) n r) r)
          (get_callees root) (Symset.insert root results)
in
  Symset.union_sets (map (fn root =>
      get_recursive_callees depth root Symset.empty) roots)
end

(* Convert the given reference from "NONE" to "SOME x", emitting an
 * error if the value is already non-NONE. *)
fun none_to_some ref_field new_value error_msg opt =
    case !(ref_field opt) of
      NONE => ((ref_field opt) := SOME new_value; opt)
    | SOME _ => error error_msg

(* Parsing expectations. *)
fun expect x y = !! (K (K ("autocorres: expected " ^ y ^ " after " ^ x)))

(* Generic parser for "NAME = THING" *)
fun named_option parser name elem_desc=
  Parse.reserved name |--
  expect (quote name) "\"=\"" (Parse.$$$ "=" |--
  expect "\"=\"" elem_desc parser)

(* Generic parser for "NAME = STRING ..." *)
val named_opt = named_option (Scan.repeat Parse.text)

(* Generic parser for "NAME = <nat>" *)
val nat_opt = named_option Parse.nat

(* Valid options. *)
val no_heap_abs_parser =
  named_opt "no_heap_abs" "function names" >>
  (fn funcs => none_to_some (#no_heap_abs) funcs "autocorres: no_heap_abs option specified multiple times")

val force_heap_abs_parser =
  named_opt "force_heap_abs" "function names" >>
  (fn funcs => none_to_some (#force_heap_abs) funcs "autocorres: force_heap_abs option specified multiple times")

val skip_heap_abs_parser =
  Parse.reserved "skip_heap_abs" >>
  (fn _ => none_to_some (#skip_heap_abs) true "autocorres: skip_heap_abs option specified multiple times")

val ts_rules_parser =
  named_opt "ts_rules" "rule names" >>
  (fn rules => none_to_some (#ts_rules) rules "autocorres: ts_rules option specified multiple times")

val scope_parser =
  named_opt "scope" "function names" >>
  (fn funcs => none_to_some (#scope) funcs "autocorres: scope option specified multiple times")

val scope_depth_parser =
  nat_opt "scope_depth" "integer" >>
  (fn value => none_to_some (#scope_depth) value "autocorres: scope option specified multiple times")

val ts_force_parser =
  ((Parse.reserved "ts_force" |--
      expect "\"ts_force\"" "rule name"
      (Parse.text :-- (fn name => expect name "\"=\"" (Parse.$$$ "="))) --
    Scan.repeat Parse.text)) >>
  (fn ((rule, _), funcs) => fn opt =>
    let
      val _ =
        (#ts_force opt) :=
          (fold (fn func => (fn table =>
              Symtab.update_new (func, rule) table
              handle Symtab.DUP _ =>
                error ("autocorres: function " ^ quote func
                    ^ " is already being forced to a particular type.")
              )) funcs (!(#ts_force opt)))
    in
      opt
    end)

val unsigned_word_abs_parser =
  named_opt "unsigned_word_abs" "function names" >>
  (fn funcs => none_to_some (#unsigned_word_abs) funcs "autocorres: unsigned_word_abs option specified multiple times")

val no_signed_word_abs_parser =
  named_opt "no_signed_word_abs" "function names" >>
  (fn funcs => none_to_some (#no_signed_word_abs) funcs "autocorres: no_signed_word_abs option specified multiple times")

val skip_word_abs_parser =
  Parse.reserved "skip_word_abs" >>
  (fn _ => none_to_some (#skip_word_abs) true "autocorres: skip_word_abs option specified multiple times")

val heap_abs_syntax_parser =
  Parse.reserved "heap_abs_syntax" >>
  (fn _ => none_to_some (#heap_abs_syntax) true "autocorres: heap_abs_syntax option specified multiple times")

val trace_heap_lift_parser =
  named_opt "trace_heap_lift" "function names" >>
  (fn funcs => none_to_some (#trace_heap_lift) funcs "autocorres: trace_heap_lift option specified multiple times")

val trace_word_abs_parser =
  named_opt "trace_word_abs" "function names" >>
  (fn funcs => none_to_some (#trace_word_abs) funcs "autocorres: trace_word_abs option specified multiple times")

val no_opt_parser =
  Parse.reserved "no_opt" >>
  (fn _ => none_to_some (#no_opt) true "autocorres: no_opt option specified multiple times")

val trace_opt_parser =
  Parse.reserved "trace_opt" >>
  (fn _ => none_to_some (#trace_opt) true "autocorres: trace_opt option specified multiple times")

val gen_word_heaps_parser =
  Parse.reserved "gen_word_heaps" >>
  (fn _ => none_to_some (#gen_word_heaps) true "autocorres: gen_word_heaps option specified multiple times")

val print_stats_parser =
  Parse.reserved "statistics" >>
  (fn _ => none_to_some (#print_stats) true "autocorres: statistics option specified multiple times")

val keep_going_parser =
  Parse.reserved "keep_going" >>
  (fn _ => none_to_some (#keep_going) true "autocorres: keep_going option specified multiple times")

val lifted_globals_field_prefix_parser =
  named_option Parse.text "lifted_globals_field_prefix" "function names" >>
  (fn funcs => none_to_some (#lifted_globals_field_prefix) funcs
                 "autocorres: lifted_globals_field_prefix option specified multiple times")

val lifted_globals_field_suffix_parser =
  named_option Parse.text "lifted_globals_field_suffix" "function names" >>
  (fn funcs => none_to_some (#lifted_globals_field_suffix) funcs
                 "autocorres: lifted_globals_field_suffix option specified multiple times")

val function_name_prefix_parser =
  named_option Parse.text "function_name_prefix" "function names" >>
  (fn funcs => none_to_some (#function_name_prefix) funcs
                 "autocorres: function_name_prefix option specified multiple times")

val function_name_suffix_parser =
  named_option Parse.text "function_name_suffix" "function names" >>
  (fn funcs => none_to_some (#function_name_suffix) funcs
                 "autocorres: function_name_suffix option specified multiple times")

(*
 * Blank set of options.
 *
 * Because we are using references, we need to construct a new set every
 * time; hence the dummy parameter.
 *)
fun default_opts _ = {
    no_heap_abs = ref NONE,
    force_heap_abs = ref NONE,
    skip_heap_abs = ref NONE,
    unsigned_word_abs = ref NONE,
    no_signed_word_abs = ref NONE,
    skip_word_abs = ref NONE,
    ts_rules = ref NONE,
    ts_force = ref Symtab.empty,
    heap_abs_syntax = ref NONE,
    scope = ref NONE,
    scope_depth = ref NONE,
    trace_heap_lift = ref NONE,
    trace_word_abs = ref NONE,
    no_opt = ref NONE,
    trace_opt = ref NONE,
    gen_word_heaps = ref NONE,
    print_stats = ref NONE,
    keep_going = ref NONE,
    lifted_globals_field_prefix = ref NONE,
    lifted_globals_field_suffix = ref NONE,
    function_name_prefix = ref NONE,
    function_name_suffix = ref NONE
  }

(* Combined parser. *)
val autocorres_parser : (autocorres_options * string) parser =
let
  val option_parser =
    (no_heap_abs_parser ||
     force_heap_abs_parser ||
     skip_heap_abs_parser ||
     ts_rules_parser ||
     ts_force_parser ||
     unsigned_word_abs_parser ||
     no_signed_word_abs_parser ||
     skip_word_abs_parser ||
     heap_abs_syntax_parser ||
     scope_parser ||
     scope_depth_parser ||
     trace_heap_lift_parser ||
     trace_word_abs_parser ||
     no_opt_parser ||
     trace_opt_parser ||
     gen_word_heaps_parser ||
     print_stats_parser ||
     keep_going_parser ||
     lifted_globals_field_prefix_parser ||
     lifted_globals_field_suffix_parser ||
     function_name_prefix_parser ||
     function_name_suffix_parser)
    |> !! (fn xs => K ("autocorres: unknown option " ^ quote (Parse.text (fst xs) |> #1)))

  val options_parser = Parse.list option_parser >> (fn opt_fns => fold I opt_fns)
in
  (* Options *)
  (Scan.optional (Parse.$$$ "[" |-- options_parser --| Parse.$$$ "]") I
      >> (fn f => f (default_opts ()))) --
  (* Filename *)
  Parse.text
end



(*
 * Worker for the autocorres command.
 *)
fun do_autocorres (opt : autocorres_options) filename thy =
let
  (* Ensure that the filename has already been parsed by the C parser. *)
  val csenv = case CalculateState.get_csenv thy filename of
      NONE => error ("Filename '" ^ filename ^ "' has not been parsed by the C parser yet.")
    | SOME x => x

  (* Enter into the correct context. *)
  val {base = locale_name,...} = OS.Path.splitBaseExt (OS.Path.file filename)
  val lthy = Named_Target.begin (locale_name, Position.none) thy

  (* Fetch basic program information. *)
  val prog_info = ProgramInfo.get_prog_info lthy filename
  val fn_info = FunctionInfo.init_fn_info lthy filename
  val all_functions = Symset.make (Symtab.keys (FunctionInfo.get_functions fn_info))

  (* Process autocorres options. *)
  val keep_going = !(#keep_going opt) = SOME true

  val _ = if not (!(#unsigned_word_abs opt) = NONE) andalso not (!(#skip_word_abs opt) = NONE) then
              error "autocorres: unsigned_word_abs and skip_word_abs cannot be used together."
          else if not (!(#no_signed_word_abs opt) = NONE) andalso not (!(#skip_word_abs opt) = NONE) then
              error "autocorres: no_signed_word_abs and skip_word_abs cannot be used together."
          else ()
  val skip_word_abs = !(#skip_word_abs opt) = SOME true

  val _ = if not (!(#force_heap_abs opt) = NONE) andalso not (!(#skip_heap_abs opt) = NONE) then
              error "autocorres: force_heap_abs and skip_heap_abs cannot be used together."
          else if not (!(#no_heap_abs opt) = NONE) andalso not (!(#skip_heap_abs opt) = NONE) then
              error "autocorres: no_heap_abs and skip_heap_abs cannot be used together."
          else ()
  val no_heap_abs = if !(#skip_heap_abs opt) = SOME true then Symset.dest all_functions else these (!(#no_heap_abs opt))

  (* Disallow referring to functions that don't exist. *)
  val funcs_in_options =
        these (!(#no_heap_abs opt))
        @ these (!(#force_heap_abs opt))
        @ these (!(#unsigned_word_abs opt))
        @ these (!(#no_signed_word_abs opt))
        @ these (!(#scope opt))
        @ Symtab.keys (!(#ts_force opt))
        @ these (!(#trace_heap_lift opt))
        @ these (!(#trace_word_abs opt))
  val invalid_functions =
        Symset.subtract all_functions (Symset.make funcs_in_options)
  val _ =
    if Symset.card invalid_functions > 0 then
      error ("autocorres: no such function(s): " ^ commas (Symset.dest invalid_functions))
    else ()

  (* Resolve rule names for ts_rules and ts_force. *)
  val ts_force = Symtab.map (K (fn name => Monad_Types.get_monad_type name (Context.Proof lthy)
                                  |> the handle Option => Monad_Types.error_no_such_mt name))
                            (!(#ts_force opt))
  val ts_rules = Monad_Types.get_ordered_rules (these (!(#ts_rules opt))) (Context.Proof lthy)

  (* heap_abs_syntax defaults to off. *)
  val heap_abs_syntax = !(#heap_abs_syntax opt) = SOME true

  (* Ensure that we are not both forcing and preventing a function from being heap lifted. *)
  val conflicting_heap_lift_fns =
      Symset.inter (Symset.make (these (!(#no_heap_abs opt)))) (Symset.make (these (!(#force_heap_abs opt))))
  val _ = if not (Symset.is_empty conflicting_heap_lift_fns) then
            error ("autocorres: Functions are declared as both 'no_heap_abs' and 'force_heap_abs': "
                  ^ commas (Symset.dest conflicting_heap_lift_fns))
          else
            ()

  (* Check that recursive function groups are all lifted to the same monad. *)
  val _ = FunctionInfo.get_topo_sorted_functions fn_info
          |> map (TypeStrengthen.compute_lift_rules ts_rules ts_force)

  (* (Finished processing options.) *)

  (* Strip out functions that shouldn't be processed. *)
  val fn_info =
    case !(#scope opt) of
        NONE => fn_info
      | SOME x =>
        let
          val scope_depth = the_default 2 (!(#scope_depth opt))
          val valid_functions =
            (get_function_deps (FunctionInfo.get_function_callees fn_info) x scope_depth)
        in
          FunctionInfo.map_fn_info (fn def =>
            if Symset.contains valid_functions (#name def) then SOME def else NONE) fn_info
          |> (fn fi => (let val fns = FunctionInfo.get_functions fi |> Symtab.dest |> map fst
                            val _ = @{trace} ("autocorres scope: selected " ^ Int.toString (length fns) ^ " functions:")
                        in map (fn f => @{trace} f) fns end; fi))
        end
  val all_functions = Symset.make (Symtab.keys (FunctionInfo.get_functions fn_info))

  (*
   * Sanity check the C parser's output.
   *
   * In the past, the C parser has defined terms that haven't type-checked due
   * to sort constraints on constants. This doesn't violate the Isabelle
   * kernel's soundness, but does wreck havoc on us.
   *)
  val sanity_errors = AutoCorresUtil.map_all lthy fn_info (fn fn_name =>
    let
      val def =
        FunctionInfo.get_function_def fn_info fn_name
        |> #definition
        |> Thm.prop_of
        |> Utils.rhs_of
    in
      (Syntax.check_term lthy def; NONE)
      handle (ERROR str) => SOME (fn_name, str)
    end)
    |> map_filter I
  val _ =
    if length sanity_errors > 0 then
      error ("C parser failed sanity checks. Erroneous functions: "
          ^ commas (map fst sanity_errors))
    else
      ()

  val do_opt = !(#no_opt opt) <> SOME true
  val trace_opt = !(#trace_opt opt) = SOME true
  val gen_word_heaps = !(#gen_word_heaps opt) = SOME true

  (* Any function that was declared in the C file (but never defined) should
   * stay in the nondet-monad unless explicitly instructed by the user to be
   * something else. *)
  val ts_force = let
    val invented_functions =
      all_functions
      (* Select functions with an invented body. *)
      |> Symset.filter (fn n => FunctionInfo.get_function_def fn_info n |> #invented_body)
      (* Ignore functions which already have a "ts_force" rule applied to them. *)
      |> Symset.subtract (Symset.make (Symtab.keys ts_force))
      |> Symset.dest
  in
    (* Use the most general monadic type allowed by the user. *)
    fold (fn n => Symtab.update_new (n, List.last ts_rules)) invented_functions ts_force
  end

  (* Prefixes/suffixes for generated names. *)
  val make_lifted_globals_field_name = let
    val prefix = case !(#lifted_globals_field_prefix opt) of
                     NONE => ""
                   | SOME p => p
    val suffix = case !(#lifted_globals_field_suffix opt) of
                     NONE => "_''"
                   | SOME s => s
  in fn f => prefix ^ f ^ suffix end

  (* Prefixes/suffixes for generated names. *)
  val make_function_name = let
    val prefix = case !(#function_name_prefix opt) of
                     NONE => ""
                   | SOME p => p
    val suffix = case !(#function_name_suffix opt) of
                     NONE => "'"
                   | SOME s => s
  in fn f => prefix ^ f ^ suffix end

  (* Do the translation. *)
  val (lthy, fn_info) =
        SimplConv.translate_simpl
            filename fn_info
            do_opt trace_opt (prefix "l1_" o make_function_name) lthy
    |> (fn (lthy, fn_info) =>
        LocalVarExtract.translate_l2 filename fn_info do_opt trace_opt (prefix "l2_" o make_function_name) lthy)
    |> (fn (lthy, fn_info) =>
        HeapLift.system_heap_lift filename fn_info
            no_heap_abs (these (!(#force_heap_abs opt)))
            make_lifted_globals_field_name heap_abs_syntax keep_going
            (these (!(#trace_heap_lift opt))) do_opt trace_opt
            (prefix "hl_" o make_function_name) gen_word_heaps lthy)
    |> (fn (lthy, fn_info) =>
        if skip_word_abs then (lthy, fn_info) else
        WordAbstract.word_abstract
            filename fn_info (these (!(#unsigned_word_abs opt))) (these (!(#no_signed_word_abs opt)))
            (these (!(#trace_word_abs opt))) do_opt trace_opt
            (prefix "wa_" o make_function_name) lthy)
    |> (fn (lthy, fn_info) =>
        TypeStrengthen.type_strengthen
            ts_rules ts_force filename fn_info make_function_name
            keep_going do_opt lthy)
    |> (fn (lthy, fn_info) =>
        (lthy, fn_info))

  (* Save fn_info for future reference. *)
  val _ = @{trace} "Saving function info to AutoCorresFunctionInfo."
  val lthy = Local_Theory.background_theory (
	  AutoCorresFunctionInfo.map (fn tbl =>
	    Symtab.update (filename, fn_info) tbl)) lthy
in
  (* Exit context. *)
  Named_Target.exit lthy
end

end