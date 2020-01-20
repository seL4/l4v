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
 * These options are documented in the README.md.
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

  (* Only translate a subset of functions. *)
  scope: string list option ref,
  scope_depth: int option ref,

  (* Do the translation in this locale (and use functions in this locale) *)
  c_locale: string option ref,

  (* Generate SIMPL wrappers that do not assert termination for the SIMPL.
   * Also generates ac_corres proofs minus the termination flag.
   * This option is for temporary CRefine compatibility. *)
  no_c_termination: bool option ref,

  (* Store detailed traces for conversions of the selected functions. *)
  trace_heap_lift : string list option ref,
  trace_word_abs : string list option ref,

  (* Disable L1Peephole, L2Peephole and L2Opt rules. *)
  no_opt : bool option ref,

  (* Trace simplification rules. Note that some simplification is performed even with no_opt set. *)
  trace_opt : bool option ref,

  (* Define word{8,16,32,64} heaps even if the program does not use them. *)
  gen_word_heaps : bool option ref,

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
  fun get_calleess fns = Symset.union_sets (fns :: map get_callees (Symset.dest fns))
in
  funpow depth get_calleess (Symset.make roots)
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

val c_locale_parser =
  named_option Parse.text "c_locale" "locale name" >>
  (fn funcs => none_to_some (#c_locale) funcs
                 "autocorres: c_locale option specified multiple times")

val no_c_termination_parser =
  Parse.reserved "no_c_termination" >>
  (fn _ => none_to_some (#no_c_termination) true "autocorres: no_c_termination option specified multiple times")

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

val keep_going_parser =
  Parse.reserved "keep_going" >>
  (fn _ => none_to_some (#keep_going) true "autocorres: keep_going option specified multiple times")

val lifted_globals_field_prefix_parser =
  named_option Parse.text "lifted_globals_field_prefix" "string" >>
  (fn funcs => none_to_some (#lifted_globals_field_prefix) funcs
                 "autocorres: lifted_globals_field_prefix option specified multiple times")

val lifted_globals_field_suffix_parser =
  named_option Parse.text "lifted_globals_field_suffix" "string" >>
  (fn funcs => none_to_some (#lifted_globals_field_suffix) funcs
                 "autocorres: lifted_globals_field_suffix option specified multiple times")

val function_name_prefix_parser =
  named_option Parse.text "function_name_prefix" "string" >>
  (fn funcs => none_to_some (#function_name_prefix) funcs
                 "autocorres: function_name_prefix option specified multiple times")

val function_name_suffix_parser =
  named_option Parse.text "function_name_suffix" "string" >>
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
    c_locale = ref NONE,
    no_c_termination = ref NONE,
    trace_heap_lift = ref NONE,
    trace_word_abs = ref NONE,
    no_opt = ref NONE,
    trace_opt = ref NONE,
    gen_word_heaps = ref NONE,
    keep_going = ref NONE,
    lifted_globals_field_prefix = ref NONE,
    lifted_globals_field_suffix = ref NONE,
    function_name_prefix = ref NONE,
    function_name_suffix = ref NONE
  } : autocorres_options

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
     c_locale_parser ||
     no_c_termination_parser ||
     trace_heap_lift_parser ||
     trace_word_abs_parser ||
     no_opt_parser ||
     trace_opt_parser ||
     gen_word_heaps_parser ||
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
  val locale_name = case !(#c_locale opt) of NONE => locale_name
                                           | SOME l => l
  val lthy = case try (Named_Target.begin (locale_name, Position.none)) thy of
                 SOME lthy => lthy
               | NONE => error ("autocorres: no such locale: " ^ locale_name)

  (* Fetch program information from the C-parser output. *)
  val prog_info = ProgramInfo.get_prog_info lthy filename
  val all_simpl_info = FunctionInfo.init_function_info lthy filename
  val all_simpl_functions = Symset.make (Symtab.keys all_simpl_info)

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
  val no_heap_abs = these (!(#no_heap_abs opt))

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

  (* (Finished processing options.) *)

  val existing_phases = Symtab.lookup (AutoCorresFunctionInfo.get thy) filename
  val _ = if not (isSome existing_phases) then () else
            tracing ("Attempting to restart from previous translation of " ^ filename)

  (* Fetch any existing translations, when being run in incremental mode. *)
  fun get_existing_optional_phase phase =
        case existing_phases of
            NONE => SOME Symtab.empty
          | SOME phases => FunctionInfo.Phasetab.lookup phases phase
  fun get_existing_phase phase =
        Option.getOpt (get_existing_optional_phase phase, Symtab.empty)
  val [existing_simpl_info,
       existing_l1_info,
       existing_l2_info,
       existing_hl_info,
       existing_wa_info,
       existing_ts_info] =
      map get_existing_phase
        [FunctionInfo.CP,
         FunctionInfo.L1,
         FunctionInfo.L2,
         FunctionInfo.HL,
         FunctionInfo.WA,
         FunctionInfo.TS]
  (* HL and WA functions may be missing if skip_heap_abs and skip_word_abs
   * are set. In that case, we carry forward the L2 or HL functions and
   * cross our fingers. (Should work fine if skip_foo is used consistently
   * for all functions, might not work if they are mixed.) *)
  val existing_hl_info = Utils.symtab_merge_with snd (existing_l2_info, existing_hl_info);
  val existing_wa_info = Utils.symtab_merge_with snd (existing_hl_info, existing_wa_info);

  (* Skip functions that have already been translated. *)
  val already_translated = Symset.make (Symtab.keys existing_ts_info)

  (* Determine which functions should be translated.
   * If "scope" is not specified, we translate all functions.
   * Otherwise, we translate only "scope"d functions and their direct callees
   * (which are translated using a trivial wrapper so that they can be called). *)
  val (functions_to_translate, functions_to_wrap) =
    case !(#scope opt) of
        NONE => (all_simpl_functions, Symset.empty)
      | SOME x =>
        let
          val scope_depth = the_default 2 (!(#scope_depth opt))
          val get_deps = get_function_deps (fn f =>
                           FunctionInfo.all_callees (the (Symtab.lookup all_simpl_info f)))
          val funcs = get_deps x scope_depth
          val _ = tracing ("autocorres scope: selected " ^ Int.toString (Symset.card funcs) ^ " function(s):")
          val _ = app (fn f => tracing ("  " ^ f)) (Symset.dest funcs)
          val funcs_callees =
            Symset.subtract (Symset.union already_translated funcs) (get_deps (Symset.dest funcs) 1)
          val _ = if Symset.is_empty funcs_callees then () else
                    (tracing ("autocorres scope: wrapping " ^
                       Int.toString (Symset.card funcs_callees) ^ " function(s):");
                     app (fn f => tracing ("  " ^ f)) (Symset.dest funcs_callees))
        in (funcs, funcs_callees) end

  (* Functions that have already been translated cannot be translated again. *)
  val already_translated = Symset.inter already_translated functions_to_translate
  val _ = if Symset.is_empty already_translated then () else
            error ("autocorres scope: these functions have already been translated: " ^
                   commas (Symset.dest already_translated))

  (* If a function has no SIMPL body, we will not wrap its body;
   * instead we create a dummy definition and translate it via the usual process. *)
  val undefined_functions =
        Symset.filter (fn f => #invented_body (the (Symtab.lookup all_simpl_info f))) functions_to_wrap
  val functions_to_wrap = Symset.subtract undefined_functions functions_to_wrap
  val functions_to_translate = Symset.union undefined_functions functions_to_translate

  (* We will process these functions... *)
  val functions_to_process = Symset.union functions_to_translate functions_to_wrap
  (* ... and ignore these functions. *)
  val functions_to_ignore = Symset.subtract functions_to_process all_simpl_functions

  (* Disallow referring to functions that don't exist or are excluded from processing. *)
  val funcs_in_options =
        these (!(#no_heap_abs opt))
        @ these (!(#force_heap_abs opt))
        @ these (!(#unsigned_word_abs opt))
        @ these (!(#no_signed_word_abs opt))
        @ these (!(#scope opt))
        @ Symtab.keys (!(#ts_force opt))
        @ these (!(#trace_heap_lift opt))
        @ these (!(#trace_word_abs opt))
        |> Symset.make
  val invalid_functions =
        Symset.subtract all_simpl_functions funcs_in_options
  val ignored_functions =
        Symset.subtract (Symset.union invalid_functions functions_to_process) funcs_in_options
  val _ =
    if Symset.card invalid_functions > 0 then
      error ("autocorres: no such function(s): " ^ commas (Symset.dest invalid_functions))
    else if Symset.card ignored_functions > 0 then
      error ("autocorres: cannot configure translation for excluded function(s): " ^
             commas (Symset.dest ignored_functions))
    else
      ()

  (* Only translate "scope" functions and their direct callees. *)
  val simpl_info =
        Symtab.dest all_simpl_info
        |> List.mapPartial (fn (name, info) =>
             if Symset.contains functions_to_translate name then
               SOME (name, FunctionInfo.function_info_upd_is_simpl_wrapper false info)
             else if Symset.contains functions_to_wrap name then
               SOME (name, FunctionInfo.function_info_upd_is_simpl_wrapper true info)
             else
               NONE)
        |> Symtab.make

  (* Recalculate callees after "scope" restriction. *)
  val (simpl_call_graph, simpl_info) = FunctionInfo.calc_call_graph simpl_info

  (* Check that recursive function groups are all lifted to the same monad. *)
  val _ = #topo_sorted_functions simpl_call_graph
          |> map (TypeStrengthen.compute_lift_rules ts_rules ts_force o Symset.dest)

  (* Disable heap lifting for all un-translated functions. *)
  val force_heap_abs = Symset.make (these (!(#force_heap_abs opt)))
  val conflicting_heap_lift_fns = Symset.subtract functions_to_translate force_heap_abs
  val _ = if not (Symset.is_empty conflicting_heap_lift_fns) then
            error ("autocorres: Functions marked 'force_heap_abs' but excluded from 'scope': "
                  ^ commas (Symset.dest conflicting_heap_lift_fns))
          else
            ()
  val no_heap_abs = Symset.union (Symset.make no_heap_abs) functions_to_wrap

  (* Disable word abstraction for all un-translated functions. *)
  val unsigned_word_abs = these (!(#unsigned_word_abs opt)) |> Symset.make
  val no_signed_word_abs = these (!(#no_signed_word_abs opt)) |> Symset.make
  val conflicting_unsigned_abs_fns =
        Symset.subtract functions_to_translate unsigned_word_abs
  val _ = if Symset.is_empty conflicting_unsigned_abs_fns then () else
            error ("autocorres: Functions marked 'unsigned_word_abs' but excluded from 'scope': "
                   ^ commas (Symset.dest conflicting_unsigned_abs_fns))
  val no_signed_word_abs = Symset.union no_signed_word_abs functions_to_wrap

  (*
   * Sanity check the C parser's output.
   *
   * In the past, the C parser has defined terms that haven't type-checked due
   * to sort constraints on constants. This doesn't violate the Isabelle
   * kernel's soundness, but does wreck havoc on us.
   *)
  val sanity_errors =
        Symtab.dest simpl_info
        |> List.mapPartial (fn (fn_name, info) =>
            case Symtab.lookup existing_l1_info fn_name of
                SOME _ => NONE (* already translated; ignore *)
              | _ => let
                       val def =
                         info
                         |> #definition
                         |> Thm.prop_of
                         |> Utils.rhs_of
                     in
                       (Syntax.check_term lthy def; NONE)
                       handle (ERROR str) => SOME (fn_name, str)
                     end)
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
      functions_to_process
      (* Select functions with an invented body. *)
      |> Symset.filter (Symtab.lookup simpl_info #> the #> #invented_body)
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

  (* Initialise database for traces.
   * Currently, this is implemented by mutating a global table.
   * While slightly ugly, it does simplify adding more tracing to AutoCorres
   * without cluttering the return types of existing code. *)
  val trace_db: AutoCorresData.Trace Symtab.table (* type *) Symtab.table (* func *) Synchronized.var =
        Synchronized.var "AutoCorres traces" Symtab.empty
  fun add_trace f_name trace_name trace =
        Synchronized.change trace_db
          (Symtab.map_default (f_name, Symtab.empty) (Symtab.update_new (trace_name, trace)))

  (* Do the translation. *)
  val l1_results =
        SimplConv.translate
            filename prog_info simpl_info existing_simpl_info existing_l1_info
            (!(#no_c_termination opt) <> SOME true)
            do_opt trace_opt add_trace (prefix "l1_" o make_function_name) lthy

  val l2_results =
        LocalVarExtract.translate
            filename prog_info l1_results existing_l1_info existing_l2_info
            do_opt trace_opt add_trace (prefix "l2_" o make_function_name)

  val skip_heap_abs = !(#skip_heap_abs opt) = SOME true
  val (hl_results, maybe_heap_info) =
        if skip_heap_abs
        then (l2_results, NONE)
        else let
          val (l2_results', HL_setup) =
                HeapLift.prepare_heap_lift
                    filename prog_info l2_results lthy all_simpl_info
                    make_lifted_globals_field_name gen_word_heaps heap_abs_syntax;
          in (HeapLift.translate
                 filename prog_info l2_results' existing_l2_info existing_hl_info
                 HL_setup no_heap_abs force_heap_abs
                 heap_abs_syntax keep_going
                 (these (!(#trace_heap_lift opt))) do_opt trace_opt add_trace
                (prefix "hl_" o make_function_name),
              SOME (#heap_info HL_setup))
          end

  val wa_results =
        if skip_word_abs
        then hl_results
        else WordAbstract.translate
               filename prog_info maybe_heap_info
               hl_results existing_hl_info existing_wa_info
               unsigned_word_abs no_signed_word_abs
               (these (!(#trace_word_abs opt))) do_opt trace_opt add_trace
               (prefix "wa_" o make_function_name)

  val ts_results =
        TypeStrengthen.translate
            ts_rules ts_force filename prog_info
            wa_results existing_wa_info existing_ts_info
            make_function_name keep_going do_opt add_trace

  (* Collect final translation results. *)
  val l1_info = FSeq.list_of l1_results |> map snd |> Utils.symtab_merge false;
  val l2_info = FSeq.list_of l2_results |> map snd |> Utils.symtab_merge false;
  val hl_info = if skip_heap_abs then Symtab.empty else
                  FSeq.list_of hl_results |> map snd |> Utils.symtab_merge false;
  val wa_info = if skip_word_abs then Symtab.empty else
                  FSeq.list_of wa_results |> map snd |> Utils.symtab_merge false;
  val ts_results' = FSeq.list_of ts_results;
  val ts_info = ts_results' |> map snd |> Utils.symtab_merge false;

  val lthy = if null ts_results' then lthy else fst (List.last ts_results');

  (* Put together final ac_corres theorems.
   * TODO: we should also store these as theory data. *)
  fun prove_ac_corres fn_name =
  let
    val l1_thm = #corres_thm (the (Symtab.lookup l1_info fn_name))
          handle Option => raise SimplConv.FunctionNotFound fn_name
    val l2_thm = #corres_thm (the (Symtab.lookup l2_info fn_name))
          handle Option => raise SimplConv.FunctionNotFound fn_name
    val hl_thm = #corres_thm (the (Symtab.lookup hl_info fn_name))
          (* If heap lifting was disabled, we use a placeholder *)
          handle Option => @{thm L2Tcorres_trivial_from_local_var_extract} OF [l2_thm]
    val wa_thm = #corres_thm (the (Symtab.lookup wa_info fn_name))
          (* Placeholder for when word abstraction is disabled *)
          handle Option => @{thm corresTA_trivial_from_heap_lift} OF [hl_thm]
    val ts_thm = #corres_thm (the (Symtab.lookup ts_info fn_name))
          handle Option => raise SimplConv.FunctionNotFound fn_name

  in let
       val final_thm = @{thm ac_corres_chain} OF [l1_thm, l2_thm, hl_thm, wa_thm, ts_thm]
       (* Remove fluff, like "f o id", that gets introduced by the HL and WA placeholders *)
       val final_thm' = Simplifier.simplify (put_simpset AUTOCORRES_SIMPSET lthy) final_thm
     in SOME final_thm' end
     handle THM _ =>
         (Utils.THM_non_critical keep_going
              ("autocorres: failed to prove ac_corres theorem for " ^ fn_name)
              0 [l1_thm, l2_thm, hl_thm, wa_thm, ts_thm];
          NONE)
  end

  val ac_corres_thms =
        Symtab.keys ts_info
        |> Par_List.map (fn f => Option.map (pair f) (prove_ac_corres f))
        |> List.mapPartial I

  val lthy = fold (fn (f, thm) =>
                     Utils.define_lemma (make_function_name f ^ "_ac_corres") thm #> snd)
                  ac_corres_thms lthy

  (* Name final mono theorems and add them to the simpset. *)
  val lthy =
        fold (fn (f, info) => fn lthy =>
                case #mono_thm info of
                    NONE => lthy
                  | SOME mono_thm =>
                      Utils.define_lemma (make_function_name f ^ "_mono") mono_thm lthy |> snd
                      |> Utils.simp_add [mono_thm])
              (Symtab.dest ts_info) lthy

  (* Save function info for future reference. *)
  val simpl_info' = Symtab.merge (K false) (existing_simpl_info, simpl_info);
  val l1_info' = Symtab.merge (K false) (existing_l1_info, l1_info);
  val l2_info' = Symtab.merge (K false) (existing_l2_info, l2_info);
  val hl_info' = Symtab.merge (K false) (existing_hl_info, hl_info);
  val wa_info' = Symtab.merge (K false) (existing_wa_info, wa_info);
  val ts_info' = Symtab.merge (K false) (existing_ts_info, ts_info);
  val new_results =
        FunctionInfo.Phasetab.make
          ([(FunctionInfo.CP, simpl_info'),
            (FunctionInfo.L1, l1_info'),
            (FunctionInfo.L2, l2_info'),
            (FunctionInfo.TS, ts_info')]
           @ (if skip_heap_abs andalso Symtab.is_empty existing_hl_info
              then [] else [(FunctionInfo.HL, hl_info')])
           @ (if skip_word_abs andalso Symtab.is_empty existing_wa_info
              then [] else [(FunctionInfo.WA, wa_info')])
          )

  val _ = tracing "Saving function info to AutoCorresFunctionInfo."
  val lthy = Local_Theory.background_theory (
          AutoCorresFunctionInfo.map (fn tbl =>
            Symtab.update (filename, new_results) tbl)) lthy
  (* All traces should be available at this point. Archive them. *)

  val traces = Synchronized.value trace_db;
  val _ = if Symtab.is_empty traces then () else
            tracing "Saving translation traces to AutoCorresData.Traces."
  val lthy = lthy |> Local_Theory.background_theory (
          AutoCorresData.Traces.map
            (Symtab.map_default (filename, Symtab.empty)
               (fn old_traces => Utils.symtab_merge_with snd (old_traces, traces))));

in
  (* Exit context. *)
  Named_Target.exit lthy
end

end