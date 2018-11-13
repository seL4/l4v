(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *
 * Report generating for autolevity. Computes proof start/end ranges, tracks levity tags
 * and reports on lemma, const, type and theory dependencies.
 *)

theory AutoLevity_Theory_Report
imports AutoLevity_Base
begin

ML \<open>
(* An antiquotation for creating json-like serializers for
   simple records. Serializers for primitive types are automatically used,
   while serializers for complex types are given as parameters. *)
val JSON_string_encode: string -> string =
  String.translate (
      fn #"\\" => "\\\\"
       | #"\n" => "\\n"
       | x => if Char.isPrint x then String.str x else
                "\\u" ^ align_right "0" 4 (Int.fmt StringCvt.HEX (Char.ord x)))
  #> quote;

fun JSON_int_encode (i: int): string =
  if i < 0 then "-" ^ Int.toString (~i) else Int.toString i

val _ = Theory.setup(
ML_Antiquotation.inline @{binding string_record}
  (Scan.lift
    (Parse.name --|
      Parse.$$$ "=" --
      Parse.position Parse.string) >>
    (fn (name,(source,pos)) =>

    let

      val entries =
      let
        val chars = String.explode source
          |> filter_out (fn #"\n" => true | _ => false)

        val trim =
        String.explode
        #> chop_prefix (fn #" " => true | _ => false)
        #> snd
        #> chop_suffix (fn #" " => true | _ => false)
        #> fst
        #> String.implode

        val str = String.implode chars
          |> String.fields (fn #"," => true | #":" => true | _ => false)
          |> map trim


        fun pairify [] = []
          | pairify (a::b::l) = ((a,b) :: pairify l)
          | pairify _  = error ("Record syntax error" ^ Position.here pos)

      in
        pairify str
      end

      val typedecl =
      "type " ^ name ^ "= { "
      ^ (map (fn (nm,typ) => nm ^ ":" ^ typ) entries |> String.concatWith ",")
      ^ "};"

      val base_typs = ["string","int","bool", "string list"]


      val encodes = map snd entries |> distinct (op =)
        |> filter_out (member (op =) base_typs)

      val sanitize = String.explode
      #> map (fn #" " => #"_"
                | #"." => #"_"
                | #"*" => #"P"
                | #"(" => #"B"
                | #")" => #"R"
                | x => x)
      #> String.implode

      fun mk_encode typ =
      if typ = "string"
      then "JSON_string_encode"
      else if typ = "int"
      then "JSON_int_encode"
      else if typ = "bool"
      then "Bool.toString"
      else if typ = "string list"
      then "(fn xs => (enclose \"[\" \"]\" (String.concatWith \", \" (map JSON_string_encode xs))))"
       else  (sanitize typ) ^ "_encode"


      fun mk_elem nm _ value =
        (ML_Syntax.print_string (JSON_string_encode nm) ^ "^ \" : \" ") ^ "^ (" ^ value ^ ")"

      fun mk_head body =
        "(\"" ^ "{\" ^ String.concatWith \", \" (" ^  body ^ ") ^ \"}\")"


      val global_head = if (null encodes) then "" else
      "fn (" ^ (map mk_encode encodes |> String.concatWith ",") ^ ") => "


      val encode_body =
        "fn {" ^ (map fst entries |> String.concatWith ",") ^ "} : " ^ name ^ " => " ^
        mk_head
        (ML_Syntax.print_list (fn (field,typ) => mk_elem field typ (mk_encode typ ^ " " ^ field)) entries)


      val val_expr =
      "val (" ^  name ^ "_encode) = ("
        ^ global_head ^ "(" ^ encode_body ^ "))"

      val _ = @{print} val_expr

    in
      typedecl  ^ val_expr
    end)))
\<close>

ML \<open>

@{string_record deps = "consts : string list, types: string list"}
@{string_record lemma_deps = "consts: string list, types: string list, lemmas: string list"}
@{string_record location = "file : string, start_line : int, end_line : int"}
@{string_record levity_tag = "tag : string, location : location"}
@{string_record apply_dep = "name : string, attribs : string list"}

@{string_record proof_command =
  "command_name : string, location : location, subgoals : int, depth : int,
   apply_deps : apply_dep list" }

@{string_record lemma_entry =
  "name : string, command_name : string, levity_tag : levity_tag option, location : location,
   proof_commands : proof_command list,
   deps : lemma_deps"}

@{string_record dep_entry =
  "name : string, command_name : string, levity_tag : levity_tag option, location: location,
   deps : deps"}

@{string_record theory_entry =
  "name : string, file : string"}

@{string_record log_entry =
  "errors : string list, location : location"}

fun encode_list enc x = "[" ^ (String.concatWith ", " (map enc x)) ^ "]"

fun encode_option enc (SOME x) = enc x
  | encode_option _ NONE = "{}"

val opt_levity_tag_encode = encode_option (levity_tag_encode location_encode);

val proof_command_encode = proof_command_encode (location_encode, encode_list apply_dep_encode);

val lemma_entry_encode = lemma_entry_encode
  (opt_levity_tag_encode, location_encode, encode_list proof_command_encode, lemma_deps_encode)

val dep_entry_encode = dep_entry_encode
  (opt_levity_tag_encode, location_encode, deps_encode)

val log_entry_encode = log_entry_encode (location_encode)

\<close>

ML \<open>

signature AUTOLEVITY_THEORY_REPORT =
sig
val get_reports_for_thy: theory ->
  string * log_entry list * theory_entry list * lemma_entry list * dep_entry list * dep_entry list

val string_reports_of:
  string * log_entry list * theory_entry list * lemma_entry list * dep_entry list * dep_entry list
  -> string list

end;

structure AutoLevity_Theory_Report : AUTOLEVITY_THEORY_REPORT =
struct

fun map_pos_line f pos =
let
  val line = Position.line_of pos |> the;
  val file = Position.file_of pos |> the;

  val line' = f line;

  val _ = if line' < 1 then raise Option else ();

in SOME (Position.line_file_only line' file) end handle Option => NONE


(* A Position.T table based on offsets (Postab_strict) can be collapsed into a line-based one
   with lists of entries on for each line. This function searches such a table
   for the closest entry, either backwards (LESS) or forwards (GREATER) from
   the given position. *)

(* TODO: If everything is sane then the search depth shouldn't be necessary. In practice
   entries won't be more than one or two lines apart, but if something has gone wrong in the
   collection phase we might end up wasting a lot of time looking for an entry that doesn't exist. *)

fun search_by_lines depth ord_kind f h pos = if depth = 0 then NONE else
  let
    val line_change = case ord_kind of LESS => ~1 | GREATER => 1 | _ => raise Fail "Bad relation"
    val idx_change = case ord_kind of GREATER => 1 | _ => 0;
  in
  case f pos of
   SOME x =>
    let
      val i = find_index (fn e => h (pos, e) = ord_kind) x;
    in if i > ~1 then SOME (List.nth(x, i + idx_change)) else SOME (hd x) end

  | NONE =>
    (case (map_pos_line (fn i => i + line_change) pos) of
      SOME pos' => search_by_lines (depth - 1) ord_kind f h pos'
     | NONE => NONE)
   end

fun location_from_range (start_pos, end_pos) =
  let
    val start_file = Position.file_of start_pos |> the;
    val end_file = Position.file_of end_pos |> the;
    val _ = if start_file = end_file then () else raise Option;
    val start_line = Position.line_of start_pos |> the;
    val end_line = Position.line_of end_pos |> the;
  in
  SOME ({file = start_file, start_line = start_line, end_line = end_line} : location) end
  handle Option => NONE

(* Here we collapse our proofs (lemma foo .. done) into single entries with start/end positions. *)

fun get_command_ranges_of keywords thy_nm =
let
  fun is_ignored nm' = nm' = "<ignored>"
  fun is_levity_tag nm' = nm' = "levity_tag"

  fun is_proof_cmd nm' = nm' = "apply" orelse nm' = "by" orelse nm' = "proof"

  (* All top-level transactions for the given theory *)

  val (transactions, log) =
          Symtab.lookup (AutoLevity_Base.get_transactions ()) thy_nm
          |> the_default (Postab_strict.empty, Postab_strict.empty)
          ||> Postab_strict.dest
          |>> Postab_strict.dest

  (* Line-based position table of all apply statements for the given theory *)

  val applytab =
    Symtab.lookup (AutoLevity_Base.get_applys ()) thy_nm
    |> the_default Postab_strict.empty
    |> Postab_strict.dest
    |> map (fn (pos,e) => (pos, (pos,e)))
    |> Postab.make_list
    |> Postab.map (fn _ => sort (fn ((pos,_),(pos', _)) => pos_ord true (pos, pos')))


  (* A special "ignored" command lets us find the real end of commands which span
     multiple lines. After finding a real command, we assume the last "ignored" one
     was part of the syntax for that command *)

  fun find_cmd_end last_pos ((pos', (nm', ext)) :: rest) =
    if is_ignored nm' then
       find_cmd_end pos' rest
    else (last_pos, ((pos', (nm', ext)) :: rest))
    | find_cmd_end last_pos [] = (last_pos, [])

  fun change_level nm level =
    if Keyword.is_proof_open keywords nm then level + 1
    else if Keyword.is_proof_close keywords nm then level - 1
    else if Keyword.is_qed_global keywords nm then ~1
    else level


  fun make_apply_deps lemma_deps =
    map (fn (nm, atts) => {name = nm, attribs = atts} : apply_dep) lemma_deps

  (* For a given apply statement, search forward in the document for the closest method to retrieve
     its lemma dependencies *)

  fun find_apply pos = if Postab.is_empty applytab then [] else
   search_by_lines 5 GREATER (Postab.lookup applytab) (fn (pos, (pos', _)) => pos_ord true (pos, pos')) pos
   |> Option.map snd |> the_default [] |> make_apply_deps

  fun find_proof_end level ((pos', (nm', ext)) :: rest) =
    let val level' = change_level nm' level in
     if level' > ~1 then
       let
         val (cmd_end, rest') = find_cmd_end pos' rest;
         val ((prf_cmds, prf_end), rest'') = find_proof_end level' rest'
       in (({command_name = nm', location = location_from_range (pos', cmd_end) |> the,
            depth = level, apply_deps = if is_proof_cmd nm' then find_apply pos' else [],
            subgoals = #subgoals ext} :: prf_cmds, prf_end), rest'') end
     else
       let
         val (cmd_end, rest') = find_cmd_end pos' rest;
        in (([{command_name = nm', location = location_from_range (pos', cmd_end) |> the,
            apply_deps = if is_proof_cmd nm' then find_apply pos' else [],
            depth = level, subgoals = #subgoals ext}], cmd_end), rest') end
     end
     | find_proof_end _ _ = (([], Position.none), [])


  fun find_ends tab tag ((pos,(nm, ext)) :: rest) =
   let
     val (cmd_end, rest') = find_cmd_end pos rest;

     val ((prf_cmds, pos'), rest'') =
       if Keyword.is_theory_goal keywords nm
       then find_proof_end 0 rest'
       else (([],cmd_end),rest');

     val tab' = Postab.cons_list (pos, (pos, (nm, pos', tag, prf_cmds))) tab;

     val tag' =
       if is_levity_tag nm then Option.map (rpair (pos,pos')) (#levity_tag ext) else NONE;

   in find_ends tab' tag' rest'' end
     | find_ends tab _ [] = tab

   val command_ranges = find_ends Postab.empty NONE transactions
    |> Postab.map (fn _ => sort (fn ((pos,_),(pos',_)) => pos_ord true (pos, pos')))

in (command_ranges, log) end



fun make_deps (const_deps, type_deps): deps =
  {consts = distinct (op =) const_deps, types = distinct (op =) type_deps}

fun make_lemma_deps (const_deps, type_deps, lemma_deps): lemma_deps =
  {
    consts = distinct (op =) const_deps,
    types = distinct (op =) type_deps,
    lemmas = distinct (op =) lemma_deps
  }

fun make_tag (SOME (tag, range)) = (case location_from_range range
  of SOME rng => SOME ({tag = tag, location = rng} : levity_tag)
  | NONE => NONE)
  | make_tag NONE = NONE



fun add_deps (((Defs.Const, nm), _) :: rest) =
  let val (consts, types) = add_deps rest in
    (nm :: consts, types) end
  | add_deps (((Defs.Type, nm), _) :: rest) =
  let val (consts, types) = add_deps rest in
    (consts, nm :: types) end
  | add_deps _ = ([], [])

fun get_deps ({rhs, ...} : Defs.spec) = add_deps rhs

fun typs_of_typ (Type (nm, Ts)) = nm :: (map typs_of_typ Ts |> flat)
  | typs_of_typ _ = []

fun typs_of_term t = Term.fold_types (append o typs_of_typ) t []

fun deps_of_thm thm =
let
  val consts = Term.add_const_names (Thm.prop_of thm) [];
  val types = typs_of_term (Thm.prop_of thm);
in (consts, types) end

fun file_of_thy thy =
  let
    val path = Resources.master_directory thy;
    val name = Context.theory_name thy;
    val path' = Path.append path (Path.basic (name ^ ".thy"))
  in Path.smart_implode path' end;

fun entry_of_thy thy = ({name = Context.theory_name thy, file = file_of_thy thy} : theory_entry)

fun used_facts thy thm =
  AutoLevity_Base.used_named_props_of thm
    |> map_filter (AutoLevity_Base.disambiguate_indices (Proof_Context.init_global thy))
    |> List.map fst;

fun get_reports_for_thy thy =
  let
    val thy_nm = Context.theory_name thy;
    val all_facts = Global_Theory.facts_of thy;
    val fact_space = Facts.space_of all_facts;

    val (tab, log) = get_command_ranges_of (Thy_Header.get_keywords thy) thy_nm;

    val parent_facts = map Global_Theory.facts_of (Theory.parents_of thy);

    val search_backwards = search_by_lines 5 LESS (Postab.lookup tab)
      (fn (pos, (pos', _)) => pos_ord true (pos, pos'))
      #> the

    val lemmas =  Facts.dest_static false parent_facts (Global_Theory.facts_of thy)
    |> map_filter (fn (xnm, thms) =>
       let
          val {pos, theory_name, ...} = Name_Space.the_entry fact_space xnm;
          in
            if theory_name = thy_nm then
            let
             val thms' = map (Thm.transfer thy) thms;

             val (real_start, (cmd_name, end_pos, tag, prf_cmds)) = search_backwards pos

             val lemma_deps =
                  if cmd_name = "datatype"
                  then []
                  else map (used_facts thy) thms' |> flat |> distinct (op =);

             val (consts, types) = map deps_of_thm thms' |> ListPair.unzip |> apply2 flat
             val deps = make_lemma_deps (consts, types, lemma_deps)

             val location = location_from_range (real_start, end_pos) |> the;

             val (lemma_entry : lemma_entry) =
              {name  = xnm, command_name = cmd_name, levity_tag = make_tag tag,
               location = location, proof_commands = prf_cmds, deps = deps}

            in SOME (pos, lemma_entry) end
            else NONE end handle Option => NONE)
      |> Postab_strict.make_list
      |> Postab_strict.dest |> map snd |> flat

    val defs = Theory.defs_of thy;

    fun get_deps_of kind space xnms = xnms
    |> map_filter (fn xnm =>
      let
          val {pos, theory_name, ...} = Name_Space.the_entry space xnm;
          in
            if theory_name = thy_nm then
            let
              val specs = Defs.specifications_of defs (kind, xnm);

              val deps =
                map get_deps specs
               |> ListPair.unzip
               |> (apply2 flat #> make_deps);

              val (real_start, (cmd_name, end_pos, tag, _)) = search_backwards pos

              val loc = location_from_range (real_start, end_pos) |> the;

              val entry =
                ({name = xnm, command_name = cmd_name, levity_tag = make_tag tag,
                  location = loc, deps = deps} : dep_entry)

            in SOME (pos, entry) end
            else NONE end handle Option => NONE)
      |> Postab_strict.make_list
      |> Postab_strict.dest |> map snd |> flat

    val {const_space, constants, ...} = Consts.dest (Sign.consts_of thy);

    val consts = get_deps_of Defs.Const const_space (map fst constants);

    val {types, ...} = Type.rep_tsig (Sign.tsig_of thy);

    val type_space = Name_Space.space_of_table types;
    val type_names = Name_Space.fold_table (fn (xnm, _) => cons xnm) types [];

    val types = get_deps_of Defs.Type type_space type_names;

    val thy_parents = map entry_of_thy (Theory.parents_of thy);

    val logs = log |>
     map (fn (pos, errs) => {errors = errs, location = location_from_range (pos, pos) |> the} : log_entry)

   in (thy_nm, logs, thy_parents, lemmas, consts, types) end

fun add_commas (s :: s' :: ss) = s ^ "," :: (add_commas (s' :: ss))
  | add_commas [s] = [s]
  | add_commas _ = []


fun string_reports_of (thy_nm, logs, thy_parents, lemmas, consts, types) =
      ["{\"theory_name\" : " ^ JSON_string_encode thy_nm ^ ","] @
      ["\"logs\" : ["] @
      add_commas (map (log_entry_encode) logs) @
      ["],","\"theory_imports\" : ["] @
      add_commas (map (theory_entry_encode) thy_parents) @
      ["],","\"lemmas\" : ["] @
      add_commas (map (lemma_entry_encode) lemmas) @
      ["],","\"consts\" : ["] @
      add_commas (map (dep_entry_encode) consts) @
      ["],","\"types\" : ["] @
      add_commas (map (dep_entry_encode) types) @
      ["]}"]
      |> map (fn s => s ^ "\n")

end
\<close>

end
