(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

fun all_eq (a :: b :: l) = if a = b then all_eq (b :: l) else false
  | all_eq [_] = true
  | all_eq [] = true

fun common_head (lss as (l :: _)) =
let
  fun common_head i = if all_eq (map (fn ls => List.nth (ls,i)) lss) handle Subscript => false then common_head (i + 1) else i
in
  List.take (l,common_head 0) end
 | common_head [] = []

fun common_prefix strs = String.implode (common_head (map String.explode strs))


signature PROOF_GRAPH =
sig


type proof_entry = {name : string, file : string, lines : int * int,
  prems : int list list, concl : int list, kind : Proof_Count.lemmaT option}

val contains : proof_entry -> int list

val map_contains : (int list -> int list) -> proof_entry -> proof_entry

val size_of : proof_entry -> int

val proper_theory_list : (string * string list) Symtab.table -> string list -> string list

val get_full_spec : theory -> Spec_Graph.entry Int_Graph.T * proof_entry String_Graph.T * (string * string list) Symtab.table

val write_graph_spec_of : Spec_Graph.entry Int_Graph.T * proof_entry String_Graph.T  * (string * string list) Symtab.table -> string -> string -> unit

val read_graph_spec_from : string ->
    Spec_Graph.entry Int_Graph.T * proof_entry String_Graph.T  * (string * string list) Symtab.table

val restrict_subgraph :  (String_Graph.key * 'a -> bool) -> 'a String_Graph.T -> 'a String_Graph.T

val merge_multi_thms : proof_entry String_Graph.T -> proof_entry String_Graph.T

val relative_path_of : string -> string



end

structure Proof_Graph : PROOF_GRAPH =
struct

val isabelle_home = File.full_path Path.root (Path.variable "ISABELLE_HOME")

(*FIXME: Not general *)
fun relative_path_of s = if s = "" then "" else
  let
    val home_base = Path.dir isabelle_home |> Path.implode
  in
    try (fn s => "~~/.." ^ (unprefix home_base s)) s
    |> the_default s end

type proof_entry = {name : string, file : string, lines : int * int,
   prems : int list list, concl : int list, kind : Proof_Count.lemmaT option}

fun contains ({prems, concl, ...} : proof_entry) = flat prems @ concl

fun map_contains f ({name, file, lines, prems, concl, kind}) =
let
  val (concl' :: prems') = (burrow f (concl :: prems))
in
  ({name = name, file = file, lines = lines, prems = prems', concl = concl', kind = kind} : proof_entry)
end

fun restrict_subgraph f graph =
let
  val restrs = String_Graph.fold (fn (id,(e,edge)) => if f (id,e) then I else cons edge) graph []
  |> map (fn (preds,sucs) => map_product pair (String_Graph.Keys.dest preds) (String_Graph.Keys.dest sucs))
in
  fold (fold (String_Graph.add_edge)) restrs graph
  |> String_Graph.restrict (fn id => f (id,(String_Graph.get_node graph id)))
end

fun size_of {lines, ...} = case lines of (a,b) => (b - a) + 1

fun thms_of (PBody {thms,...}) = thms

fun proof_body_descend' f (_,(nm,_,body)) =
  if f nm then
    fold (append o (proof_body_descend' f)) (thms_of (Future.join body)) []
  else
    [nm]

fun used_facts' f thm = fold (append o (proof_body_descend' f)) (thms_of (Thm.proof_body_of thm)) []



fun used_facts f thm =
  let
    val nm = Thm.get_name_hint thm
  in
    used_facts' (fn nm' => nm' = "" orelse nm' = nm orelse f nm) thm
  end

fun graph_proof thy =
  let

    val report = Proof_Count.get_size_report ()
    |> Proof_Count.compute_sizes


    fun get_lines (SOME (_,(begin,done))) =
      (((the (Position.line_of begin),the (Position.line_of done))) handle Option => (~1,~1))
      | get_lines NONE = (~1,~1)

    fun get_transaction (SOME (t,_)) = SOME t
     | get_transaction NONE = NONE

    val all_thms = Global_Theory.all_thms_of thy true

    val (graph,access) = Spec_Graph.get_graph thy

    val all_defs = Int_Graph.fold (fn (_,(e,_)) => (case (#def_name e) of SOME d => Symtab.update (d,()) | NONE => I)) graph Symtab.empty

    (* "interesting" defined as being a phyiscal lemma or a definitino *)
    fun is_interesting name =
    let
      val lines = Symtab.lookup report name |> get_lines
    in
      (Symtab.defined all_defs name) orelse
      (not (lines = (~1,~1)))
    end

    val _ = tracing ((@{make_string} (length all_thms)) ^ " total theorems found")

    val interesting_thms = filter (fn (i,_) => is_interesting i) all_thms
    |> sort_distinct (prod_ord string_ord (make_ord (K false)))


    fun mk_entry (name,thm) =
    let
      (* Skip uninteresting lemmas, finding their first interesting dependant *)
      val used = used_facts (not o is_interesting) thm
      |> filter is_interesting

      fun contains t = Term.fold_aterms (fn (Const c) => (case (access c) of SOME i => cons i | _ => I) | _ => I) t []

      val report_entry = Symtab.lookup report name

      val t = prop_of thm

      val e = {name = Long_Name.base_name name,
               file = ((Symtab.lookup report name) |> the |> snd |> fst |> Position.file_of |> the |> relative_path_of) handle Option => "",
               lines = get_lines report_entry,
               prems = map contains (Logic.strip_imp_prems t),
               concl = contains (Logic.strip_imp_concl t),
               kind = get_transaction report_entry}
    in
      ((name,e),used)
    end

    val _ = tracing ((@{make_string} (length interesting_thms)) ^ " facts to process")


    val raw_graph = Par_List.map (fn e => (mk_entry e)) interesting_thms

    val proof_graph = String_Graph.make raw_graph


  in (graph,proof_graph) end;


(*Attempt to merge lemmas statements back together*)
fun merge_entries (entries as (n,e) :: _)  graph =
let
  val id = unsuffix "_" (common_prefix (map fst entries))

  val name = unsuffix "_" (common_prefix (map (#name o snd) entries))
  val prems = flat (map (#prems o snd) entries)
  val concl = flat (map (#concl o snd) entries)

  fun rep_old nm' = if exists (fn (n,_) => nm' = n) entries then id else nm'

  val preds = flat (map (String_Graph.immediate_preds graph o fst) entries) |> map rep_old
  val succs = flat (map (String_Graph.immediate_succs graph o fst) entries) |> map rep_old
in
   fold (fn (n,_) => String_Graph.del_node n) entries graph
  |> String_Graph.new_node (id,{name = name,prems = prems,concl = concl, file = #file e,lines = #lines e, kind = #kind e})
  |> fold (fn e => String_Graph.add_edge (e,id)) preds
  |> fold (fn e => String_Graph.add_edge (id,e)) succs
  end handle General.Fail "unsuffix" => graph

(*Merge theorems which share document position*)
fun merge_multi_thms graph =
let
  val files = String_Graph.fold (fn (n,(e,_)) => Symtab.insert_list (K false) (#file e,(n,e))) graph Symtab.empty
  fun do_partition es =
  let
    val parts = partition_eq (fn ((_,e),(_,e')) => #lines e = #lines e') (filter_out (fn (_,e) => #lines e = (~1,~1)) es)
    |> filter (fn l => length l > 1)
    |> filter_out (fn l => all_eq (map (#name o snd) l))

  in
    fold merge_entries parts end
in
  Symtab.fold (fn (_,es) => do_partition es) files graph end

val lemma_prefixK = "Lemma: "
val declare_prefixK = "Declare: "
val noneK = "NONE"

fun transaction_to_str s = let
  open Proof_Count in case s of
  SOME (Lemma n) => lemma_prefixK ^ n
 | SOME (Declare n) => declare_prefixK ^ n
 | NONE => noneK
end

fun str_to_transaction s = if s = noneK then NONE else
SOME (
  case (try (unprefix "Lemma: ") s) of
  SOME x => Proof_Count.Lemma x
  | NONE => case (try (unprefix "Declare: ") s) of
      SOME x => Proof_Count.Declare x
    | NONE => error ("Deserialization failure: unexpected lemma type: " ^ s))

fun to_props (e : proof_entry) = []
  |> Properties.put ("name", #name e)
  |> Properties.put ("file", #file e)
  |> Properties.put ("start", Int.toString (#lines e |> fst))
  |> Properties.put ("end", Int.toString (#lines e |> snd))
  |> Properties.put ("kind",transaction_to_str (#kind e))


fun from_props (prop,(prems,concl)) =
  ({ name = Properties.get prop "name" |> the,
    file = Properties.get prop "file" |> the,
    lines = (Int.fromString (Properties.get prop "start" |> the) |> the,
             Int.fromString (Properties.get prop "end" |> the) |> the),
    kind = Properties.get prop "kind" |> the_default "Unknown" |> str_to_transaction,
    prems = prems,
    concl = concl} : proof_entry)

fun encode_proof_graph_entry e =
  let open XML.Encode
  in
    (pair properties (pair (list (list int)) (list int))) (to_props e, (#prems e,#concl e)) end

val encode_proof_graph = String_Graph.encode XML.Encode.string encode_proof_graph_entry

fun decode_proof_graph_entry e =
  let open XML.Decode
  in
    (pair properties (pair (list (list int)) (list int))) e |> from_props end

val decode_proof_graph = String_Graph.decode XML.Decode.string decode_proof_graph_entry

fun get_thy_deps' thy tab =
let
  val ancestors = Theory.nodes_of thy
  val nm = Context.theory_name thy
in
  if Symtab.defined tab nm then tab else
  Symtab.update (nm,(Resources.master_directory thy |> Path.implode |> relative_path_of,(map Context.theory_name ancestors))) tab
  |> fold get_thy_deps' ancestors end

fun get_thy_deps thy = get_thy_deps' thy Symtab.empty

fun encode_thy_deps deps =
  let open XML.Encode in
    (list (pair (string) (pair (string) (list string)))) (Symtab.dest deps) end

fun decode_thy_deps body =
  let open XML.Decode in
    (list (pair (string) (pair (string) (list string)))) body
    |> Symtab.make end

fun proper_theory_list tab (bottoms : string list) =
  let
    fun has_bottom (_,(_,deps)) = exists (fn th => member (op =) bottoms th) deps
  in
    Symtab.dest tab
    |> filter has_bottom
    |> map fst end;

fun get_full_spec thy =
let

    val thy_deps = get_thy_deps thy
    |> Symtab.delete (Context.theory_name thy)

    val (full_graph,proof_graph) = graph_proof thy

in
  (full_graph,proof_graph,thy_deps) end


fun write_graph_spec_of (full_graph,proof_graph,thy_deps) metadata file =
  let

    val spec_xml = XML.Elem (("Spec_Graph",[]),Spec_Graph.encode_graph full_graph)

    val proof_xml = XML.Elem (("Proof_Graph",[]),encode_proof_graph proof_graph)

    val thy_deps_xml = XML.Elem(("Thy_Deps",[]),encode_thy_deps thy_deps)

    val toplevel_xml = XML.Elem(("Toplevel",[("metadata",metadata)]),[spec_xml,proof_xml,thy_deps_xml])

  in
     File.open_output (XML.output (toplevel_xml)) (Path.explode file) end

fun read_graph_spec_from file =
  let
    val tree = File.read (Path.explode file)
    |> XML.parse


    fun deconstruct (
      XML.Elem (("Toplevel",_),
        [XML.Elem(("Spec_Graph",[]),spec_body),
         XML.Elem(("Proof_Graph",[]),proof_body),
         XML.Elem(("Thy_Deps",[]),thy_deps)])) = (spec_body,proof_body,thy_deps)
     | deconstruct _ = error "Not a valid spec graph"

   val (spec_body,proof_body,thy_deps) = deconstruct tree

   val full_graph = Spec_Graph.decode_graph spec_body
   val proof_graph = decode_proof_graph proof_body
   val thy_deps = decode_thy_deps thy_deps

  in
    (full_graph,proof_graph,thy_deps) end

end
