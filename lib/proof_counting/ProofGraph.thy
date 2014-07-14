(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory ProofGraph
imports Main ProofCount SpecGraph List
begin

(*TODO: Move to library?*)
ML {* 

fun all_eq (a :: b :: l) = if a = b then all_eq (b :: l) else false
  | all_eq [a] = true
  | all_eq [] = true

fun common_head (lss as (l :: _)) = 
let
  fun common_head i = if all_eq (map (fn ls => List.nth (ls,i)) lss) handle Subscript => false then common_head (i + 1) else i
in
  List.take (l,common_head 0) end
 | common_head [] = []

fun common_prefix strs = String.implode (common_head (map String.explode strs))
*}

ML {*
signature PROOF_GRAPH =
sig


type proof_entry = {name : string, file : string, lines : int * int, contains : int list, kind : Proof_Count.transaction}

val size_of : proof_entry -> int

val proper_theory_list : (string * string list) Symtab.table -> string list -> string list

val get_full_spec : Proof.context -> Spec_Graph.graph_entry Int_Graph.T * proof_entry String_Graph.T * (string * string list) Symtab.table

val write_graph_spec_of : Spec_Graph.graph_entry Int_Graph.T * proof_entry String_Graph.T  * (string * string list) Symtab.table -> string -> string -> unit

val read_graph_spec_from : string ->
    Spec_Graph.graph_entry Int_Graph.T * proof_entry String_Graph.T  * (string * string list) Symtab.table

val restrict_subgraph :  (String_Graph.key * 'a -> bool) -> 'a String_Graph.T -> 'a String_Graph.T

val merge_multi_thms : proof_entry String_Graph.T -> proof_entry String_Graph.T

val relative_path_of : string -> string

end
*}

ML {* structure Proof_Graph : PROOF_GRAPH =
struct

val isabelle_home = File.full_path Path.root (Path.variable "ISABELLE_HOME")

(*FIXME: Not general *)
fun relative_path_of s = if s = "" then "" else
  let
    val home_base = Path.dir isabelle_home |> Path.implode
  in
    "~~/.." ^ (unprefix home_base s) end

type proof_entry = {name : string, file : string, lines : int * int, contains : int list, kind : Proof_Count.transaction}

fun restrict_subgraph f graph = 
let
  val restrs = String_Graph.fold (fn (id,(e,edge)) => if f (id,e) then I else cons edge) graph []
  |> map (fn (preds,sucs) => map_product pair (String_Graph.Keys.dest preds) (String_Graph.Keys.dest sucs))
in
  fold (fold (String_Graph.add_edge)) restrs graph
  |> String_Graph.restrict (fn id => f (id,(String_Graph.get_node graph id))) end

fun size_of {lines, ...} = case lines of (a,b) => (b - a) + 1

fun join_thms thms = ignore (Future.joins (map (#3 o #2) thms));

fun fold_body_thms f =
  let            
    fun app (nms,(PBody {thms, ...})) =
      tap join_thms thms |> fold (fn (i, (name, prop, body)) => fn (x, seen, count) =>
        if Inttab.defined seen i then (f (nms,name,prop,NONE) x, seen, count)
        else
          let
            val _ = if count mod 1000 = 0 then tracing ((@{make_string} count) ^ " unique facts processed.") else ()
            val body' = Future.join body;
            val (x', seen', count') = app (name :: nms,body') (x, Inttab.update (i, ()) seen, count + 1);
          in (f (nms, name, prop, SOME body') x', seen', count') end);
  in fn bodies => fn x => #1 (fold app bodies (x, Inttab.empty,0)) end;

fun graph_proof' ctxt =
  let
    val report = Proof_Count.get_size_report ()
    |> Proof_Count.compute_sizes
   

    fun get_lines (SOME (_,(begin,done))) = ((the (Position.line_of begin),the (Position.line_of done)))
      | get_lines NONE = (~1,~1)

    fun get_transaction (SOME (t,_)) = t
     | get_transaction NONE = Proof_Count.Unknown

    fun first_parent parents = parents 
    |> find_first (fn s => not (s = ""))
    
    (* Weird self-edges occur due to attributes *)
    fun safe_add_edge (n,n') tab = (if n = n' then tab else tab
      |> String_Graph.default_node (n,NONE)
      |> String_Graph.default_node (n',NONE)
      |> String_Graph.add_edge (n,n'))
      
    fun safe_add_node (n,entry) tab = tab
      |> String_Graph.default_node (n,NONE)
      |> String_Graph.map_node n (fn NONE => SOME (entry ()) | x => x)

    fun get_thms nm = the_default [] (try (Proof_Context.get_thms ctxt) nm)
          
    val thms = fold (append o get_thms) (Symtab.keys report) []

    val graph = fold (Spec_Graph.extend_spec ctxt o prop_of) thms (Spec_Graph.empty)
    
    fun add_dep (_,"", _, _) tab = tab
      | add_dep (parents,name,_, NONE) tab = tab
        |> (case (first_parent parents) of SOME p => safe_add_edge (p,name) | NONE => I)
      | add_dep (parents,name, t, SOME (PBody {thms = thms,...})) tab =
          let
            val depends = thms
                |> map (fn (_,(n,_,_)) => n)
                |> filter_out (fn s => s = "")
            
            fun entry _ =
            let
              val contains = Term.fold_aterms (fn t => append (Spec_Graph.get_entries ctxt graph t)) t []
              val report_entry = Symtab.lookup report name
            in
              {name = Long_Name.base_name name,
               file = ((Symtab.lookup report name) |> the |> snd |> fst |> Position.file_of |> the |> relative_path_of) handle Option => "",
               lines = get_lines report_entry,
               contains = map #id contains,
               kind = get_transaction report_entry} end
 
            val tab' =         
            tab
            |> safe_add_node (name,entry)
            |> (case (first_parent parents) of SOME p => safe_add_edge (p,name) | NONE => I)        
            |> fold (fn d => if d = name then I else safe_add_edge (name,d)) depends          
                
          in tab' end;
    

    val deps = fold_body_thms add_dep (map (pair []) (Thm.proof_bodies_of thms)) String_Graph.empty;

  in (graph,deps |> restrict_subgraph (fn (i,_) => Option.isSome (String_Graph.get_node deps i)) |> String_Graph.map (K the)) end;
  

fun graph_proof ctxt = graph_proof' ctxt


(*Attempt to merge lemmas statements back together*)
fun merge_entries (entries as (n,e) :: _)  graph =
let
  val id = unsuffix "_" (common_prefix (map fst entries))
  
  val name = unsuffix "_" (common_prefix (map (#name o snd) entries))
  val contains = flat (map (#contains o snd) entries)
  
  fun rep_old nm' = if exists (fn (n,_) => nm' = n) entries then id else nm'

  val preds = flat (map (String_Graph.immediate_preds graph o fst) entries) |> map rep_old
  val succs = flat (map (String_Graph.immediate_succs graph o fst) entries) |> map rep_old
in
   fold (fn (n,_) => String_Graph.del_node n) entries graph
  |> String_Graph.new_node (id,{name = name,contains = contains,file = #file e,lines = #lines e, kind = #kind e})
  |> fold (fn e => String_Graph.add_edge (e,id)) preds
  |> fold (fn e => String_Graph.add_edge (id,e)) succs  
  end handle General.Fail "unsuffix" => graph

(*Merge theorems which share document position*)
(*Excludes: Crunched lemmas and lemmas that share the same local name.
    This is to prevent merging lemmas which are proved within a locale
    and thus extend to all instantiations of it*)
fun merge_multi_thms graph =
let
  val files = String_Graph.fold (fn (n,(e,_)) => Symtab.insert_list (K false) (#file e,(n,e))) graph Symtab.empty
  fun do_partition es =
  let
    val parts = partition_eq (fn ((_,e),(_,e')) => #lines e = #lines e') (filter_out (fn (_,e) => #lines e = (~1,~1) orelse #kind e = Proof_Count.Crunch) es)
    |> filter (fn l => length l > 1)
    |> filter_out (fn l => all_eq (map (#name o snd) l))

  in
    fold merge_entries parts end
in
  Symtab.fold (fn (_,es) => do_partition es) files graph end

fun transaction_to_str s = let
  open Proof_Count in case s of
  Lemma => "Lemma"
 | Lemmas => "Lemmas"
 | Unknown => "Unknown"
 | Crunch => "Crunch"
 | Other => "Other"
 | Done => "Done"
end

fun str_to_transaction s = let
  open Proof_Count in case s of
  "Lemma" => Lemma
| "Lemmas" => Lemmas
| "Unknown" => Unknown
| "Crunch" => Crunch
| "Other" => Other
| "Done" => Done
end
  
fun to_props (e : proof_entry) = []
  |> Properties.put ("name", #name e)
  |> Properties.put ("file", #file e)
  |> Properties.put ("start", Int.toString (#lines e |> fst))
  |> Properties.put ("end", Int.toString (#lines e |> snd))
  |> Properties.put ("kind",transaction_to_str (#kind e))
  

fun from_props (prop,contains) =
  ({ name = Properties.get prop "name" |> the,
    file = Properties.get prop "file" |> the,
    lines = (Int.fromString (Properties.get prop "start" |> the) |> the,
             Int.fromString (Properties.get prop "end" |> the) |> the),
    kind = Properties.get prop "kind" |> the_default "Unknown" |> str_to_transaction,
    contains = contains} : proof_entry)

fun encode_proof_graph_entry e =
  let open XML.Encode
  in
    (pair properties (list int)) (to_props e, #contains e) end
    
val encode_proof_graph = String_Graph.encode XML.Encode.string encode_proof_graph_entry
    
fun decode_proof_graph_entry e =
  let open XML.Decode
  in
    (pair properties (list int)) e |> from_props end
    
val decode_proof_graph = String_Graph.decode XML.Decode.string decode_proof_graph_entry

fun get_thy_deps' thy tab = 
let
  val ancestors = Theory.nodes_of thy
  val nm = Context.theory_name thy
in
  if Symtab.defined tab nm then tab else
  Symtab.update (nm,(Thy_Load.master_directory thy |> Path.implode |> relative_path_of,(map Context.theory_name ancestors))) tab
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
   
fun get_full_spec ctxt =
let
    val thy = Proof_Context.theory_of ctxt

    val thy_deps = get_thy_deps thy
    |> Symtab.delete (Context.theory_name thy)
    
    val (graph,proof_graph) = graph_proof ctxt

    val full_graph = Spec_Graph.get_graph thy graph
    
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

*}

end
