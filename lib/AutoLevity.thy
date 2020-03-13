(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory AutoLevity (* FIXME: broken *)
imports "../tools/proofcount/ProofGraph"
begin
ML \<open>val infoflow_file = "~~/../lib/proof_counting/Noninterference_Refinement_graphs.xml"\<close>
ML \<open>val (full_spec,proof_spec_raw,thy_deps) = Proof_Graph.read_graph_spec_from infoflow_file\<close>

ML \<open>val proof_spec = Proof_Graph.merge_multi_thms proof_spec_raw\<close>

(* Extracts "general" lemmas from proof graph and produces lemma buckets from them *)
(* Does theory and lemma dependency management. Might be better to produce a report and
   have a bash/perl script consume this, rather than doing the file manipulation in ML *)
(* Cleanup: Not really using name spaces properly *)


(*TODO: Can possibly extract lemmas from the middle of locales *)
ML \<open>

fun range (beg,fin) l = List.take (List.drop (l,beg),fin - beg)

fun map_range f (beg,fin) l =
let
  fun do_clear (h :: l') i = if beg <= i andalso i <= fin then (f h) :: (do_clear l' (i + 1)) else h :: (do_clear l' (i + 1))
    | do_clear [] i = []
in
  do_clear l 0 end

fun add_thy thy_deps thy thys' =
let
  fun reachable i j =
    let
      val deps = Option.map snd (Symtab.lookup thy_deps i)
    in
      case deps of SOME deps => member (=) deps j | NONE => false end

   val thys = distinct (=) thys'

in
  if exists (fn ex_thy => reachable ex_thy thy) thys then thys else
  thys
  |> filter_out (fn ex_thy => reachable thy ex_thy)
  |> cons thy
end

fun thy_list thy_deps thys = fold (add_thy thy_deps) thys []
  |> sort_wrt I

fun add_thy_consts spec_graph (e : Proof_Graph.proof_entry) =
  let
    val thys' = map (Int_Graph.get_node spec_graph #> #theory) (#contains e)
  in
    (union (=) thys') end



fun sort_lemmas (proof_graph,spec_graph : Spec_Graph.graph_entry Int_Graph.T,thy_deps) spec_theories facts  =
let

  fun do_sort (nm,e) (thy_names,thy_imports) =
  let
    val thy_list = thy_list thy_deps (add_thy_consts spec_graph e [])
    val i = (space_implode "__" thy_list) ^ "_Bucket"
  in
    (Symtab.update_new (nm,i) thy_names,
     Symtab.update (i,thy_list) thy_imports) end

  val (thy_names,thy_imports) = fold do_sort facts (Symtab.empty,Symtab.empty)


  fun extra_deps (nm,e) (thm_deps,thytab) =
  let
    val thy_name = Symtab.lookup thy_names nm |> the

    val all_succs  = String_Graph.all_succs proof_graph [nm]


    fun get_dep nm' b =
    let
      val thyn = Long_Name.explode nm' |> hd
      fun warn _ = if not (Symtab.defined thy_names nm') then (warning (nm ^ " depends on " ^ nm' ^ " which is not marked for levitation and is outside theory import chain. NOT levitating.");true) else b

    in if member (=) spec_theories thyn then (NONE,warn ()) else (SOME thyn,b) end

    val (deps,rem) = fold_map get_dep all_succs false
    |>> map_filter I
    |>> append (map_filter (Symtab.lookup thy_names) all_succs)
    |>> remove (=) thy_name

    val imm_succs  = String_Graph.immediate_succs proof_graph nm


  in
    (if rem then (thm_deps,thytab) else
      (Symtab.update (nm,(e,imm_succs)) thm_deps,fold (fn dep => Symtab.insert_list (=) (thy_name,dep)) deps thytab)) end

  fun rem_cycles (thy_names,thy_imports) =
  let
    val thy_graph = thy_imports
      |> Symtab.dest
      |> map (fn (id,e) => ((id,()),filter (Symtab.defined thy_imports) e))
      |> String_Graph.make

   fun merge_deps (n :: l) (thy_names,thy_graph) =
   let


    val thy_graph' =
    Proof_Graph.restrict_subgraph (fn (i,_) => not (member (=) l i)) thy_graph

    val thy_names' = Symtab.map (fn _ => fn thyn => if member (=) l thyn then n else thyn) thy_names
   in
    (thy_names',thy_graph') end;

  fun cycles_of i =
    fold (fn j => append (String_Graph.irreducible_paths thy_graph (j,i))) (String_Graph.immediate_succs thy_graph i) []

   val cycles = map (flat o cycles_of) (String_Graph.keys thy_graph)
    |> filter_out null
    |> map (sort_wrt I #> distinct (=) #> rev)
    |> distinct (=)

   val thy_graph = thy_imports
      |> Symtab.dest
      |> map (fn (id,e) => ((id,()),e))
      |> append (map (fn (id,(_,e)) => ((id,()),e)) (Symtab.dest thy_deps))
      |> String_Graph.make

   val (thy_names',thy_graph') = fold merge_deps cycles (thy_names,thy_graph)

   val thy_imports' = map (fn i => (i,String_Graph.all_succs thy_graph' [i] |> remove (=) i)) (String_Graph.keys thy_graph')
    |> filter (fn (i,_) => Symtab.defined thy_imports i)
    |> Symtab.make

  in
    (thy_names',thy_imports') end

  val (thm_deps,thy_imports) = fold extra_deps facts (Symtab.empty,thy_imports)

  val (thy_names',thy_imports') = rem_cycles (thy_names,thy_imports)
    ||> Symtab.map (K (thy_list thy_deps))

  val order = String_Graph.topological_order proof_graph
    |> (fn l => fold_map (fn nm => fn i => ((nm,i),i+1)) l 0)
    |> fst
    |> Symtab.make

  fun do_lookup e tab nm = (Symtab.lookup tab nm |> the) handle Option => error ("No entry " ^ nm ^ " in symtab:\n" ^ e)

  val compare_facts = make_ord (fn ((nm,_),(nm',_)) => (do_lookup "order" order nm) < (do_lookup "order" order nm'))


  val thys = Symtab.fold (fn (nm,e) => Symtab.insert_list (K false) (do_lookup "thy_names" thy_names' nm,(nm,e))) thm_deps Symtab.empty
  |> Symtab.map (K (sort compare_facts))
  |> Symtab.map (fn i => fn e => (do_lookup "thy_imports" thy_imports' i,e))
  |> Symtab.dest

  val base_thy =
  let
    val all_imports = thy_imports'
    |> Symtab.dest
    |> map snd
    |> flat
    |> distinct (=)
    |> filter_out (member (=) (Symtab.keys thy_imports'))
    |> thy_list thy_deps
    |> map (fn n => "\"" ^ (Symtab.lookup thy_deps n |> the |> fst) ^ "/" ^ n ^ "\"")
    |> distinct (=)
  in
    ("AutoLevity_Base",(all_imports,[])) end

  val toplevel_thy = ("AutoLevity_Top",(thy_list thy_deps (Symtab.keys thy_imports'),[]))

in
  (toplevel_thy :: base_thy :: thys) end

(*TODO: Have a more sensible way of generating this list*)
val declare_attribs = ["simp","wp","intro","intro!","elim","elim!"]

fun get_attribs str =
let
  val toks = (Outer_Syntax.scan Position.none str
  |> filter (Token.is_proper)
  ) @ ([Token.eof])

  val ((nm,attribs),_) =
    (Parse.command |-- Parse_Spec.opt_thm_name ":") toks handle _  => error ("Failed to parse lemma attributes" ^ str)
in
  map (fst o fst o Args.dest_src) attribs
  |> filter (member (=) declare_attribs) end

fun parse_attribs sorted =
let
  fun do_parse (id,(e : Proof_Graph.proof_entry,thm_deps)) =
  let
    val thy_file = File.read_lines (Path.explode (#file e))
    val (begin,fin) = (#lines e)
    val text = range (begin -1,fin) thy_file
      |> space_implode "\n"

    val new_attribs = get_attribs text
  in
    (id,(e,thm_deps,new_attribs)) end
in
  map (fn (file,(deps,lemmas)) => (file,(deps,map do_parse lemmas))) sorted end



fun get_raw_proofs debug (id : string,(e : Proof_Graph.proof_entry,thm_deps,attribs)) =
  let
    val thy_file = File.read_lines (Path.explode (#file e))
    val (begin,fin) = (#lines e)
    val text = range (begin -1,fin) thy_file
      |> space_implode "\n"

    val new_attribs = attribs
    |> map (fn s => s ^ " del")
    |> space_implode ","


    val text' = text ^ (if new_attribs = "" then "" else ("\ndeclare " ^ (#name e) ^ "[" ^ new_attribs ^ "]"))
     ^ (if debug then "\n(* THM_DEPS: " ^ space_implode " " thm_deps ^ "*)\n" else "")

    (* Make sure we don't have any ride-alongs *)
    val _ = if (String.isSubstring "method_setup" text) then warning ("Found method setup" ^ (@{make_string} (id,e)) ^ "\n" ^ text) else ()
  in
    cons (#file e,text') end


fun add_buffer (f,text) (cur_f,buf) =
let
  val buf' = buf
    |> Buffer.add (if f = cur_f then "" else "\n(* " ^ f ^ " *)\n\n")
    |> Buffer.add ("\n" ^ text ^ "\n")
in
  (f,buf') end

fun get_thy debug (nm,(imports,lemmas)) =
let

  val lemma_text = fold (get_raw_proofs debug) lemmas []

  val buf = Buffer.empty
  |> Buffer.add ("theory " ^ nm ^ "\nimports ")
  |> Buffer.add (space_implode " " imports)
  |> Buffer.add ("\nbegin\n")
  |> (fn b => fold add_buffer lemma_text ("",b))
  |> snd
  |> Buffer.add ("\nend")

in
  (nm,buf) end



fun write_thys debug sorted base_path =
let
  val bufs = map (get_thy debug) sorted
in
  (map (fn (nm,buf) => (File.write_buffer (Path.append base_path (Path.explode (nm ^ ".thy"))) buf)) bufs;()) end



fun remove_lemma thy_nm (nm,(e : Proof_Graph.proof_entry,thm_deps,attribs)) (new_deps,cache) =
let
  val (beg',fin) = #lines e
  val beg = beg' -1

  val thy_file = case Symtab.lookup cache (#file e) of SOME s => s | NONE => File.read_lines (Path.explode (#file e)) |> map SOME



  val header = "(* " ^ #name e ^ " moved to " ^ thy_nm ^ " *)"

  val new_attribs = attribs
  |> space_implode ","

  val declare = if new_attribs = "" then "" else "\ndeclare " ^ thy_nm ^ "." ^ (#name e) ^ "[" ^ new_attribs ^ "]"

  val thy_file' = thy_file
  |> map_range (K NONE) (beg,fin-1)
  |> map_range (K (SOME (header ^ declare) )) (beg,beg)

in
  (Symtab.insert_list (=) (#file e,thy_nm) new_deps,Symtab.update (#file e,thy_file') cache) end

(*TODO: Auto-generate thy dependencies or assume everyone will import us?*)
fun remove_thy (thy_nm,(deps,lemmas)) cache = fold (remove_lemma thy_nm) lemmas cache


fun clear_thys thy_deps sorted =
let
  val (new_deps,cache) = fold remove_thy sorted (Symtab.empty,Symtab.empty)

  fun thy_to_file thy_nm = (Symtab.lookup thy_deps thy_nm |> the |> fst) ^ "/" ^ thy_nm ^ ".thy"

  val file_deps = map (fn (thy,(f,deps)) => (thy_to_file thy,map thy_to_file deps)) (Symtab.dest thy_deps)
  |> Symtab.make

  fun is_already_imported file_nm dep =
  let
    val deps = Symtab.lookup file_deps file_nm |> the
    |> remove (=) file_nm
  in
    exists (fn d => case (Symtab.lookup new_deps d) of SOME deps' => member (=) deps' dep | NONE => false) deps end

  fun add_deps file_nm file =
  let
    val deps = Symtab.lookup new_deps file_nm |> the
    |> filter_out (is_already_imported file_nm)


    val index_line = find_index (fn (SOME s) => String.isPrefix "imports" s | NONE => false) file

    val new_dep_line = if null deps then "" else " " ^ (space_implode " " deps)

    val file' =
      map_range (fn SOME s => SOME (s ^ new_dep_line) | NONE => error ("No import line in file " ^ file_nm)) (index_line,index_line) file
  in
    file' end

   val cache' = Symtab.map add_deps cache
in
  (Symtab.map (fn file => fn body => File.write_list (Path.explode file) (map (fn SOME s => s ^ "\n" | NONE => "") body)) cache';()) end;


\<close>

end


