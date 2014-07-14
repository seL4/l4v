(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory ProofGraph_Test
imports ProofGraph
begin


ML {* val infoflow_file = "./Noninterference_Refinement_graphs.xml" *}
ML {* val (full_spec,proof_spec_raw,thy_deps) = Proof_Graph.read_graph_spec_from infoflow_file *}

ML {* val proof_spec = proof_spec_raw |> Proof_Graph.restrict_subgraph (fn (_,e) => not (#lines e = (~1,~1))) *}

(*Truncate graphs to only discuss constants in mentioned theories*)
ML {*

fun filter_contains (spec : Spec_Graph.graph_entry Int_Graph.T) theories i (e : Proof_Graph.proof_entry) =
  let 
    val contains' = #contains e
      |> filter (fn id => (member (op =) theories) (#theory (Int_Graph.get_node spec id)))    
  in
    ({name = #name e, file = #file e, lines = #lines e, contains = contains', kind = #kind e} : Proof_Graph.proof_entry) end

(* Connect child and parent nodes before removing them, preserving connectedness. *)


fun truncate_proof_spec spec_theories proof_theories spec proof_spec = proof_spec
|> Proof_Graph.restrict_subgraph (fn (nm,e) => member (op =) proof_theories ((Long_Name.explode #> hd) nm))
|> String_Graph.map (filter_contains spec spec_theories)



(*This is likely a bad idea because we lose information about case analyses in the body*)

fun truncate_full_spec theories (full_spec : Spec_Graph.graph_entry Int_Graph.T) = 
let
  fun is_theory id = member (op =) theories (#theory (Int_Graph.get_node full_spec id))
  
  fun fix_contains (e : Spec_Graph.graph_entry) =
                  {name = #name e, 
                   theory = #theory e, 
                   contains = #contains e |> map (filter (fn (freq,id) => is_theory id)),
                   def_names = #def_names e,
                   spec_type = #spec_type e,
                   size = #size e}
  
in
  full_spec
  |> Int_Graph.restrict (is_theory)
  |> Int_Graph.map (K fix_contains)
end
*}

ML{*
(*Examples of extra metrics that can be computed*)


(*Finds the longest cycle in the dependency graph of a constant (to find mutually recursive definitions) *)
fun cycle_of g i = 
  fold (fn j => append (Int_Graph.irreducible_paths g (j,i))) (Int_Graph.immediate_succs g i) []
    |> sort (int_ord o swap o pairself length)
    |> find_first (not o null)
    |> the_default []
    
    
fun cycles_of g = map (fn i => (i,cycle_of g i)) (Int_Graph.keys g) |> Inttab.make

(*Generalized recursive complexity function.
  adj : (id,graph_entry) -> accumulated recursive_complexity -> recursive_complexity
      Defines how complexity is accumulated when folding over a spec body*)
(* Recursive specs are defaulted to this function with 0 accumulated recursive complexity *)
fun gen_recursive_complexity adj base (g : Spec_Graph.graph_entry Int_Graph.T)  =
  let
    
    fun flat_contains e = (flat (#contains e))
    |> map (fn (freq,id) => replicate freq id)
    |> flat
  
  
    fun complexity_of_entry id (sz,tab) = 
      let
        val e = Int_Graph.get_node g id
      in
        (case Inttab.lookup tab id of SOME sz' => (((adj (id,e) sz sz')),tab) | 
                                  NONE => (let 
                                            val (sz',tab') = fold complexity_of_entry (flat_contains e) (base,Inttab.default (id,adj (id,e) base base) tab)
                                          in
                                            (((adj (id,e) sz sz')),Inttab.update (id,adj (id,e) base sz') tab') end)) end;
                                          
                            
  in
    fold complexity_of_entry (Int_Graph.keys g) (base,Inttab.empty) |> snd end;        
   
fun raw_case_complexity e = if (#spec_type e) = Spec_Graph.Case then (Real.fromInt (length (#contains e))) else 0.0
                                                                              
(* Flat complexity function *)
fun basic_complexity raw_complexity = gen_recursive_complexity (fn (id,e) => fn cur_sz => fn rec_sz => cur_sz + (raw_complexity e))


(*Calculate a collection of metrics from the given spec. Theories is meant to be a list of theories
  indicating which constants are part of the current spec. *)
fun get_metrics graph theories =
let 
  
   val cycles = cycles_of graph
   
   fun is_in_theory e = member (op =) theories (#theory e)
   
   val rec_comp_tab = gen_recursive_complexity (fn (_,e) => fn cur_sz => 
            fn rec_sz => cur_sz + (if is_in_theory e then ((rec_sz / 3.0) + raw_case_complexity e) 
              else raw_case_complexity e)) 0.0  graph

   val comp_tab = basic_complexity raw_case_complexity 0.0 graph 
   
   val rec_pow_comp_tab = gen_recursive_complexity (fn (id,e) => fn cur_sz => fn rec_sz =>
    cur_sz + (if is_in_theory e then ((rec_sz / 3.0) + raw_case_complexity e) * (Real.fromInt ((Inttab.lookup cycles id |> the |> length) + 1))
    else raw_case_complexity e)) 0.0
    graph
   
    val rec_comp_mult_tab = gen_recursive_complexity (fn (_,e) => fn cur_sz => fn rec_sz => cur_sz * (if is_in_theory e then ((Real.fromInt (#size e) / 3.0)) else 1.0)) 1.0  graph
    
   fun collate_metrics i = 
   let
    val all_succs = insert (op =) i (Int_Graph.all_succs graph [i])
    fun all_complexity tab =  (fold (fn j => fn r => (Inttab.lookup tab j |> the) + r) all_succs) 0.0
    
   in
    (i,{case_complexity = Inttab.lookup comp_tab i |> the, cycle = cycle_of graph i, rec_complexity = Inttab.lookup rec_comp_tab i |> the,
                              total_rec_complexity = all_complexity rec_comp_tab,
                              total_case_complexity = all_complexity comp_tab,
                              rec_pow_complexity = Inttab.lookup rec_pow_comp_tab i |> the,
                              total_size = Integer.sum (map (fn j => Int_Graph.get_node graph j |> #size) all_succs),
                              total_rec_pow_complexity = all_complexity rec_pow_comp_tab,
                              rec_comp_mult = Inttab.lookup rec_comp_mult_tab i |> the,
                              total_rec_comp_mult = all_complexity rec_comp_mult_tab})
    end
in
  map collate_metrics (Int_Graph.keys graph) |> Inttab.make end;
    
  
fun named_entries graph tab nm =
let
  val es = Spec_Graph.get_named_constants graph nm
in
  map (fn e => (e,Inttab.lookup tab e |> the)) es end

  
fun get_proof_metrics (proof_spec : Proof_Graph.proof_entry String_Graph.T) =
let

  (*Count a lemmas complexity as the size of all its immediate children, plus its own size.*)
  fun size_of_imm_succs i = Integer.sum (map (fn j => String_Graph.get_node proof_spec j |> Proof_Graph.size_of) (String_Graph.immediate_succs proof_spec i)) + (String_Graph.get_node proof_spec i |> Proof_Graph.size_of)
  
  val size_of_imm_succs_tab = map (fn ((i,_),_) => (i,size_of_imm_succs i)) (String_Graph.dest proof_spec) |> Symtab.make
  
  fun all_sucs i  = i :: (String_Graph.all_succs proof_spec [i])

(*Avoid double-counting multi-lemmas*)
  fun get_proper_size i = fold (fn j => let val e = String_Graph.get_node proof_spec j in Symtab.insert_list (op =) (#file e,#lines e) end) (all_sucs i) Symtab.empty
  |> Symtab.dest_list
  |> map (fn (_,(a,b)) => (b - a) + 1)
  |> Integer.sum
  
  
  fun collate_metrics i = (i,{total_size = get_proper_size i,
                              size_of_children = Symtab.lookup size_of_imm_succs_tab i |> the,
                              total_size_of_children = Integer.sum (map (fn j => Symtab.lookup size_of_imm_succs_tab j |> the) (all_sucs i))})

in map collate_metrics (String_Graph.keys proof_spec) |> Symtab.make end

fun get_overloads (g : Spec_Graph.graph_entry Int_Graph.T) = 
  Int_Graph.fold (fn (id,(e,_)) => Symtab.map_default (#name e,[]) (cons id)) g Symtab.empty
 |> (fn t => Symtab.fold (fn (_,ids) => fold (fn id => Inttab.update_new (id,ids)) ids) t Inttab.empty)
 |> Inttab.map (remove (op =))

(*
fun get_spec_roots g =
let
  fun get_roots (i :: is) = if null (Int_Graph.immediate_preds g i) then (i :: (get_roots is)) else []
   | get_roots [] = []
in
  get_roots (Int_Graph.topological_order g) end

fun get_proof_roots g =
let
  fun get_roots (i :: is) = if null (String_Graph.immediate_preds g i) then (i :: (get_roots is)) else []
   | get_roots [] = []
in
  get_roots (String_Graph.topological_order g) end*)

fun get_theories (bottom_theories,top_theories) = Proof_Graph.proper_theory_list thy_deps bottom_theories
    |> filter_out (member (op =) (Proof_Graph.proper_theory_list thy_deps top_theories))
    |> union (op =) top_theories

fun toplevel_parent g nm = 
let
  val preds = String_Graph.all_preds g [nm]
  val ppreds = map (fn i => `(String_Graph.immediate_preds g) i) preds
in
  find_first (null o fst) ppreds |> Option.map snd end


*}

(*
ML {* fun find_consts nm = full_spec |> Int_Graph.dest |> filter (fn ((id,e),_) => if String.isSubstring nm (#name e) then true else false)*}
ML {* fun find_facts nm = proof_spec' |> String_Graph.dest |> filter (fn ((id,e),_) => if String.isSubstring nm id then true else false)*}
ML {* find_consts "Noninterference" *}
ML {* find_facts "Noninterference" *}
ML {* map (Int_Graph.get_node full_spec) [7571, 2658, 7564, 7563, 7562, 2579, 3308, 1129, 7561, 2] *}

(*Note there are three version of each, one for each spec, plus the extensible version!*)
ML {* named_entries full_spec spec_metrics "Schedule_A.state_ext_sched_class.schedule" *}
ML {* named_entries full_spec spec_metrics "Noninterference_Refinement.valid_initial_state_C" *}
ML {* named_entries full_spec spec_metrics "Invariants_AI.invs" *}
ML {* named_entries full_spec spec_metrics "CSpace_A.cap_swap_for_delete" *}

*)

ML {* fun compute_and_write_specs proof_range spec_range name =
let

  val proof_theories = get_theories proof_range

  val spec_theories = get_theories spec_range

  val proof_spec' = (truncate_proof_spec spec_theories proof_theories full_spec proof_spec)

  val overloads = get_overloads full_spec


  val spec_metrics = get_metrics full_spec spec_theories
  val proof_metrics = get_proof_metrics proof_spec'

(*Only count the largest version of an overloaded constant in a lemma statement.*)
fun gen_measure (filter_overload,spec_accessor,proof_accessor,base,acc) m prf =
  let

    fun is_in_theory i = member (op =) spec_theories (Int_Graph.get_node full_spec i |> #theory)

    
    val totals = map_filter (fn (i,t) => if is_in_theory i then SOME (i,spec_accessor t) else NONE) m

    fun has_overload (i,t) = 
      let
        val overloads = Inttab.lookup overloads i |> the
        val b = map_filter (fn i' => Option.map (pair i') (AList.lookup (op =) totals i)) overloads
      in
        exists (fn (i',a) => a > t orelse (if (not (t > a)) then (i' > i) else false)) b end       

    val rec_pow = fold (curry acc) (totals |> (if filter_overload then (filter_out has_overload) else I) |> map snd) base
    

  in
    if null totals then NONE else SOME (rec_pow,proof_accessor prf) end


fun gen_write_metrics metric measure_name = 
  let
    val paired =   
    let   
      fun final_entry (fact_id,metric_entry) = 
      let
        val proof_entry = String_Graph.get_node proof_spec' fact_id
        val contains_metrics = map (fn i => (i,Inttab.lookup spec_metrics i |> the)) (#contains proof_entry)
        val (result : (string * (real * int)) option) = Option.map (pair fact_id) ((gen_measure metric) contains_metrics metric_entry)
      in
       result end
     in
       proof_metrics |> Symtab.dest |> map_filter final_entry end

    fun mk_string (s,(c,f)) = (Real.toString c) ^ " " ^ (Int.toString f) ^ "\n"

    val buf = Buffer.empty
    |> fold (fn e => Buffer.add (mk_string e)) paired

  in
    File.write_buffer (Path.explode ("./metrics_" ^ name ^ "_" ^ measure_name ^ ".txt")) buf end

val _ = (gen_write_metrics  (false,#total_rec_pow_complexity,#total_size,0.0,op +) "total_rec_pow";
         gen_write_metrics  (false,#total_rec_pow_complexity,#total_size,1.0,op *) "total_rec_pow_mult";
         gen_write_metrics  (false,Real.fromInt o #total_size,#total_size,0.0,op +) "total_size";
         gen_write_metrics  (false,#total_rec_pow_complexity,#total_size_of_children,0.0,op +) "total_rec_pow_children")

  val (largestp,ep) = Symtab.fold (fn (id,e) => fn (id',e') => if (#total_size e) > (#total_size e') then (id,e) else (id',e')) proof_metrics (Symtab.dest proof_metrics |> hd)
  
fun write_orphans toplevel_fact  =
  let
    val orphaned = subtract (op =) (String_Graph.all_succs proof_spec' [toplevel_fact]) (String_Graph.keys proof_spec')
    val parents = map (the_default "" o toplevel_parent proof_spec') orphaned

    val buf = fold2 (fn or => fn p => Buffer.add (or ^ " -> " ^ p ^ "\n")) orphaned parents Buffer.empty
  in
    (File.write_buffer (Path.explode ("./" ^ name ^ "_orphans.txt")) buf;orphaned) end

val orphaned = write_orphans largestp

  val buf = Buffer.empty
  |> Buffer.add ("Total number of facts: " ^ (Int.toString (length (String_Graph.dest proof_spec'))) ^ "\n")
  |> Buffer.add ("Largest proof: " ^ largestp ^ " with " ^ (Int.toString (#total_size ep)) ^ " lop.\n")
  |> Buffer.add ("Unused lemmas: " ^ (Int.toString (length orphaned)) ^ "\n")
  |> Buffer.add ("Proof Theories: \n")
  |> fold (Buffer.add "\n" oo Buffer.add) proof_theories
  |> Buffer.add "\n"
  |> Buffer.add ("Spec Theories: \n")
  |> fold (Buffer.add "\n" oo Buffer.add) spec_theories

val _ = File.write_buffer (Path.explode ("./" ^ name ^ "_report.txt")) buf
  
in
  (proof_spec',spec_metrics,proof_metrics) end
*}

ML {* val (proof_spec',spec_metrics,proof_metrics) = compute_and_write_specs (["Invariants_AI"],["AInvs"]) (["Structures_A","Deterministic_A"],["AInvs"]) "AInvs"*}

ML {* compute_and_write_specs (["Invariants_AI"],["Refine"]) (["Structures_A"],["Refine"]) "Refine"*}
                
end
