(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

signature PROOF_METRICS =
sig

type metric_head = {proof_bottom : string list ,
                    proof_top : string list,
                    spec_theories : string list,
                    toplevel_facts : string list,
                    name  : string
                   }

type metric_configs = {min_proof_size : int,
                       filter_locale_consts : bool,
                       filter_kinds : Proof_Count.lemmaT list,
                       thy_deps : (string * string list) Symtab.table,
                       full_spec : Spec_Graph.entry Int_Graph.T,
                       proof_spec : Proof_Graph.proof_entry String_Graph.T,
                       base_path : string
                      }


val get_root_theories_of : (string * string list) Symtab.table -> (string -> string -> bool) -> string list

val get_theories_from_range : (string * string list) Symtab.table -> string list * string list -> string list

val compute_and_write_metrics : (metric_head * metric_configs) -> unit

end

structure Proof_Metrics : PROOF_METRICS =
struct

(*Truncate graphs to only discuss constants in mentioned theories*)

fun theory_of (e : Spec_Graph.entry) = (Long_Name.explode #> hd) (#name e)

fun filter_contains (spec : Spec_Graph.entry Int_Graph.T) theories =
  Proof_Graph.map_contains (filter (fn id => (member (op =) theories) (theory_of (Int_Graph.get_node spec id))))

(* Connect child and parent nodes before removing them, preserving connectedness. *)

fun truncate_proof_spec spec_theories proof_theories spec proof_spec = proof_spec
|> Proof_Graph.restrict_subgraph (fn (nm,e) =>
  (member (op =) proof_theories ((Long_Name.explode #> hd) nm))
  andalso (not (#lines e = (~1,~1))))
|> String_Graph.map (K(filter_contains spec spec_theories))


fun get_proof_metrics (proof_spec : Proof_Graph.proof_entry String_Graph.T) =
let

  fun all_sucs i  = String_Graph.all_succs proof_spec [i]

(*Avoid double-counting multi-lemmas*)
  fun get_proper_deps i = fold (fn j => let val e = String_Graph.get_node proof_spec j in Symtab.insert_list (op =) (#file e,#lines e) end) (all_sucs i) Symtab.empty
    |> Symtab.dest_list
    |> map (fn (_,(a,b)) => (b - a) + 1)

  fun collate_metrics i = (i,{total_size = get_proper_deps i |> Integer.sum})

in map collate_metrics (String_Graph.keys proof_spec) |> Symtab.make end

fun filter_all_deps thy_deps (thys as (_ :: _)) =
  let
    val all_deps = fold (fn thy => union (op =) (Symtab.lookup thy_deps thy |> the |> snd)) thys []
  in
    filter (member (op =) all_deps)
  end
  | filter_all_deps _ [] = I

fun get_theories_from_range thy_deps (bottom_theories as _ :: _,top_theories) = Proof_Graph.proper_theory_list thy_deps bottom_theories
    |> filter_out (member (op =) (Proof_Graph.proper_theory_list thy_deps top_theories))
    |> (filter_all_deps thy_deps top_theories)
    |> union (op =) top_theories
  | get_theories_from_range thy_deps ([],_) = Symtab.dest thy_deps |> map fst

fun toplevel_parent g nm =
let
  val preds = String_Graph.all_preds g [nm]
  val ppreds = map (fn i => `(String_Graph.immediate_preds g) i) preds
in
  find_first (null o fst) ppreds |> Option.map snd end



(* Note if the top of a spec or proof range is empty, this will encompass
   all known theories which depend on the bottom of the range *)

type metric_head = {proof_bottom : string list ,
                    proof_top : string list,
                    spec_theories : string list,
                    toplevel_facts : string list,
                    name  : string
                   }

type metric_configs = {min_proof_size : int,
                       filter_locale_consts : bool,
                       filter_kinds : Proof_Count.lemmaT list,
                       thy_deps : (string * string list) Symtab.table,
                       full_spec : Spec_Graph.entry Int_Graph.T,
                       proof_spec : Proof_Graph.proof_entry String_Graph.T,
                       base_path : string
                      }


(* toplevel_facts are those whose dependencies actually show up in the final data.
   If it is empty then all facts are included *)

fun compute_and_write_metrics (header : metric_head,(args : metric_configs)) =
let

  val toplevel_facts = #toplevel_facts header
  val name = #name header
  val proof_spec' = #proof_spec args
  val full_spec = #full_spec args
  val base_path = #base_path args
  val thy_deps = #thy_deps args

  val _ =  (#spec_theories header) @ (#proof_bottom header) @ (#proof_top header)
    |> map (fn s => Symtab.defined thy_deps s orelse error ("Unknown theory: " ^ s))

  val _ = tracing "Truncating proof spec..."

  val spec_theories = get_theories_from_range thy_deps ((#spec_theories header,[]))
  val proof_theories = get_theories_from_range thy_deps (#proof_bottom header,#proof_top header)


  val proof_spec = (truncate_proof_spec spec_theories proof_theories full_spec proof_spec')

  val all_deps = case toplevel_facts of [] => String_Graph.keys proof_spec
  | _ => String_Graph.all_succs proof_spec toplevel_facts handle String_Graph.UNDEF x =>
    error ("Couldn't find fact " ^ x ^ " in known facts.\n" ^ (@{make_string} proof_theories))

  val _ = tracing "Calculating spec metrics..."

  val all_defs = Int_Graph.fold (fn (_,(e,_)) => (case (#def_name e) of SOME d => Symtab.update (d,()) | NONE => I)) full_spec Symtab.empty

  val _ = tracing "Calculating proof metrics..."

  val proof_metrics = get_proof_metrics proof_spec

  val lemma_defs = String_Graph.fold (fn (nm,_) =>
    Symtab.update (nm,String_Graph.all_succs proof_spec' [nm] |> filter (Symtab.defined all_defs))) proof_spec Symtab.empty

  val _ = tracing "done"

type metric_entry = {
                      spec_size : int,
                      ideal_spec_size : int,
                      fact_size : int,
                      consts : int list,
                      use_consts : int list
                    }


fun write_metrics measure_name =
  let
    fun filter_deps (nm,_) = if toplevel_facts = [] then true else member (op =) all_deps nm

    fun filter_kinds (nm,_) =  ((member (op =) (map SOME (#filter_kinds args)) (#kind (String_Graph.get_node proof_spec nm))))

    fun filter_size (_,t) = (#total_size t) > (#min_proof_size args)

    fun is_used fact_defs i =
        let
          val e = (Int_Graph.get_node full_spec i)
        in
          case (#def_name e) of NONE => true |
          SOME d => (case (#spec_type e) of
            Spec_Graph.Constructor => true
            | Spec_Graph.Case => true
            | _ =>  (member (op =) fact_defs d))
        end


   fun is_in_theory i = member (op =) spec_theories (Int_Graph.get_node full_spec i |> theory_of)

   fun is_locale i = Int_Graph.get_node full_spec i |> #spec_type
    |> (fn Spec_Graph.Locale => true | _ => false)

     fun final_entry (fact_id,metric_entry) =
      let
        val proof_entry = String_Graph.get_node proof_spec fact_id

        val fact_defs = Symtab.lookup lemma_defs fact_id |> the

      val prems = flat (#prems proof_entry)
      |> (#filter_locale_consts args) ? filter (not o is_locale)

       val consts = #concl proof_entry @ prems

        fun proper_sucs spec consts = consts
          |> Int_Graph.all_succs spec
          |> filter is_in_theory


        val all_consts = proper_sucs full_spec consts

        val all_used_consts = filter (is_used fact_defs) all_consts

        val result = {
                       spec_size = length all_consts,
                       ideal_spec_size = length all_used_consts,
                       fact_size = #total_size metric_entry,
                       consts = all_consts,
                       ideal_consts = all_used_consts
                     }
      in
        (fact_id,result) end


    val filtered =
    let
    in
      proof_metrics |> Symtab.dest
      |> filter filter_deps
      |> filter filter_kinds
      |> filter filter_size
       end

    val paired = Par_List.map final_entry filtered

    fun mk_string (fact_id,{spec_size,ideal_spec_size,fact_size,...}) = fact_id ^ " " ^
      (Int.toString spec_size) ^ " " ^
      (Int.toString ideal_spec_size) ^
      " " ^ (Int.toString fact_size) ^  "\n"

    val buf = Buffer.empty
    |> fold (fn e => Buffer.add (mk_string e)) paired

  in
    (File.write_buffer (Path.explode (base_path ^ "/metrics_" ^ name ^ "_" ^ measure_name ^ ".txt")) buf;(filtered,paired)) end


val (filtered_num_deps,paired_num_deps) = write_metrics "num_deps";

val _ = not (null filtered_num_deps) orelse error "No facts were counted. Check theory ranges."

fun add_top_report thm buf =
let
  val {fact_size, spec_size, ideal_spec_size, consts,ideal_consts,...} = AList.lookup (op =) paired_num_deps thm |> the

  val redundant_consts = subtract (op =) ideal_consts consts
    |> map (fn i => Int_Graph.get_node full_spec i |> #name)
in
  buf
  |> Buffer.add ("Toplevel lemma: " ^ thm ^ " with " ^ (Int.toString fact_size)
                  ^ " lines of proof, " ^ Int.toString spec_size ^ " specification size and "
                  ^ Int.toString ideal_spec_size ^ " ideal specification size\n")
  |> Buffer.add ("Redundant Toplevel Constants: " ^ (String.concatWith "\n" redundant_consts) ^ "\n")
 end

  val (largestp,_) = fold (fn (id,e) => fn (id',e') => if (#total_size e) > (#total_size e') then (id,e) else (id',e')) filtered_num_deps (filtered_num_deps |> hd)

fun add_top_reports buf = buf
    |> Buffer.add "Giving largest measured proof.\n"
    |> add_top_report largestp

(* Total number of unique lines from all dependencies. *)
val full_size = fold (fn j => let val e = String_Graph.get_node proof_spec j in Symtab.insert_list (op =) (#file e,#lines e) end) all_deps Symtab.empty
    |> Symtab.dest_list
    |> map (fn (_,(a,b)) => (b - a) + 1)
    |> Integer.sum

fun toString_commas i=
  Int.toString i
    |> String.explode
    |> rev
    |> chop_groups 3
    |> map (String.implode o rev)
    |> rev
    |> String.concatWith ","

fun latex_report thm =
  let
    val {spec_size,ideal_spec_size,fact_size,...} = AList.lookup (op =) paired_num_deps thm |> the
    fun mk_command inm i = Buffer.add ("\\newcommand{\\" ^ name ^ inm ^ "}{" ^ i ^ "\\xspace}\n")
 in
    Buffer.empty
    |> mk_command "NumDeps" (toString_commas spec_size)
    |> mk_command "IdealNumDeps" (toString_commas ideal_spec_size)
    |> mk_command "Lines" (toString_commas fact_size)
    |> mk_command "AllLines" (toString_commas full_size)
 end

val orphaned = subtract (op =) all_deps (String_Graph.keys proof_spec)
val parents = map (the_default "" o toplevel_parent proof_spec) orphaned

val buf = fold2 (fn or => fn p => Buffer.add (or ^ " -> " ^ p ^ "\n")) orphaned parents Buffer.empty

val _ = (File.write_buffer (Path.explode (base_path ^ "/" ^ name ^ "_orphans.txt")) buf)


  val buf = Buffer.empty
  |> Buffer.add ("Total number of facts plotted: " ^ (toString_commas (length paired_num_deps)) ^ "\n")
  |> Buffer.add ("Total size of all facts: \n")
  |> Buffer.add (Int.toString full_size)
  |> Buffer.add ("\n")
  |> add_top_reports
  |> Buffer.add ("Unused lemmas: " ^ (toString_commas (length orphaned)) ^ "\n")
  |> Buffer.add ("Proof Theories: \n")
  |> fold (Buffer.add "\n" oo Buffer.add) proof_theories
  |> Buffer.add "\n"
  |> Buffer.add ("Spec Theories: \n")
  |> fold (Buffer.add "\n" oo Buffer.add) spec_theories
  |> Buffer.add "\n"

val _ = File.write_buffer (Path.explode (base_path ^ "/" ^ name ^ "_report.txt")) buf

val _ = File.write_buffer (Path.explode (base_path ^ "/" ^ name ^ "_summary.tex")) (latex_report largestp)

val _ = (proof_spec,proof_metrics,filtered_num_deps,paired_num_deps,lemma_defs)

in () end

fun get_root_theories_of thy_deps f =
let
  val thy_graph = thy_deps
  |> Symtab.dest
  |> map (fn (nm,(i,es)) => ((nm,i),es))
  |> String_Graph.make
  |> (fn g => String_Graph.restrict (fn k => f k (String_Graph.get_node g k)) g)
  |> String_Graph.dest
  |> map_filter (fn ((nm,_),es) => if es = [nm] then SOME nm else NONE)
in
  thy_graph
end

end
