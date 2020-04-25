(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

signature SPEC_GRAPH =
sig

datatype spec_type =
    Definition | Constructor |  Case | Locale

type entry = {name : string, def_name: string option, spec_type : spec_type}

val get_graph: theory -> ((entry Int_Graph.T) * (string * typ -> Int_Graph.key option))

val encode_graph: entry Int_Graph.T XML.Encode.T

val decode_graph : entry Int_Graph.T XML.Decode.T


end

structure Spec_Graph : SPEC_GRAPH =
struct

datatype spec_type =
  Definition | Constructor |  Case | Locale

type entry = {name : string, def_name: string option, spec_type : spec_type}


fun could_match (Ts, Us) =
  Option.isSome (SOME (Type.raw_matches (Ts, Us) Vartab.empty) handle Type.TYPE_MATCH => NONE);


fun get_graph thy =
let
  val defs = Theory.defs_of thy
  val consts = Sign.consts_of thy
  val {restricts,reducts} = Defs.dest (Theory.defs_of thy)

  fun body_of (nm,args) =
    let
      val specs = Defs.specifications_of defs nm
      val spec_of = find_first (fn {def,description,pos,lhs,rhs} => lhs = args) specs
    in
      the spec_of
      |> (fn s => (#rhs s,#def s))
  end

fun add_general nm ls =
let
  val c = Consts.the_const consts nm
  val args = Consts.typargs consts c
in
  if null args orelse exists (fn (args',_) =>
      could_match (args',args)) ls
  then ls else (ls @ [(args,([],NONE))])
end

val reduct_tab = map (fn ((nm,args),_) => (nm,(args,(body_of (nm,args))))) reducts
  |> Symtab.make_list
  |> Symtab.map add_general


val id_reduct_tab =
  fold_map (fn entry => fn id => ((id,entry),id + 1)) (Symtab.dest_list reduct_tab) 0
  |> fst
  |> map (fn (id,(nm,entry)) => (nm,(id,entry)))
  |> Symtab.make_list

fun id_of (nm,args) = case Symtab.lookup id_reduct_tab nm of SOME e =>
    get_first (fn (id,(args',_)) => if could_match (args',args) then SOME id else NONE) e
  | NONE => NONE

fun mk_graph_entry (nm,(id,(args,(body,def)))) =
let

  val T = Consts.the_constraint consts nm

  val case_suffixes = ["_case","_rec","_rec_set","_rep_set","_update","_Tuple_Iso"]

  val spec_type = case (Datatype.info_of_constr thy (nm,T)) of
      SOME _ => Constructor
    | NONE => if Locale.defined thy nm then Locale else
       if exists (fn n => String.isSuffix n nm) case_suffixes then Case else Definition

  fun clean_def_name nm = if String.isSuffix "_raw" nm then (unsuffix "_raw" nm) else nm

  val entry = {name = nm, def_name = Option.map clean_def_name def, spec_type = spec_type}
in
  ((id,entry),map_filter id_of body)
end

val raw_graph = map mk_graph_entry (Symtab.dest_list id_reduct_tab)

val graph = Int_Graph.make raw_graph

fun lookup_const (nm,T) =
  let
    val specs = Symtab.lookup id_reduct_tab nm
    val args = Consts.typargs consts (nm,T)
  in
    Option.map (get_first (fn (id,(args',_)) => if could_match (args',args) then SOME id else NONE)) specs
    |> Option.join
  end

in
  (graph,lookup_const)
end

local
  open XML.Encode

fun spec_type_tostring spec_type = case spec_type of
  Definition => "Definition"
 | Constructor => "Constructor"
 | Locale => "Locale"
 | Case => "Case"


in

fun encode_entry (e as {name, def_name, spec_type} : entry) =
  (triple string (option string) string) (name,def_name,spec_type_tostring spec_type)

val encode_graph = Int_Graph.encode XML.Encode.int encode_entry


end

local
  open XML.Decode

fun spec_type_fromstring str = case str of
  "Definition" => Definition
 | "Constructor" => Constructor
 | "Locale" => Locale
 | "Case" => Case
 | _ => error "Unknown spec type"

fun triple_to_entry (name,def_name,spec_type) = ({name = name, def_name = def_name,
  spec_type = spec_type_fromstring spec_type} : entry)

in

val decode_entry  =
  (triple string (option string) string)

fun decode_graph body = Int_Graph.decode XML.Decode.int decode_entry body
|> Int_Graph.map (fn _ => triple_to_entry)

end

end

