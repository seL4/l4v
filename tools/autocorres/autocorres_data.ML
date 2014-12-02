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
 * Definition of context data.
 *)
signature AUTOCORRES_DATA =
sig
  val get_thm: theory -> string -> string -> string -> thm option
  val add_thm: string -> string -> string -> thm -> theory -> theory
  val get_def: theory -> string -> string -> string -> thm option
  val add_def: string -> string -> string -> thm -> theory -> theory

  datatype Trace =
      RuleTrace of thm AutoCorresTrace.RuleTrace
    | SimpTrace of AutoCorresTrace.SimpTrace

  val add_trace: string -> string -> string -> Trace -> theory -> theory
  val get_trace: theory -> string -> string -> string -> Trace option

  val debug : theory -> ((string * string * string) * thm) list * ((string * string * string) * Trace) list
end

structure AutoCorresData : AUTOCORRES_DATA =
struct

(* Construct an ordering for 3-ples. *)
fun triple_ord a b c ((x1, y1, z1), (x2, y2, z2)) =
  prod_ord (prod_ord a b) c (((x1, y1), z1), ((x2, y2), z2))

(* Symbol table with three string inputs. *)
structure Symtab3 = Table(
  type key = string * string * string
  val ord = triple_ord fast_string_ord fast_string_ord fast_string_ord
);


(*
 * Container type for various trace data.
 * TODO: consolidate these in a better way.
 *)

datatype Trace =
    RuleTrace of thm AutoCorresTrace.RuleTrace (* HeapLift and WordAbstract main stages *)
  | SimpTrace of AutoCorresTrace.SimpTrace (* simp lemma bucket for L2Opt and TypeStrengthen *)



(* AutoCorres Context Data. *)
type ac_record = {
  proofs : thm Symtab3.table,
  traces : Trace Symtab3.table
};
datatype ac_data = ACData of ac_record;

fun dest_ac_data (ACData x) = x

(* Instantiate AutoCorres Data. *)
structure Terms = Theory_Data(
  type T = ac_data;
  val empty = ACData { proofs = Symtab3.empty, traces = Symtab3.empty };
  val extend = I;
  fun merge (ACData ts1, ACData ts2) =
    ACData {
      proofs = Symtab3.merge Thm.eq_thm (#proofs ts1, #proofs ts2),
      traces = Symtab3.merge (K true) (#traces ts1, #traces ts2)
    }
)

(* Fetch a trace. *)
fun get_trace thy filename module fn_name =
  Terms.get thy
  |> dest_ac_data
  |> #traces
  |> (fn x => Symtab3.lookup x (filename, module, fn_name))

(* Add a trace. *)
fun add_trace filename module fn_name trace =
  Terms.map (fn ACData x =>
    ACData {
      proofs = #proofs x,
      traces = Symtab3.update_new
          ((filename, module, fn_name), trace) (#traces x)
    })

(* Fetch a theorem. *)
fun get_thm thy filename module fn_name =
  Terms.get thy
  |> dest_ac_data
  |> #proofs
  |> (fn x => Symtab3.lookup x (filename, module, fn_name))

(* Add a theorem. *)
fun add_thm filename module fn_name thm thy =
  Terms.map (fn ACData x =>
    ACData {
      proofs = Symtab3.update_new
          ((filename, module, fn_name), thm) (#proofs x),
      traces = #traces x
    }) thy

(* Fetch a definition. *)
fun get_def thy filename module fn_name =
  get_thm thy filename (module ^ "'def") fn_name

(* Add a definition. *)
fun add_def filename module fn_name =
  add_thm filename (module ^ "'def") fn_name

(* Dump everything. *)
fun debug thy = Terms.get thy |> dest_ac_data |> (fn x => (Symtab3.dest (#proofs x), Symtab3.dest (#traces x)))

end
