(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Definition of context data.
 *)
signature AUTOCORRES_DATA =
sig
  datatype Trace =
      RuleTrace of thm AutoCorresTrace.RuleTrace
    | SimpTrace of AutoCorresTrace.SimpTrace

  (* Actual storage for traces. See below for documentation *)
  structure Traces: THEORY_DATA
end

structure AutoCorresData : AUTOCORRES_DATA =
struct

(*
 * Container type for various trace data.
 * TODO: consolidate these in a better way.
 *)
datatype Trace =
    RuleTrace of thm AutoCorresTrace.RuleTrace (* HeapLift and WordAbstract main stages *)
  | SimpTrace of AutoCorresTrace.SimpTrace (* simp lemma bucket for L2Opt and TypeStrengthen *)

(* Function translation traces.
 * These are for informational or debugging usage. *)
structure Traces = Theory_Data (
  type T = Trace Symtab.table (* trace type *)
                 Symtab.table (* func name *)
                 Symtab.table (* file *);
  val empty = Symtab.empty;
  (* We need a deep merge due to incremental translations (which can span
   * multiple theories). snd is arbitrary. *)
  val merge = Utils.symtab_merge_with (Utils.symtab_merge_with (Utils.symtab_merge_with snd));
)

end (* structure AutoCorresData *)

(* Function translation information.
 * This is needed for resuming incremental translations. *)
structure AutoCorresFunctionInfo = Theory_Data(
  type T = FunctionInfo.function_info Symtab.table
             FunctionInfo.Phasetab.table Symtab.table;
  val empty = Symtab.empty;
  val merge = Symtab.merge (K true);
)
