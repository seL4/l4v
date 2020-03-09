(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Tracing AutoCorres internals.
 *
 * AutoCorres has experimental support for tracing some of the
 * translation phases.
 *)

theory TraceDemo imports "AutoCorres.AutoCorres" begin

external_file "trace_demo.c"
install_C_file "trace_demo.c"

autocorres [
  (* Trace heap lifting and word abstraction.
   * These stages proceed by proving a schematic theorem using a set of proof rules.
   * The trace will record the individual steps of the proof. *)
  trace_heap_lift = incr, trace_word_abs = incr,
  (* Trace internal simplification ("optimisation") phases.
   * The trace will record the rules used by the simplifier. *)
  trace_opt
  ] "trace_demo.c"


(*
 * Proof traces are stored in the RuleTrace datatype.
 * These tend to be very large and detailed.
 *)

(* All traces are stored in the AutoCorresData.Traces theory data. *)
ML \<open>
val all_traces = the (Symtab.lookup (AutoCorresData.Traces.get @{theory}) "trace_demo.c")
\<close>

(* Heap lifting trace. *)
ML \<open>
the (Symtab.lookup (the (Symtab.lookup all_traces "incr")) "HL")
|> (fn AutoCorresData.RuleTrace x => x)
|> AutoCorresTrace.print_ac_trace
|> writeln
\<close>

(* Word abstraction trace. *)
ML \<open>
the (Symtab.lookup (the (Symtab.lookup all_traces "incr")) "WA")
|> (fn AutoCorresData.RuleTrace x => x)
|> AutoCorresTrace.print_ac_trace
|> writeln
\<close>

(* To navigate a trace in jEdit, write it to a file: *)
ML \<open>
the (Symtab.lookup (the (Symtab.lookup all_traces "incr")) "HL")
|> (fn AutoCorresData.RuleTrace x => x)
|> AutoCorresTrace.print_ac_trace
|> AutoCorresTrace.writeFile
       (Path.append (Resources.master_directory @{theory}) (Path.make ["trace_demo_incr.trace"])
        |> File.standard_path)
\<close>
(* Then, open the file and set the "folding mode" buffer option to "indent". *)


(*
 * Simplification traces are stored in the SimpTrace datatype.
 * Three simplification steps are traced: after local variable lifting, heap lifting, and word abstraction.
 *)

(* Peephole optimisations (ie. rewrite rules). *)
ML \<open>
the (Symtab.lookup (the (Symtab.lookup all_traces "incr")) "L2 peephole opt")
|> (fn AutoCorresData.SimpTrace x => x)
\<close>
(* Flow-sensitive optimisations. If you use the no_opt option, they will be disabled and there will be no trace. *)
ML \<open>
Symtab.lookup (the (Symtab.lookup all_traces "incr")) "L2 flow opt"
|> Option.map (fn AutoCorresData.SimpTrace x => x)
\<close>

ML \<open>
the (Symtab.lookup (the (Symtab.lookup all_traces "incr")) "HL peephole opt")
|> (fn AutoCorresData.SimpTrace x => x)
\<close>
ML \<open>
Symtab.lookup (the (Symtab.lookup all_traces "incr")) "HL flow opt"
|> Option.map (fn AutoCorresData.SimpTrace x => x)
\<close>

ML \<open>
the (Symtab.lookup (the (Symtab.lookup all_traces "incr")) "WA peephole opt")
|> (fn AutoCorresData.SimpTrace x => x)
\<close>
ML \<open>
Symtab.lookup (the (Symtab.lookup all_traces "incr")) "WA flow opt"
|> Option.map (fn AutoCorresData.SimpTrace x => x)
\<close>


end
