(*
 * Tracing AutoCorres internals.
 *
 * AutoCorres has experimental support for tracing some of the
 * translation phases.
 *)

theory TraceDemo imports "../../AutoCorres" begin

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

(* Heap lifting trace. *)
ML {*
AutoCorresData.get_trace @{theory} "trace_demo.c" "HL" "incr"
|> the |> (fn AutoCorresData.RuleTrace x => x)
|> AutoCorresTrace.print_ac_trace
|> writeln
*}

(* Word abstraction trace. *)
ML {*
AutoCorresData.get_trace @{theory} "trace_demo.c" "WA" "incr"
|> the |> (fn AutoCorresData.RuleTrace x => x)
|> AutoCorresTrace.print_ac_trace
|> writeln
*}

(* To navigate a trace in jEdit, write it to a file: *)
ML {*
AutoCorresData.get_trace @{theory} "trace_demo.c" "HL" "incr"
|> the |> (fn AutoCorresData.RuleTrace x => x)
|> AutoCorresTrace.print_ac_trace
|> AutoCorresTrace.writeFile
       (Path.append (Resources.master_directory @{theory}) (Path.make ["trace_demo_incr.trace"]) |> Path.implode)
*}
(* Then, open the file and set the "folding mode" buffer option to "indent". *)


(*
 * Simplification traces are stored in the SimpTrace datatype.
 * Three simplification steps are traced: after local variable lifting, heap lifting, and word abstraction.
 *)

(* Peephole optimisations (ie. rewrite rules). *)
ML {*
AutoCorresData.get_trace @{theory} "trace_demo.c" "L2 peephole opt" "incr"
|> the |> (fn AutoCorresData.SimpTrace x => x)
*}
(* Flow-sensitive optimisations. If you use the no_opt option, they will be disabled and there will be no trace. *)
ML {*
AutoCorresData.get_trace @{theory} "trace_demo.c" "L2 flow opt" "incr"
|> Option.map (fn AutoCorresData.SimpTrace x => x)
*}

ML {*
AutoCorresData.get_trace @{theory} "trace_demo.c" "HL peephole opt" "incr"
|> the |> (fn AutoCorresData.SimpTrace x => x)
*}
ML {*
AutoCorresData.get_trace @{theory} "trace_demo.c" "HL flow opt" "incr"
|> Option.map (fn AutoCorresData.SimpTrace x => x)
*}

ML {*
AutoCorresData.get_trace @{theory} "trace_demo.c" "WA peephole opt" "incr"
|> the |> (fn AutoCorresData.SimpTrace x => x)
*}
ML {*
AutoCorresData.get_trace @{theory} "trace_demo.c" "WA flow opt" "incr"
|> Option.map (fn AutoCorresData.SimpTrace x => x)
*}


end