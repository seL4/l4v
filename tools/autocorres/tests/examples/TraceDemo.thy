(*
 * Tracing AutoCorres internals.
 *
 * AutoCorres has experimental support for tracing the
 * heap lifting and word abstraction phases.  These stages proceed
 * by proving a schematic theorem using a set of proof rules.
 *
 * A trace consists of the proof, its intermediate subgoals,
 * and the proof rules used at each step.
 *
 * NB: the traces do not include the L2Opt simplification stage.
 *)

theory TraceDemo imports "../../AutoCorres" begin

install_C_file "trace_demo.c"

autocorres [ trace_heap_lift = incr, trace_word_abs = incr ] "trace_demo.c"

(* Heap lifting trace. *)
ML {*
AutoCorresData.get_trace @{theory} "trace_demo.c" "HL" "incr"
|> the
|> AutoCorresTrace.print_ac_trace
|> writeln
*}

(* Word abstraction trace. *)
ML {*
AutoCorresData.get_trace @{theory} "trace_demo.c" "WA" "incr"
|> the
|> AutoCorresTrace.print_ac_trace
|> writeln
*}

(* To navigate a trace in jEdit, write it to a file: *)
ML {*
AutoCorresData.get_trace @{theory} "trace_demo.c" "HL" "incr"
|> the
|> AutoCorresTrace.print_ac_trace
|> AutoCorresTrace.writeFile
       (Path.append (Resources.master_directory @{theory}) (Path.make ["trace_demo_incr.trace"]) |> Path.implode)
*}
(* Then, open the file and set the "folding mode" buffer option to "indent". *)

end