(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Tracing anti-quotations.
 *
 * Use "val _ = @{trace} foo" to pretty-print "foo".
 *
 * The string "tracing_str" is inlined into the ML sources at the point the
 * anti-quotation is written.
 *)

structure TraceAntiquote =
struct

val tracing_str =
  "(fn x => (Pretty.writeln (Pretty.enum \" \" \"\" \"\" ["
    ^ "Pretty.str \"Trace:\", (Pretty.from_ML ("
      ^ "ML_system_pretty (x, FixedInt.fromInt (ML_Print_Depth.get_print_depth ()))))])))"

val _ = Theory.setup (ML_Antiquotation.inline (Binding.name "trace") (Scan.succeed tracing_str))

end
