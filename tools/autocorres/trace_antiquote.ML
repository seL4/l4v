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
    ^ "Pretty.str \"Trace:\", (Pretty.from_ML (ML_Pretty.from_polyml ("
      ^ "ML_system_pretty (x, ML_Print_Depth.get_print_depth ()))))])))"

val _ = Theory.setup (ML_Antiquotation.inline (Binding.name "trace") (Scan.succeed tracing_str))

end
