(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory SEL4SimplExport
imports "ArchSEL4SimplExport"
begin

ML \<open>
val csenv = let
    val the_csenv = CalculateState.get_csenv @{theory} "../c/build/$L4V_ARCH/kernel_all.c_pp" |> the
  in fn () => the_csenv end
\<close>

context kernel_all_substitute begin

declare ctcb_offset_defs[simp]

ML \<open>
  ParseGraph.mkdir_relative @{theory} (getenv "L4V_ARCH");
  val CFunDump_filename_export = getenv "L4V_ARCH" ^ "/" ^ "CFunDump.txt";
  val CFunDump_filename = "export/" ^ CFunDump_filename_export;
  emit_C_everything_relative @{context} (csenv ()) CFunDump_filename_export "Kernel_C";
\<close>

end

end
