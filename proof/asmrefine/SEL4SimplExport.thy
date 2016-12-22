(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory SEL4SimplExport

imports
  "../../tools/asmrefine/SimplExport"
  "../../spec/cspec/Substitute"

begin

declare Char_eq_Char_iff [simp del]

ML {*
val csenv = let
    val the_csenv = CalculateState.get_csenv @{theory} "c/kernel_all.c_pp" |> the
  in fn () => the_csenv end
*}

context kernel_all_substitute begin

ML {* 
  emit_C_everything_relative @{context} (csenv ()) "CFunDump.txt";
*}

end

end

