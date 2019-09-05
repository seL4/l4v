(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory Local_Method
imports Main
keywords "supply_local_method" :: prf_script % "proof"
begin

text \<open>See documentation in @{path Local_Method_Tests.thy}.\<close>

ML \<open>
  structure MethodData = Proof_Data(
    type T = Method.method Symtab.table
    val init = K Symtab.empty);
\<close>

method_setup local_method = \<open>
  Scan.lift Parse.liberal_name >>
  (fn name => fn _ => fn facts => fn (ctxt, st) =>
    case (ctxt |> MethodData.get |> Symtab.lookup) name of
        SOME method => method facts (ctxt, st)
      | NONE => Seq.succeed (Seq.Error (K ("Couldn't find method text named " ^ quote name))))
\<close>

ML \<open>
local

val parse_name_text_ranges =
  Scan.repeat1 (Parse.liberal_name --| Parse.!!! @{keyword "="} -- Method.parse)

fun supply_method_cmd name_text_ranges ctxt =
  let
    fun add_method ((name, (text, range)), ctxt) =
      let
        val _ = Method.report (text, range)
        val method = Method.evaluate text ctxt
      in
        MethodData.map (Symtab.update (name, method)) ctxt
      end
  in
    List.foldr add_method ctxt name_text_ranges
  end

val _ =
  Outer_Syntax.command @{command_keyword\<open>supply_local_method\<close>}
    "Add a local method alias to the current proof context"
    (parse_name_text_ranges >> (Toplevel.proof o Proof.map_context o supply_method_cmd))

in end
\<close>

end