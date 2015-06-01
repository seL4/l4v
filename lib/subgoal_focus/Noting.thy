(* Backwards version of "note" command. Most applicable within a subgoal focus.*)

theory Noting
imports Pure
keywords "noting" :: prf_decl
begin

ML\<open>

local

fun gen_thmss prep_atts prep_fact args state =
  state
  |> Proof.map_context_result (fn ctxt => ctxt |> Proof_Context.note_thmss ""
    (Attrib.map_facts_refs (map (prep_atts ctxt)) (prep_fact ctxt) args))
  |> snd;

in

val noting_thmss = gen_thmss  (K I) (K I);
val noting_thmss_cmd = gen_thmss Attrib.attribute_cmd Proof_Context.get_fact;

end
  
val _ =
  Outer_Syntax.command @{command_keyword noting} "define facts"
    (Parse_Spec.name_facts >> (Toplevel.proof o noting_thmss_cmd));
\<close>

end

