(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory ProofGraph_Serialize_InfoflowC
imports ProofGraph Noninterference_Refinement
begin


(*Expects to be run from repo of theory*)

ML {* val (raw_revision,st) = Isabelle_System.bash_output "hg tip | grep changeset | sed 's/.*:\\(.*\\)/\\1/' " *}

ML {*
val thy_name = "Noninterference_Refinement"
val revision = if st = 0 andalso not (raw_revision = "") then trim_line raw_revision else "unknown_revision"
val file_name = "~~/../lib/proof_counting/" ^ thy_name ^ "_graphs" ^ ".xml"
*}

ML {* val i = Spec_Graph.get_defs @{context} @{term "Noninterference_Refinement.valid_initial_state_C"}*}
ML {* val (full_spec,proof_spec,thy_deps) = Proof_Graph.get_full_spec @{context}*}

ML {* Proof_Graph.write_graph_spec_of (full_spec,proof_spec,thy_deps) revision file_name*}

end
