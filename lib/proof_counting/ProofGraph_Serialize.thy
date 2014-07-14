(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory ProofGraph_Serialize
imports ProofGraph Noninterference_Refinement
begin

ML {*
val toplevel_thm_name = "xnonleakage_C"
val revision = "de5ec6b0b4ea"
*}

ML {* 
val toplevel_thm = Proof_Context.get_thm @{context} toplevel_thm_name
val toplevel_spec = prop_of toplevel_thm
val file_name = "./" ^ toplevel_thm_name ^ "_graphs" ^ ".xml"
*}

ML {* val (full_spec,proof_spec,thy_deps) = Proof_Graph.get_full_spec @{context} toplevel_spec*}

ML {* Proof_Graph.write_graph_spec_of (full_spec,proof_spec,thy_deps) revision file_name*}

end
