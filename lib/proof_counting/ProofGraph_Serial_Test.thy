(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory ProofGraph_Serial_Test
imports ProofGraph
begin


ML {* val (full_spec,proof_spec,thy_deps) = Proof_Graph.get_full_spec @{context}*}

ML {* Proof_Graph.write_graph_spec_of (full_spec,proof_spec,thy_deps) "de5ec6b0b4ea" "./ainvs_graphs.xml"*}

ML {* val (full_spec',proof_spec',thy_deps') = Proof_Graph.read_graph_spec_from "./ainvs_graphs.xml" *}

ML {* if (Int_Graph.dest full_spec) = (Int_Graph.dest full_spec')
          andalso (String_Graph.dest proof_spec = String_Graph.dest proof_spec') 
          andalso (Symtab.dest thy_deps = Symtab.dest thy_deps') then () else error "Serialization failure" *}

         
          
end
