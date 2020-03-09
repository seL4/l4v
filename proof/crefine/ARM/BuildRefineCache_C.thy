(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory BuildRefineCache_C (* FIXME: broken *)
imports Main
begin

ML \<open>

(* needed to generate a proof cache *)
proofs := 1;
DupSkip.record_proofs := true;

tracing "Building crefinement image using Refine_C";

time_use_thy "Refine_C";

\<close>

ML \<open>

tracing "Synching proof cache";

DupSkip.sync_cache @{theory Refine_C};

tracing "Dumping proof cache";

let
  val xml = XML_Syntax.xml_forest_of_cache (! DupSkip.the_cache);
in
  File.open_output (XML_Syntax.output_forest xml) (Path.basic "proof_cache.xml")
end;

\<close>

end;
