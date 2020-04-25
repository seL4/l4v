(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory BuildRefineCache
imports Main
begin

ML \<open>

(* needed to generate a proof cache *)
proofs := 1;
DupSkip.record_proofs := true;
quick_and_dirty := true;

tracing "Building refinement image using ROOT.ML";

use "ROOT.ML";

\<close>

ML \<open>

tracing "Synching proof cache";

DupSkip.sync_cache @{theory Refine};

tracing "Dumping proof cache";

let
  val xml = XML_Syntax.xml_forest_of_cache (! DupSkip.the_cache);
in
  File.open_output (XML_Syntax.output_forest xml) (Path.basic "proof_cache.xml")
end;

\<close>

end
