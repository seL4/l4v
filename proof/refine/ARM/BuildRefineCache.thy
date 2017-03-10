(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory BuildRefineCache
imports "~~/src/HOL/Main"
begin

ML {*

(* needed to generate a proof cache *)
proofs := 1;
DupSkip.record_proofs := true;
quick_and_dirty := true;

tracing "Building refinement image using ROOT.ML";

use "ROOT.ML";

*}

ML {*

tracing "Synching proof cache";

DupSkip.sync_cache @{theory Refine};

tracing "Dumping proof cache";

let
  val xml = XML_Syntax.xml_forest_of_cache (! DupSkip.the_cache);
in
  File.open_output (XML_Syntax.output_forest xml) (Path.basic "proof_cache.xml")
end;

*}

end
