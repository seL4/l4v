(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory BuildRefineCache_C (* FIXME: broken *)
imports "~~/src/HOL/Main"
begin

ML {*

(* needed to generate a proof cache *)
proofs := 1;
DupSkip.record_proofs := true;

tracing "Building crefinement image using Refine_C";

time_use_thy "Refine_C";

*}

ML {*

tracing "Synching proof cache";

DupSkip.sync_cache @{theory Refine_C};

tracing "Dumping proof cache";

let
  val xml = XML_Syntax.xml_forest_of_cache (! DupSkip.the_cache);
in
  File.open_output (XML_Syntax.output_forest xml) (Path.basic "proof_cache.xml")
end;

*}

end;
