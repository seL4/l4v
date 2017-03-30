(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Cache (* FIXME: broken *)
imports "~~/src/HOL/Main"
begin

text {* Enable the proof cache, both skipping from it
        and recording to it. *}
ML {* DupSkip.record_proofs := true *}
ML {* proofs := 1 *}

ML {* DupSkip.skip_dup_proofs := true *}

text {* If executed in reverse order, save the cache *}
ML {* val cache_thy_save_cache = ref false; *}
ML {* 
if (! cache_thy_save_cache)
then File.open_output (XML_Syntax.output_forest
           (XML_Syntax.xml_forest_of_cache (! DupSkip.the_cache)))
       (Path.basic "proof_cache.xml")
else () *}
ML {* cache_thy_save_cache := true *}
ML {* cache_thy_save_cache := false *}

text {* Load the proof cache 
           - can take up to a minute *}

ML {* 
DupSkip.the_cache := XML_Syntax.cache_of_xml_forest (
    File.open_input (XML_Syntax.input_forest)
           (Path.basic "proof_cache.xml")) *}

end
