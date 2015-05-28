(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Sep_Select
imports Separation_Algebra
begin

ML_file "sep_tactics.ML"

ML{* 
 structure SepSelect_Rules = Named_Thms (
  val name = @{binding "sep_select"};
  val description = "sep_select rules";
  );
*}
setup SepSelect_Rules.setup

ML {*
  structure SepSelectAsm_Rules = Named_Thms (
    val name = @{binding "sep_select_asm"};
    val description = "sep_select_asm rules";
  );
*}

setup SepSelectAsm_Rules.setup

ML {*
  fun sep_selects_tactic ns ctxt =
      let val thms = SepSelect_Rules.get ctxt in
      sep_select_tactic (resolve_tac ctxt thms) ns ctxt  
  end;
  
  fun sep_select_asms_tactic ns ctxt =
      let val thms = SepSelectAsm_Rules.get ctxt in
      sep_select_tactic (dresolve_tac ctxt thms) ns ctxt  
  end; 

  fun sep_select_asms_method ns ctxt = SIMPLE_METHOD' 
                                       (sep_select_asms_tactic ns ctxt)
  fun sep_selects_method ns ctxt     = SIMPLE_METHOD' 
                                       (sep_selects_tactic ns ctxt)
*}

lemma sep_eq: "(\<And>s. T s = (P \<and>* R) s) \<Longrightarrow> T s \<Longrightarrow> (P \<and>* R) s" by clarsimp
lemma sep_asm_eq: "(P \<and>* R) s \<Longrightarrow> (\<And>s. T s = (P \<and>* R) s) \<Longrightarrow> T s" by clarsimp

declare sep_eq[sep_select]
declare sep_asm_eq[sep_select_asm]

method_setup sep_select_asm = {*
  Scan.lift (Scan.repeat Parse.int) >> sep_select_asms_method
*} "Reorder assumptions"

method_setup sep_select = {*
  Scan.lift (Scan.repeat Parse.int) >> sep_selects_method
*} "Reorder conclusions"


ML {* 
 fun sep_select_generic_method_inner ((lens, n), asm) ctxt =
   let val lens_tac = (if asm then (dresolve_tac ctxt lens) else (resolve_tac ctxt lens))
    in sep_select_method lens_tac n ctxt
  end;

  fun sep_select_generic_method asm thms ns ctxt =
      sep_select_generic_method_inner ((thms,ns),asm) ctxt
*}

method_setup sep_select_gen = {*
 Attrib.thms --| (Scan.lift Args.colon) -- Scan.lift (Scan.repeat Parse.int) -- (Scan.lift (Args.mode "asm")) >>
 sep_select_generic_method_inner
*}

end
