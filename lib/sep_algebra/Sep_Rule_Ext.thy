(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Sep_Rule_Ext
imports
  Sep_Provers
  Sep_Attribs
  Sep_ImpI
  Sep_MP
begin


ML {*
  fun backwardise ctxt thm = SOME (backward ctxt thm) handle THM _  => NONE
  fun sep_curry ctxt thm = SOME (sep_curry_inner ctxt thm) handle THM _ => NONE

  fun make_sep_drule direct thms ctxt i =
  let
    val default = sep_drule_comb_tac direct
    fun make_sep_rule_inner i thm =
    let
      val goal = i + Thm.nprems_of thm - 1
    in
      case sep_curry ctxt thm of
        SOME thm' =>
          (sep_drule_tac (fn i => sep_drule_tactic ctxt [thm'] i THEN
                                  (sep_mp_solver ctxt THEN' (TRY o sep_flatten ctxt)) goal) ctxt) i
      | NONE => default [thm] ctxt i
    end
  in
    if direct then default thms ctxt i else FIRST (map (make_sep_rule_inner i) thms)
  end

  fun make_sep_rule direct thms ctxt =
  let
    val default = sep_rule_comb_tac direct
    fun make_sep_rule_inner thm =
      case backwardise ctxt thm of
        SOME thm' => sep_rule_comb_tac true [thm'] ctxt THEN'
                     REPEAT_ALL_NEW (sep_match_trivial_tac ctxt) THEN'
                     TRY o sep_flatten ctxt
      | NONE => default [thm] ctxt
  in
    if direct then default thms ctxt else  FIRST' (map make_sep_rule_inner thms)
  end

  fun sep_rule_method direct thms ctxt = SIMPLE_METHOD' (make_sep_rule direct thms ctxt)
  fun sep_drule_method direct thms ctxt = SIMPLE_METHOD' (make_sep_drule direct thms ctxt)
*}

method_setup sep_rule = {*
  Scan.lift (Args.mode "direct") -- Attrib.thms  >> uncurry sep_rule_method
*}

method_setup sep_drule = {*
  Scan.lift (Args.mode "direct") -- Attrib.thms  >> uncurry sep_drule_method
*}

end
