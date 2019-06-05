(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory SEL4SimplExport
imports "AsmRefine.SimplExport" "CSpec.Substitute"
begin

ML \<open>
val csenv = let
    val the_csenv = CalculateState.get_csenv @{theory} "../c/build/$L4V_ARCH/kernel_all.c_pp" |> the
  in fn () => the_csenv end
\<close>

context kernel_all_substitute begin

lemma ctzl_body_refines:
  "simple_simpl_refines \<Gamma> (Guard ImpossibleSpec \<lbrace>\<acute>x \<noteq> 0\<rbrace>
    (\<acute>ret__long :== ucast (bv_ctz (\<acute>x)))) ctzl_body"
  apply (simp add: ctzl_body_def)
  apply (rule simple_simpl_refines_guarded_Basic_guarded_spec_body)
  apply (clarsimp simp: bv_ctz_def meq_def)
  done

lemma clzl_body_refines:
  "simple_simpl_refines \<Gamma> (Guard ImpossibleSpec \<lbrace>\<acute>x \<noteq> 0\<rbrace>
    (\<acute>ret__long :== ucast (bv_clz (\<acute>x)))) clzl_body"
  apply (simp add: clzl_body_def)
  apply (rule simple_simpl_refines_guarded_Basic_guarded_spec_body)
  apply (clarsimp simp: bv_clz_def meq_def)
  done

declare ctcb_offset_defs[simp]

ML \<open>
  emit_C_everything_relative @{context} (csenv ()) "CFunDump.txt";
\<close>

end

end

