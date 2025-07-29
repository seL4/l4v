(*
 * Copyright 2025, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Multikernel_C
imports ArchMultikernel_C
begin

ML \<open>
structure GammaLift = struct
  (* Prove impl theorem for x_proc of the form "\<Gamma> x_'proc = x_body"
     from existing x_impl on \<Gamma>0 and x_'proc \<noteq> special_'proc.
     Return (thm name, thm). *)
  fun prove_impl ctxt special_proc_def gamma_def gamma proc =
  let
    val _ = tracing ("Proving impl theorem for " ^ proc)
    val body_name = unsuffix Hoare.proc_deco proc |> suffix "_body"
    val impl_name = unsuffix Hoare.proc_deco proc |> suffix HoarePackage.implementationN
    val impl_goal =
      Syntax.read_term ctxt (gamma ^ " " ^ proc ^ " = Some " ^ body_name)
      |> HOLogic.mk_Trueprop
    val proc_def = Proof_Context.get_thm ctxt (proc ^ "_def")
    val impl_thm = Proof_Context.get_thm ctxt impl_name
    fun impl_tac _ = EVERY [
      simp_tac (ctxt addsimps [gamma_def]) 1,
      resolve_tac ctxt @{thms conjI} 1,
      simp_tac (ctxt addsimps [special_proc_def, proc_def]) 1,
      resolve_tac ctxt @{thms impI} 1,
      resolve_tac ctxt [impl_thm] 1]
  in
    (impl_name, Goal.prove_future ctxt [] [] impl_goal impl_tac)
  end

  (* Prove all *_impl theorems, except for the procedure "special",
     which we assume has been overridden. *)
  fun prove_impls special gamma0 gamma ctxt =
  let
    val special_proc = suffix Hoare.proc_deco special
    val special_proc_def = Proof_Context.get_thm ctxt (special_proc ^ "_def")

    val gamma0_def = Proof_Context.get_thm ctxt (gamma0 ^ "_def")
    val gamma_def = Proof_Context.get_thm ctxt (gamma ^ "_def")

    (* \<Gamma>0 is a tree definition that mentions all *_proc constants.
       Start with all constants in \<Gamma>0_def and filter out the one we want *)
    val proc_names =
      Term.add_const_names (Thm.concl_of gamma0_def) []
      |> filter (String.isSuffix Hoare.proc_deco)
      |> filter (fn name => Long_Name.base_name name <> special_proc)
      |> map Long_Name.base_name

    val impls = map (prove_impl ctxt special_proc_def gamma_def gamma) proc_names
  in
    Local_Theory.notes (map (fn (n, thm) => ((Binding.name n, []), [([thm], [])])) impls) ctxt |> snd
  end
end
\<close>

context kernel_all_substitute
begin

(* prove *_impl theorems *)
local_setup \<open>GammaLift.prove_impls special_proc_name "\<Gamma>0" "\<Gamma>"\<close>

(* prove *_modifies theorems in \<Gamma> *)
local_setup \<open>
  (fn lthy =>
      Context_Position.set_visible false lthy |>
      Modifies_Proofs.prove_all_modifies_goals_local
        (CalculateState.get_csenv @{theory} "../c/build/$L4V_ARCH/kernel_all.c_pp" |> the)
        "\<Gamma>"
        (fn _ => true)
        [@{typ "globals myvars"}, @{typ int}, @{typ strictc_errortype}] |>
      Context_Position.restore_visible lthy)
\<close>

end

end
