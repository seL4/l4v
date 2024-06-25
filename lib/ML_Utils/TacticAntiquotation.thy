(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * This provides the ML antiquotations @{inline_tactic} and @{inline_method}.
 * They take a string containing Isabelle method text and give you an ML
 * Tactical.tactic or Method.method, respectively.
 *
 * See TacticAntiquotation_Test for examples.
 *)

theory TacticAntiquotation
imports
  Main
begin

ML \<open>
structure TacticAntiquotation = struct

(* Basically clagged from Pure/ML/ml_thms.ML *)

structure Data = Proof_Data
(
  type T = (string * Method.text) list;
  fun init _ = [];
);

fun method_binding kind method_text ctxt =
  let
    val initial = null (Data.get ctxt);
    val (name, ctxt') = ML_Context.variant kind ctxt;
    val ctxt'' = Data.map (cons (name, method_text)) ctxt';

    fun decl final_ctxt = let
      val method_text_ref = ML_Context.struct_name ctxt ^ "." ^ name;
      (* XXX: it seems that we need to re-evaluate the method text every time
       *      the method is run, otherwise Isabelle complains about a context
       *      mismatch. Figure out how to avoid this *)
      val method_val =
            "(fn facts => fn st => Method.evaluate " ^ method_text_ref ^
              (* XXX: is this the correct way to get dynamic context? *)
              " (Context.the_local_context ()) facts st)";
      val ml_body =
            if kind = "inline_method"
            then method_val
            else "(fn st => NO_CONTEXT_TACTIC " ^
                   (* XXX: as above *)
                   "(Context.the_local_context ()) (" ^ method_val ^ " []) st)";
      in
        if initial then
          let
            val binds = Data.get final_ctxt |> map fst;
            val ml_env = "val [" ^ commas binds ^ "] = " ^
                           "TacticAntiquotation.Data.get ML_context |> map snd;\n";
          in (ml_env, ml_body) end
        else ("", ml_body)
      end;
  in (decl, ctxt'') end;

end
\<close>

setup \<open>
  ML_Antiquotation.declaration
        \<^binding>\<open>inline_tactic\<close>
        Method.text_closure (K (TacticAntiquotation.method_binding "inline_tactic"))
  #>
  ML_Antiquotation.declaration
        \<^binding>\<open>inline_method\<close>
        Method.text_closure (K (TacticAntiquotation.method_binding "inline_method"))
\<close>

end