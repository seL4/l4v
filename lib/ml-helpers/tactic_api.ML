(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*
 * Easy Invocation of Standard Isabelle Tactics.
 *)

signature TACTIC_API =
sig
  datatype tactic_arg =
      SimpOnly
    | SimpAdd of thm
    | SimpDef of thm
    | SplitAdd of thm
    | SplitDel of thm
    | CongAdd of thm
    | CongDel of thm
    | IntroAdd of thm
    | DestAdd of thm
    | ElimAdd of thm
    | SafeIntroAdd of thm
    | SafeDestAdd of thm
    | SafeElimAdd of thm;

  val apply_args_to_ctxt : tactic_arg list -> local_theory -> local_theory

  val auto_tactic : local_theory -> tactic_arg list -> tactic
  val safe_tactic : local_theory -> tactic_arg list -> tactic
  val clarsimp_tactic : local_theory -> tactic_arg list -> int -> tactic
  val fastforce_tactic : local_theory -> tactic_arg list -> int -> tactic
  val force_tactic : local_theory -> tactic_arg list -> int -> tactic
  val blast_tactic : local_theory -> tactic_arg list -> int -> tactic
  val metis_tactic : local_theory -> thm list -> int -> tactic
  val intro_tactic : local_theory -> thm list -> int -> tactic
  val elim_tactic : local_theory -> thm list -> int -> tactic

  val mk_tac : string -> local_theory -> tactic
  val tactic_antiquotation_setup : theory -> theory
end;

structure TacticAPI : TACTIC_API =
struct

(*
 * Standard tactic arguments for adding/deleting theorems to the various
 * theory sets in isabelle.
 *)
datatype tactic_arg =
    SimpOnly
  | SimpAdd of thm
  | SimpDef of thm
  | SplitAdd of thm
  | SplitDel of thm
  | CongAdd of thm
  | CongDel of thm
  | IntroAdd of thm
  | DestAdd of thm
  | ElimAdd of thm
  | SafeIntroAdd of thm
  | SafeDestAdd of thm
  | SafeElimAdd of thm;

(* Update a context with the given list of arguments. *)
fun apply_arg_to_ctxt arg ctxt =
  case arg of
    SimpOnly => Simplifier.map_simpset (K HOL_basic_ss) ctxt
  | SimpAdd thm => Simplifier.map_simpset (Simplifier.add_simp thm) ctxt
  | SimpDef thm => Simplifier.map_simpset (Simplifier.del_simp thm) ctxt
  | SplitAdd thm => Simplifier.map_simpset (Splitter.add_split thm) ctxt
  | SplitDel thm => Simplifier.map_simpset (Splitter.del_split thm) ctxt
  | CongAdd thm => Simplifier.map_simpset (Simplifier.add_cong thm) ctxt
  | CongDel thm => Simplifier.map_simpset (Simplifier.del_cong thm) ctxt
  | IntroAdd thm => ctxt addIs [thm]
  | DestAdd thm => ctxt addDs [thm]
  | ElimAdd thm => ctxt addEs [thm]
  | SafeIntroAdd thm => ctxt addSIs [thm]
  | SafeDestAdd thm => ctxt addSDs [thm]
  | SafeElimAdd thm => ctxt addSEs [thm]

fun apply_args_to_ctxt args ctxt =
  fold apply_arg_to_ctxt args ctxt

(*
 * Perform operations on the context preparing it for use in our tactics.
 *
 * For instance, we mark the context as "hidden" so duplicate simp rules
 * don't produce warnings.
 *)
fun ctxt_init ctxt =
    Context_Position.set_visible false ctxt

(*
 * Standard Isabelle tactics using "tactic_args" to modify their behaviour.
 *
 * Example calls might be:
 *
 *    auto_tac ctxt [SimpAdd @{thm foo}, SimpAdd @{thm bar}]
 *    simp_tac ctxt [SimpOnly @{thm bar}]
 *    clarsimp_tac ctxt [SplitAdd @{thm baz.splits}, SafeIntroAdd @{thm moo}]
 *)

fun auto_tactic ctxt args =
  Clasimp.auto_tac (ctxt_init ctxt |> apply_args_to_ctxt args)

fun safe_tactic ctxt args =
  Classical.safe_tac (ctxt_init ctxt |> apply_args_to_ctxt args)

fun clarsimp_tactic ctxt args n =
  Clasimp.clarsimp_tac (ctxt_init ctxt |> apply_args_to_ctxt args) n

fun fastforce_tactic ctxt args n =
  Clasimp.fast_force_tac (ctxt_init ctxt |> apply_args_to_ctxt args) n

fun force_tactic ctxt args n =
  Clasimp.force_tac (ctxt_init ctxt |> apply_args_to_ctxt args) n

fun blast_tactic ctxt args n =
  Blast.blast_tac (ctxt_init ctxt |> apply_args_to_ctxt args) n

fun metis_tactic ctxt rules n =
  Metis_Tactic.metis_tac
    ATP_Proof_Reconstruct.partial_type_encs
    ATP_Proof_Reconstruct.metis_default_lam_trans
    (ctxt_init ctxt)
    rules n

fun intro_tactic _ rules n =
  (CHANGED_PROP o REPEAT_ALL_NEW (Tactic.match_tac rules)) n

fun elim_tactic _ rules n =
  (CHANGED_PROP o REPEAT_ALL_NEW (Tactic.ematch_tac rules)) n

(*
 * Generate an ML tactic object of the given Isar string.
 *
 * For example,
 *
 *   mk_tac "auto simp: field_simps intro!: ext" @{context}
 *
 * will generate the corresponding "tactic" object.
 *)
fun mk_tac str ctxt =
let
  (* Parse the "tac" input string into a tactic name and token list. *)
  val (tactic_name, tactic_arg_tokens) =
    Outer_Syntax.scan Position.start str
    |> filter Token.is_proper
    |> Args.name
  val tactic_args = Token.src ((tactic_name, tactic_arg_tokens), Position.start)

  (* Parse a list of theorems. *)
  fun parsed_thms _ = Method.syntax Attrib.thms tactic_args ctxt |> fst

  (* Update the input context (such as the simpset, claset) using the
   * given modifiers. *)
  fun update_ctxt modifiers =
    Method.syntax (Method.sections modifiers) tactic_args ctxt |> snd
in
  case tactic_name of
     "clarsimp"  => clarsimp_tac (update_ctxt Clasimp.clasimp_modifiers) 1
   | "simp"      => simp_tac (update_ctxt Simplifier.simp_modifiers' |> simpset_of) 1
   | "auto"      => auto_tac (update_ctxt Clasimp.clasimp_modifiers)
   | "fastforce" => fast_force_tac (update_ctxt Clasimp.clasimp_modifiers) 1
   | "force"     => force_tac (update_ctxt Clasimp.clasimp_modifiers) 1
   | "rule"      => resolve_tac (parsed_thms ()) 1
   | "drule"     => dresolve_tac (parsed_thms ()) 1
   | "erule"     => eresolve_tac (parsed_thms ()) 1
   | "frule"     => forward_tac (parsed_thms ()) 1
   | "metis"     => Metis_Tactic.metis_tac ATP_Proof_Reconstruct.partial_type_encs
                       ATP_Proof_Reconstruct.metis_default_lam_trans ctxt (parsed_thms ()) 1
   | _ => raise Fail ("unknown tactic '" ^ tactic_name ^ "'")
end

(*
 * Setup an antiquotation of the form:
 *
 *    @{tactic "auto simp: foo intro!: bar"}
 *
 * which returns an object of type "context -> tactic".
 *
 * While this doesn't provide any benefits over a direct call to "mk_tac" just
 * yet, in the future it may generate code to avoid parsing the tactic at
 * run-time.
 *)
val tactic_antiquotation_setup =
let
  val parse_string =
    ((Args.context -- Scan.lift Args.name) >> snd)
      #>> ML_Syntax.print_string
      #>> (fn s => "TacticAPI.mk_tac " ^ s)
      #>> ML_Syntax.atomic
in
  ML_Antiquote.inline @{binding "tactic"} parse_string
end

end
