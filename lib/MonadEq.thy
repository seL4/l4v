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
 * Tactic for solving monadic equalities, such as:
 *
 * (liftE (return 3) = returnOk 3
 *
 * Theorems of the form:
 *
 *   ((a, s') \<in> fst (A s)) = P a s s'
 *
 * and
 *
 *   snd (A s) = P s
 *
 * are added to the "monad_eq" set.
 *)
theory MonadEq
imports "Monad_WP/NonDetMonadVCG"
begin

(* Setup "monad_eq" attributes. *)
ML \<open>
structure MonadEqThms = Named_Thms (
    val name = Binding.name "monad_eq"
    val description = "monad equality-prover theorems"
    )
\<close>
attribute_setup monad_eq = \<open>
  Attrib.add_del
    (Thm.declaration_attribute MonadEqThms.add_thm)
    (Thm.declaration_attribute MonadEqThms.del_thm)\<close>
  "Monad equality-prover theorems"

(* Setup tactic. *)

ML \<open>
fun monad_eq_tac ctxt =
let
  (* Set a simpset as being hidden, so warnings are not printed from it. *)
  val ctxt' = Context_Position.set_visible false ctxt
in
  CHANGED (clarsimp_tac (ctxt' addsimps (MonadEqThms.get ctxt')) 1)
end
\<close>

method_setup monad_eq = \<open>
    Method.sections Clasimp.clasimp_modifiers >> (K (SIMPLE_METHOD o monad_eq_tac))\<close>
  "prove equality on monads"

lemma monad_eq_simp_state [monad_eq]:
  "((A :: ('s, 'a) nondet_monad) s = B s') =
      ((\<forall>r t. (r, t) \<in> fst (A s) \<longrightarrow> (r, t) \<in> fst (B s'))
         \<and> (\<forall>r t. (r, t) \<in> fst (B s') \<longrightarrow> (r, t) \<in> fst (A s))
         \<and> (snd (A s) = snd (B s')))"
  apply (auto intro!: set_eqI prod_eqI)
  done

lemma monad_eq_simp [monad_eq]:
  "((A :: ('s, 'a) nondet_monad) = B) =
      ((\<forall>r t s. (r, t) \<in> fst (A s) \<longrightarrow> (r, t) \<in> fst (B s))
         \<and> (\<forall>r t s. (r, t) \<in> fst (B s) \<longrightarrow> (r, t) \<in> fst (A s))
         \<and> (\<forall>x. snd (A x) = snd (B x)))"
  apply (auto intro!: set_eqI prod_eqI)
  done

declare in_monad [monad_eq]
declare in_bindE [monad_eq]

(* Test *)
lemma "returnOk 3 = liftE (return 3)"
  apply monad_eq
  oops

end
