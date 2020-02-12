(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory SplitRule
imports Main
begin

ML \<open>

fun str_of_term t = Pretty.string_of (Syntax.pretty_term @{context} t)

structure SplitSimps = struct

val conjunct_rules = foldr1 (fn (a, b) => [a, b] MRS conjI);

fun was_split t = let
    val is_free_eq_imp = is_Free o fst o HOLogic.dest_eq
              o fst o HOLogic.dest_imp;
    val get_conjs = HOLogic.dest_conj o HOLogic.dest_Trueprop;
    fun dest_alls (Const ("HOL.All", _) $ Abs (_, _, t)) = dest_alls t
      | dest_alls t = t;
  in forall (is_free_eq_imp o dest_alls) (get_conjs t) end
        handle TERM _ => false;

fun apply_split ctxt split t = Seq.of_list let
    val (t', thaw) = Misc_Legacy.freeze_thaw_robust ctxt t;
  in (map (thaw 0) (filter (was_split o Thm.prop_of) ([t'] RL [split]))) end;

fun forward_tac rules t = Seq.of_list ([t] RL rules);

val refl_imp = refl RSN (2, mp);

val get_rules_once_split =
  REPEAT (forward_tac [conjunct1, conjunct2])
    THEN REPEAT (forward_tac [spec])
    THEN (forward_tac [refl_imp]);

fun do_split ctxt split = let
    val split' = split RS iffD1;
    val split_rhs = Thm.concl_of (fst (Misc_Legacy.freeze_thaw_robust ctxt split'));
  in if was_split split_rhs
     then apply_split ctxt split' THEN get_rules_once_split
     else raise TERM ("malformed split rule: " ^ (str_of_term split_rhs), [split_rhs])
  end;

val atomize_meta_eq = forward_tac [meta_eq_to_obj_eq];

fun better_split ctxt splitthms thm = conjunct_rules
  (Seq.list_of ((TRY atomize_meta_eq
                 THEN (REPEAT (FIRST (map (do_split ctxt) splitthms)))) thm));

val split_att
  = Attrib.thms >>
    (fn thms => Thm.rule_attribute thms (fn context => better_split (Context.proof_of context) thms));


end;

\<close>

ML \<open>
val split_att_setup =
  Attrib.setup @{binding split_simps} SplitSimps.split_att
    "split rule involving case construct into multiple simp rules";
\<close>

setup split_att_setup

definition
  split_rule_test :: "((nat => 'a) + ('b * (('b => 'a) option))) => ('a => nat) => nat"
where
 "split_rule_test x f = f (case x of Inl af \<Rightarrow> af 1
    | Inr (b, None) => inv f 0
    | Inr (b, Some g) => g b)"

lemmas split_rule_test_simps
    = split_rule_test_def[split_simps sum.split prod.split option.split]

end
