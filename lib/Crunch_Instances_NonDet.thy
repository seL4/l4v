(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Crunch_Instances_NonDet
imports
  Crunch
  Monads.WPEx
  Monads.Nondet_Empty_Fail
  Monads.Nondet_No_Fail
begin

lemmas [crunch_param_rules] = Let_def return_bind returnOk_bindE
    K_bind_def split_def bind_assoc bindE_assoc
    trans[OF liftE_bindE return_bind]

ML \<open>
  fun dest_nondet_monad (Type (@{type_name "fun"},
                          [Type (@{type_name "monad_state_record_ext"}, [env, st]),
                           Type (@{type_name "prod"},
                             [Type (@{type_name "set"}, [Type (@{type_name "prod"}, [rv, st'])]),
                              @{typ bool}])])) = if st = st' then SOME (env, st, rv) else NONE
    | dest_nondet_monad _ = NONE

  fun is_nondet_monad T = dest_nondet_monad T <> NONE

  fun mk_nondet_monad (env, st, rv) =
                    Type (@{type_name "fun"},
                          [Type (@{type_name "monad_state_record_ext"}, [env, st]),
                           Type (@{type_name "prod"},
                             [Type (@{type_name "set"}, [Type (@{type_name "prod"}, [rv, st])]),
                              @{typ bool}])])
\<close>

ML \<open>
structure CrunchValidInstance : CrunchInstance =
struct
  val name = "valid";
  val prefix_name_scheme = false;
  type extra = term;
  val eq_extra = ae_conv;
  fun parse_extra ctxt extra
        = case extra of
            "" => error "A post condition is required"
          | extra => let val pre = Syntax.parse_term ctxt extra
              in (pre, Abs ("_", dummyT, pre)) end;
  val has_preconds = true;
  fun mk_term pre body post =
    (Syntax.parse_term @{context} "valid") $ pre $ body $ post;
  fun dest_term ((Const (@{const_name "valid"}, _)) $ pre $ body $ post)
        = SOME (pre, body, post)
    | dest_term _ = NONE;
  fun put_precond pre ((v as Const (@{const_name "valid"}, _)) $ _ $ body $ post)
        = v $ pre $ body $ post
    | put_precond _ _ = error "put_precond: not a hoare triple";
  val pre_thms = @{thms "hoare_pre"};
  val wpc_tactic = wp_cases_tactic_weak;
  val wps_tactic = wps_tac;
  val magic = Syntax.parse_term @{context}
    "\<lambda>mapp_lambda_ignore. valid P_free_ignore mapp_lambda_ignore Q_free_ignore";
  val is_monad_type = is_nondet_monad;
end;

structure CrunchValid : CRUNCH = Crunch(CrunchValidInstance);

structure CrunchNoFailInstance : CrunchInstance =
struct
  val name = "no_fail";
  val prefix_name_scheme = true;
  type extra = unit;
  val eq_extra = op =;
  fun parse_extra ctxt extra
        = case extra of
            "" => (Syntax.parse_term ctxt "%_. True", ())
          | _ => (Syntax.parse_term ctxt extra, ());
  val has_preconds = true;
  fun mk_term pre body _ =
    (Syntax.parse_term @{context} "no_fail") $ pre $ body;
  fun dest_term ((Const (@{const_name "no_fail"}, _)) $ pre $ body)
        = SOME (pre, body, ())
    | dest_term _ = NONE;
  fun put_precond pre ((v as Const (@{const_name "no_fail"}, _)) $ _ $ body)
        = v $ pre $ body
    | put_precond _ _ = error "put_precond: not a no_fail term";
  val pre_thms = @{thms "no_fail_pre"};
  val wpc_tactic = wp_cases_tactic_weak;
  fun wps_tactic _ _ _ = no_tac;
  val magic = Syntax.parse_term @{context}
    "\<lambda>mapp_lambda_ignore. no_fail P_free_ignore mapp_lambda_ignore";
  val is_monad_type = is_nondet_monad;
end;

structure CrunchNoFail : CRUNCH = Crunch(CrunchNoFailInstance);

structure CrunchEmptyFailInstance : CrunchInstance =
struct
  val name = "empty_fail";
  val prefix_name_scheme = false;
  type extra = unit;
  val eq_extra = op =;
  fun parse_extra ctxt extra
        = case extra of
            "" => (Syntax.parse_term ctxt "%_. True", ())
          | _ => error "empty_fail does not need a precondition";
  val has_preconds = false;
  fun mk_term _ body _ =
    (Syntax.parse_term @{context} "empty_fail") $ body;
  fun dest_term (Const (@{const_name empty_fail}, _) $ b)
        = SOME (Term.dummy, b, ())
    | dest_term _ = NONE;
  fun put_precond _ _ = error "crunch empty_fail should not be calling put_precond";
  val pre_thms = [];
  val wpc_tactic = wp_cases_tactic_weak;
  fun wps_tactic _ _ _ = no_tac;
  val magic = Syntax.parse_term @{context}
    "\<lambda>mapp_lambda_ignore. empty_fail mapp_lambda_ignore";
  val is_monad_type = is_nondet_monad;
end;

structure CrunchEmptyFail : CRUNCH = Crunch(CrunchEmptyFailInstance);

structure CrunchValidEInstance : CrunchInstance =
struct
  val name = "valid_E";
  val prefix_name_scheme = false;
  type extra = term * term;
  fun eq_extra ((a, b), (c, d)) = (ae_conv (a, c) andalso ae_conv (b, d));
  fun parse_extra ctxt extra
        = case extra of
            "" => error "A post condition is required"
          | extra => let val pre = Syntax.parse_term ctxt extra
              in (pre, (Abs ("_", dummyT, pre), Abs ("_", dummyT, pre))) end;
  val has_preconds = true;
  fun mk_term pre body extra =
    (Syntax.parse_term @{context} "validE") $ pre $ body $ fst extra $ snd extra;
  fun dest_term (Const (@{const_name "validE"}, _) $ pre $ body $ p1 $ p2)
        = SOME (pre, body, (p1, p2))
    | dest_term _ = NONE;
  fun put_precond pre ((v as Const (@{const_name "validE"}, _)) $ _ $ body $ post $ post')
        = v $ pre $ body $ post $ post'
    | put_precond _ _ = error "put_precond: not a validE term";
  val pre_thms = @{thms "hoare_pre"};
  val wpc_tactic = wp_cases_tactic_weak;
  val wps_tactic = wps_tac;
  val magic = Syntax.parse_term @{context}
    "\<lambda>mapp_lambda_ignore. validE P_free_ignore mapp_lambda_ignore Q_free_ignore Q_free_ignore";
  val is_monad_type = is_nondet_monad;
end;

structure CrunchValidE : CRUNCH = Crunch(CrunchValidEInstance);
\<close>

setup \<open>
  add_crunch_instance "" (CrunchValid.crunch_x, CrunchValid.crunch_ignore_add_dels)
\<close>
setup \<open>
  add_crunch_instance "valid" (CrunchValid.crunch_x, CrunchValid.crunch_ignore_add_dels)
\<close>
setup \<open>
  add_crunch_instance "no_fail" (CrunchNoFail.crunch_x, CrunchNoFail.crunch_ignore_add_dels)
\<close>
setup \<open>
  add_crunch_instance "empty_fail" (CrunchEmptyFail.crunch_x, CrunchEmptyFail.crunch_ignore_add_dels)
\<close>

end