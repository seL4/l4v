(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Crunch_Instances_Trace
imports
  Crunch
  "Monad_WP/TraceMonadVCG"
begin

lemmas [crunch_param_rules] = Let_def return_bind returnOk_bindE
    K_bind_def split_def bind_assoc bindE_assoc
    trans[OF liftE_bindE return_bind]

ML \<open>
fun get_trace_monad_state_type
  (Type ("Set.set",
         [Type ("Product_Type.prod",
                [Type ("List.list", [Type ("Product_Type.prod", [_,v])]), _])]))
      = SOME v
  | get_trace_monad_state_type _ = NONE

structure CrunchValidInstance : CrunchInstance =
struct
  val name = "valid";
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
  val magic = Syntax.parse_term @{context}
    "\<lambda>mapp_lambda_ignore. valid P_free_ignore mapp_lambda_ignore Q_free_ignore";
  val get_monad_state_type = get_trace_monad_state_type;
end;

structure CrunchValid : CRUNCH = Crunch(CrunchValidInstance);

structure CrunchNoFailInstance : CrunchInstance =
struct
  val name = "no_fail";
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
  val magic = Syntax.parse_term @{context}
    "\<lambda>mapp_lambda_ignore. no_fail P_free_ignore mapp_lambda_ignore";
  val get_monad_state_type = get_trace_monad_state_type;
end;

structure CrunchNoFail : CRUNCH = Crunch(CrunchNoFailInstance);

structure CrunchValidEInstance : CrunchInstance =
struct
  val name = "valid_E";
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
  val magic = Syntax.parse_term @{context}
    "\<lambda>mapp_lambda_ignore. validE P_free_ignore mapp_lambda_ignore Q_free_ignore Q_free_ignore";
  val get_monad_state_type = get_trace_monad_state_type;
end;

structure CrunchValidE : CRUNCH = Crunch(CrunchValidEInstance);

structure CrunchPrefixClosedInstance : CrunchInstance =
struct
  val name = "prefix_closed";
  type extra = unit;
  val eq_extra = op =;
  fun parse_extra ctxt extra
        = case extra of
            "" => (Syntax.parse_term ctxt "%_. True", ())
          | _ => error "prefix_closed does not need a precondition";
  val has_preconds = false;
  fun mk_term _ body _ =
    (Syntax.parse_term @{context} "prefix_closed") $ body;
  fun dest_term (Const (@{const_name prefix_closed}, _) $ b)
        = SOME (Term.dummy, b, ())
    | dest_term _ = NONE;
  fun put_precond _ _ = error "crunch prefix_closed should not be calling put_precond";
  val pre_thms = [];
  val wpc_tactic = wp_cases_tactic_weak;
  val magic = Syntax.parse_term @{context}
    "\<lambda>mapp_lambda_ignore. prefix_closed mapp_lambda_ignore";
  val get_monad_state_type = get_trace_monad_state_type;
end;

structure CrunchPrefixClosed : CRUNCH = Crunch(CrunchPrefixClosedInstance);
\<close>

setup \<open>
  add_crunch_instance "" (CrunchValid.crunch_x, CrunchValid.crunch_ignore_add_del)
\<close>
setup \<open>
  add_crunch_instance "valid" (CrunchValid.crunch_x, CrunchValid.crunch_ignore_add_del)
\<close>
setup \<open>
  add_crunch_instance "no_fail" (CrunchNoFail.crunch_x, CrunchNoFail.crunch_ignore_add_del)
\<close>
setup \<open>
  add_crunch_instance "pfx_closed" (CrunchPrefixClosed.crunch_x, CrunchPrefixClosed.crunch_ignore_add_del)
\<close>

end