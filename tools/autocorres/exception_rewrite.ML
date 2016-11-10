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
 * Rewrite L1 specifications to reduce the use of exception constructs.
 *)
structure ExceptionRewrite =
struct

(*
 * States what control flow a block of code exhibits.
 *
 * NoThrow and NoReturn states that the block never/always throws exceptions.
 *
 * AlwaysFail states that the block always fails (with no return states); this
 * can be converted into either NoThrow or NoReturn at will.
 *
 * UnknownExc states that we just don't know what the block of code does.
 *)
datatype exc_status =
    NoThrow of thm
  | NoReturn of thm
  | AlwaysFail of thm
  | UnknownExc

(* Convert a "always_fail" theorem into a "no_throw" or "no_return" theorem. *)
fun fail_to_nothrow t = @{thm alwaysfail_nothrow} OF [t]
fun fail_to_noreturn t = @{thm alwaysfail_noreturn} OF [t]

(*
 * Anonymize "uninteresting" parts of a L1 program to make caching more efficient.
 *
 * Structure of the program is retained, but everything else becomes bogus.
 *)
fun anon term =
  case term of
      (Const (@{const_name "L1_skip"}, _)) => @{term L1_skip}
    | (Const (@{const_name "L1_modify"}, _) $ _) => @{term "L1_modify m"}
    | (Const (@{const_name "L1_guard"}, _) $ _) => @{term "L1_guard g"}
    | (Const (@{const_name "L1_init"}, _) $ _) => @{term "L1_init i"}
    | (Const (@{const_name "L1_spec"}, _) $ _) => @{term "L1_spec s"}
    | (Const (@{const_name "L1_throw"}, _)) => @{term "L1_throw"}
    | (Const (@{const_name "L1_fail"}, _)) => @{term "L1_fail"}
    | (Const (@{const_name "L1_call"}, _) $ _ $ body $ _ $ _) =>
        @{term "L1_call"} $ Free ("a", dummyT) $ anon body $ Free ("b", dummyT) $ Free ("c", dummyT)
    | (Const (@{const_name "L1_condition"}, _) $ _ $ lhs $ rhs) =>
        @{term "L1_condition"} $ Free ("C", dummyT) $ anon lhs $ anon rhs
    | (Const (@{const_name "L1_seq"}, _) $ lhs $ rhs) =>
        @{term "L1_seq"} $ anon lhs $ anon rhs
    | (Const (@{const_name "L1_catch"}, _) $ lhs $ rhs) =>
        @{term "L1_catch"} $ anon lhs $ anon rhs
    | (Const (@{const_name "L1_while"}, _) $ _ $ body) =>
        @{term "L1_while"} $ Free ("C", dummyT) $ anon body
    | x => x

(*
 * Prove "empty_fail" on a block of code.
 *
 * That is, if a block of code does not return any states (such as "select {}"),
 * that block of code also sets the "fail" flag.
 *
 * All code we generate should obey this property.
 *)
fun empty_fail term =
  case term of
      (Const (@{const_name "L1_skip"}, _)) => @{thm L1_skip_empty_fail}
    | (Const (@{const_name "L1_modify"}, _) $ _) => @{thm L1_modify_empty_fail}
    | (Const (@{const_name "L1_guard"}, _) $ _) => @{thm L1_guard_empty_fail}
    | (Const (@{const_name "L1_init"}, _) $ _) => @{thm L1_init_empty_fail}
    | (Const (@{const_name "L1_spec"}, _) $ _) => @{thm L1_spec_empty_fail}
    | (Const (@{const_name "L1_throw"}, _)) => @{thm L1_throw_empty_fail}
    | (Const (@{const_name "L1_fail"}, _)) => @{thm L1_fail_empty_fail}
    | (Const (@{const_name "L1_call"}, _) $ _ $ body $ _ $ _) =>
        @{thm L1_call_empty_fail} OF [empty_fail body]
    | (Const (@{const_name "L1_condition"}, _) $ _ $ lhs $ rhs) =>
        @{thm L1_condition_empty_fail} OF [empty_fail lhs, empty_fail rhs]
    | (Const (@{const_name "L1_seq"}, _) $ lhs $ rhs) =>
        @{thm L1_seq_empty_fail} OF [empty_fail lhs, empty_fail rhs]
    | (Const (@{const_name "L1_catch"}, _) $ lhs $ rhs) =>
        @{thm L1_catch_empty_fail} OF [empty_fail lhs, empty_fail rhs]
    | (Const (@{const_name "L1_while"}, _) $ _ $ body) =>
        @{thm L1_while_empty_fail} OF [empty_fail body]
    | x => Utils.invalid_term "L1_term" x
val empty_fail = Term_Ord.term_cache (fn x => empty_fail (anon x))

(*
 * Determine what control flow the given block of code exhibits.
 *)
fun throws_exception' term =
  case term of
      (Const (@{const_name "L1_skip"}, _)) =>
        NoThrow @{thm L1_skip_nothrow}
    | (Const (@{const_name "L1_modify"}, _) $ _) =>
        NoThrow @{thm L1_modify_nothrow}
    | (Const (@{const_name "L1_guard"}, _) $ _) =>
        NoThrow @{thm L1_guard_nothrow}
    | (Const (@{const_name "L1_call"}, _) $ _ $ _ $ _ $ _) =>
        NoThrow @{thm L1_call_nothrow}
    | (Const (@{const_name "L1_init"}, _) $ _) =>
        NoThrow @{thm L1_init_nothrow}
    | (Const (@{const_name "L1_spec"}, _) $ _) =>
        NoThrow @{thm L1_spec_nothrow}
    | (Const (@{const_name "L1_throw"}, _)) =>
        NoReturn @{thm L1_throw_noreturn}
    | (Const (@{const_name "L1_fail"}, _)) =>
        AlwaysFail @{thm L1_fail_alwaysfail}

    | (Const (@{const_name "L1_while"}, _) $ _ $ body) =>
       (case (throws_exception' body) of
           NoThrow thm => NoThrow (@{thm L1_while_nothrow} OF [thm])
         | _ => UnknownExc)

    | (Const (@{const_name "L1_condition"}, _) $ _ $ lhs $ rhs) =>
        (case (throws_exception' lhs, throws_exception' rhs) of
            (AlwaysFail lhs_thm, AlwaysFail rhs_thm) =>
              AlwaysFail (@{thm L1_condition_alwaysfail} OF [lhs_thm, rhs_thm])
          | (NoThrow lhs_thm, NoThrow rhs_thm) =>
              NoThrow (@{thm L1_condition_nothrow} OF [lhs_thm, rhs_thm])
          | (NoReturn lhs_thm, NoReturn rhs_thm) =>
              NoReturn (@{thm L1_condition_noreturn} OF [lhs_thm, rhs_thm])

          | (NoThrow lhs_thm, AlwaysFail rhs_thm) =>
              NoThrow (@{thm L1_condition_nothrow} OF [lhs_thm, fail_to_nothrow rhs_thm])
          | (NoReturn lhs_thm, AlwaysFail rhs_thm) =>
              NoReturn (@{thm L1_condition_noreturn} OF [lhs_thm, fail_to_noreturn rhs_thm])
          | (AlwaysFail lhs_thm, NoThrow rhs_thm) =>
              NoThrow (@{thm L1_condition_nothrow} OF [fail_to_nothrow lhs_thm, rhs_thm])
          | (AlwaysFail lhs_thm, NoReturn rhs_thm) =>
              NoReturn (@{thm L1_condition_noreturn} OF [fail_to_noreturn lhs_thm, rhs_thm])

          | (_, _) => UnknownExc)

    | (Const (@{const_name "L1_seq"}, _) $ lhs $ rhs) =>
        (case (throws_exception' lhs, throws_exception' rhs,
            SOME (empty_fail lhs) handle Utils.InvalidInput _ => NONE) of
            (AlwaysFail lhs_thm, _, _) =>
              AlwaysFail (@{thm L1_seq_alwaysfail_lhs} OF [lhs_thm])
          | (NoThrow lhs_thm, AlwaysFail rhs_thm, SOME ef) =>
              AlwaysFail (@{thm L1_seq_alwaysfail_rhs} OF [ef, lhs_thm, rhs_thm])
          | (NoThrow lhs_thm, AlwaysFail rhs_thm, _) =>
              NoThrow (@{thm L1_seq_nothrow} OF [lhs_thm, fail_to_nothrow rhs_thm])
          | (NoReturn lhs_thm, _, _) =>
              NoReturn (@{thm L1_seq_noreturn_lhs} OF [lhs_thm])
          | (_, NoReturn rhs_thm, _) =>
              NoReturn (@{thm L1_seq_noreturn_rhs} OF [rhs_thm])
          | (NoThrow lhs_thm, NoThrow rhs_thm, _) =>
              NoThrow (@{thm L1_seq_nothrow} OF [lhs_thm, rhs_thm])
          | (_, _, _) =>
              UnknownExc)

    | (Const (@{const_name "L1_catch"}, _) $ lhs $ rhs) =>
        (case (throws_exception' lhs, throws_exception' rhs,
            SOME (empty_fail lhs) handle Utils.InvalidInput _ => NONE) of
            (AlwaysFail lhs_thm, _, _) =>
              AlwaysFail (@{thm L1_catch_alwaysfail_lhs} OF [lhs_thm])
          | (NoReturn lhs_thm, AlwaysFail rhs_thm, SOME ef) =>
              AlwaysFail (@{thm L1_catch_alwaysfail_rhs} OF [ef, lhs_thm, rhs_thm])
          | (NoReturn lhs_thm, AlwaysFail rhs_thm, _) =>
              NoReturn (@{thm L1_catch_noreturn} OF [lhs_thm, fail_to_noreturn rhs_thm])
          | (NoReturn lhs_thm, NoReturn rhs_thm, _) =>
              NoReturn (@{thm L1_catch_noreturn} OF [lhs_thm, rhs_thm])
          | (NoThrow lhs_thm, _, _) =>
              NoThrow (@{thm L1_catch_nothrow_lhs} OF [lhs_thm])
          | (_, NoThrow rhs_thm, _) =>
              NoThrow (@{thm L1_catch_nothrow_rhs} OF [rhs_thm])
          | (_, _, _) =>
              UnknownExc)

    | x => (warning ("throws_exception: Unknown term: " ^ (@{make_string} x)); UnknownExc)
val throws_exception = Term_Ord.term_cache (fn x => throws_exception' (anon x))


(*
 * Simprocs.
 *)

(*
 * L1_condition simplification procedure.
 *
 * Most conversions to non-exception form are trivial rewrites. The one exception
 * is "L1_condition", which _does_ have a simple conversion which causes exponential
 * blow-up in code size in the worst case.
 *
 * We hence use this complex simproc to determine if we are in a safe situation or not.
 * If so, we perform the rewrite. Otherwise, we just leave the exceptions in place.
 *)
fun l1_condition_simproc redex =
  case Thm.term_of redex of
      (Const (@{const_name "L1_catch"}, _)
          $ (Const (@{const_name "L1_seq"}, _)
            $ (Const (@{const_name "L1_condition"}, _) $ _ $ cond_lhs $ cond_rhs)
            $ seq_rhs)
        $ exc) =>
      let
        val cond_lhs_res = throws_exception cond_lhs
        val cond_rhs_res = throws_exception cond_rhs
        val exc_res = throws_exception exc
        val seq_rhs_is_short = case seq_rhs of
            (Const (@{const_name "L1_skip"}, _)) => true
          | (Const (@{const_name "L1_throw"}, _)) => true
          | (Const (@{const_name "L1_fail"}, _)) => true
          | _ => false
      in
        case (cond_lhs_res, cond_rhs_res, exc_res, seq_rhs_is_short) of
            (NoThrow l, NoThrow r, _, _) =>
              SOME (@{thm L1_catch_seq_cond_nothrow} OF [l, r])
          | (NoThrow l, AlwaysFail r, _, _) =>
              SOME (@{thm L1_catch_seq_cond_nothrow} OF [l, fail_to_nothrow r])
          | (AlwaysFail l, NoThrow r, _, _) =>
              SOME (@{thm L1_catch_seq_cond_nothrow} OF [fail_to_nothrow l, r])
          | (AlwaysFail l, AlwaysFail r, _, _) =>
              SOME (@{thm L1_catch_seq_cond_nothrow} OF [fail_to_nothrow l, fail_to_nothrow r])

          (* L1_catch_cond_seq can cause exponential blowup: the
           * following cases are safe, because one side will always
           * cause "seq_rhs" to be stripped away. *)
          | (NoReturn _, _, _, _) =>
              SOME (@{thm L1_catch_cond_seq})
          | (_, NoReturn _, _, _) =>
              SOME (@{thm L1_catch_cond_seq})
          | (AlwaysFail _, _, _, _) =>
              SOME (@{thm L1_catch_cond_seq})
          | (_, AlwaysFail _, _, _) =>
              SOME (@{thm L1_catch_cond_seq})

          (* Only duplicating something tiny. *)
          | (_, _, _, true) =>
              SOME (@{thm L1_catch_cond_seq})

          (* The exception handler doesn't return. *)
          | (_, _, NoReturn thm, _) =>
              SOME (@{thm L1_catch_seq_cond_noreturn_ex} OF [thm])
          | (_, _, AlwaysFail thm, _) =>
              SOME (@{thm L1_catch_seq_cond_noreturn_ex} OF [fail_to_noreturn thm])

          (* May cause duplication of "rhs_seq" which we don't want,
           * so we don't optimise in this case. *)
          | _ => NONE
      end
    | _ => NONE

fun nothrow_simproc redex =
  case Thm.term_of redex of
      (Const (@{const_name "no_throw"}, _)
          $ Abs (_, _, Const (@{const_name True}, _))
          $ body) =>
        (case throws_exception body of
            NoThrow thm => SOME thm
          | AlwaysFail thm => SOME (fail_to_nothrow thm)
          | _ => NONE)
    | _ => NONE

fun noreturn_simproc redex =
  case Thm.term_of redex of
      (Const (@{const_name "no_return"}, _)
          $ Abs (_, _, Const (@{const_name True}, _))
          $ body) =>
        (case throws_exception body of
            NoReturn thm => SOME thm
          | AlwaysFail thm => SOME (fail_to_noreturn thm)
          | _ => NONE)
    | _ => NONE

fun alwaysfail_simproc redex =
  case Thm.term_of redex of
      (Const (@{const_name "always_fail"}, _)
          $ Abs (_, _, Const (@{const_name True}, _))
          $ body) =>
        (case throws_exception body of
            AlwaysFail thm => SOME thm
          | _ => NONE)
    | _ => NONE

fun emptyfail_simproc redex =
  case Thm.term_of redex of
      (Const (@{const_name "empty_fail"}, _)
          $ body) =>
        ((SOME (empty_fail body)) handle Utils.InvalidInput _ => NONE)
    | _ => NONE

val simprocs =
let
  fun wrapper proc =
    fn ctxt => fn x =>
      proc x
      |> Option.map (fn thm => Raw_Simplifier.mksimps ctxt thm |> hd)
in
  map (Utils.mk_simproc' @{context}) [
    ("l1_condition_simproc",
        ["L1_catch (L1_seq (L1_condition ?c ?L ?R) ?X) ?E"],
        wrapper l1_condition_simproc),
    ("nothrow_simproc", ["no_throw \<top> ?X"], wrapper nothrow_simproc),
    ("noreturn_simproc", ["no_return \<top> ?X"], wrapper noreturn_simproc),
    ("alwaysfail_simproc", ["always_fail \<top> ?X"], wrapper alwaysfail_simproc),
    ("emptyfail_simproc", ["empty_fail ?X"], wrapper emptyfail_simproc)
  ]
end

(* Exception rewrite conversion. *)
fun except_rewrite_conv ctxt do_opt =
  Simplifier.asm_full_rewrite (
    put_simpset HOL_basic_ss (Utils.set_hidden_ctxt ctxt)
        addsimps (Utils.get_rules ctxt @{named_theorems L1except})
        addsimps (if do_opt then Utils.get_rules ctxt @{named_theorems L1opt} else [])
        addsimprocs simprocs)

end
