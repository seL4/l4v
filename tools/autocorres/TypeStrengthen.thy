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
 * Strengthen functions into simpler monads.
 *
 * Each block of lifting lemmas converts functions in the "L2" monadic
 * framework (an exception framework) into its own framework.
 *)

theory TypeStrengthen
imports
  L2Defs
  "Lib.OptionMonadND"
  ExecConcrete
begin

(* Set up the database and ts_rule attribute. *)
ML_file "monad_types.ML"
setup \<open>
 Attrib.setup (Binding.name "ts_rule") Monad_Types.ts_attrib
              "AutoCorres type strengthening rule"
\<close>

(*
 * Helpers for exception polymorphism lemmas (L2_call_Foo_polymorphic).
 *
 * They are used to rewrite a term like
 *
 *   L2_call x = Foo y
 *
 * into an identical term with a different exception type.
 *)

definition
  unliftE
where
  "unliftE (x :: ('a, 'u + 'b) nondet_monad) \<equiv> x <catch> (\<lambda>_. fail)"

lemma L2_call_liftE_unliftE:
    "L2_call x = liftE (unliftE (L2_call x))"
  apply (clarsimp simp: L2_call_def unliftE_def)
  apply (rule ext)
  apply (clarsimp simp: handleE'_def catch_def liftE_def bind_assoc)
  apply (clarsimp cong: bind_apply_cong)
  apply (clarsimp simp: bind_def split_def return_def split: sum.splits)
  apply (force simp: return_def fail_def split: sum.splits)+
  done

lemma unliftE_liftE [simp]:
    "unliftE (liftE x) = x"
  apply (clarsimp simp: unliftE_def catch_liftE)
  done



(*
 * Lifting into pure functional Isabelle.
 *)

definition "TS_return x \<equiv> liftE (return x)"

lemma L2_call_TS_return: "L2_call (TS_return a) = L2_gets (\<lambda>_. a) [''ret'']"
  apply (monad_eq simp: L2_call_def L2_gets_def TS_return_def)
  done

lemma TS_return_L2_gets:
    "L2_gets (\<lambda>_. P) n = TS_return P"
  by (monad_eq simp: L2_defs TS_return_def)

lemma L2_call_L2_gets_polymorphic:
  "(L2_call x :: ('s, 'a, 'e1) L2_monad) = L2_gets y n
    \<Longrightarrow> (L2_call x  :: ('s, 'a, 'e2) L2_monad) = L2_gets y n"
  apply (monad_eq simp: L2_defs L2_call_def Ball_def split: sum.splits)
  apply blast
  done

setup \<open>
Monad_Types.new_monad_type
  "pure"
  "Pure function"
  (Monad_Types.check_lifting_head [@{term "TS_return"}])
  100
  @{thms L2_call_TS_return TS_return_L2_gets}
  @{term "(%a. L2_gets (%_. a) [''ret'']) :: 'a => ('s, 'a, unit) L2_monad"}
  @{thm L2_call_L2_gets_polymorphic}
  #2
  (fn _ => error "monad_mono not applicable for pure monad")
|> Context.theory_map
\<close>

lemma TS_return_L2_seq:
    "L2_seq (TS_return A) (\<lambda>a. TS_return (B a))
       = TS_return (let a = A in B a)"
  by (monad_eq simp: L2_defs TS_return_def)

lemma TS_return_L2_condition:
    "L2_condition (\<lambda>_. c) (TS_return A) (TS_return B) = TS_return (if c then A else B)"
  by (monad_eq simp: L2_defs TS_return_def)

lemmas [ts_rule pure] =
  TS_return_L2_gets
  TS_return_L2_seq
  TS_return_L2_condition
  split_distrib[where T = TS_return]

lemma L2_seq_TS_return:
    "TS_return (let a = A in B a) = L2_seq (L2_gets (\<lambda>_. A) []) (\<lambda>a. L2_gets (\<lambda>_. B a) [])"
  by (monad_eq simp: L2_defs TS_return_def)

lemma L2_condition_TS_return:
    "TS_return (if c then A else B) = L2_condition (\<lambda>_. c) (L2_gets (\<lambda>_. A) []) (L2_gets (\<lambda>_. B) [])"
  by (monad_eq simp: L2_defs TS_return_def)

lemmas [ts_rule pure unlift] =
  TS_return_L2_gets      [where n = "[]", symmetric]
  TS_return_L2_seq       [symmetric]
  TS_return_L2_condition [symmetric]
  L2_seq_TS_return
  L2_condition_TS_return
  split_distrib[where T = TS_return, symmetric]



(*
 * Lifting into pure functional Isabelle with state.
 *)

definition "TS_gets x \<equiv> liftE (gets x)"

lemma TS_gets_L2_gets:
    "L2_gets X n = TS_gets X"
  by (monad_eq simp: L2_defs TS_gets_def)

lemma L2_call_TS_gets: "L2_call (TS_gets a) = L2_gets a [''TS_internal_retval'']"
  apply (monad_eq simp: L2_call_def L2_gets_def TS_gets_def)
  done

setup \<open>
Monad_Types.new_monad_type
  "gets"
  "Read-only function"
  (Monad_Types.check_lifting_head [@{term "TS_gets"}])
  80
  @{thms L2_call_TS_gets TS_gets_L2_gets}
  @{term "(%x. L2_gets x [''ret'']) :: ('s => 'a) => ('s, 'a, unit) L2_monad"}
  @{thm L2_call_L2_gets_polymorphic}
  (fn (state, ret, ex) => state --> ret)
  (fn _ => error "monad_mono not applicable for gets monad")
|> Context.theory_map
\<close>

lemma TS_gets_L2_seq:
    "L2_seq (TS_gets A) (\<lambda>x. TS_gets (B x)) = (TS_gets (\<lambda>s. let x = A s in B x s))"
  by (monad_eq simp: L2_defs TS_gets_def)

lemma TS_gets_L2_condition:
    "L2_condition c (TS_gets A) (TS_gets B) = TS_gets (\<lambda>s. if c s then (A s) else (B s))"
  by (monad_eq simp: L2_defs TS_gets_def)

lemmas [ts_rule gets] =
  TS_gets_L2_gets
  TS_gets_L2_seq
  TS_gets_L2_condition
  split_distrib[where T = TS_gets]

lemmas [ts_rule gets unlift] =
  TS_gets_L2_gets      [where n = "[]", symmetric]
  TS_gets_L2_seq       [symmetric]
  TS_gets_L2_condition [symmetric]
  split_distrib[where T = TS_gets, symmetric]



(*
 * Lifting into option monad.
 *)

definition "gets_theE \<equiv> \<lambda>x. (liftE (gets_the x))"

lemma L2_call_gets_theE [simp]: "L2_call (gets_theE x) = gets_theE x"
  apply (monad_eq simp: L2_call_def L2_gets_def gets_theE_def)
  done

lemma liftE_gets_theE: "gets_theE X = liftE (gets_the X)"
  apply (clarsimp simp: gets_theE_def)
  done
lemma L2_call_gets_theE_polymorphic:
  "(L2_call x :: ('s, 'a, 'e1) L2_monad) = gets_theE y
    \<Longrightarrow> (L2_call x  :: ('s, 'a, 'e2) L2_monad) = gets_theE y"
  apply (metis L2_call_liftE_unliftE liftE_gets_theE unliftE_liftE)
  done

lemma in_gets_theE [monad_eq]:
     "(rv, s') \<in> fst (gets_theE M s) = (\<exists>v'. rv = Inr v' \<and> s' = s \<and> M s = Some v')"
  apply (monad_eq simp: gets_theE_def)
  done

lemma snd_gets_theE [monad_eq]:
     "snd (gets_theE M s) = (M s = None)"
  apply (monad_eq simp: gets_theE_def gets_the_def Bex_def assert_opt_def split: option.splits)
  done

lemma gets_theE_ofail [simp]:
  "gets_theE ofail = fail"
  by (monad_eq simp: L2_defs ofail_def split: option.splits)

(* unused *)
lemma monad_mono_transfer_option:
  "\<lbrakk> \<And>m. (L2_call (f m) :: ('s, 'a, 'e) L2_monad) = gets_theE (f' m); monad_mono f \<rbrakk> \<Longrightarrow> option_monad_mono f'"
  apply atomize
  apply (clarsimp simp: monad_mono_def option_monad_mono_def)
  apply (clarsimp split: option.splits)
  apply (erule allE, erule allE, erule (1) impE)
  apply (erule_tac x=s in allE)
  apply (frule_tac x=x in spec)
  apply (drule_tac x=y in spec)
  apply rule
   apply (monad_eq simp: L2_call_def split: sum.splits)
   apply metis
  apply (monad_eq simp: L2_call_def split: sum.splits)
  apply (metis (full_types) sum.inject(2))
  done

setup \<open>
Monad_Types.new_monad_type
  "option"
  "Option monad"
  (Monad_Types.check_lifting_head [@{term "gets_theE"}])
  60
  @{thms L2_call_gets_theE gets_theE_ofail}
  @{term "gets_theE :: ('s => 'a option) => ('s, 'a, unit) L2_monad"}
  @{thm L2_call_gets_theE_polymorphic}
  (fn (state, ret, ex) =>
     state --> Term.map_atyps (fn t => if t = @{typ "'a"} then ret else t) @{typ "'a option"})
  (fn def => fn mono_thm => @{thm monad_mono_transfer_option} OF [def, mono_thm])
|> Context.theory_map
\<close>

lemma gets_theE_L2_gets:
  "L2_gets a n = gets_theE (ogets a)"
  by (monad_eq simp: L2_defs ogets_def)

lemma gets_theE_L2_seq:
  "L2_seq (gets_theE X) (\<lambda>x. gets_theE (Y x)) = gets_theE (X |>> Y)"
  by (monad_eq simp: L2_defs ogets_def Bex_def obind_def split: option.splits)

lemma gets_theE_L2_guard:
  "L2_guard G = gets_theE (oguard G)"
  by (monad_eq simp: L2_defs oguard_def split: option.splits)

lemma gets_theE_L2_condition:
  "L2_condition C (gets_theE L) (gets_theE R) = gets_theE (ocondition C L R)"
  by (monad_eq simp: L2_defs ocondition_def split: option.splits)

lemma gets_theE_L2_fail:
  "L2_fail = gets_theE (ofail)"
  by (monad_eq simp: L2_defs ofail_def split: option.splits)

lemma gets_theE_L2_recguard:
  "L2_recguard m (gets_theE x) = gets_theE (ocondition (\<lambda>_. m = 0) ofail x)"
  by (monad_eq simp: L2_defs ocondition_def ofail_def split: option.splits)

lemma gets_theE_L2_while:
  "L2_while C (\<lambda>x. gets_theE (B x)) i n = gets_theE (owhile C B i)"
  unfolding L2_while_def gets_theE_def gets_the_whileLoop[symmetric]
  by (rule whileLoopE_liftE)


lemmas [ts_rule option] =
  gets_theE_L2_seq
  gets_theE_L2_fail
  gets_theE_L2_guard
  gets_theE_L2_recguard
  gets_theE_L2_gets
  gets_theE_L2_condition
  gets_theE_L2_while
  split_distrib[where T = gets_theE]

lemmas [ts_rule option unlift] =
  gets_theE_L2_seq       [symmetric]
  gets_theE_L2_fail      [symmetric]
  gets_theE_L2_guard     [symmetric]
  gets_theE_L2_recguard  [symmetric]
  gets_theE_L2_gets      [where n = "[]", symmetric]
  gets_theE_L2_condition [symmetric]
  gets_theE_L2_while     [symmetric]
  split_distrib[where T = gets_theE, symmetric]


(*
 * Lifting into the nondeterministic state monad.
 * All L2 terms can be lifted into it.
 *)

lemma L2_call_liftE_polymorphic:
  "((L2_call x) :: ('s, 'a, 'e1) L2_monad) = liftE y
    \<Longrightarrow> (L2_call x :: ('s, 'a, 'e2) L2_monad) = liftE y"
  apply (metis L2_call_liftE_unliftE unliftE_liftE)
  done

lemma monad_mono_transfer_nondet:
  "\<lbrakk> \<And>m. (L2_call (f m) :: ('s, 'a, 'e) L2_monad) = liftE (f' m); monad_mono f \<rbrakk> \<Longrightarrow> monad_mono f'"
  apply atomize
  apply (clarsimp simp: monad_mono_def option_monad_mono_def)
  apply (erule allE, erule allE, erule (1) impE)
  apply (erule_tac x=s in allE)
  apply (frule_tac x=x in spec)
  apply (drule_tac x=y in spec)
  apply rule
   apply (monad_eq simp: L2_call_def split: sum.splits)
   apply (metis set_rev_mp sum.inject(2))
  apply (monad_eq simp: L2_call_def split: sum.splits)
  apply (* not *) fast
  done

setup \<open>
Monad_Types.new_monad_type
  "nondet"
  "Nondeterministic state monad (default)"
  (Monad_Types.check_lifting_head [@{term "liftE"}])
  0
  @{thms L2_call_liftE}
  @{term "liftE :: ('s, 'a) nondet_monad => ('s, 'a, unit) L2_monad"}
  @{thm L2_call_liftE_polymorphic}
  (fn (state, ret, ex) =>
     Term.map_atyps (fn t => if t = @{typ "'a"} then ret
                               else if t = @{typ "'s"} then state else t)
       @{typ "('s, 'a) nondet_monad"})
  (fn def => fn mono_thm => @{thm monad_mono_transfer_nondet} OF [def, mono_thm])
|> Context.theory_map
\<close>

lemma liftE_L2_seq: "L2_seq (liftE A) (\<lambda>x. liftE (B x)) = (liftE (A >>= B))"
  apply (clarsimp simp: L2_defs)
  apply (clarsimp simp: liftE_def bindE_def bind_assoc)
  done

lemma liftE_L2_condition: "L2_condition c (liftE A) (liftE B) = liftE (condition c A B)"
  apply (clarsimp simp: L2_defs)
  apply (rule ext)+
  apply monad_eq
  apply blast
  done

lemma liftE_L2_modify: "L2_modify m = liftE (modify m)"
  apply (clarsimp simp: L2_defs)
  done

lemma liftE_L2_gets: "L2_gets a n = liftE (gets a)"
  apply (clarsimp simp: L2_defs)
  done

lemma liftE_L2_recguard:
  "(L2_recguard x (liftE A)) = liftE (condition (\<lambda>s. x > 0) A fail)"
  apply (case_tac "x = 0")
   apply clarsimp
  apply (clarsimp simp: L2_recguard_def)
  done

lemma liftE_L2_while: "L2_while c (\<lambda>r. liftE (B r)) i n = liftE (whileLoop c B i)"
  apply (clarsimp simp: L2_while_def)
  apply (rule whileLoopE_liftE)
  done

lemma liftE_L2_throw: "L2_throw X n = throwError X"
  apply (monad_eq simp: L2_throw_def)
  done

lemma liftE_L2_catch: "L2_catch (liftE A) B = liftE A"
  apply (clarsimp simp: L2_defs)
  done

lemma liftE_L2_catch': "L2_catch A (\<lambda>x. liftE (B x)) = liftE (A <catch> B)"
  apply (clarsimp simp: L2_defs)
  apply (clarsimp simp: handleE'_def liftE_def catch_def bind_assoc)
  apply (rule arg_cong [where f="\<lambda>x. (A >>= x)"])
  apply (rule ext)
  apply (clarsimp split: sum.splits)
  done

lemma liftE_L2_unknown: "L2_unknown name = liftE (select UNIV)"
  apply (clarsimp simp: L2_defs)
  done

lemma liftE_L2_spec: "L2_spec S = liftE (spec S >>= (\<lambda>_. select UNIV))"
  apply (clarsimp simp: L2_defs)
  done

lemma liftE_L2_guard: "L2_guard G = liftE (guard G)"
  apply (clarsimp simp: L2_defs)
  done

lemma liftE_L2_fail: "L2_fail = liftE (fail)"
  apply (clarsimp simp: L2_defs liftE_def)
  done

lemma liftE_exec_concrete:
  "exec_concrete st (liftE x) = liftE (exec_concrete st x)"
  apply (rule monad_eqI)
    apply (clarsimp simp: in_liftE in_exec_concrete)
    apply force
   apply (clarsimp simp: in_liftE in_exec_concrete)
   apply force
  apply (clarsimp simp: snd_exec_concrete snd_liftE)
  done

lemma liftE_exec_abstract:
  "exec_abstract st (liftE x) = liftE (exec_abstract st x)"
  apply (rule monad_eqI)
    apply (clarsimp simp: in_liftE in_exec_abstract)
   apply (clarsimp simp: in_liftE in_exec_abstract)
  apply (clarsimp simp: snd_exec_abstract snd_liftE)
  done

lemma liftE_measure_call:
  "\<lbrakk> monad_mono A; \<And>m. L2_call (A m) = liftE (B m) \<rbrakk>
   \<Longrightarrow> L2_call (measure_call A) = liftE (measure_call B)"
  apply (monad_eq simp: measure_call_def L2_call_def L2_defs)
  apply (fast dest: monad_mono_incl)
  done

lemmas [ts_rule nondet] =
  liftE_L2_seq
  liftE_L2_condition
  liftE_L2_modify
  liftE_L2_gets
  liftE_L2_while
  liftE_L2_throw
  liftE_L2_catch
  liftE_L2_catch'
  liftE_L2_spec
  liftE_L2_guard
  liftE_L2_unknown
  liftE_L2_fail
  liftE_L2_recguard
  liftE_exec_concrete
  liftE_exec_abstract
  liftE_gets_theE
  liftE_measure_call
  split_distrib [where T=liftE]

definition
  "AC_call_L1 arg_xf gs ret_xf l1body
    = liftM (\<lambda>rv. case rv of Inr v \<Rightarrow> v)
        (L2_call_L1 arg_xf gs ret_xf l1body)"

lemma liftE_L2_call_L1[ts_rule nondet]:
  "L2_call_L1 arg_xf gs ret_xf l1body
    = liftE (AC_call_L1 arg_xf gs ret_xf l1body)"
  apply (simp add: AC_call_L1_def L2_call_L1_def
                   liftE_def liftM_def bind_assoc)
  apply (rule ext)
  apply (simp add: exec_gets exec_get)
  apply (rule bind_apply_cong[OF refl])+
  apply (clarsimp simp: bind_assoc returnOk_def in_monad split: sum.splits)
  done

lemmas [ts_rule nondet unlift] =
  liftE_L2_seq        [symmetric]
  liftE_L2_condition  [symmetric]
  liftE_L2_modify     [symmetric]
  liftE_L2_gets       [symmetric]
  liftE_L2_while      [symmetric]
  liftE_L2_throw      [symmetric]
  liftE_L2_catch      [symmetric]
  liftE_L2_catch'     [symmetric]
  liftE_L2_spec       [symmetric]
  liftE_L2_guard      [symmetric]
  liftE_L2_unknown    [symmetric]
  liftE_L2_fail       [symmetric]
  liftE_L2_recguard   [symmetric]
  liftE_exec_concrete [symmetric]
  liftE_exec_abstract [symmetric]
  liftE_gets_theE     [symmetric]
  split_distrib [where T=liftE, symmetric]

end
