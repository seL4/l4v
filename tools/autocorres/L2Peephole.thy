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
 * Peep-hole optimisations for applied to L2.
 *)

theory L2Peephole
imports L2Defs
begin

lemma L2_seq_skip [L2opt]:
  "L2_seq (L2_gets (\<lambda>_. ()) n) X = (X ())"
  "L2_seq Y (\<lambda>_. (L2_gets (\<lambda>_. ()) n)) = Y"
  apply (clarsimp simp: L2_seq_def L2_gets_def returnOk_liftE[symmetric])+
  done

lemma L2_seq_L2_gets [L2opt]: "L2_seq X (\<lambda>x. L2_gets (\<lambda>_. x) n) = X"
  apply (clarsimp simp: L2_defs cong: bindE_cong)
  apply (fold returnOk_liftE)
  apply simp
  done

lemma L2_seq_assoc [L2opt]:
  "L2_seq (L2_seq A (\<lambda>x. B x)) C = L2_seq A (\<lambda>x. L2_seq (B x) C)"
  apply (clarsimp simp: L2_seq_def bindE_assoc)
  done

lemma L2_trim_after_throw [L2opt]:
  "L2_seq (L2_throw x n) Z = (L2_throw x n)"
  apply (clarsimp simp: L2_seq_def L2_throw_def)
  done

lemma L2_guard_true [L2opt]: "\<lbrakk> \<And>s. P s \<rbrakk> \<Longrightarrow> L2_guard P = L2_gets (\<lambda>_. ()) [''ret'']"
  apply (monad_eq simp: L2_defs)
  done

lemma L2_guard_false [L2opt]: "\<lbrakk> \<And>s. \<not> P s \<rbrakk> \<Longrightarrow> L2_guard P = L2_fail"
  apply (monad_eq simp: L2_defs)
  done

lemma L2_spec_empty [L2opt]:
  (* FIXME: do we need both? *)
  "L2_spec {} = L2_fail"
  "\<lbrakk> \<And>s t. \<not> C s t \<rbrakk> \<Longrightarrow> L2_spec {(s, t). C s t} = L2_fail"
  by (monad_eq simp: L2_defs)+

lemma L2_unknown_bind [L2opt]:
  "(\<And>a b. f a = f b) \<Longrightarrow> (L2_seq (L2_unknown name) f) = f undefined"
  apply (atomize)
  apply (subst (asm) all_comm)
  apply (erule allE [where x=undefined])
  apply (rule ext)
  apply (clarsimp simp: L2_seq_def L2_unknown_def)
  apply (clarsimp simp: liftE_def select_def bindE_def)
  apply (clarsimp simp: NonDetMonad.lift_def bind_def)
  apply (clarsimp simp: NonDetMonad.bind_def split_def)
  apply (rule prod_eqI)
   apply (rule set_eqI)
   apply (clarsimp)
   apply (rule iffI)
    apply clarsimp
    apply metis
   apply force
  apply (clarsimp simp: image_def)
  apply (rule iffI)
   apply (clarsimp simp: prod_eq_iff)
   apply metis
  apply force
  done

lemma L2_guard_cong:
  "\<lbrakk> P = P'; \<And>s. P s \<Longrightarrow> X s = X' s \<rbrakk> \<Longrightarrow> L2_seq (L2_guard P) (\<lambda>_. X) = L2_seq (L2_guard P') (\<lambda>_. X')"
  apply (rule ext)
  apply (atomize)
  apply (erule_tac x=x in allE)
  apply (monad_eq simp: L2_defs Bex_def)
  done

lemma L2_condition_true [L2opt]: "\<lbrakk> \<And>s. C s \<rbrakk> \<Longrightarrow> L2_condition C A B = A"
  apply (clarsimp simp: L2_condition_def condition_def)
  done

lemma L2_condition_false [L2opt]: "\<lbrakk> \<And>s. \<not> C s \<rbrakk> \<Longrightarrow> L2_condition C A B = B"
  apply (clarsimp simp: L2_condition_def condition_def)
  done

lemma L2_condition_same [L2opt]: "L2_condition C A A = A"
  apply (clarsimp simp: L2_defs condition_def)
  done

lemma L2_fail_seq [L2opt]: "L2_seq L2_fail X = L2_fail"
  apply (clarsimp simp: L2_seq_def L2_fail_def)
  done

lemma L2_fail_propagates [L2opt]:
  "L2_seq (L2_gets V n) (\<lambda>_. L2_fail) = L2_fail"
  "L2_seq (L2_modify M) (\<lambda>_. L2_fail) = L2_fail"
  "L2_seq (L2_spec S) (\<lambda>_. L2_fail) = L2_fail"
  "L2_seq (L2_guard G) (\<lambda>_. L2_fail) = L2_fail"
  "L2_seq (L2_unknown name) (\<lambda>_. L2_fail) = L2_fail"
  "L2_seq L2_fail (\<lambda>_. L2_fail) = L2_fail"
  apply (unfold L2_defs)
  apply (auto intro!: bindE_fail_propagates empty_fail_bindE
      no_throw_bindE [where B="\<top>"] hoare_TrueI simp: empty_fail_error_bits)
  done

lemma L2_condition_distrib:
  "L2_seq (L2_condition C L R) X = L2_condition C (L2_seq L X) (L2_seq R X)"
  apply (unfold L2_defs)
  apply (rule ext)
  apply (clarsimp split: condition_splits)
  apply (rule conjI)
   apply (clarsimp simp: condition_def cong: bindE_apply_cong)
  apply (clarsimp simp: condition_def cong: bindE_apply_cong)
  done

lemmas L2_fail_propagate_condition [L2opt] = L2_condition_distrib [where X="\<lambda>_. L2_fail"]

lemma L2_fail_propagate_catch [L2opt]:
  "(L2_seq (L2_catch L R) (\<lambda>_. L2_fail)) = (L2_catch (L2_seq L (\<lambda>_. L2_fail)) (\<lambda>e. L2_seq (R e) (\<lambda>_. L2_fail)))"
  apply (unfold L2_defs)
  apply (clarsimp simp: bindE_def)
  apply (clarsimp simp: handleE'_def handleE_def)
  apply (clarsimp simp: bind_assoc)
  apply (rule arg_cong [where f="bind L"])
  apply (rule ext)+
  apply (clarsimp split: sum.splits)
  apply (clarsimp simp: throwError_def)
  done

lemma L2_condition_fail_lhs [L2opt]:
  "L2_condition C L2_fail A = L2_seq (L2_guard (\<lambda>s. \<not> C s)) (\<lambda>_. A)"
  apply (rule ext)
  apply (clarsimp simp: L2_guard_def L2_fail_def guard_def get_def
    L2_seq_def bindE_def bind_def fail_def liftE_def2 L2_condition_def
    return_def split: condition_splits)
  done

lemma L2_condition_fail_rhs [L2opt]:
  "L2_condition C A L2_fail = L2_seq (L2_guard (\<lambda>s. C s)) (\<lambda>_. A)"
  apply (rule ext)
  apply (clarsimp simp: L2_guard_def L2_fail_def guard_def get_def
    L2_seq_def bindE_def bind_def fail_def liftE_def2 L2_condition_def
    return_def split: condition_splits)
  done

lemma L2_catch_fail [L2opt]: "L2_catch L2_fail A = L2_fail"
  apply (clarsimp simp: L2_catch_def L2_fail_def handleE'_def)
  done

lemma L2_while_fail [L2opt]: "L2_while C (\<lambda>_. L2_fail) i n = (L2_seq (L2_guard (\<lambda>s. \<not> C i s)) (\<lambda>_. L2_gets (\<lambda>s. i) n))"
  apply (rule ext)+
  apply (clarsimp simp: L2_defs)
  apply (subst whileLoopE_unroll)
  apply (clarsimp split: condition_splits)
  apply (monad_eq)
  done

lemma L2_returncall_trivial [L2opt]:
  "\<lbrakk> \<And>s v. f v s = v \<rbrakk> \<Longrightarrow> L2_returncall x f = L2_call x"
  apply (rule ext)+
  apply (monad_eq simp: L2_defs L2_call_def)
  done

(*
 * Trim "L2_gets" commands where the value is never actually used.
 *
 * This would be nice to apply automatically, but in practice causes
 * everything to slow down significantly.
 *)
lemma L2_gets_unused:
  "\<lbrakk> \<And>x y s. B x s = B y s \<rbrakk> \<Longrightarrow> L2_seq (L2_gets A n) B = (B undefined)"
  apply (clarsimp simp: L2_defs)
  apply (clarsimp simp: bindE_def simpler_gets_def)
  apply (clarsimp simp: bind_def lift_def split_def liftE_def2)
  apply (rule ext)
  apply simp
  done

lemma L2_gets_bind:
  "L2_seq (L2_gets (\<lambda>_. x :: 'var_type) n) f = f x"
  apply (monad_eq simp: L2corres_def corresXF_def L1_defs L2_defs Bex_def)
  done

lemma split_seq_assoc [L2opt]:
     "(\<lambda>x. L2_seq (case x of (a, b) \<Rightarrow> B a b) (G x)) = (\<lambda>x. case x of (a, b) \<Rightarrow> (L2_seq (B a b) (G x)))"
  apply (rule ext)
  apply clarsimp
  done

lemma L2_while_infinite [L2opt]:
        "L2_while (\<lambda>i s. C s) (\<lambda>x. L2_gets (\<lambda>s. B s x) n') i n
                  = (L2_seq (L2_guard (\<lambda>s. \<not> C s)) (\<lambda>_. L2_gets (\<lambda>_. i) n))"
  apply (clarsimp simp: L2_defs whileLoopE_def)
  apply (rule ext)
  apply (case_tac "C x")
   apply (rule whileLoop_rule_strong)
       apply (rule valid_whileLoop [where I="\<lambda>r s. C s \<and> (\<exists>x. r = Inr x)"])
        apply simp
       apply (monad_eq simp: valid_def)
      apply monad_eq
     apply monad_eq
    apply (rule snd_whileLoop [where I="\<lambda>r s. True"])
      apply monad_eq
     apply monad_eq
    apply (monad_eq simp: exs_valid_def split: sum.splits)
   apply monad_eq
  apply (subst whileLoop_unroll)
  apply monad_eq
  done

(*
 * We are happy to collapse away automatically generated constructs.
 *
 * In particular, anything of type "c_exntype" (which is used to track
 * what the current exception represents at the C level) is
 * autogenerated, and hence can be collapsed.
 *)
lemmas L2_gets_bind_c_exntype [L2opt] = L2_gets_bind [where 'var_type=c_exntype]
lemmas L2_gets_bind_unit [L2opt] = L2_gets_bind [where 'var_type=unit]

declare L2_voidcall_def [L2opt]
declare L2_modifycall_def [L2opt]
declare ucast_id [L2opt]
declare scast_id [L2opt]

(* Other misc lemmas. *)
declare singleton_iff [L2opt]

(* Optimising "if" structres. *)

lemma L2_gets_L2_seq_if_P_1_0 [L2opt]:
    "L2_seq (L2_gets (\<lambda>s. if P s then 1 else 0) n) (\<lambda>x. Q x)
        = (L2_seq (L2_gets P n) (\<lambda>x. Q (if x then 1 else 0)))"
  apply (clarsimp simp: L2_defs)
  apply (rule monad_eqI)
   apply (clarsimp simp: L2_defs in_liftE in_gets in_bindE)
   apply (clarsimp simp: L2_defs in_liftE in_gets in_bindE)
   apply (clarsimp simp: L2_defs in_liftE snd_liftE snd_gets snd_bindE Bex_def in_gets)
  done

(* Join up guards, so that we can potentially solve some just by using
 * HOL.conj_cong. We will split them out again during the polish phase. *)

lemma L2_guard_join_simple [L2opt]: "L2_seq (L2_guard A) (\<lambda>_. L2_guard B) = L2_guard (\<lambda>s. A s \<and> B s)"
  apply (monad_eq simp: L2_defs')
  done

lemma L2_guard_join_nested [L2opt]:
      "L2_seq (L2_guard A) (\<lambda>_. L2_seq (L2_guard B) (\<lambda>_. C))
            = L2_seq (L2_guard (\<lambda>s. A s \<and> B s)) (\<lambda>_. C)"
  apply (monad_eq simp: L2_defs')
  done


end
