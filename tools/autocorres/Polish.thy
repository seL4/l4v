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
 * Final simplifications applied to function specs.
 *)

theory Polish
imports WordPolish TypeStrengthen
begin

(* Final simplification after type strengthening. *)
named_theorems polish

(* Remove the Hoare modifies constants after heap abstraction, as they have
 * very buggy print translations.
 * In particular, applying abs_spec_modify_global replaces the bound variable by "x"
 * and confuses the print translation into producing "may_only_modify_globals [x]". *)
lemmas [polish] = mex_def meq_def

(* Clean up "WORD_MAX TYPE(32)", etc. after word abstraction. *)
lemmas [polish] =
  WORD_MAX_simps
  WORD_MIN_simps
  UWORD_MAX_simps
  WORD_signed_to_unsigned
  INT_MIN_MAX_lemmas

declare singleton_iff [polish]

lemma L2polish [polish]:
  "L2_seq = bindE"
  "L2_unknown n = unknownE"
  "L2_gets g n = getsE g"
  "L2_modify = modifyE"
  "L2_condition = condition"
  "L2_catch = handleE'"
  "L2_while C B i n = whileLoopE C B i"
  "L2_spec s = (specE s >>=E (\<lambda>x. unknownE))"
  "L2_fail = fail"
  "L2_throw v n = throwError v"
  apply (auto simp: L2_defs skipE_def modifyE_def unknownE_def
      getsE_def specE_def bind_liftE_distrib selectE_def intro!: ext)
  done

lemma returnOk_skip [polish]: "returnOk () = skipE"
  by (clarsimp simp: skipE_def)

lemma return_skip [polish]: "return () = skip"
  by (clarsimp simp: skip_def)

lemma liftE_foo_to_fooE [polish]:
  "liftE (unknown) = unknownE"
  "liftE (gets x) = getsE x"
  "liftE (return a) = returnOk a"
  "liftE (modify m) = modifyE m"
  "liftE (spec s) = specE s"
  "liftE skip = skipE"
  "liftE (guard g) = guardE g"
  apply (monad_eq simp: unknownE_def selectE_def unknown_def
    getsE_def modifyE_def specE_def skip_def skipE_def guardE_def)+
  done

lemma gets_to_return [polish]:
  "gets (\<lambda>x. a) = return a"
  apply (clarsimp simp: simpler_gets_def return_def)
  done

lemma getsE_to_returnOk [polish]:
  "getsE (\<lambda>x. a) = returnOk a"
  apply (clarsimp simp: getsE_def simpler_gets_def returnOk_def2 return_def)
  done

lemma select_UNIV_unknown [polish]: "select UNIV = unknown"
  by (clarsimp simp: unknown_def)
lemma selectE_UNIV_unknown [polish]: "liftE (select UNIV) = unknownE"
  by (clarsimp simp: unknownE_def selectE_def)

lemma unknown_unit [polish, simp]: "(unknown :: ('s, unit) nondet_monad) = skip"
  apply (rule ext)+
  apply (clarsimp simp: skip_def select_def return_def skipE_def unknown_def)
  apply force
  done

lemma unknownE_unit [polish,simp]: "(unknownE :: ('s, 'a + unit) nondet_monad) = skipE"
  apply (rule ext)+
  apply (monad_eq simp: skip_def selectE_def skipE_def unknownE_def)
  done

lemma condition_to_when [polish]:
  "condition (\<lambda>s. C) A skip = when C A"
  "condition (\<lambda>s. C) A' skipE = whenE C A'"
  apply (auto simp: condition_def when_def skip_def skipE_def whenE_def)
  done

lemma condition_to_unless [polish]:
  "condition (\<lambda>s. C) skip A = unless C A"
  "condition (\<lambda>s. C) skipE A' = unlessE C A'"
  apply (auto simp: condition_def unless_def when_def skip_def skipE_def unlessE_def)
  done

lemma bind_skip [simp, polish]:
  "(x >>= (\<lambda>_. skip)) = x"
  by (monad_eq simp: skip_def)

lemma bindE_skipE [simp, polish]:
  "(x >>=E (\<lambda>_. skipE)) = x"
  by (monad_eq simp: skipE_def)

lemma skip_bind [simp, polish]:
  "(skip >>= P) = (P ())"
  by (monad_eq simp: skip_def)

lemma skipE_bindE [simp, polish]:
  "(skipE >>=E P) = (P ())"
  by (monad_eq simp: skip_def skipE_def)

lemma ogets_to_oreturn [polish]: "ogets (\<lambda>s. P) = oreturn P"
  apply (clarsimp simp: ogets_def oreturn_def)
  done

lemma ocondition_ret_ret [polish]:
  "ocondition P (oreturn A) (oreturn B) = ogets (\<lambda>s. if P s then A else B)"
  by (auto intro!:ext simp: ocondition_def ogets_def)

lemma ocondition_gets_ret [polish]:
  "ocondition P (ogets A) (oreturn B) = ogets (\<lambda>s. if P s then A s else B)"
  by (auto intro!:ext simp: ocondition_def ogets_def)

lemma ocondition_ret_gets [polish]:
  "ocondition P (oreturn A) (ogets B) = ogets (\<lambda>s. if P s then A else B s)"
  by (auto intro!:ext simp: ocondition_def ogets_def)

lemma ocondition_gets_gets [polish]:
  "ocondition P (ogets A) (ogets B) = ogets (\<lambda>s. if P s then A s else B s)"
  by (auto intro!:ext simp: ocondition_def ogets_def)

lemma bindE_K_bind [polish]: "A >>=E (\<lambda>x :: unit. B) = (A >>=E K_bind B)"
  apply (clarsimp simp: K_bind_def)
  done
lemma bind_K_bind [polish]: "A >>= (\<lambda>x :: unit. B) = (A >>= K_bind B)"
  apply (clarsimp simp: K_bind_def)
  done
lemma obind_K_bind [polish]: "A |>> (\<lambda>x :: unit. B) = (A  |>> K_bind B)"
  apply (clarsimp simp: K_bind_def)
  done

lemma K_bind_apply [polish]:
    "K_bind a b = a"
  by simp

lemma condition_to_if [polish]:
  "condition (\<lambda>s. C) (return a) (return b) = return (if C then a else b)"
  apply (clarsimp simp: condition_splits)
  done

lemma guard_True_bind [polish, simp]:
    "(guard (\<lambda>_. True) >>= M) = M ()"
  by monad_eq

declare condition_fail_rhs [polish]
declare condition_fail_lhs [polish]
declare simple_bind_fail [polish]
declare simple_bindE_fail [polish]
declare condition_bind_fail [polish]

lemma simple_K_bind_fail [polish, simp]:
  "(guard X >>= K_bind (fail)) = fail"
  "(modify M >>= K_bind (fail)) = fail"
  "(return Y >>= K_bind (fail)) = fail"
  "(gets Z >>= K_bind (fail)) = fail"
  "(skip >>= K_bind (fail)) = fail"
  apply -
  apply monad_eq+
  done

lemma simple_K_bindE_fail [polish]:
  "(guardE X >>=E K_bind (fail)) = fail"
  "(modifyE M >>=E K_bind (fail)) = fail"
  "(returnOk Y >>=E K_bind (fail)) = fail"
  "(getsE Z >>=E K_bind (fail)) = fail"
  "(skipE >>=E K_bind (fail)) = fail"
  apply -
  apply monad_eq+
  done

declare whileLoop_fail [polish]
declare whileLoopE_fail [polish]
declare owhile_fail [polish]

lemma oguard_True [simp, polish]: "oguard (\<lambda>_. True) = oreturn ()"
  by (clarsimp simp: oreturn_def oguard_def)

lemma oguard_False [simp, polish]: "oguard (\<lambda>_. False) = ofail"
  by (clarsimp simp: ofail_def oguard_def)

lemma infinite_option_while': "(Some x, Some y) \<notin> option_while' (\<lambda>_. True) B"
  apply (rule notI)
  apply (induct "Some x :: 'a option" "Some y :: 'a option"
      arbitrary: x y rule: option_while'.induct)
  apply auto
  done


lemma expand_guard_conj [polish]:
  "guard (\<lambda>s. A s \<and> B s) = (do _ \<leftarrow> guard (\<lambda>s. A s); guard (\<lambda>s. B s) od)"
  by monad_eq

lemma expand_guardE_conj [polish]:
  "guardE (\<lambda>s. A s \<and> B s) = (doE _ \<leftarrow> guardE (\<lambda>s. A s); guardE (\<lambda>s. B s) odE)"
  by monad_eq

lemma expand_oguard_conj [polish]:
  "oguard (\<lambda>s. A s \<and> B s) = (DO _ \<leftarrow> oguard (\<lambda>s. A s); oguard (\<lambda>s. B s) OD)"
  by (rule ext) (clarsimp simp: oguard_def obind_def split: option.splits)

lemma owhile_infinite_loop [simp, polish]:
    "owhile (\<lambda>r s. C) B x = (oguard (\<lambda>s. \<not> C) |>> (\<lambda>_. oreturn x))"
  apply (case_tac C)
   apply (rule ext)
   apply (clarsimp simp: owhile_def option_while_def obind_def split: option.splits)
   apply (metis infinite_option_while' None_not_eq option_while'_THE)
  apply (subst owhile_unroll)
  apply (clarsimp simp: obind_def oreturn_def split: option.splits)
  done

declare obind_return [polish]
declare bind_return [polish]
declare bindE_returnOk [polish]

declare fail_bind [polish]
declare fail_bindE [polish]
declare ofail_bind [polish]
declare obind_fail [polish]

lemmas returnOk_bindE_throwError [polish]
  = returnOk_bindE [where f=throwError]

declare singleton_iff [polish]
declare when_True [polish]
declare when_False [polish]
declare unless_True [polish]
declare unless_False [polish]
declare recguard_dec_def [polish]

lemma let_triv [polish]: "(let x = y in x) = y"
  apply (clarsimp simp: Let_def)
  done

lemma ucast_scast_same [polish, L2opt, simp]:
    "ucast ((scast x :: ('a::len) word)) = (x :: 'a word)"
  apply (clarsimp simp: ucast_def scast_def)
  done

lemma [polish, L2opt, simp]:
    "word_of_int (int x) = of_nat x"
  by (clarsimp simp: word_of_nat)

(* Optimising "if" constructs. *)

lemma return_if_P_1_0_bind [polish]:
    "(return (if P then 1 else 0) >>= (\<lambda>x. Q x))
        = (return P >>= (\<lambda>x. Q (if x then 1 else 0)))"
  apply simp
  done

lemma returnOk_if_P_1_0_bindE [polish]:
    "(returnOk (if P then 1 else 0) >>=E (\<lambda>x. Q x))
        = (returnOk P >>=E (\<lambda>x. Q (if x then 1 else 0)))"
  apply simp
  done

lemma gets_if_P_1_0_bind [polish]:
    "(gets (\<lambda>s. if P s then 1 else 0) >>= (\<lambda>x. Q x))
        = (gets P >>= (\<lambda>x. Q (if x then 1 else 0)))"
  apply (auto intro!: monad_eqI simp: in_gets in_bind snd_gets snd_bind Bex_def)
  done

lemma getsE_if_P_1_0_bindE [polish]:
    "(getsE (\<lambda>s. if P s then 1 else 0) >>=E (\<lambda>x. Q x))
        = (getsE P >>=E (\<lambda>x. Q (if x then 1 else 0)))"
  apply (auto intro!: monad_eqI simp: getsE_def in_gets
        in_liftE in_bindE snd_gets snd_bindE snd_liftE Bex_def)
  done

lemma if_P_1_0_neq_0 [polish, simp]:
    "((if P then 1 else (0::('a::{zero_neq_one}))) \<noteq> 0) = P"
  apply simp
  done

lemma if_P_1_0_eq_0 [polish, simp]:
    "((if P then 1 else (0::('a::{zero_neq_one}))) = 0) = (\<not> P)"
  apply simp
  done

lemma if_if_same_output [polish]:
  "(if a then if b then x else y else y) = (if a \<and> b then x else y)"
  "(if a then x else if b then x else y) = (if a \<or> b then x else y)"
  by auto

(* C-parser turns a C expression into a chain of guarded statements
   if some of the subexpressions can fail. This gets annoying when
   the expression was being used as a condition.

   Here we try to rewrite the statements to one big guard followed by
   the actual expression.
   TODO: this should be in L2Opt or something *)
lemma collect_guarded_conj[polish]:
  "condition C1 (do guard G; gets (\<lambda>s. if C2 s then 1 else 0) od)
                (return 0)
    = do guard (\<lambda>s. C1 s \<longrightarrow> G s);
         gets (\<lambda>s. if C1 s \<and> C2 s then 1 else 0) od"
  by monad_eq auto

lemma collect_guarded_disj[polish]:
  "condition C1 (return 1)
                (do guard G; gets (\<lambda>s. if C2 s then 1 else 0) od)
    = do guard (\<lambda>s. \<not> C1 s \<longrightarrow> G s);
         gets (\<lambda>s. if C1 s \<or> C2 s then 1 else 0) od"
  by monad_eq auto

(* Need this to merge the new statements into the program *)
lemmas [polish] = bind_assoc bindE_assoc obind_assoc

lemma obind_K_bind_eta_contract [polish]:
  "(DO x \<leftarrow> A; y \<leftarrow> K_bind B x; C y OD) = (DO A; y \<leftarrow> B; C y OD)"
  by simp

lemma bind_K_bind_eta_contract [polish]:
  "(do x \<leftarrow> A; y \<leftarrow> K_bind B x; C y od) = (do A; y \<leftarrow> B; C y od)"
  by simp

lemma bindE_K_bind_eta_contract [polish]:
  "(doE x \<leftarrow> A; y \<leftarrow> K_bind B x; C y odE) = (doE A; y \<leftarrow> B; C y odE)"
  by simp

(* Need this because collect_guarded_disj generates nots *)
declare not_not [polish]

(* Normally the boolean result from above is used in a condition,
   simplify that as well. *)
lemma collect_then_cond_1_0[polish]:
   "do cond \<leftarrow> gets (\<lambda>s. if P s then (1::('a::{zero_neq_one})) else 0);
       condition (\<lambda>_. cond \<noteq> 0) L R od
    = condition P L R"
  by monad_eq
lemma collect_then_cond_1_0_assoc[polish]:
   "(do cond \<leftarrow> gets (\<lambda>s. if P s then (1::('a::{zero_neq_one})) else 0);
        condition (\<lambda>_. cond \<noteq> 0) L R
        >>= f od)
    = (condition P L R >>= f)"
  by monad_eq

lemma bind_return_bind [polish]:
    "(A >>= (\<lambda>x. (return x >>= (\<lambda>y. B x y)))) = (A >>= (\<lambda>x. B x x))"
  by simp

lemma bindE_returnOk_bindE [polish]:
    "(A >>=E (\<lambda>x. (returnOk x >>=E (\<lambda>y. B x y)))) = (A >>=E (\<lambda>x. B x x))"
  by simp

lemma obind_oreturn_obind [polish]:
    "(A |>> (\<lambda>x. (oreturn x |>> (\<lambda>y. B x y)))) = (A |>> (\<lambda>x. B x x))"
  by simp

declare obind_assoc [polish]

declare if_distrib [where f=scast, polish, simp]
declare if_distrib [where f=ucast, polish, simp]
declare if_distrib [where f=unat, polish, simp]
declare if_distrib [where f=uint, polish, simp]
declare if_distrib [where f=sint, polish, simp]

declare cast_simps [polish]

lemma Suc_0_eq_1 [polish]: "Suc 0 = 1"
  by simp

(*
 * Return / case_prod combinations.
 *
 * These can probably be improved to avoid duplication.
 *)

lemma bind_return_case_prod [polish, simp]:
  "(do (a) \<leftarrow> A1; return (a) od) = A1"
  "(do (a, b) \<leftarrow> A2; return (a, b) od) = A2"
  "(do (a, b, c) \<leftarrow> A3; return (a, b, c) od) = A3"
  "(do (a, b, c, d) \<leftarrow> A4; return (a, b, c, d) od) = A4"
  "(do (a, b, c, d, e) \<leftarrow> A5; return (a, b, c, d, e) od) = A5"
  "(do (a, b, c, d, e, f) \<leftarrow> A6; return (a, b, c, d, e, f) od) = A6"
  by auto

lemma bindE_returnOk_prodE_case [polish, simp]:
  "(doE (a) \<leftarrow> A1; returnOk (a) odE) = A1"
  "(doE (a, b) \<leftarrow> A2; returnOk (a, b) odE) = A2"
  "(doE (a, b, c) \<leftarrow> A3; returnOk (a, b, c) odE) = A3"
  "(doE (a, b, c, d) \<leftarrow> A4; returnOk (a, b, c, d) odE) = A4"
  "(doE (a, b, c, d, e) \<leftarrow> A5; returnOk (a, b, c, d, e) odE) = A5"
  "(doE (a, b, c, d, e, f) \<leftarrow> A6; returnOk (a, b, c, d, e, f) odE) = A6"
  by auto

lemma obind_returnOk_prodE_case [polish, simp]:
  "(DO (a) \<leftarrow> A1; oreturn (a) OD) = A1"
  "(DO (a, b) \<leftarrow> A2; oreturn (a, b) OD) = A2"
  "(DO (a, b, c) \<leftarrow> A3; oreturn (a, b, c) OD) = A3"
  "(DO (a, b, c, d) \<leftarrow> A4; oreturn (a, b, c, d) OD) = A4"
  "(DO (a, b, c, d, e) \<leftarrow> A5; oreturn (a, b, c, d, e) OD) = A5"
  "(DO (a, b, c, d, e, f) \<leftarrow> A6; oreturn (a, b, c, d, e, f) OD) = A6"
  by auto

(* Word simplifications *)

lemma scast_1_simps [simp, L2opt, polish]:
  "scast (1 :: ('a::len) bit1 word) = 1"
  "scast (1 :: ('a::len) bit0 word) = 1"
  "scast (1 :: ('a::len) bit1 signed word) = 1"
  "scast (1 :: ('a::len) bit0 signed word) = 1"
  by auto

lemma scast_1_simps_direct [simp, L2opt, polish]:
   "scast (1 :: sword64) = (1 :: word64)"
   "scast (1 :: sword64) = (1 :: word32)"
   "scast (1 :: sword64) = (1 :: word16)"
   "scast (1 :: sword64) = (1 :: word8)"
   "scast (1 :: sword32) = (1 :: word32)"
   "scast (1 :: sword32) = (1 :: word16)"
   "scast (1 :: sword32) = (1 :: word8)"
   "scast (1 :: sword16) = (1 :: word16)"
   "scast (1 :: sword16) = (1 :: word8)"
   "scast (1 :: sword8) = (1 :: word8)"
  by auto

declare scast_0 [L2opt, polish]

declare sint_0 [polish]

lemma sint_1_eq_1_x [polish, simp]:
    "sint (1 :: (('a::len) bit0) word) = 1"
    "sint (1 :: (('a::len) bit1) word) = 1"
    "sint (1 :: (('a::len) bit0) signed word) = 1"
    "sint (1 :: (('a::len) bit1) signed word) = 1"
  by auto

lemma if_P_then_t_else_f_eq_t [L2opt, polish]:
    "((if P then t else f) = t) = (P \<or> t = f)"
  by auto

lemma if_P_then_t_else_f_eq_f [L2opt, polish]:
    "((if P then t else f) = f) = (\<not> P \<or> t = f)"
  by auto

lemma sint_1_ne_sint_0: "sint 1 \<noteq> sint 0"
  by simp

lemmas if_P_then_t_else_f_eq_f_simps [L2opt, polish] =
  if_P_then_t_else_f_eq_f [where t = "sint 1" and f = "sint 0", simplified sint_1_ne_sint_0 simp_thms]
  if_P_then_t_else_f_eq_t [where t = "sint 1" and f = "sint 0", simplified sint_1_ne_sint_0 simp_thms]
  if_P_then_t_else_f_eq_f [where t = "1 :: int" and f = "0 :: int", simplified zero_neq_one_class.one_neq_zero simp_thms]
  if_P_then_t_else_f_eq_t [where t = "1 :: int" and f = "0 :: int", simplified zero_neq_one_class.one_neq_zero simp_thms]

lemma boring_bind_K_bind [simp, polish]:
    "(gets X >>= K_bind M) = M"
    "(return Y >>= K_bind M) = M"
    "(skip >>= K_bind M) = M"
  apply -
  apply monad_eq+
  done

lemma boringE_bind_K_bind [simp, polish]:
    "(getsE X >>=E K_bind M) = M"
    "(returnOk Y >>=E K_bind M) = M"
    "(skipE >>=E K_bind M) = M"
  apply -
  apply monad_eq+
  done

(* Misc *)

declare pred_and_true_var [L2opt, polish]
declare pred_and_true [L2opt, polish]

lemmas [polish] = rel_simps eq_numeral_extra

declare ptr_add_0_id[polish]
declare ptr_coerce.simps[polish]

(* simplify constructs like "p +\<^sub>p int (unat k)" to "p +\<^sub>p uint k",
 * generated by unsigned word abstraction *)
declare uint_nat[symmetric, polish]

end
