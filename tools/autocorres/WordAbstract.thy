(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory WordAbstract
imports L2Defs ExecConcrete
begin

definition "WORD_MAX x \<equiv> ((2 ^ (len_of x - 1) - 1) :: int)"
definition "WORD_MIN x \<equiv> (- (2 ^ (len_of x - 1)) :: int)"
definition "UWORD_MAX x \<equiv> ((2 ^ (len_of x)) - 1 :: nat)"

lemma WORD_values [simplified]:
  "WORD_MAX (TYPE( 8 signed)) = (2 ^  7 - 1)"
  "WORD_MAX (TYPE(16 signed)) = (2 ^ 15 - 1)"
  "WORD_MAX (TYPE(32 signed)) = (2 ^ 31 - 1)"
  "WORD_MAX (TYPE(64 signed)) = (2 ^ 63 - 1)"

  "WORD_MIN (TYPE( 8 signed)) = - (2 ^  7)"
  "WORD_MIN (TYPE(16 signed)) = - (2 ^ 15)"
  "WORD_MIN (TYPE(32 signed)) = - (2 ^ 31)"
  "WORD_MIN (TYPE(64 signed)) = - (2 ^ 63)"

  "UWORD_MAX (TYPE( 8)) = (2 ^  8 - 1)"
  "UWORD_MAX (TYPE(16)) = (2 ^ 16 - 1)"
  "UWORD_MAX (TYPE(32)) = (2 ^ 32 - 1)"
  "UWORD_MAX (TYPE(64)) = (2 ^ 64 - 1)"
  by (auto simp: WORD_MAX_def WORD_MIN_def UWORD_MAX_def)

lemmas WORD_values_add1 =
   WORD_values [THEN arg_cong [where f="\<lambda>x. x + 1"],
    simplified semiring_norm, simplified numeral_One]

lemmas WORD_values_minus1 =
   WORD_values [THEN arg_cong [where f="\<lambda>x. x - 1"],
    simplified semiring_norm, simplified numeral_One nat_numeral]

lemmas [L1unfold] =
  WORD_values [symmetric]
  WORD_values_add1 [symmetric]
  WORD_values_minus1 [symmetric]

lemma WORD_signed_to_unsigned [simp]:
   "WORD_MAX TYPE('a signed) = WORD_MAX TYPE('a::len)"
   "WORD_MIN TYPE('a signed) = WORD_MIN TYPE('a::len)"
   "UWORD_MAX TYPE('a signed) = UWORD_MAX TYPE('a::len)"
  by (auto simp: WORD_MAX_def WORD_MIN_def UWORD_MAX_def)

(*
 * The following set of theorems allow us to discharge simple
 * equalities involving INT_MIN, INT_MAX and UINT_MAX without
 * the constants being unfolded in the final output.
 *
 * For example:
 *
 *    (4 < INT_MAX)  becomes  True
 *    (x < INT_MAX)  remains  (x < INT_MAX)
 *)

lemma INT_MIN_comparisons [simp]:
  "\<lbrakk> a \<le> - (2 ^ (len_of TYPE('a) - 1)) \<rbrakk> \<Longrightarrow> a \<le> WORD_MIN (TYPE('a::len))"
  "a < - (2 ^ (len_of TYPE('a) - 1)) \<Longrightarrow> a < WORD_MIN (TYPE('a::len))"
  "a \<ge> - (2 ^ (len_of TYPE('a) - 1)) \<Longrightarrow> a \<ge> WORD_MIN (TYPE('a::len))"
  "a > - (2 ^ (len_of TYPE('a) - 1)) \<Longrightarrow> a \<ge> WORD_MIN (TYPE('a::len))"
  by (auto simp: WORD_MIN_def)

lemma INT_MAX_comparisons [simp]:
  "a \<le> (2 ^ (len_of TYPE('a) - 1)) - 1 \<Longrightarrow> a \<le> WORD_MAX (TYPE('a::len))"
  "a < (2 ^ (len_of TYPE('a) - 1)) - 1 \<Longrightarrow> a < WORD_MAX (TYPE('a::len))"
  "a \<ge> (2 ^ (len_of TYPE('a) - 1)) - 1 \<Longrightarrow> a \<ge> WORD_MAX (TYPE('a::len))"
  "a > (2 ^ (len_of TYPE('a) - 1)) - 1 \<Longrightarrow> a \<ge> WORD_MAX (TYPE('a::len))"
  by (auto simp: WORD_MAX_def)

lemma UINT_MAX_comparisons [simp]:
  "x \<le> (2 ^ (len_of TYPE('a))) - 1 \<Longrightarrow> x \<le> UWORD_MAX (TYPE('a::len))"
  "x < (2 ^ (len_of TYPE('a))) - 1 \<Longrightarrow> x \<le> UWORD_MAX (TYPE('a::len))"
  "x \<ge> (2 ^ (len_of TYPE('a))) - 1 \<Longrightarrow> x \<ge> UWORD_MAX (TYPE('a::len))"
  "x > (2 ^ (len_of TYPE('a))) - 1 \<Longrightarrow> x > UWORD_MAX (TYPE('a::len))"
  by (auto simp: UWORD_MAX_def)

(*
 * This definition is used when we are trying to introduce a new type
 * in the program text: it simply states that introducing a given
 * abstraction is desired in the current context.
 *)
definition "introduce_typ_abs_fn f \<equiv> True"

declare introduce_typ_abs_fn_def [simp]

lemma introduce_typ_abs_fn:
  "introduce_typ_abs_fn f"
  by simp

(*
 * Show that a binary operator "X" (of type "'a \<Rightarrow> 'a \<Rightarrow> bool") is an
 * abstraction (over function f) of "X'".
 *
 * For example, (a \<le>\<^sub>i\<^sub>n\<^sub>t b) could be an abstraction of (a \<le>\<^sub>w\<^sub>3\<^sub>2 b)
 * over the abstraction function "unat".
 *)
definition
  abstract_bool_binop :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'a)
               \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> bool"
where
  "abstract_bool_binop P f X X' \<equiv> \<forall>a b. P (f a) (f b) \<longrightarrow> (X' a b = X (f a) (f b))"

(* Show that a binary operator "X" (of type "'a \<Rightarrow> 'a \<Rightarrow> 'b") abstracts "X'". *)
definition
  abstract_binop :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'a)
               \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> bool"
where
   "abstract_binop P f X X' \<equiv> \<forall>a b. P (f a) (f b) \<longrightarrow> (f (X' a b) = X (f a) (f b))"

(* The value "a" is the abstract version of "b" under precondition "P". *)
definition "abstract_val P a f b \<equiv> P \<longrightarrow> (a = f b)"

(* The variable "a" is the abstracted version of the variable "b". *)
definition "abs_var a f b \<equiv> abstract_val True a f b"

declare abstract_bool_binop_def [simp]
declare abstract_binop_def [simp]
declare abstract_val_def [simp]
declare abs_var_def [simp]

lemma abstract_val_trivial:
  "abstract_val True (f b) f b"
  by simp

lemma abstract_binop_is_abstract_val:
    "abstract_binop P f X X' = (\<forall>a b. abstract_val (P (f a) (f b)) (X (f a) (f b)) f (X' a b))"
  by auto

lemma abstract_expr_bool_binop:
  "\<lbrakk> abstract_bool_binop E f X X';
     introduce_typ_abs_fn f;
     abstract_val P a f a';
     abstract_val Q b f b' \<rbrakk> \<Longrightarrow>
           abstract_val (P \<and> Q \<and> E a b) (X a b) id (X' a' b')"
  by clarsimp

lemma abstract_expr_binop:
  "\<lbrakk> abstract_binop E f X X';
     abstract_val P a f a';
     abstract_val Q b f b' \<rbrakk> \<Longrightarrow>
           abstract_val (P \<and> Q \<and> E a b) (X a b) f (X' a' b')"
  by clarsimp

lemma unat_abstract_bool_binops:
    "abstract_bool_binop (\<lambda>_ _. True) (unat :: ('a::len) word \<Rightarrow> nat) (op <) (op <)"
    "abstract_bool_binop (\<lambda>_ _. True) (unat :: ('a::len) word \<Rightarrow> nat) (op \<le>) (op \<le>)"
    "abstract_bool_binop (\<lambda>_ _. True) (unat :: ('a::len) word \<Rightarrow> nat) (op =) (op =)"
  by (auto simp:  word_less_nat_alt word_le_nat_alt eq_iff)

lemmas unat_mult_simple = iffD1 [OF unat_mult_lem [unfolded word_bits_len_of]]

lemma le_to_less_plus_one:
    "((a::nat) \<le> b) = (a < b + 1)"
  by arith

lemma unat_abstract_binops:
  "abstract_binop (\<lambda>a b. a + b \<le> UWORD_MAX TYPE('a::len)) (unat :: 'a word \<Rightarrow> nat) (op +) (op +)"
  "abstract_binop (\<lambda>a b. a * b \<le> UWORD_MAX TYPE('a)) (unat :: 'a word \<Rightarrow> nat) (op * ) (op * )"
  "abstract_binop (\<lambda>a b. a \<ge> b) (unat :: 'a word \<Rightarrow> nat) (op -) (op -)"
  "abstract_binop (\<lambda>a b. True) (unat :: 'a word \<Rightarrow> nat) (op div) (op div)"
  "abstract_binop (\<lambda>a b. True) (unat :: 'a word \<Rightarrow> nat) (op mod) (op mod)"
  by (auto simp: unat_plus_if' unat_div unat_mod UWORD_MAX_def le_to_less_plus_one
              WordAbstract.unat_mult_simple word_bits_def unat_sub word_le_nat_alt)

lemma snat_abstract_bool_binops:
    "abstract_bool_binop (\<lambda>_ _. True) (sint :: ('a::len) signed word \<Rightarrow> int) (op <) (word_sless)"
    "abstract_bool_binop (\<lambda>_ _. True) (sint :: 'a signed word \<Rightarrow> int) (op \<le>) (word_sle)"
    "abstract_bool_binop (\<lambda>_ _. True) (sint :: 'a signed word \<Rightarrow> int) (op =) (op =)"
  by (auto simp: word_sless_def word_sle_def less_le)

lemma snat_abstract_binops:
  "abstract_binop (\<lambda>a b. WORD_MIN TYPE('a::len) \<le> a + b \<and> a + b \<le> WORD_MAX TYPE('a)) (sint :: 'a signed word \<Rightarrow> int) (op +) (op +)"
  "abstract_binop (\<lambda>a b. WORD_MIN TYPE('a) \<le> a * b \<and> a * b \<le> WORD_MAX TYPE('a)) (sint :: 'a signed word \<Rightarrow> int) (op *) (op *)"
  "abstract_binop (\<lambda>a b. WORD_MIN TYPE('a) \<le> a - b \<and> a - b \<le> WORD_MAX TYPE('a)) (sint :: 'a signed word \<Rightarrow> int) (op -) (op -)"
  "abstract_binop (\<lambda>a b. WORD_MIN TYPE('a) \<le> a sdiv b \<and> a sdiv b \<le> WORD_MAX TYPE('a)) (sint :: 'a signed word \<Rightarrow> int) (op sdiv) (op sdiv)"
  "abstract_binop (\<lambda>a b. WORD_MIN TYPE('a) \<le> a smod b \<and> a smod b \<le> WORD_MAX TYPE('a)) (sint :: 'a signed word \<Rightarrow> int) (op smod) (op smod)"
  by (auto simp: signed_arith_sint word_size WORD_MIN_def WORD_MAX_def)

lemma abstract_val_signed_unary_minus:
  "\<lbrakk> abstract_val P r sint r' \<rbrakk> \<Longrightarrow>
       abstract_val (P \<and> (- r) \<le> WORD_MAX TYPE('a)) (- r) sint ( - (r' :: ('a :: len) signed word))"
  apply clarsimp
  using sint_range_size [where w=r']
  apply -
  apply (subst signed_arith_sint)
   apply (clarsimp simp: word_size WORD_MAX_def)
  apply simp
  done

lemma abstract_val_unsigned_unary_minus:
  "\<lbrakk> abstract_val P r unat r' \<rbrakk> \<Longrightarrow>
       abstract_val P (if r = 0 then 0 else UWORD_MAX TYPE('a::len) + 1 - r) unat ( - (r' :: 'a word))"
  by (clarsimp simp: unat_minus' word_size unat_eq_zero UWORD_MAX_def)

lemmas abstract_val_signed_ops [simplified simp_thms] =
  abstract_expr_bool_binop [OF snat_abstract_bool_binops(1)]
  abstract_expr_bool_binop [OF snat_abstract_bool_binops(2)]
  abstract_expr_bool_binop [OF snat_abstract_bool_binops(3)]
  abstract_expr_binop [OF snat_abstract_binops(1)]
  abstract_expr_binop [OF snat_abstract_binops(2)]
  abstract_expr_binop [OF snat_abstract_binops(3)]
  abstract_expr_binop [OF snat_abstract_binops(4)]
  abstract_expr_binop [OF snat_abstract_binops(5)]
  abstract_val_signed_unary_minus

lemmas abstract_val_unsigned_ops [simplified simp_thms] =
  abstract_expr_bool_binop [OF unat_abstract_bool_binops(1)]
  abstract_expr_bool_binop [OF unat_abstract_bool_binops(2)]
  abstract_expr_bool_binop [OF unat_abstract_bool_binops(3)]
  abstract_expr_binop [OF unat_abstract_binops(1)]
  abstract_expr_binop [OF unat_abstract_binops(2)]
  abstract_expr_binop [OF unat_abstract_binops(3)]
  abstract_expr_binop [OF unat_abstract_binops(4)]
  abstract_expr_binop [OF unat_abstract_binops(5)]
  abstract_val_unsigned_unary_minus

lemma mod_less:
  "(a :: nat) < c \<Longrightarrow> a mod b < c"
  by (metis less_trans mod_less_eq_dividend order_leE)

lemma abstract_val_ucast:
    "\<lbrakk> introduce_typ_abs_fn (unat :: ('a::len) word \<Rightarrow> nat);
       abstract_val P v unat v' \<rbrakk>
       \<Longrightarrow>  abstract_val (P \<and> v \<le> nat (WORD_MAX TYPE('a)))
                  (int v) sint (ucast (v' :: 'a word) :: 'a signed word)"
  apply (clarsimp simp: uint_nat [symmetric])
  apply (subst sint_eq_uint)
   apply (rule not_msb_from_less)
   apply (clarsimp simp: word_less_nat_alt unat_ucast WORD_MAX_def le_to_less_plus_one)
   apply (subst (asm) nat_diff_distrib)
     apply simp
    apply clarsimp
   apply clarsimp
   apply (metis of_nat_numeral nat_numeral nat_power_eq of_nat_0_le_iff)
  apply (clarsimp simp: uint_up_ucast is_up)
  done

lemma abstract_val_scast:
    "\<lbrakk> introduce_typ_abs_fn (sint :: ('a::len) signed word \<Rightarrow> int);
       abstract_val P C' sint C \<rbrakk>
            \<Longrightarrow>  abstract_val (P \<and> 0 \<le> C') (nat C') unat (scast (C :: ('a::len) signed word) :: ('a::len) word)"
  apply (clarsimp simp: down_cast_same [symmetric] is_down unat_ucast)
  apply (subst sint_eq_uint)
   apply (clarsimp simp: word_msb_sint)
  apply (clarsimp simp: unat_def [symmetric])
  apply (subst word_unat.norm_Rep [symmetric])
  apply clarsimp
  done

lemma abstract_val_scast_upcast:
    "\<lbrakk> len_of TYPE('a::len) \<le> len_of TYPE('b::len);
       abstract_val P C' sint C \<rbrakk>
            \<Longrightarrow>  abstract_val P (C') sint (scast (C :: 'a signed word) :: 'b signed word)"
  by (clarsimp simp: down_cast_same [symmetric] sint_up_scast is_up)

lemma abstract_val_scast_downcast:
    "\<lbrakk> len_of TYPE('b) < len_of TYPE('a::len);
       abstract_val P C' sint C \<rbrakk>
            \<Longrightarrow>  abstract_val P (sbintrunc ((len_of TYPE('b::len) - 1)) C') sint (scast (C :: 'a signed word) :: 'b signed word)"
  apply (clarsimp simp: scast_def word_of_int_def sint_uint bintrunc_mod2p [symmetric])
  apply (subst bintrunc_sbintrunc_le)
   apply clarsimp
  apply (subst Abs_word_inverse)
   apply (metis len_signed uint word_ubin.eq_norm)
  apply clarsimp
  done

lemma abstract_val_ucast_upcast:
    "\<lbrakk> len_of TYPE('a::len) \<le> len_of TYPE('b::len);
       abstract_val P C' unat C \<rbrakk>
            \<Longrightarrow>  abstract_val P (C') unat (ucast (C :: 'a word) :: 'b word)"
  by (clarsimp simp: is_up unat_ucast_upcast)

lemma abstract_val_ucast_downcast:
    "\<lbrakk> len_of TYPE('b::len) < len_of TYPE('a::len);
       abstract_val P C' unat C \<rbrakk>
            \<Longrightarrow>  abstract_val P (C' mod (UWORD_MAX TYPE('b) + 1)) unat (ucast (C :: 'a word) :: 'b word)"
  apply (clarsimp simp: scast_def word_of_int_def sint_uint UWORD_MAX_def)
  unfolding ucast_def unat_def
  apply (subst int_word_uint)
  apply (metis (hide_lams, mono_tags) uint_mod uint_power_lower
      unat_def unat_mod unat_power_lower)
  done

(*
 * The pair A/C are a valid abstraction/concrete-isation function pair,
 * under the precondition's P and Q.
 *)
definition
 "valid_typ_abs_fn (P :: 'a \<Rightarrow> bool) (Q :: 'a \<Rightarrow> bool) (A :: 'c \<Rightarrow> 'a) (C :: 'a \<Rightarrow> 'c) \<equiv>
     (\<forall>v. P v \<longrightarrow> A (C v) = v) \<and> (\<forall>v. Q (A v) \<longrightarrow> C (A v) = v)"

declare valid_typ_abs_fn_def [simp]

lemma valid_typ_abs_fn_id:
  "valid_typ_abs_fn \<top> \<top> id id"
  by clarsimp

lemma valid_typ_abs_fn_unit:
  "valid_typ_abs_fn \<top> \<top> id (id :: unit \<Rightarrow> unit)"
  by clarsimp

lemma valid_typ_abs_fn_unat:
  "valid_typ_abs_fn (\<lambda>v. v \<le> UWORD_MAX TYPE('a::len)) \<top> (unat :: 'a word \<Rightarrow> nat) (of_nat :: nat \<Rightarrow> 'a word)"
  by (clarsimp simp: unat_of_nat_eq UWORD_MAX_def le_to_less_plus_one)

lemma valid_typ_abs_fn_sint:
  "valid_typ_abs_fn (\<lambda>v. WORD_MIN TYPE('a::len) \<le> v \<and> v \<le> WORD_MAX TYPE('a)) \<top> (sint :: 'a signed word \<Rightarrow> int) (of_int :: int \<Rightarrow> 'a signed word)"
  by (clarsimp simp: sint_of_int_eq WORD_MIN_def WORD_MAX_def)

lemma valid_typ_abs_fn_tuple:
  "\<lbrakk> valid_typ_abs_fn P_a Q_a abs_a conc_a; valid_typ_abs_fn P_b Q_b abs_b conc_b \<rbrakk> \<Longrightarrow>
          valid_typ_abs_fn (\<lambda>(a, b). P_a a \<and> P_b b) (\<lambda>(a, b). Q_a a \<and> Q_b b) (map_prod abs_a abs_b) (map_prod conc_a conc_b)"
  by clarsimp

lemma introduce_typ_abs_fn_tuple:
  "\<lbrakk> introduce_typ_abs_fn abs_a; introduce_typ_abs_fn abs_b \<rbrakk> \<Longrightarrow>
         introduce_typ_abs_fn (map_prod abs_a abs_b)"
  by clarsimp

definition [simp]:
  "corresTA P rx ex A C \<equiv> corresXF (\<lambda>s. s) (\<lambda>r s. rx r) (\<lambda>r s. ex r) P A C"

lemma corresTA_L2_gets:
  "\<lbrakk> \<And>s. abstract_val (Q s) (C s) rx (C' s) \<rbrakk> \<Longrightarrow>
     corresTA Q rx ex (L2_gets (\<lambda>s. C s) n) (L2_gets (\<lambda>s. C' s) n)"
  apply (monad_eq simp: L2_defs corresXF_def)
  done

lemma corresTA_L2_modify:
    "\<lbrakk> \<And>s. abstract_val (P s) (m s) id (m' s) \<rbrakk> \<Longrightarrow>
            corresTA P rx ex (L2_modify (\<lambda>s. m s)) (L2_modify (\<lambda>s. m' s))"
  by (monad_eq simp: L2_modify_def corresXF_def)

lemma corresTA_L2_throw:
  "\<lbrakk> abstract_val Q C ex C' \<rbrakk> \<Longrightarrow>
     corresTA (\<lambda>_. Q) rx ex (L2_throw C n) (L2_throw C' n)"
  apply (monad_eq simp: L2_defs corresXF_def)
  done

lemma corresTA_L2_skip:
  "corresTA \<top> rx ex L2_skip L2_skip"
  apply (monad_eq simp: L2_defs corresXF_def)
  done

lemma corresTA_L2_fail:
  "corresTA \<top> rx ex L2_fail L2_fail"
  by (clarsimp simp: L2_defs corresXF_def)

lemma corresTA_L2_seq':
  fixes L' :: "('s, 'e + 'c1) nondet_monad"
  fixes R' :: "'c1 \<Rightarrow> ('s, 'e + 'c2) nondet_monad"
  fixes L :: "('s, 'ea + 'a1) nondet_monad"
  fixes R :: "'a1 \<Rightarrow> ('s, 'ea + 'a2) nondet_monad"
  shows
  "\<lbrakk> corresTA P rx1 ex L L';
     \<And>r. corresTA (Q (rx1 r)) rx2 ex (R (rx1 r)) (R' r) \<rbrakk> \<Longrightarrow>
    corresTA P rx2 ex
       (L2_seq L (\<lambda>r. L2_seq (L2_guard (\<lambda>s. Q r s)) (\<lambda>_. R r)))
       (L2_seq L' (\<lambda>r. R' r))"
  apply atomize
  apply (clarsimp simp: L2_seq_def L2_guard_def)
  apply (erule corresXF_join [where P'="\<lambda>x y s. rx1 y = x"])
    apply (monad_eq simp: corresXF_def split: sum.splits)
   apply clarsimp
   apply (rule hoareE_TrueI)
  apply simp
  done

lemma corresTA_L2_seq:
  "\<lbrakk> introduce_typ_abs_fn rx1;
    corresTA P (rx1 :: 'a \<Rightarrow> 'b) ex L L';
     \<And>r r'. abs_var r rx1 r' \<Longrightarrow> corresTA (\<lambda>s. Q r s) rx2 ex (\<lambda>s. R r s) (\<lambda>s. R' r' s) \<rbrakk> \<Longrightarrow>
       corresTA P rx2 ex (L2_seq L (\<lambda>r. L2_seq (L2_guard (\<lambda>s. Q r s)) (\<lambda>_ s. R r s))) (L2_seq L' (\<lambda>r s. R' r s))"
  by (rule corresTA_L2_seq', simp+)

lemma corresTA_L2_seq_unit:
  fixes L' :: "('s, 'e + unit) nondet_monad"
  fixes R' :: "unit \<Rightarrow> ('s, 'e + 'r) nondet_monad"
  fixes L :: "('s, 'ea + unit) nondet_monad"
  fixes R :: "('s, 'ea + 'ra) nondet_monad"
  shows
  "\<lbrakk> corresTA P id ex L L';
     corresTA Q rx ex (\<lambda>s. R s) (\<lambda>s. R' () s) \<rbrakk> \<Longrightarrow>
    corresTA P rx ex
       (L2_seq L (\<lambda>r. L2_seq (L2_guard Q) (\<lambda>r s. R s)))
       (L2_seq L' (\<lambda>r s. R' r s))"
  by (rule corresTA_L2_seq', simp+)

lemma corresTA_L2_catch':
  fixes L' :: "('s, 'e1 + 'c) nondet_monad"
  fixes R' :: "'e1 \<Rightarrow> ('s, 'e2 + 'c) nondet_monad"
  fixes L :: "('s, 'e1a + 'ca) nondet_monad"
  fixes R :: "'e1a \<Rightarrow> ('s, 'e2a + 'ca) nondet_monad"
  shows
  "\<lbrakk> corresTA P rx ex1 L L';
     \<And>r. corresTA (Q (ex1 r)) rx ex2 (R (ex1 r)) (R' r) \<rbrakk> \<Longrightarrow>
    corresTA P rx ex2 (L2_catch L (\<lambda>r. L2_seq (L2_guard (\<lambda>s. Q r s)) (\<lambda>_. R r))) (L2_catch L' (\<lambda>r. R' r))"
  apply atomize
  apply (clarsimp simp: L2_seq_def L2_catch_def L2_guard_def)
  apply (erule corresXF_except [where P'="\<lambda>x y s. ex1 y = x"])
    apply (monad_eq simp: corresXF_def split: sum.splits cong: rev_conj_cong)
   apply clarsimp
   apply (rule hoareE_TrueI)
  apply simp
  done

lemma corresTA_L2_catch:
  "\<lbrakk> introduce_typ_abs_fn ex1;
     corresTA P rx ex1 L L';
     \<And>r r'. abs_var r ex1 r' \<Longrightarrow> corresTA (Q r) rx ex2 (R r) (R' r') \<rbrakk> \<Longrightarrow>
       corresTA P rx ex2 (L2_catch L (\<lambda>r. L2_seq (L2_guard (\<lambda>s. Q r s)) (\<lambda>_. R r))) (L2_catch L' (\<lambda>r. R' r))"
  by (rule corresTA_L2_catch', simp+)

lemma corresTA_L2_while:
  assumes init_corres: "abstract_val Q i rx i'"
  and cond_corres: "\<And>r r' s. abs_var r rx r'
                           \<Longrightarrow> abstract_val (G r s) (C r s) id (C' r' s)"
  and body_corres: "\<And>r r'. abs_var r rx r'
                           \<Longrightarrow> corresTA (P r) rx ex (B r) (B' r')"
  shows "corresTA (\<lambda>_. Q) rx ex
       (L2_guarded_while (\<lambda>r s. G r s) (\<lambda>r s. C r s) (\<lambda>r. L2_seq (L2_guard (\<lambda>s. P r s)) (\<lambda>_. B r)) i x)
       (L2_while (\<lambda>r s. C' r s) B' i' x)"
proof -
  note body_corres' =
       corresXF_guarded_while_body [OF body_corres [unfolded corresTA_def]]

  have init_corres':
    "Q \<Longrightarrow> i = rx i'"
    using init_corres
    by simp

  show ?thesis
    apply (clarsimp simp: L2_defs guardE_def [symmetric] returnOk_liftE [symmetric])
    apply (rule corresXF_assume_pre)
    apply (rule corresXF_guarded_while [where P="\<lambda>r s. G (rx r) s"])
        apply (cut_tac r'=x in body_corres, simp)
        apply (monad_eq simp: guardE_def corresXF_def split: sum.splits)
       apply (insert cond_corres)[1]
       apply clarsimp
      apply clarsimp
      apply (rule hoareE_TrueI)
     apply (clarsimp simp: init_corres)
     apply (insert init_corres)[1]
     apply (clarsimp)
    apply (clarsimp simp: init_corres')
  done
qed

lemma corresTA_L2_guard:
  "\<lbrakk> \<And>s. abstract_val (Q s) (G s) id (G' s) \<rbrakk>
           \<Longrightarrow> corresTA \<top> rx ex (L2_guard (\<lambda>s. G s \<and> Q s)) (L2_guard (\<lambda>s. G' s))"
  apply (monad_eq simp: L2_defs corresXF_def)
  done

lemma corresTA_L2_spec:
  "(\<And>s t. abstract_val (Q s) (P s t) id (P' s t)) \<Longrightarrow>
   corresTA Q rx ex (L2_spec {(s, t). P s t}) (L2_spec {(s, t). P' s t})"
  apply (monad_eq simp: L2_defs corresXF_def in_liftE split: sum.splits)
  apply (erule exI)
  done

lemma corresTA_L2_condition:
  "\<lbrakk> corresTA P rx ex L L';
     corresTA Q rx ex R R';
     \<And>s. abstract_val (T s) (C s) id (C' s)  \<rbrakk>
   \<Longrightarrow> corresTA T rx ex
          (L2_condition (\<lambda>s. C s)
            (L2_seq (L2_guard P) (\<lambda>_. L))
            (L2_seq (L2_guard Q) (\<lambda>_. R))
           ) (L2_condition (\<lambda>s. C' s) L' R')"
  apply atomize
  apply (monad_eq simp: L2_defs corresXF_def Ball_def split: sum.splits)
  apply force
  done


(* Backup rule to corresTA_L2_call. Converts the return type of the function call. *)
lemma corresTA_L2_call':
  "\<lbrakk> corresTA P f1 x1 A B;
     valid_typ_abs_fn Q1 Q1' f1 f1';
     valid_typ_abs_fn Q2 Q2' f2 f2'
   \<rbrakk> \<Longrightarrow>
   corresTA (\<lambda>s. P s) f2 x2
       (L2_seq (L2_call A) (\<lambda>ret. (L2_seq (L2_guard (\<lambda>_. Q1' ret)) (\<lambda>_. L2_gets (\<lambda>_. f2 (f1' ret)) [''ret'']))))
       (L2_call B)"
  apply (clarsimp simp: L2_defs L2_call_def corresXF_def)
  apply (monad_eq split: sum.splits)
  apply (rule conjI)
   apply metis
  apply clarsimp
  apply blast
  done

lemma corresTA_L2_call:
  "\<lbrakk> corresTA P rx ex A B \<rbrakk> \<Longrightarrow>
        corresTA P rx ex' (L2_call A) (L2_call B)"
  apply (clarsimp simp: L2_defs L2_call_def corresXF_def)
  apply (monad_eq split: sum.splits)
  apply fastforce
  done

lemma corresTA_measure_call:
  "\<lbrakk> monad_mono B; \<And>m. corresTA P rx id (A m) (B m) \<rbrakk> \<Longrightarrow>
        corresTA P rx id (measure_call A) (measure_call B)"
  by (simp add: corresXF_measure_call)

lemma corresTA_L2_unknown:
  "corresTA \<top> rx ex (L2_unknown x) (L2_unknown x)"
  apply (monad_eq simp: L2_defs corresXF_def)
  done

lemma corresTA_L2_call_exec_concrete:
  "\<lbrakk> corresTA P rx id A B \<rbrakk> \<Longrightarrow>
        corresTA (\<lambda>s. \<forall>s'. s = st s' \<longrightarrow> P s') rx id
               (exec_concrete st (L2_call A))
               (exec_concrete st (L2_call B))"
  apply (clarsimp simp: L2_defs L2_call_def corresXF_def)
  apply (monad_eq split: sum.splits)
  apply fastforce
  done

lemma corresTA_L2_call_exec_abstract:
  "\<lbrakk> corresTA P rx id A B \<rbrakk> \<Longrightarrow>
        corresTA (\<lambda>s. P (st s)) rx id
               (exec_abstract st (L2_call A))
               (exec_abstract st (L2_call B))"
  apply (clarsimp simp: L2_defs L2_call_def corresXF_def)
  apply (monad_eq split: sum.splits)
  apply fastforce
  done

(* More backup rules for calls. *)
lemma corresTA_L2_call_exec_concrete':
  "\<lbrakk> corresTA P f1 x1 A B;
     valid_typ_abs_fn Q1 Q1' f1 f1';
     valid_typ_abs_fn Q2 Q2' f2 f2'
   \<rbrakk> \<Longrightarrow>
   corresTA (\<lambda>s. \<forall>s'. s = st s' \<longrightarrow> P s') f2 x2
       (L2_seq (exec_concrete st (L2_call A)) (\<lambda>ret. (L2_seq (L2_guard (\<lambda>_. Q1' ret)) (\<lambda>_. L2_gets (\<lambda>_. f2 (f1' ret)) [''ret'']))))
       (exec_concrete st (L2_call B))"
  apply (clarsimp simp: L2_defs L2_call_def corresXF_def)
  apply (monad_eq split: sum.splits)
  apply (rule conjI)
   apply clarsimp
   apply metis
  apply clarsimp
  apply blast
  done

lemma corresTA_L2_call_exec_abstract':
  "\<lbrakk> corresTA P f1 x1 A B;
     valid_typ_abs_fn Q1 Q1' f1 f1';
     valid_typ_abs_fn Q2 Q2' f2 f2'
   \<rbrakk> \<Longrightarrow>
   corresTA (\<lambda>s. P (st s)) f2 x2
       (L2_seq (exec_abstract st (L2_call A)) (\<lambda>ret. (L2_seq (L2_guard (\<lambda>_. Q1' ret)) (\<lambda>_. L2_gets (\<lambda>_. f2 (f1' ret)) [''ret'']))))
       (exec_abstract st (L2_call B))"
  apply (clarsimp simp: L2_defs L2_call_def corresXF_def)
  apply (monad_eq split: sum.splits)
  apply (rule conjI)
   apply metis
  apply clarsimp
  apply blast
  done


lemma abstract_val_fun_app:
   "\<lbrakk> abstract_val Q b id b'; abstract_val P a id a' \<rbrakk> \<Longrightarrow>
           abstract_val (P \<and> Q) (f $ (a $ b)) f (a' $ b')"
  by simp

lemma corresTA_precond_to_guard:
  "corresTA (\<lambda>s. P s) rx ex A A' \<Longrightarrow> corresTA \<top> rx ex (L2_seq (L2_guard (\<lambda>s. P s)) (\<lambda>_. A)) A'"
  apply (monad_eq simp: corresXF_def L2_defs split: sum.splits)
  done

lemma corresTA_precond_to_asm:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> corresTA \<top> rx ex A A' \<rbrakk> \<Longrightarrow> corresTA P rx ex A A'"
  by (clarsimp simp: corresXF_def)

lemma L2_guard_true: "L2_seq (L2_guard \<top>) A = A ()"
  by (monad_eq simp: L2_defs)
lemma corresTA_simp_trivial_guard:
  "corresTA P rx ex (L2_seq (L2_guard \<top>) A) C \<equiv> corresTA P rx ex (A ()) C"
  by (simp add: L2_guard_true)

definition "L2_assume P \<equiv> condition P (returnOk ()) (selectE {})"

lemma L2_assume_alt_def:
  "L2_assume P = (\<lambda>s. (if P s then {(Inr (), s)} else {}, False))"
  by (monad_eq simp: L2_assume_def selectE_def)

lemma corresTA_assume_values:
  "\<lbrakk> abstract_val P a f a'; corresTA \<top> rx ex X X' \<rbrakk>
              \<Longrightarrow> corresTA \<top> rx ex (L2_seq (L2_assume (\<lambda>s. P \<longrightarrow> (\<exists>a'. a = f a'))) (\<lambda>_. X)) X'"
  apply (monad_eq simp: corresXF_def L2_defs L2_assume_alt_def split: sum.splits)
  apply force
  done

lemma corresTA_extract_preconds_of_call_init:
  "\<lbrakk> corresTA (\<lambda>s. P) rx ex A A' \<rbrakk> \<Longrightarrow> corresTA (\<lambda>s. P \<and> True) rx ex A A'"
  by simp

lemma corresTA_extract_preconds_of_call_step:
  "\<lbrakk> corresTA (\<lambda>s. (abs_var a f a' \<and> R) \<and> C) rx ex A A'; abstract_val Y a f a' \<rbrakk>
           \<Longrightarrow> corresTA (\<lambda>s. R \<and> (Y \<and> C)) rx ex A A'"
  by (clarsimp simp: corresXF_def)

lemma corresTA_extract_preconds_of_call_final:
  "\<lbrakk> corresTA (\<lambda>s. (abs_var a f a') \<and> C) rx ex A A'; abstract_val Y a f a' \<rbrakk>
           \<Longrightarrow> corresTA (\<lambda>s. (Y \<and> C)) rx ex A A'"
  by (clarsimp simp: corresXF_def)

lemma corresTA_extract_preconds_of_call_final':
  "\<lbrakk> corresTA (\<lambda>s. True \<and> C) rx ex A A' \<rbrakk>
           \<Longrightarrow> corresTA (\<lambda>s. C) rx ex A A'"
  by (clarsimp simp: corresXF_def)

lemma corresTA_case_prod:
 "\<lbrakk> introduce_typ_abs_fn rx1;
    introduce_typ_abs_fn rx2;
    abstract_val (Q x) x (map_prod rx1 rx2) x';
      \<And>a b a' b'. \<lbrakk> abs_var a rx1 a'; abs_var  b rx2 b' \<rbrakk>
                      \<Longrightarrow>  corresTA (P a b) rx ex (M a b) (M' a' b') \<rbrakk>  \<Longrightarrow>
    corresTA (\<lambda>s. case x of (a, b) \<Rightarrow> P a b s \<and> Q (a, b)) rx ex (case x of (a, b) \<Rightarrow> M a b) (case x' of (a, b) \<Rightarrow> M' a b)"
  apply clarsimp
  apply (rule corresXF_assume_pre)
  apply (clarsimp simp: split_def map_prod_def)
  done

lemma abstract_val_case_prod:
  "\<lbrakk> abstract_val True r (map_prod f g) r';
       \<And>a b a' b'. \<lbrakk>  abs_var a f a'; abs_var  b g b' \<rbrakk>
                     \<Longrightarrow> abstract_val (P a b) (M a b) h (M' a' b') \<rbrakk>
       \<Longrightarrow> abstract_val (P (fst r) (snd r))
            (case r of (a, b) \<Rightarrow> M a b) h
            (case r' of (a, b) \<Rightarrow> M' a b)"
  apply (case_tac r, case_tac r')
  apply (clarsimp simp: map_prod_def)
  done

lemma abstract_val_case_prod_fun_app:
  "\<lbrakk> abstract_val True r (map_prod f g) r';
       \<And>a b a' b'. \<lbrakk>  abs_var a f a'; abs_var b g b' \<rbrakk>
                     \<Longrightarrow> abstract_val (P a b) (M a b s) h (M' a' b' s) \<rbrakk>
       \<Longrightarrow> abstract_val (P (fst r) (snd r))
            ((case r of (a, b) \<Rightarrow> M a b) s) h
            ((case r' of (a, b) \<Rightarrow> M' a b) s)"
  apply (case_tac r, case_tac r')
  apply (clarsimp simp: map_prod_def)
  done

lemma abstract_val_of_nat:
  "abstract_val (r \<le> UWORD_MAX TYPE('a::len)) r unat (of_nat r :: 'a word)"
  by (clarsimp simp: unat_of_nat_eq UWORD_MAX_def le_to_less_plus_one)

lemma abstract_val_of_int:
  "abstract_val (WORD_MIN TYPE('a::len) \<le> r \<and> r \<le> WORD_MAX TYPE('a)) r sint (of_int r :: 'a signed word)"
  by (clarsimp simp: sint_of_int_eq WORD_MIN_def WORD_MAX_def)

lemma abstract_val_tuple:
  "\<lbrakk> abstract_val P a absL a';
     abstract_val Q b absR b' \<rbrakk> \<Longrightarrow>
         abstract_val (P \<and> Q) (a, b) (map_prod absL absR) (a', b')"
  by clarsimp

lemma abstract_val_func:
   "\<lbrakk> abstract_val P a id a'; abstract_val Q b id b' \<rbrakk>
        \<Longrightarrow>  abstract_val (P \<and> Q) (f a b) id (f a' b')"
  by simp

lemma abstract_val_conj:
  "\<lbrakk> abstract_val P a id a';
        abstract_val Q b id b' \<rbrakk> \<Longrightarrow>
     abstract_val (P \<and> (a \<longrightarrow> Q)) (a \<and> b) id (a' \<and> b')"
  apply clarsimp
  apply blast
  done

lemma abstract_val_disj:
  "\<lbrakk> abstract_val P a id a';
        abstract_val Q b id b' \<rbrakk> \<Longrightarrow>
     abstract_val (P \<and> (\<not> a \<longrightarrow> Q)) (a \<or> b) id (a' \<or> b')"
  apply clarsimp
  apply blast
  done

lemma abstract_val_unwrap:
  "\<lbrakk> introduce_typ_abs_fn f; abstract_val P a f b \<rbrakk>
        \<Longrightarrow> abstract_val P a id (f b)"
  by simp

lemma abstract_val_uint:
  "\<lbrakk> introduce_typ_abs_fn unat; abstract_val P x unat x' \<rbrakk>
      \<Longrightarrow> abstract_val P (int x) id (uint x')"
  by (clarsimp simp: uint_nat)

lemma corresTA_L2_recguard:
  "corresTA (\<lambda>s. P s) rx ex A A' \<Longrightarrow>
        corresTA \<top> rx ex (L2_recguard m (L2_seq (L2_guard (\<lambda>s. P s)) (\<lambda>_. A))) (L2_recguard m A')"
  by (monad_eq simp: corresXF_def L2_defs split: sum.splits)

lemma corresTA_recguard_0:
    "corresTA st rx ex (L2_recguard 0 A) C"
  by (clarsimp simp: L2_recguard_def corresXF_def)

lemma abstract_val_lambda:
   "\<lbrakk> \<And>v. abstract_val (P v) (a v) id (a' v) \<rbrakk> \<Longrightarrow>
           abstract_val (\<forall>v. P v) (\<lambda>v. a v) id (\<lambda>v. a' v)"
  by auto

(* Rules for translating simpl wrappers. *)
lemma corresTA_call_L1:
  "abstract_val True arg_xf id arg_xf' \<Longrightarrow>
   corresTA \<top> id id
     (L2_call_L1 arg_xf gs ret_xf l1body)
     (L2_call_L1 arg_xf' gs ret_xf l1body)"
  apply (unfold corresTA_def abstract_val_def id_def)
  apply (subst (asm) simp_thms)
  apply (erule subst)
  apply (rule corresXF_id[simplified id_def])
  done

lemma abstract_val_call_L1_args:
  "abstract_val P x id x' \<Longrightarrow> abstract_val P y id y' \<Longrightarrow>
   abstract_val P (x and y) id (x' and y')"
  by simp

lemma abstract_val_call_L1_arg:
  "abs_var x id x' \<Longrightarrow> abstract_val P (\<lambda>s. f s = x) id (\<lambda>s. f s = x')"
  by simp

(* Variable abstraction *)

lemma abstract_val_abs_var [consumes 1]:
  "\<lbrakk> abs_var a f a' \<rbrakk> \<Longrightarrow> abstract_val True a f a'"
  by (clarsimp simp: fun_upd_def split: if_splits)

lemma abstract_val_abs_var_concretise [consumes 1]:
  "\<lbrakk> abs_var a A a'; introduce_typ_abs_fn A; valid_typ_abs_fn PA PC A (C :: 'a \<Rightarrow> 'c)  \<rbrakk>
      \<Longrightarrow> abstract_val (PC a) (C a) id a'"
  by (clarsimp simp: fun_upd_def split: if_splits)

lemma abstract_val_abs_var_give_up [consumes 1]:
  "\<lbrakk> abs_var a id a' \<rbrakk> \<Longrightarrow> abstract_val True (A a) A a'"
  by (clarsimp simp: fun_upd_def split: if_splits)

(* Misc *)

lemma len_of_word_comparisons [L2opt]:
  "len_of TYPE(64) \<le> len_of TYPE(64)"
  "len_of TYPE(32) \<le> len_of TYPE(64)"
  "len_of TYPE(16) \<le> len_of TYPE(64)"
  "len_of TYPE( 8) \<le> len_of TYPE(64)"
  "len_of TYPE(32) \<le> len_of TYPE(32)"
  "len_of TYPE(16) \<le> len_of TYPE(32)"
  "len_of TYPE( 8) \<le> len_of TYPE(32)"
  "len_of TYPE(16) \<le> len_of TYPE(16)"
  "len_of TYPE( 8) \<le> len_of TYPE(16)"
  "len_of TYPE( 8) \<le> len_of TYPE( 8)"

  "len_of TYPE(32) < len_of TYPE(64)"
  "len_of TYPE(16) < len_of TYPE(64)"
  "len_of TYPE( 8) < len_of TYPE(64)"
  "len_of TYPE(16) < len_of TYPE(32)"
  "len_of TYPE( 8) < len_of TYPE(32)"
  "len_of TYPE( 8) < len_of TYPE(16)"

  "len_of TYPE('a::len signed) = len_of TYPE('a)"
  "(len_of TYPE('a) = len_of TYPE('a)) = True"
  by auto

lemma scast_ucast_simps [simp, L2opt]:
  "\<lbrakk> len_of TYPE('b) \<le> len_of TYPE('a); len_of TYPE('c) \<le> len_of TYPE('b) \<rbrakk> \<Longrightarrow>
         (scast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  "\<lbrakk> len_of TYPE('c) \<le> len_of TYPE('a); len_of TYPE('c) \<le> len_of TYPE('b) \<rbrakk> \<Longrightarrow>
         (scast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  "\<lbrakk> len_of TYPE('a) \<le> len_of TYPE('b); len_of TYPE('c) \<le> len_of TYPE('b) \<rbrakk> \<Longrightarrow>
         (scast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  "\<lbrakk> len_of TYPE('a) \<le> len_of TYPE('b) \<rbrakk> \<Longrightarrow>
     (scast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  "\<lbrakk> len_of TYPE('b) \<le> len_of TYPE('a); len_of TYPE('c) \<le> len_of TYPE('b) \<rbrakk> \<Longrightarrow>
            (ucast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  "\<lbrakk> len_of TYPE('c) \<le> len_of TYPE('a); len_of TYPE('c) \<le> len_of TYPE('b) \<rbrakk> \<Longrightarrow>
     (ucast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  "\<lbrakk> len_of TYPE('a) \<le> len_of TYPE('b); len_of TYPE('c) \<le> len_of TYPE('b) \<rbrakk> \<Longrightarrow>
     (ucast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  "\<lbrakk> len_of TYPE('c) \<le> len_of TYPE('b) \<rbrakk> \<Longrightarrow>
        (ucast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  "\<lbrakk> len_of TYPE('a) \<le> len_of TYPE('b) \<rbrakk> \<Longrightarrow>
     (ucast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  "\<lbrakk> len_of TYPE('a) \<le> len_of TYPE('b) \<rbrakk> \<Longrightarrow>
            (scast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  by (auto simp: is_up is_down
      scast_ucast_1 scast_ucast_3 scast_ucast_4
      ucast_scast_1 ucast_scast_3 ucast_scast_4
      scast_scast_a scast_scast_b
      ucast_ucast_a ucast_ucast_b)

declare len_signed [L2opt]

lemmas [L2opt] = zero_sle_ucast_up

lemma zero_sle_ucast_WORD_MAX [L2opt]:
  "(0 <=s ((ucast (b::('a::len) word)) :: ('a::len) signed word))
                = (uint b \<le> WORD_MAX (TYPE('a)))"
  by (clarsimp simp: WORD_MAX_def zero_sle_ucast)

lemmas [L2opt] =
    is_up is_down unat_ucast_upcast sint_ucast_eq_uint

lemmas [L2opt] =
    ucast_down_add scast_down_add
    ucast_down_minus scast_down_minus
    ucast_down_mult scast_down_mult

(*
 * Setup word abstraction rules.
 *)

named_theorems word_abs

(* Common word abstraction rules. *)

lemmas [word_abs] =
  corresTA_L2_gets
  corresTA_L2_modify
  corresTA_L2_throw
  corresTA_L2_skip
  corresTA_L2_fail
  corresTA_L2_seq
  corresTA_L2_seq_unit
  corresTA_L2_catch
  corresTA_L2_while
  corresTA_L2_guard
  corresTA_L2_spec
  corresTA_L2_condition
  corresTA_L2_unknown
  corresTA_L2_recguard
  corresTA_case_prod
  corresTA_L2_call_exec_concrete'
  corresTA_L2_call_exec_concrete
  corresTA_L2_call_exec_abstract'
  corresTA_L2_call_exec_abstract
  corresTA_L2_call'
  corresTA_L2_call
  corresTA_measure_call
  corresTA_call_L1

lemmas [word_abs] =
  abstract_val_tuple
  abstract_val_conj
  abstract_val_disj
  abstract_val_case_prod
  abstract_val_trivial
  abstract_val_of_int
  abstract_val_of_nat

  abstract_val_call_L1_arg
  abstract_val_call_L1_args

  abstract_val_abs_var_give_up
  abstract_val_abs_var_concretise
  abstract_val_abs_var

lemmas word_abs_base [word_abs] =
  valid_typ_abs_fn_id [where 'a="'a::c_type"]
  valid_typ_abs_fn_id [where 'a="bool"]
  valid_typ_abs_fn_id [where 'a="c_exntype"]
  valid_typ_abs_fn_tuple
  valid_typ_abs_fn_unit
  valid_typ_abs_fn_sint
  valid_typ_abs_fn_unat
  len_of_word_comparisons

(*
 * Signed word abstraction rules: 'a sword \<rightarrow> int
 *)

lemmas word_abs_sword =
  abstract_val_signed_ops
  abstract_val_scast
  abstract_val_scast_upcast
  abstract_val_scast_downcast
  abstract_val_unwrap [where f=sint]
  introduce_typ_abs_fn [where f="sint :: (sword64 \<Rightarrow> int)"]
  introduce_typ_abs_fn [where f="sint :: (sword32 \<Rightarrow> int)"]
  introduce_typ_abs_fn [where f="sint :: (sword16 \<Rightarrow> int)"]
  introduce_typ_abs_fn [where f="sint :: (sword8 \<Rightarrow> int)"]

(*
 * Unsigned word abstraction rules: 'a word \<rightarrow> nat
 *)

lemmas word_abs_word =
  abstract_val_unsigned_ops
  abstract_val_uint
  abstract_val_ucast
  abstract_val_ucast_upcast
  abstract_val_ucast_downcast
  abstract_val_unwrap [where f=unat]
  introduce_typ_abs_fn [where f="unat :: (word64 \<Rightarrow> nat)"]
  introduce_typ_abs_fn [where f="unat :: (word32 \<Rightarrow> nat)"]
  introduce_typ_abs_fn [where f="unat :: (word16 \<Rightarrow> nat)"]
  introduce_typ_abs_fn [where f="unat :: (word8 \<Rightarrow> nat)"]

(* 'a \<rightarrow> 'a *)
lemmas word_abs_default =
  introduce_typ_abs_fn [where f="id :: ('a::c_type \<Rightarrow> 'a)"]
  introduce_typ_abs_fn [where f="id :: (bool \<Rightarrow> bool)"]
  introduce_typ_abs_fn [where f="id :: (c_exntype \<Rightarrow> c_exntype)"]
  introduce_typ_abs_fn [where f="id :: (unit \<Rightarrow> unit)"]
  introduce_typ_abs_fn_tuple

end
