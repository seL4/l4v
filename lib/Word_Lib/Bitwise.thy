(*
 * Copyright Thomas Sewell, NICTA and Sascha Boehme, TU Muenchen
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Bitwise
  imports
    "HOL-Library.Word"
    More_Arithmetic
    Reversed_Bit_Lists
    Bit_Shifts_Infix_Syntax
begin

text \<open>Helper constants used in defining addition\<close>

definition xor3 :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool"
  where "xor3 a b c = (a = (b = c))"

definition carry :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool"
  where "carry a b c = ((a \<and> (b \<or> c)) \<or> (b \<and> c))"

lemma carry_simps:
  "carry True a b = (a \<or> b)"
  "carry a True b = (a \<or> b)"
  "carry a b True = (a \<or> b)"
  "carry False a b = (a \<and> b)"
  "carry a False b = (a \<and> b)"
  "carry a b False = (a \<and> b)"
  by (auto simp add: carry_def)

lemma xor3_simps:
  "xor3 True a b = (a = b)"
  "xor3 a True b = (a = b)"
  "xor3 a b True = (a = b)"
  "xor3 False a b = (a \<noteq> b)"
  "xor3 a False b = (a \<noteq> b)"
  "xor3 a b False = (a \<noteq> b)"
  by (simp_all add: xor3_def)

text \<open>Breaking up word equalities into equalities on their
  bit lists. Equalities are generated and manipulated in the
  reverse order to \<^const>\<open>to_bl\<close>.\<close>

lemma bl_word_sub: "to_bl (x - y) = to_bl (x + (- y))"
  by simp

lemma rbl_word_1: "rev (to_bl (1 :: 'a::len word)) = takefill False (LENGTH('a)) [True]"
  apply (rule_tac s="rev (to_bl (word_succ (0 :: 'a word)))" in trans)
   apply simp
  apply (simp only: rtb_rbl_ariths(1)[OF refl])
  apply simp
  apply (case_tac "LENGTH('a)")
   apply simp
  apply (simp add: takefill_alt)
  done

lemma rbl_word_if: "rev (to_bl (if P then x else y)) = map2 (If P) (rev (to_bl x)) (rev (to_bl y))"
  by (simp add: split_def)

lemma rbl_add_carry_Cons:
  "(if car then rbl_succ else id) (rbl_add (x # xs) (y # ys)) =
    xor3 x y car # (if carry x y car then rbl_succ else id) (rbl_add xs ys)"
  by (simp add: carry_def xor3_def)

lemma rbl_add_suc_carry_fold:
  "length xs = length ys \<Longrightarrow>
    \<forall>car. (if car then rbl_succ else id) (rbl_add xs ys) =
      (foldr (\<lambda>(x, y) res car. xor3 x y car # res (carry x y car)) (zip xs ys) (\<lambda>_. [])) car"
  apply (erule list_induct2)
   apply simp
  apply (simp only: rbl_add_carry_Cons)
  apply simp
  done

lemma to_bl_plus_carry:
  "to_bl (x + y) =
    rev (foldr (\<lambda>(x, y) res car. xor3 x y car # res (carry x y car))
      (rev (zip (to_bl x) (to_bl y))) (\<lambda>_. []) False)"
  using rbl_add_suc_carry_fold[where xs="rev (to_bl x)" and ys="rev (to_bl y)"]
  apply (simp add: word_add_rbl[OF refl refl])
  apply (drule_tac x=False in spec)
  apply (simp add: zip_rev)
  done

definition "rbl_plus cin xs ys =
  foldr (\<lambda>(x, y) res car. xor3 x y car # res (carry x y car)) (zip xs ys) (\<lambda>_. []) cin"

lemma rbl_plus_simps:
  "rbl_plus cin (x # xs) (y # ys) = xor3 x y cin # rbl_plus (carry x y cin) xs ys"
  "rbl_plus cin [] ys = []"
  "rbl_plus cin xs [] = []"
  by (simp_all add: rbl_plus_def)

lemma rbl_word_plus: "rev (to_bl (x + y)) = rbl_plus False (rev (to_bl x)) (rev (to_bl y))"
  by (simp add: rbl_plus_def to_bl_plus_carry zip_rev)

definition "rbl_succ2 b xs = (if b then rbl_succ xs else xs)"

lemma rbl_succ2_simps:
  "rbl_succ2 b [] = []"
  "rbl_succ2 b (x # xs) = (b \<noteq> x) # rbl_succ2 (x \<and> b) xs"
  by (simp_all add: rbl_succ2_def)

lemma twos_complement: "- x = word_succ (not x)"
  using arg_cong[OF word_add_not[where x=x], where f="\<lambda>a. a - x + 1"]
  by (simp add: word_succ_p1 word_sp_01[unfolded word_succ_p1] del: word_add_not)

lemma rbl_word_neg: "rev (to_bl (- x)) = rbl_succ2 True (map Not (rev (to_bl x)))"
  for x :: \<open>'a::len word\<close>
  by (simp add: twos_complement word_succ_rbl[OF refl] bl_word_not rev_map rbl_succ2_def)

lemma rbl_word_cat:
  "rev (to_bl (word_cat x y :: 'a::len word)) =
    takefill False (LENGTH('a)) (rev (to_bl y) @ rev (to_bl x))"
  by (simp add: word_cat_bl word_rev_tf)

lemma rbl_word_slice:
  "rev (to_bl (slice n w :: 'a::len word)) =
    takefill False (LENGTH('a)) (drop n (rev (to_bl w)))"
  apply (simp add: slice_take word_rev_tf rev_take)
  apply (cases "n < LENGTH('b)", simp_all)
  done

lemma rbl_word_ucast:
  "rev (to_bl (ucast x :: 'a::len word)) = takefill False (LENGTH('a)) (rev (to_bl x))"
  apply (simp add: to_bl_ucast takefill_alt)
  apply (simp add: rev_drop)
  apply (cases "LENGTH('a) < LENGTH('b)")
   apply simp_all
  done

lemma rbl_shiftl:
  "rev (to_bl (w << n)) = takefill False (size w) (replicate n False @ rev (to_bl w))"
  by (simp add: bl_shiftl takefill_alt word_size rev_drop)

lemma rbl_shiftr:
  "rev (to_bl (w >> n)) = takefill False (size w) (drop n (rev (to_bl w)))"
  by (simp add: shiftr_slice rbl_word_slice word_size)

definition "drop_nonempty v n xs = (if n < length xs then drop n xs else [last (v # xs)])"

lemma drop_nonempty_simps:
  "drop_nonempty v (Suc n) (x # xs) = drop_nonempty x n xs"
  "drop_nonempty v 0 (x # xs) = (x # xs)"
  "drop_nonempty v n [] = [v]"
  by (simp_all add: drop_nonempty_def)

definition "takefill_last x n xs = takefill (last (x # xs)) n xs"

lemma takefill_last_simps:
  "takefill_last z (Suc n) (x # xs) = x # takefill_last x n xs"
  "takefill_last z 0 xs = []"
  "takefill_last z n [] = replicate n z"
  by (simp_all add: takefill_last_def) (simp_all add: takefill_alt)

lemma rbl_sshiftr:
  "rev (to_bl (w >>> n)) = takefill_last False (size w) (drop_nonempty False n (rev (to_bl w)))"
  apply (cases "n < size w")
   apply (simp add: bl_sshiftr takefill_last_def word_size
      takefill_alt rev_take last_rev
      drop_nonempty_def)
  apply (subgoal_tac "(w >>> n) = of_bl (replicate (size w) (msb w))")
   apply (simp add: word_size takefill_last_def takefill_alt
      last_rev word_msb_alt word_rev_tf
      drop_nonempty_def take_Cons')
   apply (case_tac "LENGTH('a)", simp_all)
  apply (rule word_eqI)
  apply (simp add: bit_simps word_size test_bit_of_bl
      msb_nth)
  done

lemma nth_word_of_int:
  "bit (word_of_int x :: 'a::len word) n = (n < LENGTH('a) \<and> bit x n)"
  apply (simp add: test_bit_bl word_size to_bl_of_bin)
  apply (subst conj_cong[OF refl], erule bin_nth_bl)
  apply auto
  done

lemma nth_scast:
  "bit (scast (x :: 'a::len word) :: 'b::len word) n =
    (n < LENGTH('b) \<and>
    (if n < LENGTH('a) - 1 then bit x n
     else bit x (LENGTH('a) - 1)))"
  apply transfer
  apply (auto simp add: bit_signed_take_bit_iff min_def)
  done

lemma rbl_word_scast:
  "rev (to_bl (scast x :: 'a::len word)) = takefill_last False (LENGTH('a)) (rev (to_bl x))"
  apply (rule nth_equalityI)
   apply (simp add: word_size takefill_last_def)
  apply (clarsimp simp: nth_scast takefill_last_def
      nth_takefill word_size rev_nth to_bl_nth)
  apply (cases "LENGTH('b)")
   apply simp
  apply (clarsimp simp: less_Suc_eq_le linorder_not_less
      last_rev word_msb_alt[symmetric]
      msb_nth)
  done

definition rbl_mul :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list"
  where "rbl_mul xs ys = foldr (\<lambda>x sm. rbl_plus False (map ((\<and>) x) ys) (False # sm)) xs []"

lemma rbl_mul_simps:
  "rbl_mul (x # xs) ys = rbl_plus False (map ((\<and>) x) ys) (False # rbl_mul xs ys)"
  "rbl_mul [] ys = []"
  by (simp_all add: rbl_mul_def)

lemma takefill_le2: "length xs \<le> n \<Longrightarrow> takefill x m (takefill x n xs) = takefill x m xs"
  by (simp add: takefill_alt replicate_add[symmetric])

lemma take_rbl_plus: "\<forall>n b. take n (rbl_plus b xs ys) = rbl_plus b (take n xs) (take n ys)"
  apply (simp add: rbl_plus_def take_zip[symmetric])
  apply (rule_tac list="zip xs ys" in list.induct)
   apply simp
  apply (clarsimp simp: split_def)
  apply (case_tac n, simp_all)
  done

lemma word_rbl_mul_induct:
  "length xs \<le> size y \<Longrightarrow>
    rbl_mul xs (rev (to_bl y)) = take (length xs) (rev (to_bl (of_bl (rev xs) * y)))"
  for y :: "'a::len word"
proof (induct xs)
  case Nil
  show ?case by (simp add: rbl_mul_simps)
next
  case (Cons z zs)

  have rbl_word_plus': "to_bl (x + y) = rev (rbl_plus False (rev (to_bl x)) (rev (to_bl y)))"
    for x y :: "'a word"
    by (simp add: rbl_word_plus[symmetric])

  have mult_bit: "to_bl (of_bl [z] * y) = map ((\<and>) z) (to_bl y)"
    by (cases z) (simp cong: map_cong, simp add: map_replicate_const cong: map_cong)

  have shiftl: "of_bl xs * 2 * y = (of_bl xs * y) << 1" for xs
    by (simp add: push_bit_eq_mult shiftl_def)

  have zip_take_triv: "\<And>xs ys n. n = length ys \<Longrightarrow> zip (take n xs) ys = zip xs ys"
    by (rule nth_equalityI) simp_all

  from Cons show ?case
    apply (simp add: trans [OF of_bl_append add.commute]
        rbl_mul_simps rbl_word_plus' distrib_right mult_bit shiftl rbl_shiftl)
    apply (simp add: takefill_alt word_size rev_map take_rbl_plus min_def)
    apply (simp add: rbl_plus_def)
    apply (simp add: zip_take_triv)
    apply (simp only: mult.commute [of _ 2] to_bl_double_eq)
    apply (simp flip: butlast_rev add: take_butlast)
    done
qed

lemma rbl_word_mul: "rev (to_bl (x * y)) = rbl_mul (rev (to_bl x)) (rev (to_bl y))"
  for x :: "'a::len word"
  using word_rbl_mul_induct[where xs="rev (to_bl x)" and y=y] by (simp add: word_size)

text \<open>Breaking up inequalities into bitlist properties.\<close>

definition
  "rev_bl_order F xs ys =
     (length xs = length ys \<and>
       ((xs = ys \<and> F)
          \<or> (\<exists>n < length xs. drop (Suc n) xs = drop (Suc n) ys
                   \<and> \<not> xs ! n \<and> ys ! n)))"

lemma rev_bl_order_simps:
  "rev_bl_order F [] [] = F"
  "rev_bl_order F (x # xs) (y # ys) = rev_bl_order ((y \<and> \<not> x) \<or> ((y \<or> \<not> x) \<and> F)) xs ys"
   apply (simp_all add: rev_bl_order_def)
  apply (rule conj_cong[OF refl])
  apply (cases "xs = ys")
   apply (simp add: nth_Cons')
   apply blast
  apply (simp add: nth_Cons')
  apply safe
   apply (rule_tac x="n - 1" in exI)
   apply simp
  apply (rule_tac x="Suc n" in exI)
  apply simp
  done

lemma rev_bl_order_rev_simp:
  "length xs = length ys \<Longrightarrow>
   rev_bl_order F (xs @ [x]) (ys @ [y]) = ((y \<and> \<not> x) \<or> ((y \<or> \<not> x) \<and> rev_bl_order F xs ys))"
  by (induct arbitrary: F rule: list_induct2) (auto simp: rev_bl_order_simps)

lemma rev_bl_order_bl_to_bin:
  "length xs = length ys \<Longrightarrow>
    rev_bl_order True xs ys = (bl_to_bin (rev xs) \<le> bl_to_bin (rev ys)) \<and>
    rev_bl_order False xs ys = (bl_to_bin (rev xs) < bl_to_bin (rev ys))"
  apply (induct xs ys rule: list_induct2)
   apply (simp_all add: rev_bl_order_simps bl_to_bin_app_cat concat_bit_Suc)
  apply (auto simp add: bl_to_bin_def add1_zle_eq)
  done

lemma word_le_rbl: "x \<le> y \<longleftrightarrow> rev_bl_order True (rev (to_bl x)) (rev (to_bl y))"
  for x y :: "'a::len word"
  by (simp add: rev_bl_order_bl_to_bin word_le_def)

lemma word_less_rbl: "x < y \<longleftrightarrow> rev_bl_order False (rev (to_bl x)) (rev (to_bl y))"
  for x y :: "'a::len word"
  by (simp add: word_less_alt rev_bl_order_bl_to_bin)

definition "map_last f xs = (if xs = [] then [] else butlast xs @ [f (last xs)])"

lemma map_last_simps:
  "map_last f [] = []"
  "map_last f [x] = [f x]"
  "map_last f (x # y # zs) = x # map_last f (y # zs)"
  by (simp_all add: map_last_def)

lemma word_sle_rbl:
  "x <=s y \<longleftrightarrow> rev_bl_order True (map_last Not (rev (to_bl x))) (map_last Not (rev (to_bl y)))"
  using word_msb_alt[where w=x] word_msb_alt[where w=y]
  apply (simp add: word_sle_msb_le word_le_rbl)
  apply (subgoal_tac "length (to_bl x) = length (to_bl y)")
   apply (cases "to_bl x", simp)
   apply (cases "to_bl y", simp)
   apply (clarsimp simp: map_last_def rev_bl_order_rev_simp)
   apply auto
  done

lemma word_sless_rbl:
  "x <s y \<longleftrightarrow> rev_bl_order False (map_last Not (rev (to_bl x))) (map_last Not (rev (to_bl y)))"
  using word_msb_alt[where w=x] word_msb_alt[where w=y]
  apply (simp add: word_sless_msb_less word_less_rbl)
  apply (subgoal_tac "length (to_bl x) = length (to_bl y)")
   apply (cases "to_bl x", simp)
   apply (cases "to_bl y", simp)
   apply (clarsimp simp: map_last_def rev_bl_order_rev_simp)
   apply auto
  done

text \<open>Lemmas for unpacking \<^term>\<open>rev (to_bl n)\<close> for numerals n and also
  for irreducible values and expressions.\<close>

lemma rev_bin_to_bl_simps:
  "rev (bin_to_bl 0 x) = []"
  "rev (bin_to_bl (Suc n) (numeral (num.Bit0 nm))) = False # rev (bin_to_bl n (numeral nm))"
  "rev (bin_to_bl (Suc n) (numeral (num.Bit1 nm))) = True # rev (bin_to_bl n (numeral nm))"
  "rev (bin_to_bl (Suc n) (numeral (num.One))) = True # replicate n False"
  "rev (bin_to_bl (Suc n) (- numeral (num.Bit0 nm))) = False # rev (bin_to_bl n (- numeral nm))"
  "rev (bin_to_bl (Suc n) (- numeral (num.Bit1 nm))) =
    True # rev (bin_to_bl n (- numeral (nm + num.One)))"
  "rev (bin_to_bl (Suc n) (- numeral (num.One))) = True # replicate n True"
  "rev (bin_to_bl (Suc n) (- numeral (num.Bit0 nm + num.One))) =
    True # rev (bin_to_bl n (- numeral (nm + num.One)))"
  "rev (bin_to_bl (Suc n) (- numeral (num.Bit1 nm + num.One))) =
    False # rev (bin_to_bl n (- numeral (nm + num.One)))"
  "rev (bin_to_bl (Suc n) (- numeral (num.One + num.One))) =
    False # rev (bin_to_bl n (- numeral num.One))"
  by (simp_all add: bin_to_bl_aux_append bin_to_bl_zero_aux bin_to_bl_minus1_aux replicate_append_same)

lemma to_bl_upt: "to_bl x = rev (map (bit x) [0 ..< size x])"
  by (simp add: to_bl_eq_rev word_size rev_map)

lemma rev_to_bl_upt: "rev (to_bl x) = map (bit x) [0 ..< size x]"
  by (simp add: to_bl_upt)

lemma upt_eq_list_intros:
  "j \<le> i \<Longrightarrow> [i ..< j] = []"
  "i = x \<Longrightarrow> x < j \<Longrightarrow> [x + 1 ..< j] = xs \<Longrightarrow> [i ..< j] = (x # xs)"
  by (simp_all add: upt_eq_Cons_conv)


text \<open>Tactic definition\<close>

lemma if_bool_simps:
  "If p True y = (p \<or> y) \<and> If p False y = (\<not> p \<and> y) \<and>
    If p y True = (p \<longrightarrow> y) \<and> If p y False = (p \<and> y)"
  by auto

ML \<open>
structure Word_Bitwise_Tac =
struct

val word_ss = simpset_of \<^theory_context>\<open>Word\<close>;

fun mk_nat_clist ns =
  fold_rev (Thm.mk_binop \<^cterm>\<open>Cons :: nat \<Rightarrow> _\<close>)
    ns \<^cterm>\<open>[] :: nat list\<close>;

fun upt_conv ctxt ct =
  case Thm.term_of ct of
    \<^Const_>\<open>upt for n m\<close> =>
      let
        val (i, j) = apply2 (snd o HOLogic.dest_number) (n, m);
        val ns = map (Numeral.mk_cnumber \<^ctyp>\<open>nat\<close>) (i upto (j - 1))
          |> mk_nat_clist;
        val prop =
          Thm.mk_binop \<^cterm>\<open>(=) :: nat list \<Rightarrow> _\<close> ct ns
          |> Thm.apply \<^cterm>\<open>Trueprop\<close>;
      in
        try (fn () =>
          Goal.prove_internal ctxt [] prop
            (K (REPEAT_DETERM (resolve_tac ctxt @{thms upt_eq_list_intros} 1
                ORELSE simp_tac (put_simpset word_ss ctxt) 1))) |> mk_meta_eq) ()
      end
  | _ => NONE;

val expand_upt_simproc =
  Simplifier.make_simproc \<^context> "expand_upt"
   {lhss = [\<^term>\<open>upt x y\<close>], proc = K upt_conv};

fun word_len_simproc_fn ctxt ct =
  (case Thm.term_of ct of
    \<^Const_>\<open>len_of _ for t\<close> =>
     (let
        val T = fastype_of t |> dest_Type |> snd |> the_single
        val n = Numeral.mk_cnumber \<^ctyp>\<open>nat\<close> (Word_Lib.dest_binT T);
        val prop =
          Thm.mk_binop \<^cterm>\<open>(=) :: nat \<Rightarrow> _\<close> ct n
          |> Thm.apply \<^cterm>\<open>Trueprop\<close>;
      in
        Goal.prove_internal ctxt [] prop (K (simp_tac (put_simpset word_ss ctxt) 1))
        |> mk_meta_eq |> SOME
      end handle TERM _ => NONE | TYPE _ => NONE)
  | _ => NONE);

val word_len_simproc =
  Simplifier.make_simproc \<^context> "word_len"
   {lhss = [\<^term>\<open>len_of x\<close>], proc = K word_len_simproc_fn};

(* convert 5 or nat 5 to Suc 4 when n_sucs = 1, Suc (Suc 4) when n_sucs = 2,
   or just 5 (discarding nat) when n_sucs = 0 *)

fun nat_get_Suc_simproc_fn n_sucs ctxt ct =
  let
    val (f, arg) = dest_comb (Thm.term_of ct);
    val n =
      (case arg of \<^term>\<open>nat\<close> $ n => n | n => n)
      |> HOLogic.dest_number |> snd;
    val (i, j) = if n > n_sucs then (n_sucs, n - n_sucs) else (n, 0);
    val arg' = funpow i HOLogic.mk_Suc (HOLogic.mk_number \<^typ>\<open>nat\<close> j);
    val _ = if arg = arg' then raise TERM ("", []) else ();
    fun propfn g =
      HOLogic.mk_eq (g arg, g arg')
      |> HOLogic.mk_Trueprop |> Thm.cterm_of ctxt;
    val eq1 =
      Goal.prove_internal ctxt [] (propfn I)
        (K (simp_tac (put_simpset word_ss ctxt) 1));
  in
    Goal.prove_internal ctxt [] (propfn (curry (op $) f))
      (K (simp_tac (put_simpset HOL_ss ctxt addsimps [eq1]) 1))
    |> mk_meta_eq |> SOME
  end handle TERM _ => NONE;

fun nat_get_Suc_simproc n_sucs ts =
  Simplifier.make_simproc \<^context> "nat_get_Suc"
   {lhss = map (fn t => t $ \<^term>\<open>n :: nat\<close>) ts,
    proc = K (nat_get_Suc_simproc_fn n_sucs)};

val no_split_ss =
  simpset_of (put_simpset HOL_ss \<^context>
    |> Splitter.del_split @{thm if_split});

val expand_word_eq_sss =
  (simpset_of (put_simpset HOL_basic_ss \<^context> addsimps
       @{thms word_eq_rbl_eq word_le_rbl word_less_rbl word_sle_rbl word_sless_rbl}),
  map simpset_of [
   put_simpset no_split_ss \<^context> addsimps
    @{thms rbl_word_plus rbl_word_and rbl_word_or rbl_word_not
                                rbl_word_neg bl_word_sub rbl_word_xor
                                rbl_word_cat rbl_word_slice rbl_word_scast
                                rbl_word_ucast rbl_shiftl rbl_shiftr rbl_sshiftr
                                rbl_word_if},
   put_simpset no_split_ss \<^context> addsimps
    @{thms to_bl_numeral to_bl_neg_numeral to_bl_0 rbl_word_1},
   put_simpset no_split_ss \<^context> addsimps
    @{thms rev_rev_ident rev_replicate rev_map to_bl_upt word_size}
          addsimprocs [word_len_simproc],
   put_simpset no_split_ss \<^context> addsimps
    @{thms list.simps split_conv replicate.simps list.map
                                zip_Cons_Cons zip_Nil drop_Suc_Cons drop_0 drop_Nil
                                foldr.simps list.map zip.simps(1) zip_Nil zip_Cons_Cons takefill_Suc_Cons
                                takefill_Suc_Nil takefill.Z rbl_succ2_simps
                                rbl_plus_simps rev_bin_to_bl_simps append.simps
                                takefill_last_simps drop_nonempty_simps
                                rev_bl_order_simps}
          addsimprocs [expand_upt_simproc,
                       nat_get_Suc_simproc 4
                         [\<^term>\<open>replicate\<close>, \<^term>\<open>takefill x\<close>,
                          \<^term>\<open>drop\<close>, \<^term>\<open>bin_to_bl\<close>,
                          \<^term>\<open>takefill_last x\<close>,
                          \<^term>\<open>drop_nonempty x\<close>]],
    put_simpset no_split_ss \<^context> addsimps @{thms xor3_simps carry_simps if_bool_simps}
  ])

fun tac ctxt =
  let
    val (ss, sss) = expand_word_eq_sss;
  in
    foldr1 (op THEN_ALL_NEW)
      ((CHANGED o safe_full_simp_tac (put_simpset ss ctxt)) ::
        map (fn ss => safe_full_simp_tac (put_simpset ss ctxt)) sss)
  end;

end
\<close>

method_setup word_bitwise =
  \<open>Scan.succeed (fn ctxt => Method.SIMPLE_METHOD (Word_Bitwise_Tac.tac ctxt 1))\<close>
  "decomposer for word equalities and inequalities into bit propositions on concrete word lengths"

end
