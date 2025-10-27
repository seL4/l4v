(*
 * Copyright Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Author: Jeremy Dawson, NICTA *)

section \<open>Bit values as reversed lists of bools\<close>

theory Reversed_Bit_Lists
  imports
    "HOL-Library.Word"
    Typedef_Morphisms
    Least_significant_bit
    Most_significant_bit
    Rsplit
    Even_More_List
    "HOL-Library.Sublist"
    Aligned
    Singleton_Bit_Shifts
    Legacy_Aliases

begin

context
  includes bit_operations_syntax
begin

lemma horner_sum_of_bool_2_concat:
  \<open>horner_sum of_bool 2 (concat (map (\<lambda>x. map (bit x) [0..<LENGTH('a)]) ws)) = horner_sum uint (2 ^ LENGTH('a)) ws\<close>
  for ws :: \<open>'a::len word list\<close>
proof (induction ws)
  case Nil
  then show ?case
    by simp
next
  case (Cons w ws)
  moreover have \<open>horner_sum of_bool 2 (map (bit w) [0..<LENGTH('a)]) = uint w\<close>
  proof transfer
    fix k :: int
    have \<open>map (\<lambda>n. n < LENGTH('a) \<and> bit k n) [0..<LENGTH('a)]
      = map (bit k) [0..<LENGTH('a)]\<close>
      by simp
    then show \<open>horner_sum of_bool 2 (map (\<lambda>n. n < LENGTH('a) \<and> bit k n) [0..<LENGTH('a)])
      = take_bit LENGTH('a) k\<close>
      by (simp only: horner_sum_bit_eq_take_bit)
  qed
  ultimately show ?case
    by (simp add: horner_sum_append)
qed


subsection \<open>Implicit augmentation of list prefixes\<close>

primrec takefill :: "'a \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
    Z: "takefill fill 0 xs = []"
  | Suc: "takefill fill (Suc n) xs =
      (case xs of
        [] \<Rightarrow> fill # takefill fill n xs
      | y # ys \<Rightarrow> y # takefill fill n ys)"

lemma nth_takefill: "m < n \<Longrightarrow> takefill fill n l ! m = (if m < length l then l ! m else fill)"
  by (induct n arbitrary: m l) (auto simp: less_Suc_eq_0_disj split: list.split)

lemma takefill_alt: "takefill fill n l = take n l @ replicate (n - length l) fill"
  by (induct n arbitrary: l) (auto split: list.split)

lemma takefill_replicate [simp]: "takefill fill n (replicate m fill) = replicate n fill"
  by (simp add: takefill_alt replicate_add [symmetric])

lemma takefill_le': "n = m + k \<Longrightarrow> takefill x m (takefill x n l) = takefill x m l"
  by (induct m arbitrary: l n) (auto split: list.split)

lemma length_takefill [simp]: "length (takefill fill n l) = n"
  by (simp add: takefill_alt)

lemma take_takefill': "n = k + m \<Longrightarrow> take k (takefill fill n w) = takefill fill k w"
  by (induct k arbitrary: w n) (auto split: list.split)

lemma drop_takefill: "drop k (takefill fill (m + k) w) = takefill fill m (drop k w)"
  by (induct k arbitrary: w) (auto split: list.split)

lemma takefill_le [simp]: "m \<le> n \<Longrightarrow> takefill x m (takefill x n l) = takefill x m l"
  by (auto simp: le_iff_add takefill_le')

lemma take_takefill [simp]: "m \<le> n \<Longrightarrow> take m (takefill fill n w) = takefill fill m w"
  by (auto simp: le_iff_add take_takefill')

lemma takefill_append: "takefill fill (m + length xs) (xs @ w) = xs @ (takefill fill m w)"
  by (induct xs) auto

lemma takefill_same': "l = length xs \<Longrightarrow> takefill fill l xs = xs"
  by (induct xs arbitrary: l) auto

lemmas takefill_same [simp] = takefill_same' [OF refl]

lemma tf_rev:
  assumes "n + k = m + length bl"
  shows "takefill x m (rev (takefill y n bl)) =
         rev (takefill y m (rev (takefill x k (rev bl))))"
proof (rule nth_equalityI)
  fix i
  assume i: "i < length (takefill x m (rev (takefill y n bl)))"
  with assms
  have "length bl + m - Suc (k + i) = n - Suc i"
    by linarith
  with assms i
  show "takefill x m (rev (takefill y n bl)) ! i = rev (takefill y m (rev (takefill x k (rev bl)))) ! i"
    by (force simp: nth_takefill rev_nth)
qed auto

lemma takefill_minus: "0 < n \<Longrightarrow> takefill fill (Suc (n - 1)) w = takefill fill n w"
  by auto

lemmas takefill_Suc_cases =
  list.cases [THEN takefill.Suc [THEN trans]]

lemmas takefill_Suc_Nil = takefill_Suc_cases (1)
lemmas takefill_Suc_Cons = takefill_Suc_cases (2)

lemmas takefill_minus_simps = takefill_Suc_cases [THEN [2]
  takefill_minus [symmetric, THEN trans]]

lemma takefill_numeral_Nil [simp]:
  "takefill fill (numeral k) [] = fill # takefill fill (pred_numeral k) []"
  by (simp add: numeral_eq_Suc)

lemma takefill_numeral_Cons [simp]:
  "takefill fill (numeral k) (x # xs) = x # takefill fill (pred_numeral k) xs"
  by (simp add: numeral_eq_Suc)


subsection \<open>Range projection\<close>

definition bl_of_nth :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a list"
  where "bl_of_nth n f = map f (rev [0..<n])"

lemma bl_of_nth_simps [simp, code]:
  "bl_of_nth 0 f = []"
  "bl_of_nth (Suc n) f = f n # bl_of_nth n f"
  by (simp_all add: bl_of_nth_def)

lemma length_bl_of_nth [simp]: "length (bl_of_nth n f) = n"
  by (simp add: bl_of_nth_def)

lemma nth_bl_of_nth [simp]: "m < n \<Longrightarrow> rev (bl_of_nth n f) ! m = f m"
  by (simp add: bl_of_nth_def rev_map)

lemma bl_of_nth_inj: "(\<And>k. k < n \<Longrightarrow> f k = g k) \<Longrightarrow> bl_of_nth n f = bl_of_nth n g"
  by (simp add: bl_of_nth_def)

lemma bl_of_nth_nth_le: "n \<le> length xs \<Longrightarrow> bl_of_nth n (nth (rev xs)) = drop (length xs - n) xs"
proof (induct n arbitrary: xs)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case
    by (simp add: Suc_le_eq drop_minus)
qed

lemma bl_of_nth_nth [simp]: "bl_of_nth (length xs) ((!) (rev xs)) = xs"
  by (simp add: bl_of_nth_nth_le)


subsection \<open>More\<close>

definition rotater1 :: "'a list \<Rightarrow> 'a list"
  where "rotater1 ys =
    (case ys of [] \<Rightarrow> [] | x # xs \<Rightarrow> last ys # butlast ys)"

definition rotater :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "rotater n = rotater1 ^^ n"

lemmas rotater_0' [simp] = rotater_def [where n = "0", simplified]

lemma rotate1_rl': "rotater1 (l @ [a]) = a # l"
  by (cases l) (auto simp: rotater1_def)

lemma rotate1_rl [simp] : "rotater1 (rotate1 l) = l"
  by (metis list.simps(4) neq_Nil_conv rotate1.simps rotate1_rl' rotater1_def)

lemma rotate1_lr [simp] : "rotate1 (rotater1 l) = l"
  by (cases l) (auto simp: rotater1_def)

lemma rotater1_rev': "rotater1 (rev xs) = rev (rotate1 xs)"
  by (cases "xs") (simp add: rotater1_def, simp add: rotate1_rl')

lemma rotater_rev': "rotater n (rev xs) = rev (rotate n xs)"
  by (induct n) (auto simp: rotater_def intro: rotater1_rev')

lemma rotater_rev: "rotater n ys = rev (rotate n (rev ys))"
  using rotater_rev' [where xs = "rev ys"] by simp

lemma rotater_drop_take:
  "rotater n xs =
    drop (length xs - n mod length xs) xs @
    take (length xs - n mod length xs) xs"
  by (auto simp: rotater_rev rotate_drop_take rev_take rev_drop)

lemma rotater_Suc [simp]: "rotater (Suc n) xs = rotater1 (rotater n xs)"
  unfolding rotater_def by auto

lemma nth_rotater:
  \<open>rotater m xs ! n = xs ! ((n + (length xs - m mod length xs)) mod length xs)\<close> if \<open>n < length xs\<close>
  using that by (simp add: rotater_drop_take nth_append not_less less_diff_conv ac_simps le_mod_geq)

lemma nth_rotater1:
  \<open>rotater1 xs ! n = xs ! ((n + (length xs - 1)) mod length xs)\<close> if \<open>n < length xs\<close>
  using that nth_rotater [of n xs 1] by simp

lemma rotate_inv_plus [rule_format]:
  "\<forall>k. k = m + n \<longrightarrow> rotater k (rotate n xs) = rotater m xs \<and>
    rotate k (rotater n xs) = rotate m xs \<and>
    rotater n (rotate k xs) = rotate m xs \<and>
    rotate n (rotater k xs) = rotater m xs"
  by (induct n) (auto simp: rotater_def rotate_def intro: funpow_swap1 [THEN trans])

lemmas rotate_inv_rel = le_add_diff_inverse2 [symmetric, THEN rotate_inv_plus]

lemmas rotate_inv_eq = order_refl [THEN rotate_inv_rel, simplified]

lemmas rotate_lr [simp] = rotate_inv_eq [THEN conjunct1]
lemmas rotate_rl [simp] = rotate_inv_eq [THEN conjunct2, THEN conjunct1]

lemma rotate_gal: "rotater n xs = ys \<longleftrightarrow> rotate n ys = xs"
  by auto

lemma rotate_gal': "ys = rotater n xs \<longleftrightarrow> xs = rotate n ys"
  by auto

lemma length_rotater [simp]: "length (rotater n xs) = length xs"
  by (simp add : rotater_rev)

lemma rotate_eq_mod: "m mod length xs = n mod length xs \<Longrightarrow> rotate m xs = rotate n xs"
  by (metis rotate_conv_mod)

lemma restrict_to_left: "x = y \<Longrightarrow> x = z \<longleftrightarrow> y = z"
  by simp

lemmas rotate_eqs =
  trans [OF rotate0 [THEN fun_cong] id_apply]
  rotate_rotate [symmetric]
  rotate_id
  rotate_conv_mod
  rotate_eq_mod

lemmas rrs0 = rotate_eqs [THEN restrict_to_left,
  simplified rotate_gal [symmetric] rotate_gal' [symmetric]]
lemmas rrs1 = rrs0 [THEN refl [THEN rev_iffD1]]
lemmas rotater_eqs = rrs1 [simplified length_rotater]
lemmas rotater_0 = rotater_eqs (1)
lemmas rotater_add = rotater_eqs (2)

lemma butlast_map: "xs \<noteq> [] \<Longrightarrow> butlast (map f xs) = map f (butlast xs)"
  by (induct xs) auto

lemma rotater1_map: "rotater1 (map f xs) = map f (rotater1 xs)"
  by (cases xs) (auto simp: rotater1_def last_map butlast_map)

lemma rotater_map: "rotater n (map f xs) = map f (rotater n xs)"
  by (induct n) (auto simp: rotater_def rotater1_map)

lemma but_last_zip:
  "\<lbrakk>length xs = length ys; xs \<noteq> [] \<rbrakk> \<Longrightarrow>
    last (zip xs ys) = (last xs, last ys) \<and>
    butlast (zip xs ys) = zip (butlast xs) (butlast ys)"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by auto
next
  case Cons
  then show ?case
    by (cases ys) auto
qed

lemma but_last_map2:
  "\<lbrakk>length xs = length ys; xs \<noteq> [] \<rbrakk> \<Longrightarrow>
    last (map2 f xs ys) = f (last xs) (last ys) \<and>
    butlast (map2 f xs ys) = map2 f (butlast xs) (butlast ys)"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by auto
next
  case Cons
  then show ?case
    by (cases ys) auto
qed

lemma rotater1_zip:
  "length xs = length ys \<Longrightarrow>
    rotater1 (zip xs ys) = zip (rotater1 xs) (rotater1 ys)"
  by (metis map_fst_zip map_snd_zip rotater1_map zip_map_fst_snd)

lemma rotater1_map2:
  "length xs = length ys \<Longrightarrow>
    rotater1 (map2 f xs ys) = map2 f (rotater1 xs) (rotater1 ys)"
  by (simp add: rotater1_map rotater1_zip)

lemmas lrth =
  box_equals [OF asm_rl length_rotater [symmetric]
                 length_rotater [symmetric],
              THEN rotater1_map2]

lemma rotater_map2:
  "length xs = length ys \<Longrightarrow>
    rotater n (map2 f xs ys) = map2 f (rotater n xs) (rotater n ys)"
  by (induct n) (auto intro!: lrth)

lemma rotate1_map2:
  "length xs = length ys \<Longrightarrow>
    rotate1 (map2 f xs ys) = map2 f (rotate1 xs) (rotate1 ys)"
  by (cases xs; cases ys) auto

lemmas lth = box_equals [OF asm_rl length_rotate [symmetric]
  length_rotate [symmetric], THEN rotate1_map2]

lemma rotate_map2:
  "length xs = length ys \<Longrightarrow>
    rotate n (map2 f xs ys) = map2 f (rotate n xs) (rotate n ys)"
  by (induct n) (auto intro!: lth)


subsection \<open>Explicit bit representation of \<^typ>\<open>int\<close>\<close>

primrec bl_to_bin_aux :: "bool list \<Rightarrow> int \<Rightarrow> int"
  where
    Nil: "bl_to_bin_aux [] w = w"
  | Cons: "bl_to_bin_aux (b # bs) w = bl_to_bin_aux bs (of_bool b + 2 * w)"

lemma bin_nth_of_bl_aux:
  "bit (bl_to_bin_aux bl w) n =
    (n < size bl \<and> rev bl ! n \<or> n \<ge> length bl \<and> bit w (n - size bl))"
  by (induction bl arbitrary: w) (auto simp: not_le nth_append bit_double_iff even_bit_succ_iff split: if_splits)

lemma bl_to_bin_aux_eq:
  \<open>bl_to_bin_aux bs k = horner_sum of_bool 2 (rev bs) OR push_bit (length bs) k\<close>
  by (rule bit_eqI) (simp add: bit_simps bin_nth_of_bl_aux)

definition bl_to_bin :: "bool list \<Rightarrow> int"
  where "bl_to_bin bs = bl_to_bin_aux bs 0"

lemma bin_nth_of_bl:
  "bit (bl_to_bin bl) n = (n < length bl \<and> rev bl ! n)"
  by (simp add: bl_to_bin_def bin_nth_of_bl_aux)

lemma bl_to_bin_eq:
  \<open>bl_to_bin bs = horner_sum of_bool 2 (rev bs)\<close>
  by (simp add: bl_to_bin_def bl_to_bin_aux_eq)

primrec bin_to_bl_aux :: "nat \<Rightarrow> int \<Rightarrow> bool list \<Rightarrow> bool list"
  where
    Z: "bin_to_bl_aux 0 w bl = bl"
  | Suc: "bin_to_bl_aux (Suc n) w bl = bin_to_bl_aux n (w div 2) (odd w # bl)"

definition bin_to_bl :: "nat \<Rightarrow> int \<Rightarrow> bool list"
  where "bin_to_bl n w = bin_to_bl_aux n w []"

lemma bin_to_bl_aux_zero_minus_simp [simp]:
  "0 < n \<Longrightarrow> bin_to_bl_aux n 0 bl = bin_to_bl_aux (n - 1) 0 (False # bl)"
  by (cases n) auto

lemma bin_to_bl_aux_minus1_minus_simp [simp]:
  "0 < n \<Longrightarrow> bin_to_bl_aux n (- 1) bl = bin_to_bl_aux (n - 1) (- 1) (True # bl)"
  by (cases n) auto

lemma bin_to_bl_aux_one_minus_simp [simp]:
  "0 < n \<Longrightarrow> bin_to_bl_aux n 1 bl = bin_to_bl_aux (n - 1) 0 (True # bl)"
  by (cases n) auto

lemma bin_to_bl_aux_Bit0_minus_simp [simp]:
  "0 < n \<Longrightarrow>
    bin_to_bl_aux n (numeral (Num.Bit0 w)) bl = bin_to_bl_aux (n - 1) (numeral w) (False # bl)"
  by (cases n) simp_all

lemma bin_to_bl_aux_Bit1_minus_simp [simp]:
  "0 < n \<Longrightarrow>
    bin_to_bl_aux n (numeral (Num.Bit1 w)) bl = bin_to_bl_aux (n - 1) (numeral w) (True # bl)"
  by (cases n) simp_all

lemma bl_to_bin_aux_append: "bl_to_bin_aux (bs @ cs) w = bl_to_bin_aux cs (bl_to_bin_aux bs w)"
  by (induct bs arbitrary: w) auto

lemma bin_to_bl_aux_append: "bin_to_bl_aux n w bs @ cs = bin_to_bl_aux n w (bs @ cs)"
  by (induct n arbitrary: w bs) auto

lemma bl_to_bin_append: "bl_to_bin (bs @ cs) = bl_to_bin_aux cs (bl_to_bin bs)"
  unfolding bl_to_bin_def by (rule bl_to_bin_aux_append)

lemma bin_to_bl_aux_alt: "bin_to_bl_aux n w bs = bin_to_bl n w @ bs"
  by (simp add: bin_to_bl_def bin_to_bl_aux_append)

lemma bin_to_bl_0 [simp]: "bin_to_bl 0 bs = []"
  by (auto simp: bin_to_bl_def)

lemma size_bin_to_bl_aux: "length (bin_to_bl_aux n w bs) = n + length bs"
  by (induct n arbitrary: w bs) auto

lemma size_bin_to_bl [simp]: "length (bin_to_bl n w) = n"
  by (simp add: bin_to_bl_def size_bin_to_bl_aux)

lemma bl_bin_bl': "bin_to_bl (n + length bs) (bl_to_bin_aux bs w) = bin_to_bl_aux n w bs"
  by (induct bs arbitrary: w n) (auto simp: bin_to_bl_def simp flip: add_Suc)

lemma bl_bin_bl [simp]: "bin_to_bl (length bs) (bl_to_bin bs) = bs"
  unfolding bl_to_bin_def
  by (metis add_0 bin_to_bl_aux.Z bl_bin_bl')

lemma bl_to_bin_inj: "bl_to_bin bs = bl_to_bin cs \<Longrightarrow> length bs = length cs \<Longrightarrow> bs = cs"
  by (metis bl_bin_bl)

lemma bl_to_bin_False [simp]:
  \<open>bl_to_bin (False # bl) = bl_to_bin bl\<close>
  by (auto simp: bl_to_bin_def)

lemma bl_to_bin_Nil [simp]: "bl_to_bin [] = 0"
  by (auto simp: bl_to_bin_def)

lemma bin_to_bl_zero_aux: "bin_to_bl_aux n 0 bl = replicate n False @ bl"
  by (induct n arbitrary: bl) (auto simp: replicate_app_Cons_same)

lemma bin_to_bl_zero: "bin_to_bl n 0 = replicate n False"
  by (simp add: bin_to_bl_def bin_to_bl_zero_aux)

lemma bin_to_bl_minus1_aux: "bin_to_bl_aux n (- 1) bl = replicate n True @ bl"
  by (induct n arbitrary: bl) (auto simp: replicate_app_Cons_same)

lemma bin_to_bl_minus1: "bin_to_bl n (- 1) = replicate n True"
  by (simp add: bin_to_bl_def bin_to_bl_minus1_aux)


subsection \<open>Semantic interpretation of \<^typ>\<open>bool list\<close> as \<^typ>\<open>int\<close>\<close>

lemma bin_bl_bin': "bl_to_bin (bin_to_bl_aux n w bs) = bl_to_bin_aux bs (take_bit n w)"
  by (induct n arbitrary: w bs) (auto simp: bl_to_bin_def take_bit_Suc ac_simps mod_2_eq_odd)

lemma bin_bl_bin [simp]: "bl_to_bin (bin_to_bl n w) = take_bit n w"
  by (auto simp: bin_to_bl_def bin_bl_bin')

lemma bl_to_bin_rep_F: "bl_to_bin (replicate n False @ bl) = bl_to_bin bl"
  by (simp add: bin_to_bl_zero_aux [symmetric] bin_bl_bin') (simp add: bl_to_bin_def)

lemma bin_to_bl_trunc [simp]: "n \<le> m \<Longrightarrow> bin_to_bl n (take_bit m w) = bin_to_bl n w"
  by (auto intro: bl_to_bin_inj)

lemma bin_to_bl_aux_bintr:
  "bin_to_bl_aux n (take_bit m bin) bl =
    replicate (n - m) False @ bin_to_bl_aux (min n m) bin bl"
proof (induct n arbitrary: m bin bl)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case
    by (cases m)
       (auto simp: replicate_append_same bin_to_bl_zero_aux simp flip: bin_rest_trunc_i)
qed

lemma bin_to_bl_bintr:
  "bin_to_bl n (take_bit m bin) = replicate (n - m) False @ bin_to_bl (min n m) bin"
  unfolding bin_to_bl_def by (rule bin_to_bl_aux_bintr)

lemma bl_to_bin_rep_False: "bl_to_bin (replicate n False) = 0"
  by (induct n) auto

lemma bin_nth_bl: "n < m \<Longrightarrow> bit w n = nth (rev (bin_to_bl m w)) n"
  by (metis bin_bl_bin bin_nth_of_bl nth_bintr size_bin_to_bl)

lemma nth_bin_to_bl_aux:
  "n < m + length bl \<Longrightarrow> (bin_to_bl_aux m w bl) ! n =
    (if n < m then bit w (m - 1 - n) else bl ! (n - m))"
proof (induction bl)
  case Nil
  then show ?case
    by (simp add: bin_nth_bl [of \<open>m - Suc n\<close> m] rev_nth flip: bin_to_bl_def)
next
  case (Cons a bl)
  then show ?case
    apply (simp add: less_Suc_eq)
    by (metis add.right_neutral bin_to_bl_aux_alt bin_to_bl_def diff_Suc_eq_diff_pred list.size(3) not_add_less1 nth_append size_bin_to_bl_aux)
qed

lemma nth_bin_to_bl: "n < m \<Longrightarrow> (bin_to_bl m w) ! n = bit w (m - Suc n)"
  by (simp add: bin_to_bl_def nth_bin_to_bl_aux)

lemma takefill_bintrunc: "takefill False n bl = rev (bin_to_bl n (bl_to_bin (rev bl)))"
proof (rule nth_equalityI)
  fix i
  assume "i < length (takefill False n bl)"
  then show "takefill False n bl ! i = rev (bin_to_bl n (bl_to_bin (rev bl))) ! i"
    by (auto simp: nth_takefill rev_nth nth_bin_to_bl bin_nth_of_bl)
qed auto

lemma bl_bin_bl_rtf: "bin_to_bl n (bl_to_bin bl) = rev (takefill False n (rev bl))"
  by (simp add: takefill_bintrunc)

lemma bl_to_bin_lt2p_aux: "bl_to_bin_aux bs w < (w + 1) * (2 ^ length bs)"
proof (induction bs arbitrary: w)
  case Nil
  then show ?case
    by simp
next
  case (Cons b bs)
  from Cons.IH [of \<open>1 + 2 * w\<close>] Cons.IH [of \<open>2 * w\<close>]
  show ?case
    apply (simp add: algebra_simps)
    by (smt (verit, best) zero_le_power)
qed

lemma bl_to_bin_lt2p_drop: "bl_to_bin bs < 2 ^ length (dropWhile Not bs)"
proof (induct bs)
  case Nil
  then show ?case by simp
next
  case (Cons b bs)
  with bl_to_bin_lt2p_aux[where w=1] show ?case
    by (simp add: bl_to_bin_def)
qed

lemma bl_to_bin_lt2p: "bl_to_bin bs < 2 ^ length bs"
  by (metis bin_bl_bin bintr_lt2p bl_bin_bl)

lemma bl_to_bin_ge2p_aux: "bl_to_bin_aux bs w \<ge> w * (2 ^ length bs)"
proof (induction bs arbitrary: w)
  case Nil
  then show ?case
    by simp
next
  case (Cons b bs)
  from Cons.IH [of \<open>1 + 2 * w\<close>] Cons.IH [of \<open>2 * w\<close>]
  show ?case
    using dual_order.trans by fastforce
qed

lemma bl_to_bin_ge0: "bl_to_bin bs \<ge> 0"
  by (metis bl_to_bin_def bl_to_bin_ge2p_aux mult_zero_left)

lemma butlast_rest_bin: "butlast (bin_to_bl n w) = bin_to_bl (n - 1) (w div 2)"
proof (cases n)
  case 0
  then show ?thesis by auto
next
  case (Suc nat)
  then show ?thesis
    using bin_to_bl_aux.simps(2) bin_to_bl_aux_alt by auto
qed

lemma butlast_bin_rest: "butlast bl = bin_to_bl (length bl - Suc 0) (bl_to_bin bl div 2)"
  using butlast_rest_bin [where w="bl_to_bin bl" and n="length bl"] by simp

lemma butlast_rest_bl2bin_aux:
  "bl \<noteq> [] \<Longrightarrow> bl_to_bin_aux (butlast bl) w = bl_to_bin_aux bl w div 2"
  by (induct bl arbitrary: w) auto

lemma butlast_rest_bl2bin: "bl_to_bin (butlast bl) = bl_to_bin bl div 2"
  by (cases bl) (auto simp: bl_to_bin_def butlast_rest_bl2bin_aux)

lemma trunc_bl2bin_aux:
  "take_bit m (bl_to_bin_aux bl w) =
    bl_to_bin_aux (drop (length bl - m) bl) (take_bit (m - length bl) w)"
proof (induct bl arbitrary: w)
  case Nil
  show ?case by simp
next
  case (Cons b bl)
  show ?case
  proof (cases "m - length bl")
    case 0
    then have "Suc (length bl) - m = Suc (length bl - m)" by simp
    with Cons show ?thesis by simp
  next
    case (Suc n)
    then have "m - Suc (length bl) = n" by simp
    with Cons Suc show ?thesis by (simp add: take_bit_Suc ac_simps)
  qed
qed

lemma trunc_bl2bin: "take_bit m (bl_to_bin bl) = bl_to_bin (drop (length bl - m) bl)"
  by (simp add: bl_to_bin_def trunc_bl2bin_aux)

lemma trunc_bl2bin_len [simp]: "take_bit (length bl) (bl_to_bin bl) = bl_to_bin bl"
  by (simp add: trunc_bl2bin)

lemma bl2bin_drop: "bl_to_bin (drop k bl) = take_bit (length bl - k) (bl_to_bin bl)"
  by (metis length_rev rev_drop rev_rev_ident rev_take trunc_bl2bin)

lemma take_rest_power_bin: "m \<le> n \<Longrightarrow> take m (bin_to_bl n w) = bin_to_bl m (((\<lambda>w. w div 2) ^^ (n - m)) w)"
  by (intro nth_equalityI) (auto simp add: nth_bin_to_bl nth_rest_power_bin)

lemma last_bin_last': "size xs > 0 \<Longrightarrow> last xs \<longleftrightarrow> odd (bl_to_bin_aux xs w)"
  by (induct xs arbitrary: w) auto

lemma last_bin_last: "size xs > 0 \<Longrightarrow> last xs \<longleftrightarrow> odd (bl_to_bin xs)"
  unfolding bl_to_bin_def by (erule last_bin_last')

lemma bin_last_last: "odd w \<longleftrightarrow> last (bin_to_bl (Suc n) w)"
  by (simp add: bin_to_bl_def) (auto simp: bin_to_bl_aux_alt)

lemma drop_bin2bl_aux:
  "drop m (bin_to_bl_aux n bin bs) =
    bin_to_bl_aux (n - m) bin (drop (m - n) bs)"
proof (induction n arbitrary: m bin bs)
  case 0
  then show ?case
    by auto
next
  case (Suc n)
  show ?case
  proof (cases  "m \<le> n")
    case True
    then show ?thesis
      by (simp add: Suc_diff_le local.Suc)
  next
    case False
    with Suc  show ?thesis
      by (simp add: not_le split: nat_diff_split)
  qed
qed

lemma drop_bin2bl: "drop m (bin_to_bl n bin) = bin_to_bl (n - m) bin"
  by (simp add: bin_to_bl_def drop_bin2bl_aux)

lemma take_bin2bl_lem1: "take m (bin_to_bl_aux m w bs) = bin_to_bl m w"
  by (induct m arbitrary: w bs) (auto simp add: bin_to_bl_aux_alt)

lemma take_bin2bl_lem: "take m (bin_to_bl_aux (m + n) w bs) = take m (bin_to_bl (m + n) w)"
  by (induct n arbitrary: w bs) (simp_all (no_asm) add: bin_to_bl_def take_bin2bl_lem1, simp)

lemma bin_split_take: "bin_split n c = (a, b) \<Longrightarrow> bin_to_bl m a = take m (bin_to_bl (m + n) c)"
proof (induct n arbitrary: b c)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then have "bin_to_bl m (drop_bit (Suc n) c) = take m (bin_to_bl (Suc (m + n)) c)"
    by (simp add: bin_to_bl_def drop_bit_Suc) (metis take_bin2bl_lem)
  with Suc
   show ?case
     by (auto simp: Let_def split: prod.split_asm)
qed

lemma bin_to_bl_drop_bit:
  "k = m + n \<Longrightarrow> bin_to_bl m (drop_bit n c) = take m (bin_to_bl k c)"
  using bin_split_take by simp

lemma bin_split_take1:
  "k = m + n \<Longrightarrow> bin_split n c = (a, b) \<Longrightarrow> bin_to_bl m a = take m (bin_to_bl k c)"
  using bin_split_take by simp

lemma bl_bin_bl_rep_drop:
  "bin_to_bl n (bl_to_bin bl) =
    replicate (n - length bl) False @ drop (length bl - n) bl"
  by (simp add: bl_to_bin_inj bl_to_bin_rep_F trunc_bl2bin)

lemma bl_to_bin_aux_cat:
  "bl_to_bin_aux bs (concat_bit nv v w) =
    concat_bit (nv + length bs) (bl_to_bin_aux bs v) w"
  by (rule bit_eqI) (auto simp: bin_nth_of_bl_aux bin_nth_cat algebra_simps)

lemma bin_to_bl_aux_cat:
  "bin_to_bl_aux (nv + nw) (concat_bit nw w v) bs =
    bin_to_bl_aux nv v (bin_to_bl_aux nw w bs)"
  by (induction nw arbitrary: w bs) (simp_all add: concat_bit_Suc)

lemma bl_to_bin_aux_alt: "bl_to_bin_aux bs w = concat_bit (length bs) (bl_to_bin bs) w"
  using bl_to_bin_aux_cat [where nv = "0" and v = "0"]
  by (simp add: bl_to_bin_def [symmetric])

lemma bin_to_bl_cat:
  "bin_to_bl (nv + nw) (concat_bit nw w v) =
    bin_to_bl_aux nv v (bin_to_bl nw w)"
  by (simp add: bin_to_bl_def bin_to_bl_aux_cat)

lemmas bl_to_bin_aux_app_cat =
  trans [OF bl_to_bin_aux_append bl_to_bin_aux_alt]

lemmas bin_to_bl_aux_cat_app =
  trans [OF bin_to_bl_aux_cat bin_to_bl_aux_alt]

lemma bl_to_bin_app_cat:
  "bl_to_bin (bsa @ bs) = concat_bit (length bs) (bl_to_bin bs) (bl_to_bin bsa)"
  by (simp only: bl_to_bin_aux_app_cat bl_to_bin_def)

lemma bin_to_bl_cat_app:
  "bin_to_bl (n + nw) (concat_bit nw wa w) = bin_to_bl n w @ bin_to_bl nw wa"
  by (simp only: bin_to_bl_def bin_to_bl_aux_cat_app)

text \<open>\<open>bl_to_bin_app_cat_alt\<close> and \<open>bl_to_bin_app_cat\<close> are easily interderivable.\<close>
lemma bl_to_bin_app_cat_alt: "concat_bit n w (bl_to_bin cs) = bl_to_bin (cs @ bin_to_bl n w)"
  by (simp add: bl_to_bin_app_cat)

lemma mask_lem: "(bl_to_bin (True # replicate n False)) = bl_to_bin (replicate n True) + 1"
  unfolding bl_to_bin_def
proof (induct n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case
    unfolding Suc_eq_plus1 replicate_add append_Cons [symmetric] bl_to_bin_aux_append
    by auto
qed

lemma bin_exhaust:
  "(\<And>x b. bin = of_bool b + 2 * x \<Longrightarrow> Q) \<Longrightarrow> Q" for bin :: int
  by (metis add.commute add_0 dvd_def oddE of_bool_def)

primrec rbl_succ :: "bool list \<Rightarrow> bool list"
  where
    Nil: "rbl_succ Nil = Nil"
  | Cons: "rbl_succ (x # xs) = (if x then False # rbl_succ xs else True # xs)"

primrec rbl_pred :: "bool list \<Rightarrow> bool list"
  where
    Nil: "rbl_pred Nil = Nil"
  | Cons: "rbl_pred (x # xs) = (if x then False # xs else True # rbl_pred xs)"

primrec rbl_add :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list"
  where \<comment> \<open>result is length of first arg, second arg may be longer\<close>
    Nil: "rbl_add Nil x = Nil"
  | Cons: "rbl_add (y # ys) x =
      (let ws = rbl_add ys (tl x)
       in (y \<noteq> hd x) # (if hd x \<and> y then rbl_succ ws else ws))"

primrec rbl_mult :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list"
  where \<comment> \<open>result is length of first arg, second arg may be longer\<close>
    Nil: "rbl_mult Nil x = Nil"
  | Cons: "rbl_mult (y # ys) x =
      (let ws = False # rbl_mult ys x
       in if y then rbl_add ws x else ws)"

lemma size_rbl_pred: "length (rbl_pred bl) = length bl"
  by (induct bl) auto

lemma size_rbl_succ: "length (rbl_succ bl) = length bl"
  by (induct bl) auto

lemma size_rbl_add: "length (rbl_add bl cl) = length bl"
  by (induct bl arbitrary: cl) (auto simp: Let_def size_rbl_succ)

lemma size_rbl_mult: "length (rbl_mult bl cl) = length bl"
  by (induct bl arbitrary: cl) (auto simp: Let_def size_rbl_add)

lemmas rbl_sizes [simp] =
  size_rbl_pred size_rbl_succ size_rbl_add size_rbl_mult

lemmas rbl_Nils =
  rbl_pred.Nil rbl_succ.Nil rbl_add.Nil rbl_mult.Nil

lemma rbl_add_app2: "length blb \<ge> length bla \<Longrightarrow> rbl_add bla (blb @ blc) = rbl_add bla blb"
  by (induct bla arbitrary: blb) (auto simp: Suc_le_length_iff)

lemma rbl_add_take2:
  "length blb \<ge> length bla \<Longrightarrow> rbl_add bla (take (length bla) blb) = rbl_add bla blb"
  by (induct bla arbitrary: blb) (auto simp: Suc_le_length_iff)

lemma rbl_mult_app2: "length blb \<ge> length bla \<Longrightarrow> rbl_mult bla (blb @ blc) = rbl_mult bla blb"
proof (induct bla arbitrary: blb)
  case Nil
  then show ?case by auto
next
  case C: (Cons a bla)
  show ?case
  proof (cases "blb")
    case Nil
    with C.prems show ?thesis
      by (simp add: Let_def)
  next
    case (Cons b list)
    with C show ?thesis
      apply (simp add: Let_def rbl_add_app2)
      by (metis append_eq_Cons_conv le_Suc_eq length_Cons)
  qed
qed

lemma rbl_mult_take2:
  "length blb \<ge> length bla \<Longrightarrow> rbl_mult bla (take (length bla) blb) = rbl_mult bla blb"
  by (metis append_take_drop_id dual_order.refl length_take min_def rbl_mult_app2)

lemma rbl_add_split:
  "P (rbl_add (y # ys) (x # xs)) =
    (\<forall>ws. length ws = length ys \<longrightarrow> ws = rbl_add ys xs \<longrightarrow>
      (y \<longrightarrow> ((x \<longrightarrow> P (False # rbl_succ ws)) \<and> (\<not> x \<longrightarrow> P (True # ws)))) \<and>
      (\<not> y \<longrightarrow> P (x # ws)))"
  by (cases y) (auto simp: Let_def)

lemma rbl_mult_split:
  "P (rbl_mult (y # ys) xs) =
    (\<forall>ws. length ws = Suc (length ys) \<longrightarrow> ws = False # rbl_mult ys xs \<longrightarrow>
      (y \<longrightarrow> P (rbl_add ws xs)) \<and> (\<not> y \<longrightarrow> P ws))"
  by (auto simp: Let_def)

lemma rbl_pred: "rbl_pred (rev (bin_to_bl n bin)) = rev (bin_to_bl n (bin - 1))"
proof (unfold bin_to_bl_def, induction n arbitrary: bin)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  obtain b k where \<open>bin = of_bool b + 2 * k\<close>
    using bin_exhaust by blast
  moreover have \<open>(2 * k - 1) div 2 = k - 1\<close>
    by simp
  ultimately show ?case
    using Suc [of \<open>bin div 2\<close>]
    by simp (auto simp: bin_to_bl_aux_alt)
qed

lemma rbl_succ: "rbl_succ (rev (bin_to_bl n bin)) = rev (bin_to_bl n (bin + 1))"
  unfolding bin_to_bl_def
proof (induction n arbitrary: bin)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case
    apply (case_tac bin rule: bin_exhaust, simp)
    apply (simp add: bin_to_bl_aux_alt ac_simps)
    done
qed

lemma rbl_add:
  "rbl_add (rev (bin_to_bl n bina)) (rev (bin_to_bl n binb)) =
    rev (bin_to_bl n (bina + binb))"
  unfolding bin_to_bl_def
proof (induct n arbitrary: bina binb)
  case 0
  then show ?case by auto
next
  case (Suc n bina binb)
  obtain a x b y where "bina = of_bool a + 2 * x" "binb = of_bool b + 2 * y"
    by (meson bin_exhaust)
  with Suc show ?case
    apply simp
    by (auto simp: bin_to_bl_aux_alt rbl_succ ac_simps)
qed

lemma rbl_add_long:
  "m \<ge> n \<Longrightarrow> rbl_add (rev (bin_to_bl n bina)) (rev (bin_to_bl m binb)) =
    rev (bin_to_bl n (bina + binb))"
  using arg_cong [where f = "rbl_add (rev (bin_to_bl n bina))"]
  by (metis diff_diff_cancel drop_bin2bl length_rev rbl_add rbl_add_take2 rev_rev_ident rev_take size_bin_to_bl)

lemma rbl_mult_gt1:
  "m \<ge> length bl \<Longrightarrow>
    rbl_mult bl (rev (bin_to_bl m binb)) =
    rbl_mult bl (rev (bin_to_bl (length bl) binb))"
  by (metis diff_diff_cancel drop_bin2bl length_rev rbl_mult_take2 rev_drop size_bin_to_bl)

lemma rbl_mult_gt:
  "m > n \<Longrightarrow>
    rbl_mult (rev (bin_to_bl n bina)) (rev (bin_to_bl m binb)) =
    rbl_mult (rev (bin_to_bl n bina)) (rev (bin_to_bl n binb))"
  by (auto intro: trans [OF rbl_mult_gt1])

lemmas rbl_mult_Suc = lessI [THEN rbl_mult_gt]

lemma rbbl_Cons: "b # rev (bin_to_bl n x) = rev (bin_to_bl (Suc n) (of_bool b + 2 * x))"
  by (simp add: bin_to_bl_def) (simp add: bin_to_bl_aux_alt)

lemma rbl_mult:
  "rbl_mult (rev (bin_to_bl n bina)) (rev (bin_to_bl n binb)) =
    rev (bin_to_bl n (bina * binb))"
proof (induct n arbitrary: bina binb)
  case 0
  then show ?case by auto
next
  case (Suc n)
  obtain a x b y where "bina = of_bool a + 2 * x" "binb = of_bool b + 2 * y"
    by (meson bin_exhaust)
  with Suc show ?case
    unfolding bin_to_bl_def
    apply simp
    apply (simp_all add: bin_to_bl_aux_alt)
    apply (simp_all add: rbbl_Cons rbl_mult_Suc rbl_add algebra_simps)
    done
qed

lemma sclem: "size (concat (map (bin_to_bl n) xs)) = length xs * n"
  by (simp add: length_concat comp_def sum_list_triv)

lemma bin_cat_foldl_lem:
  "foldl (\<lambda>u k. concat_bit n k u) x xs =
    concat_bit (size xs * n) (foldl (\<lambda>u k. concat_bit n k u) y xs) x"
proof (induct xs arbitrary: x)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case
    by (metis (no_types, lifting) add_0 concat_bit_assoc drop_bit_bin_cat_eq foldl_Cons length_Cons mult_Suc)
qed

lemma bin_last_bl_to_bin: "odd (bl_to_bin bs) \<longleftrightarrow> bs \<noteq> [] \<and> last bs"
  by (metis bin_nth_of_bl bit_0 last_bin_last length_greater_0_conv)

lemma bin_rest_bl_to_bin: "bl_to_bin bs div 2 = bl_to_bin (butlast bs)"
  using butlast_rest_bl2bin by presburger

lemma bl_xor_aux_bin:
  "map2 (\<lambda>x y. x \<noteq> y) (bin_to_bl_aux n v bs) (bin_to_bl_aux n w cs) =
    bin_to_bl_aux n (v XOR w) (map2 (\<lambda>x y. x \<noteq> y) bs cs)"
proof (induction n arbitrary: v w bs cs)
  case 0
  then show ?case by auto
next
  case (Suc n)
  obtain a x b y where "v = of_bool a + 2 * x" "w = of_bool b + 2 * y"
    by (meson bin_exhaust)
  with Suc show ?case
    by (cases a; simp add: bin_to_bl_def)
qed

lemma bl_or_aux_bin:
  "map2 (\<or>) (bin_to_bl_aux n v bs) (bin_to_bl_aux n w cs) =
    bin_to_bl_aux n (v OR w) (map2 (\<or>) bs cs)"
  by (induct n arbitrary: v w bs cs) simp_all

lemma bl_and_aux_bin:
  "map2 (\<and>) (bin_to_bl_aux n v bs) (bin_to_bl_aux n w cs) =
    bin_to_bl_aux n (v AND w) (map2 (\<and>) bs cs)"
  by (induction n arbitrary: v w bs cs) simp_all

lemma bl_not_aux_bin: "map Not (bin_to_bl_aux n w cs) = bin_to_bl_aux n (NOT w) (map Not cs)"
  by (induct n arbitrary: w cs) auto

lemma bl_not_bin: "map Not (bin_to_bl n w) = bin_to_bl n (NOT w)"
  by (simp add: bin_to_bl_def bl_not_aux_bin)

lemma bl_and_bin: "map2 (\<and>) (bin_to_bl n v) (bin_to_bl n w) = bin_to_bl n (v AND w)"
  by (simp add: bin_to_bl_def bl_and_aux_bin)

lemma bl_or_bin: "map2 (\<or>) (bin_to_bl n v) (bin_to_bl n w) = bin_to_bl n (v OR w)"
  by (simp add: bin_to_bl_def bl_or_aux_bin)

lemma bl_xor_bin: "map2 (\<noteq>) (bin_to_bl n v) (bin_to_bl n w) = bin_to_bl n (v XOR w)"
  using bl_xor_aux_bin by (simp add: bin_to_bl_def)

definition bin_rcat :: \<open>nat \<Rightarrow> int list \<Rightarrow> int\<close>
  where \<open>bin_rcat n = horner_sum (take_bit n) (2 ^ n) \<circ> rev\<close>

lemma bin_rcat_eq_foldl:
  \<open>bin_rcat n = foldl (\<lambda>u v. (\<lambda>k n l. concat_bit n l k) u n v) 0\<close>
proof
  fix ks :: \<open>int list\<close>
  show \<open>bin_rcat n ks = foldl (\<lambda>u v. (\<lambda>k n l. concat_bit n l k) u n v) 0 ks\<close>
    by (induction ks rule: rev_induct)
      (simp_all add: bin_rcat_def concat_bit_eq push_bit_eq_mult)
qed

lemma bin_rcat_bl:
  \<open>bin_rcat n wl = bl_to_bin (concat (map (bin_to_bl n) wl))\<close>
  unfolding bin_rcat_eq_foldl
proof (induct wl)
  case Nil
  then show ?case by auto
next
  case (Cons a wl)
  then show ?case
    apply simp
    by (metis bin_bl_bin bin_cat_foldl_lem bl_to_bin_app_cat sclem)
qed

lemma bin_rsplit_rcat:
  "n > 0 \<Longrightarrow> bin_rsplit n (n * size ws, bin_rcat n ws) = map ((take_bit :: nat \<Rightarrow> int \<Rightarrow> int) n) ws"
  unfolding bin_rsplit_def bin_rcat_eq_foldl
proof (induction ws rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  then show ?case
    by simp (metis drop_bit_bin_cat_eq rsplit_aux_alts(1))
qed

lemma word_rcat_eq:
  \<open>word_rcat ws = word_of_int (bin_rcat (LENGTH('a::len)) (map uint ws))\<close>
  for ws :: \<open>'a::len word list\<close>
  apply (simp add: word_rcat_def bin_rcat_def rev_map)
  apply transfer
  apply (simp add: horner_sum_foldr foldr_map comp_def)
  done


subsection \<open>Type \<^typ>\<open>'a word\<close>\<close>

lift_definition of_bl :: \<open>bool list \<Rightarrow> 'a::len word\<close>
  is bl_to_bin .

lift_definition to_bl :: \<open>'a::len word \<Rightarrow> bool list\<close>
  is \<open>bin_to_bl LENGTH('a)\<close>
  by (simp add: bl_to_bin_inj)

lemma to_bl_eq:
  \<open>to_bl w = bin_to_bl (LENGTH('a)) (uint w)\<close>
  for w :: \<open>'a::len word\<close>
  by transfer simp

lemma bit_of_bl_iff [bit_simps]:
  \<open>bit (of_bl bs :: 'a word) n \<longleftrightarrow> rev bs ! n \<and> n < LENGTH('a::len) \<and> n < length bs\<close>
  by transfer (simp add: bin_nth_of_bl ac_simps)

lemma rev_to_bl_eq:
  \<open>rev (to_bl w) = map (bit w) [0..<LENGTH('a)]\<close>
  for w :: \<open>'a::len word\<close>
proof (rule nth_equalityI)
  fix i
  assume "i < length (rev (to_bl w))"
  then show "rev (to_bl w) ! i = map (bit w) [0..<LENGTH('a)] ! i"
    by (simp add: bin_nth_bl bit_word.rep_eq to_bl.rep_eq)
qed (simp add: to_bl.rep_eq)

lemma to_bl_eq_rev:
  \<open>to_bl w = map (bit w) (rev [0..<LENGTH('a)])\<close>
  for w :: \<open>'a::len word\<close>
  by (metis rev_map rev_rev_ident rev_to_bl_eq)

lemma of_bl_rev_eq: \<open>of_bl (rev bs) = horner_sum of_bool 2 bs\<close>
proof (rule bit_word_eqI)
  fix n
  assume "n < LENGTH('a)"
  show "bit (of_bl (rev bs)::'a word) n = bit (horner_sum of_bool (2::'a word) bs) n"
    using bit_horner_sum_bit_word_iff bit_of_bl_iff by fastforce
qed

lemma of_bl_eq:
  \<open>of_bl bs = horner_sum of_bool 2 (rev bs)\<close>
  using of_bl_rev_eq [of \<open>rev bs\<close>] by simp

lemma bshiftr1_eq:
  \<open>bshiftr1 b w = of_bl (b # butlast (to_bl w))\<close>
proof (rule bit_word_eqI)
  fix n
  assume "n < LENGTH('a)"
  then show "bit (w div 2 OR push_bit (LENGTH('a) - Suc 0) (of_bool b)) n = bit (of_bl (b # butlast (to_bl w))::'a word) n"
    using bit_imp_le_length
    by (force simp add:  bit_simps to_bl_eq_rev nth_append rev_nth nth_butlast not_less simp flip: bit_Suc)
qed

lemma length_to_bl_eq:
  \<open>length (to_bl w) = LENGTH('a)\<close>
  for w :: \<open>'a::len word\<close>
  by transfer simp

lemma word_rotr_eq:
  \<open>word_rotr n w = of_bl (rotater n (to_bl w))\<close>
proof (rule bit_word_eqI)
  fix na :: nat
  assume "na < LENGTH('a)"
  then
  show "bit (word_rotr n w) na = bit (of_bl (rotater n (to_bl w))::'a word) na"
    by (simp add: bit_word_rotr_iff bit_of_bl_iff rotater_rev length_to_bl_eq nth_rotate rev_to_bl_eq ac_simps)
qed

lemma word_rotl_eq:
  \<open>word_rotl n w = of_bl (rotate n (to_bl w))\<close>
proof -
  have \<section>: \<open>rotate n (to_bl w) = rev (rotater n (rev (to_bl w)))\<close>
    by (simp add: rotater_rev')
  then have "word_rotr (LENGTH('a) - n mod LENGTH('a)) w =
    of_bl (rev (rotater n (map (bit w) [0..<LENGTH('a)])))"
    by (simp add: rev_to_bl_eq rotate_rev rotater_rev word_rotr_eq)
  with \<section> show ?thesis
    by (simp add: word_rotl_eq_word_rotr bit_of_bl_iff length_to_bl_eq rev_to_bl_eq)
qed

lemma to_bl_def': "(to_bl :: 'a::len word \<Rightarrow> bool list) = bin_to_bl (LENGTH('a)) \<circ> uint"
  by transfer (simp add: fun_eq_iff)

\<comment> \<open>type definitions theorem for in terms of equivalent bool list\<close>
lemma td_bl:
  "type_definition
    (to_bl :: 'a::len word \<Rightarrow> bool list)
    of_bl
    {bl. length bl = LENGTH('a)}"
  apply (standard; transfer)
  apply (auto dest: sym)
  done

global_interpretation word_bl:
  type_definition
    "to_bl :: 'a::len word \<Rightarrow> bool list"
    of_bl
    "{bl. length bl = LENGTH('a::len)}"
  by (fact td_bl)

lemmas word_bl_Rep' = word_bl.Rep [unfolded mem_Collect_eq, iff]

lemma word_size_bl: "size w = size (to_bl w)"
  by (auto simp: word_size)

lemma to_bl_use_of_bl: "to_bl w = bl \<longleftrightarrow> w = of_bl bl \<and> length bl = length (to_bl w)"
  by (fastforce elim!: word_bl.Abs_inverse [unfolded mem_Collect_eq])

lemma length_bl_gt_0 [iff]: "0 < length (to_bl x)"
  for x :: "'a::len word"
  unfolding word_bl_Rep' by (rule len_gt_0)

lemma bl_not_Nil [iff]: "to_bl x \<noteq> []"
  for x :: "'a::len word"
  by (fact length_bl_gt_0 [unfolded length_greater_0_conv])

lemma length_bl_neq_0 [iff]: "length (to_bl x) \<noteq> 0"
  for x :: "'a::len word"
  by (fact length_bl_gt_0 [THEN gr_implies_not0])

lemma hd_to_bl_iff:
  \<open>hd (to_bl w) \<longleftrightarrow> bit w (LENGTH('a) - 1)\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: to_bl_eq_rev hd_map hd_rev)

lemma of_bl_drop':
  "lend = length bl - LENGTH('a::len) \<Longrightarrow>
    of_bl (drop lend bl) = (of_bl bl :: 'a word)"
  by transfer (simp flip: trunc_bl2bin)

lemma test_bit_of_bl:
  "bit (of_bl bl::'a::len word) n = (rev bl ! n \<and> n < LENGTH('a) \<and> n < length bl)"
  by transfer (simp add: bin_nth_of_bl ac_simps)

lemma no_of_bl: "(numeral bin ::'a::len word) = of_bl (bin_to_bl (LENGTH('a)) (numeral bin))"
  by transfer simp

lemma uint_bl: "to_bl w = bin_to_bl (size w) (uint w)"
  by transfer simp

lemma to_bl_bin: "bl_to_bin (to_bl w) = uint w"
  by (simp add: uint_bl word_size)

lemma to_bl_of_bin: "to_bl (word_of_int bin::'a::len word) = bin_to_bl (LENGTH('a)) bin"
  by (auto simp: uint_bl word_ubin.eq_norm word_size)

lemma to_bl_numeral [simp]:
  "to_bl (numeral bin::'a::len word) =
    bin_to_bl (LENGTH('a)) (numeral bin)"
  unfolding word_numeral_alt by (rule to_bl_of_bin)

lemma to_bl_neg_numeral [simp]:
  "to_bl (- numeral bin::'a::len word) =
    bin_to_bl (LENGTH('a)) (- numeral bin)"
  unfolding word_neg_numeral_alt by (rule to_bl_of_bin)

lemma to_bl_to_bin [simp] : "bl_to_bin (to_bl w) = uint w"
  by (simp add: uint_bl word_size)

lemma uint_bl_bin: "bl_to_bin (bin_to_bl (LENGTH('a)) (uint x)) = uint x"
  for x :: "'a::len word"
  by (rule trans [OF bin_bl_bin word_ubin.norm_Rep])

lemma ucast_bl: "ucast w = of_bl (to_bl w)"
  by transfer simp

lemma ucast_down_bl:
  \<open>(ucast :: 'a::len word \<Rightarrow> 'b::len word) (of_bl bl) = of_bl bl\<close>
    if \<open>is_down (ucast :: 'a::len word \<Rightarrow> 'b::len word)\<close>
  using that by transfer simp

lemma of_bl_append_same: "of_bl (X @ to_bl w) = w"
  by transfer (simp add: bl_to_bin_app_cat)

lemma ucast_of_bl_up:
  \<open>ucast (of_bl bl :: 'a::len word) = of_bl bl\<close>
  if \<open>size bl \<le> size (of_bl bl :: 'a::len word)\<close>
  using that
  by transfer (metis bintrunc_bintrunc_l trunc_bl2bin_len)

lemma word_rev_tf:
  "to_bl (of_bl bl::'a::len word) =
    rev (takefill False (LENGTH('a)) (rev bl))"
  by transfer (simp add: bl_bin_bl_rtf)

lemma word_rep_drop:
  "to_bl (of_bl bl::'a::len word) =
    replicate (LENGTH('a) - length bl) False @
    drop (length bl - LENGTH('a)) bl"
  by (simp add: word_rev_tf takefill_alt rev_take)

lemma to_bl_ucast:
  "to_bl (ucast (w::'b::len word) ::'a::len word) =
    replicate (LENGTH('a) - LENGTH('b)) False @
    drop (LENGTH('b) - LENGTH('a)) (to_bl w)"
  by (simp add: ucast_bl word_rep_drop)

lemma ucast_up_app:
  \<open>to_bl (ucast w :: 'b::len word) = replicate n False @ (to_bl w)\<close>
    if \<open>source_size (ucast :: 'a word \<Rightarrow> 'b word) + n = target_size (ucast :: 'a word \<Rightarrow> 'b word)\<close>
    for w :: \<open>'a::len word\<close>
  using that
  by (auto simp : source_size target_size to_bl_ucast)

lemma ucast_down_drop [OF refl]:
  "uc = ucast \<Longrightarrow> source_size uc = target_size uc + n \<Longrightarrow>
    to_bl (uc w) = drop n (to_bl w)"
  by (auto simp : source_size target_size to_bl_ucast)

lemma scast_down_drop [OF refl]:
  "sc = scast \<Longrightarrow> source_size sc = target_size sc + n \<Longrightarrow>
    to_bl (sc w) = drop n (to_bl w)"
  by (metis down_cast_same is_down_eq le_add1 source_size target_size ucast_down_drop)

lemma word_0_bl [simp]: "of_bl [] = 0"
  by transfer simp

lemma word_1_bl: "of_bl [True] = 1"
  by transfer (simp add: bl_to_bin_def)

lemma of_bl_0 [simp]: "of_bl (replicate n False) = 0"
  by transfer (simp add: bl_to_bin_rep_False)

lemma to_bl_0 [simp]: "to_bl (0::'a::len word) = replicate (LENGTH('a)) False"
  by (simp add: uint_bl word_size bin_to_bl_zero)

\<comment> \<open>links with \<open>rbl\<close> operations\<close>
lemma word_succ_rbl: "to_bl w = bl \<Longrightarrow> to_bl (word_succ w) = rev (rbl_succ (rev bl))"
  by transfer (simp add: rbl_succ)

lemma word_pred_rbl: "to_bl w = bl \<Longrightarrow> to_bl (word_pred w) = rev (rbl_pred (rev bl))"
  by transfer (simp add: rbl_pred)

lemma word_add_rbl:
  "to_bl v = vbl \<Longrightarrow> to_bl w = wbl \<Longrightarrow>
    to_bl (v + w) = rev (rbl_add (rev vbl) (rev wbl))"
  by (metis rbl_add rev_swap to_bl_eq to_bl_of_bin word_add_def)

lemma word_mult_rbl:
  "to_bl v = vbl \<Longrightarrow> to_bl w = wbl \<Longrightarrow>
    to_bl (v * w) = rev (rbl_mult (rev vbl) (rev wbl))"
  by (metis rbl_mult rev_swap to_bl_eq to_bl_of_bin word_mult_def)

lemma rtb_rbl_ariths:
  "rev (to_bl w) = ys \<Longrightarrow> rev (to_bl (word_succ w)) = rbl_succ ys"
  "rev (to_bl w) = ys \<Longrightarrow> rev (to_bl (word_pred w)) = rbl_pred ys"
  "rev (to_bl v) = ys \<Longrightarrow> rev (to_bl w) = xs \<Longrightarrow> rev (to_bl (v * w)) = rbl_mult ys xs"
  "rev (to_bl v) = ys \<Longrightarrow> rev (to_bl w) = xs \<Longrightarrow> rev (to_bl (v + w)) = rbl_add ys xs"
  by (auto simp: rev_swap [symmetric] word_succ_rbl word_pred_rbl word_mult_rbl word_add_rbl)

lemma of_bl_length_less:
  \<open>(of_bl x :: 'a::len word) < 2 ^ k\<close>
    if \<open>length x = k\<close> \<open>k < LENGTH('a)\<close>
proof -
  from that have \<open>length x < LENGTH('a)\<close>
    by simp
  then have \<open>(of_bl x :: 'a::len word) < 2 ^ length x\<close>
    by (simp add: bit_of_bl_iff less_2p_is_upper_bits_unset)
  with that show ?thesis
    by simp
qed

lemma word_eq_rbl_eq: "x = y \<longleftrightarrow> rev (to_bl x) = rev (to_bl y)"
  by simp

lemma bl_word_not: "to_bl (NOT w) = map Not (to_bl w)"
  by transfer (simp add: bl_not_bin)

lemma bl_word_xor: "to_bl (v XOR w) = map2 (\<noteq>) (to_bl v) (to_bl w)"
  by transfer (simp flip: bl_xor_bin)

lemma bl_word_or: "to_bl (v OR w) = map2 (\<or>) (to_bl v) (to_bl w)"
  by transfer (simp flip: bl_or_bin)

lemma bl_word_and: "to_bl (v AND w) = map2 (\<and>) (to_bl v) (to_bl w)"
  by transfer (simp flip: bl_and_bin)

lemma bin_nth_uint': "bit (uint w) n \<longleftrightarrow> rev (bin_to_bl (size w) (uint w)) ! n \<and> n < size w"
  unfolding word_size by (meson bin_nth_bl bin_nth_uint_imp)

lemmas bin_nth_uint = bin_nth_uint' [unfolded word_size]

lemma test_bit_bl: "bit w n \<longleftrightarrow> rev (to_bl w) ! n \<and> n < size w"
  by transfer (auto simp: bin_nth_bl)

lemma to_bl_nth: "n < size w \<Longrightarrow> to_bl w ! n = bit w (size w - Suc n)"
  by (simp add: word_size rev_nth test_bit_bl)

lemma map_bit_interval_eq:
  \<open>map (bit w) [0..<n] = takefill False n (rev (to_bl w))\<close> for w :: \<open>'a::len word\<close>
proof (rule nth_equalityI)
  show \<open>length (map (bit w) [0..<n]) =
    length (takefill False n (rev (to_bl w)))\<close>
    by simp
  fix m
  assume \<open>m < length (map (bit w) [0..<n])\<close>
  then have \<open>m < n\<close>
    by simp
  then have \<open>bit w m \<longleftrightarrow> takefill False n (rev (to_bl w)) ! m\<close>
    by (auto simp: nth_takefill not_less rev_nth to_bl_nth word_size dest: bit_imp_le_length)
  with \<open>m < n \<close>show \<open>map (bit w) [0..<n] ! m \<longleftrightarrow> takefill False n (rev (to_bl w)) ! m\<close>
    by simp
qed

lemma to_bl_unfold:
  \<open>to_bl w = rev (map (bit w) [0..<LENGTH('a)])\<close> for w :: \<open>'a::len word\<close>
  by (simp add: map_bit_interval_eq takefill_bintrunc to_bl_def flip: bin_to_bl_def)

lemma nth_rev_to_bl:
  \<open>rev (to_bl w) ! n \<longleftrightarrow> bit w n\<close>
  if \<open>n < LENGTH('a)\<close> for w :: \<open>'a::len word\<close>
  using that by (simp add: to_bl_unfold)

lemma nth_to_bl:
  \<open>to_bl w ! n \<longleftrightarrow> bit w (LENGTH('a) - Suc n)\<close>
  if \<open>n < LENGTH('a)\<close> for w :: \<open>'a::len word\<close>
  using that by (simp add: to_bl_unfold rev_nth)

lemma of_bl_rep_False: "of_bl (replicate n False @ bs) = of_bl bs"
  by (auto simp: of_bl_def bl_to_bin_rep_F)

lemma [code abstract]:
  \<open>Word.the_int (of_bl bs :: 'a word) = horner_sum of_bool 2 (take LENGTH('a::len) (rev bs))\<close>
  by (metis bl_to_bin_eq of_bl.abs_eq take_rev the_int.abs_eq trunc_bl2bin)

lemma [code]:
  \<open>to_bl w = map (bit w) (rev [0..<LENGTH('a::len)])\<close>
  for w :: \<open>'a::len word\<close>
  by (fact to_bl_eq_rev)

lemma word_reverse_eq_of_bl_rev_to_bl:
  \<open>word_reverse w = of_bl (rev (to_bl w))\<close>
  by (rule bit_word_eqI)
    (auto simp: bit_word_reverse_iff bit_of_bl_iff nth_to_bl)

lemmas word_reverse_no_def [simp] =
  word_reverse_eq_of_bl_rev_to_bl [of "numeral w"] for w

lemma to_bl_word_rev: "to_bl (word_reverse w) = rev (to_bl w)"
  by (rule nth_equalityI) (simp_all add: nth_rev_to_bl word_reverse_def word_rep_drop flip: of_bl_eq)

lemma to_bl_n1 [simp]: "to_bl (-1::'a::len word) = replicate (LENGTH('a)) True"
  by (metis bin_to_bl_minus1 to_bl_of_bin word_of_int_neg_1)

lemma rbl_word_or: "rev (to_bl (x OR y)) = map2 (\<or>) (rev (to_bl x)) (rev (to_bl y))"
  by (simp add: zip_rev bl_word_or rev_map)

lemma rbl_word_and: "rev (to_bl (x AND y)) = map2 (\<and>) (rev (to_bl x)) (rev (to_bl y))"
  by (simp add: zip_rev bl_word_and rev_map)

lemma rbl_word_xor: "rev (to_bl (x XOR y)) = map2 (\<noteq>) (rev (to_bl x)) (rev (to_bl y))"
  by (simp add: zip_rev bl_word_xor rev_map)

lemma rbl_word_not: "rev (to_bl (NOT x)) = map Not (rev (to_bl x))"
  by (simp add: bl_word_not rev_map)

lemma bshiftr1_numeral [simp]:
  \<open>bshiftr1 b (numeral w :: 'a word) = of_bl (b # butlast (bin_to_bl LENGTH('a::len) (numeral w)))\<close>
  by (rule bit_word_eqI) (auto simp: bit_simps rev_nth nth_append nth_butlast nth_bin_to_bl simp flip: bit_Suc)

lemma bshiftr1_bl: "to_bl (bshiftr1 b w) = b # butlast (to_bl w)"
  unfolding bshiftr1_eq by (rule word_bl.Abs_inverse) simp

lemma shiftl1_of_bl: "shiftl1 (of_bl bl) = of_bl (bl @ [False])"
proof (rule bit_word_eqI)
  fix n
  assume "n < LENGTH('a)"
  then
  show "bit (shiftl1 (of_bl bl::'a word)) n = bit (of_bl (bl @ [False])::'a word) n"
    by (cases n) (simp_all add: bit_simps)
qed

lemma shiftl1_bl: "shiftl1 w = of_bl (to_bl w @ [False])"
  by (metis shiftl1_of_bl word_bl.Rep_inverse)

lemma bl_shiftl1: "to_bl (shiftl1 w) = tl (to_bl w) @ [False]"
  for w :: "'a::len word"
  by (simp add: shiftl1_bl word_rep_drop drop_Suc drop_Cons') (fast intro!: Suc_leI)

lemma to_bl_double_eq:
  \<open>to_bl (2 * w) = tl (to_bl w) @ [False]\<close>
  using bl_shiftl1 [of w] by (simp add: shiftl1_def ac_simps)

\<comment> \<open>Generalized version of \<open>bl_shiftl1\<close>. Maybe this one should replace it?\<close>
lemma bl_shiftl1': "to_bl (shiftl1 w) = tl (to_bl w @ [False])"
  by (simp add: shiftl1_bl word_rep_drop drop_Suc del: drop_append)

lemma shiftr1_bl:
  \<open>shiftr1 w = of_bl (butlast (to_bl w))\<close>
proof (rule bit_word_eqI)
  fix n
  assume \<open>n < LENGTH('a)\<close>
  show \<open>bit (shiftr1 w) n \<longleftrightarrow> bit (of_bl (butlast (to_bl w)) :: 'a word) n\<close>
  proof (cases \<open>n = LENGTH('a) - 1\<close>)
    case True
    then show ?thesis
      by (simp add: bit_shiftr1_iff bit_of_bl_iff)
  next
    case False
    with \<open>n < LENGTH('a)\<close>
    have \<open>n < LENGTH('a) - 1\<close>
      by simp
    with \<open>n < LENGTH('a)\<close> show ?thesis
      by (simp add: bit_shiftr1_iff bit_of_bl_iff rev_nth nth_butlast
        word_size to_bl_nth)
  qed
qed

lemma bl_shiftr1: "to_bl (shiftr1 w) = False # butlast (to_bl w)"
  for w :: "'a::len word"
  by (simp add: shiftr1_bl word_rep_drop len_gt_0 [THEN Suc_leI])

\<comment> \<open>Generalized version of \<open>bl_shiftr1\<close>. Maybe this one should replace it?\<close>
lemma bl_shiftr1': "to_bl (shiftr1 w) = butlast (False # to_bl w)"
  by (simp add: bl_shiftr1)

lemma bl_sshiftr1: "to_bl (sshiftr1 w) = hd (to_bl w) # butlast (to_bl w)"
  for w :: "'a::len word"
proof (rule nth_equalityI)
  fix n
  assume \<open>n < length (to_bl (sshiftr1 w))\<close>
  then have \<open>n < LENGTH('a)\<close>
    by simp
  then show \<open>to_bl (sshiftr1 w) ! n \<longleftrightarrow> (hd (to_bl w) # butlast (to_bl w)) ! n\<close>
    by (cases n) (simp_all add: hd_conv_nth bit_sshiftr1_iff nth_butlast Suc_diff_Suc nth_to_bl)
qed simp

lemma drop_shiftr: "drop n (to_bl (w >> n)) = take (size w - n) (to_bl w)"
  for w :: "'a::len word"
  by (rule nth_equalityI) (simp_all add: word_size to_bl_nth bit_simps)

lemma drop_sshiftr: "drop n (to_bl (w >>> n)) = take (size w - n) (to_bl w)"
  for w :: "'a::len word"
  by (rule nth_equalityI) (simp_all add: word_size nth_to_bl bit_simps)

lemma take_shiftr: "n \<le> size w \<Longrightarrow> take n (to_bl (w >> n)) = replicate n False"
  by  (rule nth_equalityI) (auto simp: word_size to_bl_nth bit_simps dest: bit_imp_le_length)

lemma take_sshiftr':
  fixes w :: "'a::len word"
  assumes "n \<le> size w"
  shows "hd (to_bl (w >>> n)) = hd (to_bl w) \<and> take n (to_bl (w >>> n)) = replicate n (hd (to_bl w))"
proof (cases n)
  case 0
  then show ?thesis
    by auto
next
  case (Suc nat)
  with assms show ?thesis
    apply (intro nth_equalityI conjI)
    apply (auto simp add: hd_to_bl_iff bit_simps nth_to_bl nth_Cons word_size split: nat.split)
    done
qed

lemmas hd_sshiftr = take_sshiftr' [THEN conjunct1]
lemmas take_sshiftr = take_sshiftr' [THEN conjunct2]

lemma atd_lem: "take n xs = t \<Longrightarrow> drop n xs = d \<Longrightarrow> xs = t @ d"
  by (auto intro: append_take_drop_id [symmetric])

lemmas bl_shiftr = atd_lem [OF take_shiftr drop_shiftr]
lemmas bl_sshiftr = atd_lem [OF take_sshiftr drop_sshiftr]

lemma shiftl_of_bl: "of_bl bl << n = of_bl (bl @ replicate n False)"
  by (rule bit_word_eqI) (auto simp: bit_simps nth_append)

lemma shiftl_bl: "w << n = of_bl (to_bl w @ replicate n False)"
  for w :: "'a::len word"
  by (simp flip: shiftl_of_bl)

lemma bl_shiftl: "to_bl (w << n) = drop n (to_bl w) @ replicate (min (size w) n) False"
  by (simp add: shiftl_bl word_rep_drop word_size)

lemma shiftr1_bl_of:
  "length bl \<le> LENGTH('a) \<Longrightarrow>
    shiftr1 (of_bl bl::'a::len word) = of_bl (butlast bl)"
  by (metis bin_rest_bl_to_bin bl_to_bin_rep_F diff_is_0_eq' drop0 of_bl.abs_eq shiftr1_bl word_rep_drop)

lemma shiftr_bl_of:
  "length bl \<le> LENGTH('a) \<Longrightarrow>
     (of_bl bl::'a::len word) >> n = of_bl (take (length bl - n) bl)"
  by (rule bit_word_eqI) (auto simp: bit_simps rev_nth)

lemma shiftr_bl: "x >> n \<equiv> of_bl (take (LENGTH('a) - n) (to_bl x))"
  for x :: "'a::len word"
  using shiftr_bl_of [where 'a='a, of "to_bl x"] by simp

lemma aligned_bl_add_size [OF refl]:
  fixes x :: \<open>'a::len word\<close>
  assumes "size x - n = m"
      and "n \<le> size x"
      and "drop m (to_bl x) = replicate n False"
      and "take m (to_bl y) = replicate m False"
    shows "to_bl (x + y) = take m (to_bl x) @ drop m (to_bl y)"
proof -
  have "map2 (\<and>) (to_bl x) (to_bl y) = replicate (m + n) False"
    by (metis add.commute align_lem_and assms diff_add word_bl_Rep' wsst_TYs(3))
  then have "x AND y = 0"
    by (metis bl_to_bin_rep_False bl_word_and to_bl_to_bin unsigned_eq_0_iff)
  with assms show ?thesis
    by (metis add_diff_inverse_nat align_lem_or bl_word_or length_to_bl_eq linorder_not_less word_plus_and_or_coroll word_size_bl)
qed

lemma mask_bl: "mask n = of_bl (replicate n True)"
  by (auto simp: bit_simps intro!: word_eqI)

lemma bl_and_mask':
  "to_bl (w AND mask n :: 'a::len word) =
    replicate (LENGTH('a) - n) False @
    drop (LENGTH('a) - n) (to_bl w)"
proof (rule nth_equalityI)
  fix i
  assume i: "i < length (to_bl (w AND mask n))"
  then have "(bit w (LENGTH('a) - Suc i) \<and> LENGTH('a) - Suc i < n) =
    (replicate (LENGTH('a) - n) False @
     drop (LENGTH('a) - n) (to_bl w)) !
    i"
    by (auto simp: word_size test_bit_bl nth_append rev_nth)
  with i show "to_bl (w AND mask n) ! i = (replicate (LENGTH('a) - n) False @ drop (LENGTH('a) - n) (to_bl w)) ! i"
  by (auto simp add: to_bl_nth word_size bit_simps)
qed auto

lemma slice1_eq_of_bl:
  \<open>(slice1 n w :: 'b::len word) = of_bl (takefill False n (to_bl w))\<close>
  for w :: \<open>'a::len word\<close>
proof (rule bit_word_eqI)
  fix m
  assume \<open>m < LENGTH('b)\<close>
  show \<open>bit (slice1 n w :: 'b::len word) m \<longleftrightarrow> bit (of_bl (takefill False n (to_bl w)) :: 'b word) m\<close>
    by (cases \<open>m \<ge> n\<close>; cases \<open>LENGTH('a) \<ge> n\<close>)
      (auto simp: bit_slice1_iff bit_of_bl_iff not_less rev_nth not_le nth_takefill nth_to_bl algebra_simps)
qed

lemma slice1_no_bin [simp]:
  "slice1 n (numeral w :: 'b word) = of_bl (takefill False n (bin_to_bl (LENGTH('b::len)) (numeral w)))"
  by (simp add: slice1_eq_of_bl) (* TODO: neg_numeral *)

lemma slice_no_bin [simp]:
  "slice n (numeral w :: 'b word) = of_bl (takefill False (LENGTH('b::len) - n)
    (bin_to_bl (LENGTH('b::len)) (numeral w)))"
  by (simp add: slice_def) (* TODO: neg_numeral *)

lemma slice_take': "slice n w = of_bl (take (size w - n) (to_bl w))"
  by (simp add: slice_def word_size slice1_eq_of_bl takefill_alt)

lemmas slice_take = slice_take' [unfolded word_size]

\<comment> \<open>shiftr to a word of the same size is just slice,
    slice is just shiftr then ucast\<close>
lemmas shiftr_slice = trans [OF shiftr_bl [THEN meta_eq_to_obj_eq] slice_take [symmetric]]

lemma slice1_down_alt':
  "sl = slice1 n w \<Longrightarrow> fs = size sl \<Longrightarrow> fs + k = n \<Longrightarrow>
    to_bl sl = takefill False fs (drop k (to_bl w))"
  apply (simp add: slice1_eq_of_bl)
  by (metis append_take_drop_id drop_takefill length_takefill of_bl_append_same to_bl_use_of_bl word_bl_Rep' wsst_TYs(3))

lemma slice1_up_alt':
  "sl = slice1 n w \<Longrightarrow> fs = size sl \<Longrightarrow> fs = n + k \<Longrightarrow>
    to_bl sl = takefill False fs (replicate k False @ (to_bl w))"
  apply (simp add: slice1_eq_of_bl)
  by (metis length_replicate length_takefill of_bl_rep_False takefill_append to_bl_use_of_bl word_bl_Rep' wsst_TYs(3))

lemmas sd1 = slice1_down_alt' [OF refl refl, unfolded word_size]
lemmas su1 = slice1_up_alt' [OF refl refl, unfolded word_size]
lemmas slice1_down_alt = le_add_diff_inverse [THEN sd1]
lemmas slice1_up_alts =
  le_add_diff_inverse [symmetric, THEN su1]
  le_add_diff_inverse2 [symmetric, THEN su1]

lemma slice1_tf_tf':
  "to_bl (slice1 n w :: 'a::len word) =
    rev (takefill False (LENGTH('a)) (rev (takefill False n (to_bl w))))"
  unfolding slice1_eq_of_bl by (rule word_rev_tf)

lemmas slice1_tf_tf = slice1_tf_tf' [THEN word_bl.Rep_inverse', symmetric]

lemma revcast_eq_of_bl:
  \<open>(revcast w :: 'b::len word) = of_bl (takefill False (LENGTH('b)) (to_bl w))\<close>
  for w :: \<open>'a::len word\<close>
  by (simp add: revcast_def slice1_eq_of_bl)

lemmas revcast_no_def [simp] = revcast_eq_of_bl [where w="numeral w", unfolded word_size] for w

lemma to_bl_revcast:
  "to_bl (revcast w :: 'a::len word) = takefill False (LENGTH('a)) (to_bl w)"
proof (rule nth_equalityI)
  fix i
  assume "i < length (to_bl (revcast w::'a word))"
  then show "to_bl (revcast w::'a word) ! i = takefill False (LENGTH('a)) (to_bl w) ! i"
    by simp (metis length_takefill revcast_eq_of_bl to_bl_use_of_bl word_bl_Rep')
qed auto

lemma word_cat_bl: "word_cat a b = of_bl (to_bl a @ to_bl b)"
  by (rule bit_word_eqI) (simp add: bl_to_bin_app_cat of_bl.abs_eq word_cat_eq')

lemma of_bl_append:
  "(of_bl (xs @ ys) :: 'a::len word) = of_bl xs * 2^(length ys) + of_bl ys"
  by transfer (simp add: bl_to_bin_app_cat bin_cat_num)

lemma of_bl_False [simp]: "of_bl (False#xs) = of_bl xs"
  by (rule word_eqI) (auto simp: test_bit_of_bl nth_append)

lemma of_bl_True [simp]: "(of_bl (True # xs) :: 'a::len word) = 2^length xs + of_bl xs"
  by (subst of_bl_append [where xs="[True]", simplified]) (simp add: word_1_bl)

lemma of_bl_Cons: "of_bl (x#xs) = of_bool x * 2^length xs + of_bl xs"
  by simp

lemma word_split_bl':
  "std = size c - size b \<Longrightarrow> (word_split c = (a, b)) \<Longrightarrow>
    (a = of_bl (take std (to_bl c)) \<and> b = of_bl (drop std (to_bl c)))"
  by (metis of_bl_drop' slice_take' split_slices ucast_bl word_bl_Rep' word_split_def wsst_TYs(3))

lemma word_split_bl: "std = size c - size b \<Longrightarrow>
    (a = of_bl (take std (to_bl c)) \<and> b = of_bl (drop std (to_bl c))) \<longleftrightarrow>
    word_split c = (a, b)"
  using word_split_bl' [where c=c]
  by (auto simp: word_split_bl' word_split_def wsst_TYs(3))

lemma word_split_bl_eq:
  "(word_split c :: ('c::len word \<times> 'd::len word)) =
    (of_bl (take (LENGTH('a::len) - LENGTH('d::len)) (to_bl c)),
     of_bl (drop (LENGTH('a) - LENGTH('d)) (to_bl c)))"
  for c :: "'a::len word"
  by (simp add: word_size word_split_bin' word_split_bl')

lemma word_rcat_bl:
  \<open>word_rcat wl = of_bl (concat (map to_bl wl))\<close>
proof -
  define ws where \<open>ws = rev wl\<close>
  moreover
  have "word_of_int (horner_sum of_bool 2 (concat (map (\<lambda>x. map (bit x) [0..<LENGTH('b)]) ws))) =
        horner_sum of_bool 2 (concat (map (\<lambda>x. map (bit x) [0..<LENGTH('b)]) ws))"
    by transfer simp
  then have \<open>word_rcat (rev ws) = of_bl (concat (map to_bl (rev ws)))\<close>
    by (simp add: word_rcat_def of_bl_eq rev_concat rev_map comp_def rev_to_bl_eq flip: horner_sum_of_bool_2_concat)
  ultimately show ?thesis
    by simp
qed

lemma size_rcat_lem': "size (concat (map to_bl wl)) = length wl * size (hd wl)"
  by (induct wl) (auto simp: word_size)

lemmas size_rcat_lem = size_rcat_lem' [unfolded word_size]

lemma nth_rcat_lem:
  "n < length (wl::'a word list) * LENGTH('a::len) \<Longrightarrow>
    rev (concat (map to_bl wl)) ! n =
    rev (to_bl (rev wl ! (n div LENGTH('a)))) ! (n mod LENGTH('a))"
proof (induct wl)
  case Nil
  then show ?case by auto
next
  case (Cons a wl)
  then show ?case
    apply (clarsimp simp add: nth_append size_rcat_lem)
    by (metis diff_self_eq_0 len_gt_0 less_Suc_eq modulo_nat_def mult_Suc nth_Cons' td_gal_lt)
qed

lemma foldl_eq_foldr: "foldl (+) x xs = foldr (+) (x # xs) 0"
  for x :: "'a::comm_monoid_add"
  by (induct xs arbitrary: x) (auto simp: add.assoc)

lemmas word_cat_bl_no_bin [simp] =
  word_cat_bl [where a="numeral a" and b="numeral b", unfolded to_bl_numeral]
  for a b (* FIXME: negative numerals, 0 and 1 *)

lemmas word_split_bl_no_bin [simp] =
  word_split_bl_eq [where c="numeral c", unfolded to_bl_numeral] for c

lemmas word_rot_defs = word_roti_eq_word_rotr_word_rotl word_rotr_eq word_rotl_eq

lemma to_bl_rotl: "to_bl (word_rotl n w) = rotate n (to_bl w)"
  by (simp add: word_rotl_eq to_bl_use_of_bl)

lemmas blrs0 = rotate_eqs [THEN to_bl_rotl [THEN trans]]

lemmas word_rotl_eqs =
  blrs0 [simplified word_bl_Rep' word_bl.Rep_inject to_bl_rotl [symmetric]]

lemma to_bl_rotr: "to_bl (word_rotr n w) = rotater n (to_bl w)"
  by (simp add: word_rotr_eq to_bl_use_of_bl)

lemmas brrs0 = rotater_eqs [THEN to_bl_rotr [THEN trans]]

lemmas word_rotr_eqs =
  brrs0 [simplified word_bl_Rep' word_bl.Rep_inject to_bl_rotr [symmetric]]

declare word_rotr_eqs (1) [simp]
declare word_rotl_eqs (1) [simp]

lemmas abl_cong = arg_cong [where f = "of_bl"]

end

locale word_rotate
begin

lemmas word_rot_defs' = to_bl_rotl to_bl_rotr

lemmas blwl_syms [symmetric] = bl_word_not bl_word_and bl_word_or bl_word_xor

lemmas lbl_lbl = trans [OF word_bl_Rep' word_bl_Rep' [symmetric]]

lemmas ths_map2 [OF lbl_lbl] = rotate_map2 rotater_map2

lemmas ths_map [where xs = "to_bl v"] = rotate_map rotater_map for v

lemmas th1s [simplified word_rot_defs' [symmetric]] = ths_map2 ths_map

end

lemmas bl_word_rotl_dt = trans [OF to_bl_rotl rotate_drop_take,
  simplified word_bl_Rep']

lemmas bl_word_rotr_dt = trans [OF to_bl_rotr rotater_drop_take,
  simplified word_bl_Rep']

lemma bl_word_roti_dt':
  assumes "n = nat ((- i) mod int (size (w :: 'a::len word)))"
  shows "to_bl (word_roti i w) = drop n (to_bl w) @ take n (to_bl w)"
proof (cases "i\<ge>0")
  case True
  with assms show ?thesis
    by (simp add: bl_word_rotr_dt nat_diff_distrib' nat_mod_as_int wsst_TYs(3) zmod_zminus1_eq_if)
next
  case False
  with assms show ?thesis
    by (simp add: bl_word_rotl_dt nat_mod_distrib wsst_TYs(3))
qed

lemmas bl_word_roti_dt = bl_word_roti_dt' [unfolded word_size]

lemmas word_rotl_dt = bl_word_rotl_dt [THEN word_bl.Rep_inverse' [symmetric]]
lemmas word_rotr_dt = bl_word_rotr_dt [THEN word_bl.Rep_inverse' [symmetric]]
lemmas word_roti_dt = bl_word_roti_dt [THEN word_bl.Rep_inverse' [symmetric]]

lemmas word_rotr_dt_no_bin' [simp] =
  word_rotr_dt [where w="numeral w", unfolded to_bl_numeral] for w
  (* FIXME: negative numerals, 0 and 1 *)

lemmas word_rotl_dt_no_bin' [simp] =
  word_rotl_dt [where w="numeral w", unfolded to_bl_numeral] for w
  (* FIXME: negative numerals, 0 and 1 *)

lemma max_word_bl: "to_bl (- 1::'a::len word) = replicate LENGTH('a) True"
  by (fact to_bl_n1)

lemma to_bl_mask:
  "to_bl (mask n :: 'a::len word) =
  replicate (LENGTH('a) - n) False @ replicate (min (LENGTH('a)) n) True"
  by (simp add: mask_bl word_rep_drop min_def)

lemma map_replicate_True:
  "n = length xs \<Longrightarrow>
    map (\<lambda>(x,y). x \<and> y) (zip xs (replicate n True)) = xs"
  by (induct xs arbitrary: n) auto

lemma map_replicate_False:
  "n = length xs \<Longrightarrow> map (\<lambda>(x,y). x \<and> y)
    (zip xs (replicate n False)) = replicate n False"
  by (induct xs arbitrary: n) auto

context
  includes bit_operations_syntax
begin

lemma bl_and_mask:
  fixes w :: "'a::len word"
    and n :: nat
  defines "n' \<equiv> LENGTH('a) - n"
  shows "to_bl (w AND mask n) = replicate n' False @ drop n' (to_bl w)"
proof -
  note [simp] = map_replicate_True map_replicate_False
  have "to_bl (w AND mask n) = map2 (\<and>) (to_bl w) (to_bl (mask n::'a::len word))"
    by (simp add: bl_word_and)
  also have "to_bl w = take n' (to_bl w) @ drop n' (to_bl w)"
    by simp
  also have "map2 (\<and>) \<dots> (to_bl (mask n::'a::len word)) =
      replicate n' False @ drop n' (to_bl w)"
    unfolding to_bl_mask n'_def by (subst zip_append) auto
  finally show ?thesis .
qed

lemma drop_rev_takefill:
  "length xs \<le> n \<Longrightarrow>
    drop (n - length xs) (rev (takefill False n (rev xs))) = xs"
  by (simp add: takefill_alt rev_take)

declare bin_to_bl_def [simp]

lemmas of_bl_reasoning = to_bl_use_of_bl of_bl_append

lemma uint_of_bl_is_bl_to_bin_drop:
  \<open>uint (of_bl l :: 'a::len word) = bl_to_bin l\<close> if \<open>length (dropWhile Not l) \<le> LENGTH('a)\<close>
proof (transfer fixing: l)
  from that have *: \<open>2 ^ length (dropWhile Not l) \<le> (2::int) ^ LENGTH('a)\<close>
    by simp
  then show \<open>take_bit LENGTH('a) (bl_to_bin l) = bl_to_bin l\<close>
    using bl_to_bin_lt2p_drop [of l]
    by (simp add: take_bit_int_eq_self_iff bl_to_bin_ge0 order_less_le_trans)
qed

corollary uint_of_bl_is_bl_to_bin:
  "length l\<le>LENGTH('a) \<Longrightarrow> uint ((of_bl::bool list\<Rightarrow> ('a :: len) word) l) = bl_to_bin l"
  apply(rule uint_of_bl_is_bl_to_bin_drop)
  using le_trans length_dropWhile_le by blast

lemma bin_to_bl_or:
  "bin_to_bl n (a OR b) = map2 (\<or>) (bin_to_bl n a) (bin_to_bl n b)"
  using bl_or_aux_bin[where n=n and v=a and w=b and bs="[]" and cs="[]"]
  by simp

lemma word_and_1_bl:
  fixes x::"'a::len word"
  shows "(x AND 1) = of_bl [bit x 0]"
  by (simp add: word_and_1)

lemma word_1_and_bl:
  fixes x::"'a::len word"
  shows "(1 AND x) = of_bl [bit x 0]"
  using word_and_1_bl [of x] by (simp add: ac_simps)

lemma of_bl_drop:
  "of_bl (drop n xs) = (of_bl xs AND mask (length xs - n))"
  by (rule bit_word_eqI) (auto simp: rev_nth bit_simps cong: rev_conj_cong)

lemma to_bl_1:
  "to_bl (1::'a::len word) = replicate (LENGTH('a) - 1) False @ [True]"
  by (rule nth_equalityI) (auto simp: to_bl_unfold nth_append rev_nth bit_1_iff not_less not_le)

lemma eq_zero_set_bl:
  "(w = 0) = (True \<notin> set (to_bl w))"
  by (auto simp: to_bl_unfold intro: bit_word_eqI)

lemma of_drop_to_bl:
  "of_bl (drop n (to_bl x)) = (x AND mask (size x - n))"
  by (simp add: of_bl_drop word_size_bl)

lemma unat_of_bl_length:
  "unat (of_bl xs :: 'a::len word) < 2 ^ (length xs)"
proof (cases "length xs < LENGTH('a)")
  case True
  then have "(of_bl xs::'a::len word) < 2 ^ length xs"
    by (simp add: of_bl_length_less)
  with True
  show ?thesis
    by (simp add: word_less_nat_alt unat_of_nat)
next
  case False
  have "unat (of_bl xs::'a::len word) < 2 ^ LENGTH('a)"
    by (simp split: unat_split)
  also
  from False
  have "LENGTH('a) \<le> length xs" by simp
  then have "2 ^ LENGTH('a) \<le> (2::nat) ^ length xs"
    by (rule power_increasing) simp
  finally
  show ?thesis .
qed

lemma word_msb_alt: "msb w \<longleftrightarrow> hd (to_bl w)"
  for w :: "'a::len word"
  using hd_to_bl_iff msb_nth by blast

lemma word_lsb_last:
  \<open>lsb w \<longleftrightarrow> last (to_bl w)\<close>
  for w :: \<open>'a::len word\<close>
  using nth_to_bl [of \<open>LENGTH('a) - Suc 0\<close> w]
  by (simp add: last_conv_nth bit_0 lsb_odd)

lemma is_aligned_to_bl:
  "is_aligned (w :: 'a :: len word) n = (True \<notin> set (drop (size w - n) (to_bl w)))"
  by (simp add: is_aligned_mask eq_zero_set_bl bl_and_mask word_size)

lemma is_aligned_replicate:
  fixes w::"'a::len word"
  assumes aligned: "is_aligned w n"
  and          nv: "n \<le> LENGTH('a)"
  shows   "to_bl w = (take (LENGTH('a) - n) (to_bl w)) @ replicate n False"
proof (rule nth_equalityI)
  fix i
  assume "i < length (to_bl w)"
  with assms
  show "to_bl w ! i = (take (LENGTH('a) - n) (to_bl w) @ replicate n False) ! i"
    by (simp add: nth_append not_less word_size to_bl_nth is_aligned_imp_not_bit)
qed (auto simp: nv)

lemma is_aligned_drop:
  fixes w::"'a::len word"
  assumes "is_aligned w n" "n \<le> LENGTH('a)"
  shows "drop (LENGTH('a) - n) (to_bl w) = replicate n False"
proof -
  have "to_bl w = take (LENGTH('a) - n) (to_bl w) @ replicate n False"
    by (rule is_aligned_replicate) fact+
  then have "drop (LENGTH('a) - n) (to_bl w) = drop (LENGTH('a) - n) \<dots>" by simp
  also have "\<dots> = replicate n False" by simp
  finally show ?thesis .
qed

lemma less_is_drop_replicate:
  fixes x::"'a::len word"
  assumes lt: "x < 2 ^ n"
  shows   "to_bl x = replicate (LENGTH('a) - n) False @ drop (LENGTH('a) - n) (to_bl x)"
  by (metis assms bl_and_mask' less_mask_eq)

lemma is_aligned_add_conv:
  fixes off::"'a::len word"
  assumes aligned: "is_aligned w n"
  and        offv: "off < 2 ^ n"
  shows    "to_bl (w + off) =
   (take (LENGTH('a) - n) (to_bl w)) @ (drop (LENGTH('a) - n) (to_bl off))"
proof cases
  assume nv: "n \<le> LENGTH('a)"
  show ?thesis
  proof (subst aligned_bl_add_size, simp_all only: word_size)
    show "drop (LENGTH('a) - n) (to_bl w) = replicate n False"
      by (subst is_aligned_replicate [OF aligned nv]) (simp add: word_size)

    from offv show "take (LENGTH('a) - n) (to_bl off) = replicate (LENGTH('a) - n) False"
      by (subst less_is_drop_replicate, assumption) simp
  qed fact
next
  assume "\<not> n \<le> LENGTH('a)"
  with offv show ?thesis by (simp add: power_overflow)
qed

lemma is_aligned_replicateI:
  "to_bl p = addr @ replicate n False \<Longrightarrow> is_aligned (p::'a::len word) n"
  by (metis is_aligned_shiftl_self shiftl_of_bl word_bl.Rep_inverse)

lemma to_bl_2p:
  assumes "n < LENGTH('a)"
  shows "to_bl ((2::'a::len word) ^ n) = replicate (LENGTH('a) - Suc n) False @ True # replicate n False"
proof (rule nth_equalityI)
  fix i
  assume i: "i < length (to_bl ((2::'a word) ^ n))"
  with assms
  have "\<And>d da db.
       \<lbrakk>case db of 0 \<Rightarrow> True | Suc e \<Rightarrow> replicate (db + da) False ! e\<rbrakk>
       \<Longrightarrow> db = 0"
    by (metis Suc_le_eq le_add1 nat.case(2) nth_replicate old.nat.exhaust)
  with assms i
  show "to_bl ((2::'a word) ^ n) ! i = (replicate (LENGTH('a) - Suc n) False @ True # replicate n False) ! i"
    by (auto simp add: nth_append to_bl_nth word_size bit_simps not_less nth_Cons le_diff_conv split: nat_diff_split)
qed (use assms in auto)

lemma xor_2p_to_bl:
  fixes x::"'a::len word"
  shows "to_bl (x XOR 2^n) =
  (if n < LENGTH('a)
   then take (LENGTH('a)-Suc n) (to_bl x) @ (\<not>rev (to_bl x)!n) # drop (LENGTH('a)-n) (to_bl x)
   else to_bl x)"
proof -
  have "map (bit (x XOR 2 ^ n)) (rev [0..<LENGTH('a)]) = map (bit x) (rev [Suc n..<LENGTH('a)]) @ (\<not> rev (map (bit x) (rev [0..<LENGTH('a)])) ! n) # map (bit x) (rev [0..<n])"
    if "n < LENGTH('a)"
    using that
    by (intro nth_equalityI) (auto simp: bit_simps rev_nth nth_append Suc_diff_Suc)
  then show ?thesis
    by (auto simp: to_bl_eq_rev take_map drop_map take_rev drop_rev bit_simps)
qed

lemma is_aligned_replicateD:
  "\<lbrakk> is_aligned (w::'a::len word) n; n \<le> LENGTH('a) \<rbrakk>
     \<Longrightarrow> \<exists>xs. to_bl w = xs @ replicate n False \<and> length xs = size w - n"
  by (metis is_aligned_replicate length_take min_minus word_bl_Rep' word_size)

text \<open>right-padding a word to a certain length\<close>

definition
  "bl_pad_to bl sz \<equiv> bl @ (replicate (sz - length bl) False)"

lemma bl_pad_to_length:
  assumes lbl: "length bl \<le> sz"
  shows   "length (bl_pad_to bl sz) = sz"
  using lbl by (simp add: bl_pad_to_def)

lemma bl_pad_to_prefix:
  "prefix bl (bl_pad_to bl sz)"
  by (simp add: bl_pad_to_def)

lemma of_bl_length:
  "length xs < LENGTH('a) \<Longrightarrow> of_bl xs < (2 :: 'a::len word) ^ length xs"
  by (simp add: of_bl_length_less)

lemma of_bl_mult_and_not_mask_eq:
  fixes a :: "'a::len word"
  assumes "is_aligned a n"
      and n: "length b + m \<le> n"
    shows "a + of_bl b * (2^m) AND NOT(mask n) = a"
proof -
  obtain q where \<open>a = push_bit n (word_of_nat q)\<close> \<open>q < 2 ^ (LENGTH('a) - n)\<close>
    using assms is_alignedE' by blast
  with n have "push_bit m (of_bl b) = take_bit n a OR take_bit n (push_bit m (of_bl b))"
    unfolding take_bit_push_bit
    by (intro bit_word_eqI) (auto simp: bit_simps)
  with assms show ?thesis
    by (simp add: and_not_eq_minus_and mask_add_aligned mask_zero push_bit_eq_mult take_bit_eq_mask)
qed

lemma bin_to_bl_of_bl_eq:
  fixes a :: "'a::len word"
  assumes "is_aligned a n"
      and n: "length b + c \<le> n"
      and "length b + c < LENGTH('a)"
    shows "bin_to_bl (length b) (uint ((a + of_bl b * 2^c) >> c)) = b"
proof -
  obtain q where q: \<open>a = push_bit n (word_of_nat q)\<close> \<open>q < 2 ^ (LENGTH('a) - n)\<close>
    using assms is_alignedE' by blast
  with n assms have "bin_to_bl_aux (length b) (uint (a OR push_bit c (of_bl b) >> c)) [] = b"
    by (intro nth_equalityI) (auto simp: nth_bin_to_bl bit_simps rev_nth simp flip: bin_to_bl_def)
  with assms q show ?thesis
    apply (simp flip: push_bit_eq_mult take_bit_eq_mask)
    by (smt (verit, best) bit_of_bl_iff bit_push_bit_iff is_aligned_imp_not_bit less_diff_conv2 disjunctive_add is_aligned_weaken)
qed

(* casting a long word to a shorter word and casting back to the long word
   is equal to the original long word -- if the word is small enough.
  'l is the longer word.
  's is the shorter word.
*)
lemma bl_cast_long_short_long_ingoreLeadingZero_generic:
  "\<lbrakk> length (dropWhile Not (to_bl w)) \<le> LENGTH('s); LENGTH('s) \<le> LENGTH('l) \<rbrakk> \<Longrightarrow>
   (of_bl :: _ \<Rightarrow> 'l::len word) (to_bl ((of_bl::_ \<Rightarrow> 's::len word) (to_bl w))) = w"
  by (rule word_uint_eqI) (simp add: uint_of_bl_is_bl_to_bin uint_of_bl_is_bl_to_bin_drop)

(*
 Casting between longer and shorter word.
  'l is the longer word.
  's is the shorter word.
 For example: 'l::len word is 128 word (full ipv6 address)
              's::len word is 16 word (address piece of ipv6 address in colon-text-representation)
*)
corollary ucast_short_ucast_long_ingoreLeadingZero:
  "\<lbrakk> length (dropWhile Not (to_bl w)) \<le> LENGTH('s); LENGTH('s) \<le> LENGTH('l) \<rbrakk> \<Longrightarrow>
   (ucast:: 's::len word \<Rightarrow> 'l::len word) ((ucast:: 'l::len word \<Rightarrow> 's::len word) w) = w"
  by (simp add: bl_cast_long_short_long_ingoreLeadingZero_generic ucast_bl)

lemma length_drop_mask:
  fixes w::"'a::len word"
  shows "length (dropWhile Not (to_bl (w AND mask n))) \<le> n"
proof -
  have "length (takeWhile Not (replicate n False @ ls)) = n + length (takeWhile Not ls)"
    for ls n by(subst takeWhile_append2) simp+
  then show ?thesis
    unfolding bl_and_mask by (simp add: dropWhile_eq_drop)
qed

lemma map_bits_rev_to_bl:
  "map (bit x) [0..<size x] = rev (to_bl x)"
  by (auto simp: list_eq_iff_nth_eq test_bit_bl word_size)

lemma of_bl_length2:
  "length xs + c < LENGTH('a) \<Longrightarrow> of_bl xs * 2^c < (2::'a::len word) ^ (length xs + c)"
  by (simp add: of_bl_length word_less_power_trans2)

lemma of_bl_max:
  "(of_bl xs :: 'a::len word) \<le> mask (length xs)"
proof -
  define ys where \<open>ys = rev xs\<close>
  have \<open>take_bit (length ys) (horner_sum of_bool 2 ys :: 'a word) = horner_sum of_bool 2 ys\<close>
    by transfer (simp add: take_bit_horner_sum_bit_eq min_def)
  then have \<open>(of_bl (rev ys) :: 'a word) \<le> mask (length ys)\<close>
    by (simp only: of_bl_rev_eq less_eq_mask_iff_take_bit_eq_self)
  with ys_def show ?thesis
    by simp
qed

text\<open>Some auxiliaries for sign-shifting by the entire word length or more\<close>

lemma sshiftr_clamp_pos:
  assumes "LENGTH('a) \<le> n" "0 \<le> sint x"
  shows "(x::'a::len word) >>> n = 0"
  using assms by (auto simp: bit_simps bit_last_iff bit_word_eqI)

lemma sshiftr_clamp_neg:
  assumes
    "LENGTH('a) \<le> n"
    "sint x < 0"
  shows "(x::'a::len word) >>> n = -1"
  using assms by (auto simp: bit_simps bit_last_iff bit_word_eqI)

lemma sshiftr_clamp:
  assumes "LENGTH('a) \<le> n"
  shows "(x::'a::len word) >>> n = x >>> LENGTH('a)"
  using assms by (auto simp: bit_simps bit_last_iff bit_word_eqI)

text\<open>
Like @{thm shiftr1_bl_of}, but the precondition is stronger because we need to pick the msb out of
the list.
\<close>
lemma sshiftr1_bl_of:
  "length bl = LENGTH('a) \<Longrightarrow>
    sshiftr1 (of_bl bl::'a::len word) = of_bl (hd bl # butlast bl)"
  by (simp add: bl_sshiftr1 word_bl.Abs_inverse word_bl.Rep_eqD)

text\<open>
Like @{thm sshiftr1_bl_of}, with a weaker precondition.
We still get a direct equation for @{term \<open>sshiftr1 (of_bl bl)\<close>}, it's just uglier.
\<close>
lemma sshiftr1_bl_of':
  "LENGTH('a) \<le> length bl \<Longrightarrow>
    sshiftr1 (of_bl bl::'a::len word) =
    of_bl (hd (drop (length bl - LENGTH('a)) bl) # butlast (drop (length bl - LENGTH('a)) bl))"
  by (metis diff_diff_cancel length_drop of_bl_drop' sshiftr1_bl_of)

text\<open>
Like @{thm shiftr_bl_of}.
\<close>
lemma sshiftr_bl_of:
  assumes "length bl = LENGTH('a)"
  shows "(of_bl bl::'a::len word) >>> n = of_bl (replicate n (hd bl) @ take (length bl - n) bl)"
proof -
  from assms obtain b bs where \<open>bl = b # bs\<close>
    by (cases bl) simp_all
  then have *: \<open>bl ! 0 \<longleftrightarrow> b\<close> \<open>hd bl \<longleftrightarrow> b\<close>
    by simp_all
  show ?thesis
    using assms * by (intro bit_word_eqI) (auto simp: bit_simps nth_append rev_nth not_less)
qed

text\<open>Like @{thm shiftr_bl}\<close>
lemma sshiftr_bl: "x >>> n \<equiv> of_bl (replicate n (msb x) @ take (LENGTH('a) - n) (to_bl x))"
  for x :: "'a::len word"
  unfolding word_msb_alt
  by (smt (verit) length_to_bl_eq sshiftr_bl_of word_bl.Rep_inverse)

end

lemma of_bl_drop_eq_take_bit:
  \<open>of_bl (drop n xs) = take_bit (length xs - n) (of_bl xs)\<close>
  by (simp add: of_bl_drop take_bit_eq_mask)

lemma of_bl_take_to_bl_eq_drop_bit:
  \<open>of_bl (take n (to_bl w)) = drop_bit (LENGTH('a) - n) w\<close>
    if \<open>n \<le> LENGTH('a)\<close>
    for w :: \<open>'a::len word\<close>
  using that shiftr_bl [of w \<open>LENGTH('a) - n\<close>] by (simp add: shiftr_def)

end
