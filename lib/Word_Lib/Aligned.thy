(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

section "Word Alignment"

theory Aligned
imports
  Word_Lib
  HOL_Lemmas
  More_Divides
begin


definition
  is_aligned :: "'a :: len word \<Rightarrow> nat \<Rightarrow> bool" where
  "is_aligned ptr n \<equiv> 2^n dvd unat ptr"


lemma is_aligned_mask: "(is_aligned w n) = (w && mask n = 0)"
  unfolding is_aligned_def by (rule and_mask_dvd_nat)


lemma is_aligned_to_bl:
  "is_aligned (w :: 'a :: len word) n = (True \<notin> set (drop (size w - n) (to_bl w)))"
  apply (simp add: is_aligned_mask eq_zero_set_bl)
  apply (clarsimp simp: in_set_conv_nth word_size)
  apply (simp add: to_bl_nth word_size cong: conj_cong)
  apply (simp add: diff_diff_less)
  apply safe
   apply (case_tac "n \<le> LENGTH('a)")
    prefer 2
    apply (rule_tac x=i in exI)
    apply clarsimp
   apply (subgoal_tac "\<exists>j < LENGTH('a). j < n \<and> LENGTH('a) - n + j = i")
    apply (erule exE)
    apply (rule_tac x=j in exI)
    apply clarsimp
   apply (thin_tac "w !! t" for t)
   apply (rule_tac x="i + n - LENGTH('a)" in exI)
   apply clarsimp
   apply arith
  apply (rule_tac x="LENGTH('a) - n + i" in exI)
  apply clarsimp
  apply arith
  done

lemma unat_power_lower [simp]:
  assumes nv: "n < LENGTH('a::len)"
  shows "unat ((2::'a::len word) ^ n) = 2 ^ n"
  by (simp add: assms nat_power_eq uint_2p_alt unat_def)

lemma power_overflow:
  "n \<ge> LENGTH('a) \<Longrightarrow> 2 ^ n = (0 :: 'a::len word)"
  by simp

lemma is_alignedI [intro?]:
  fixes x::"'a::len word"
  assumes xv: "x = 2 ^ n * k"
  shows   "is_aligned x n"
proof cases
  assume nv: "n < LENGTH('a)"
  show ?thesis
    unfolding is_aligned_def
  proof (rule dvdI [where k = "unat k mod 2 ^ (LENGTH('a) - n)"])
    from xv
    have "unat x = (unat (2::word32) ^ n * unat k) mod 2 ^ LENGTH('a)"
      using nv
      by (subst (asm) word_unat.Rep_inject [symmetric], simp,
          subst unat_word_ariths, simp)

    also have "\<dots> =  2 ^ n * (unat k mod 2 ^ (LENGTH('a) - n))" using nv
      by (simp add: mult_mod_right power_add [symmetric] add_diff_inverse)

    finally show "unat x = 2 ^ n * (unat k mod 2 ^ (LENGTH('a) - n))" .
  qed
next
  assume "\<not> n < LENGTH('a)"
  with xv
  show ?thesis by (simp add: not_less power_overflow is_aligned_def)
qed

lemma is_aligned_weaken:
  "\<lbrakk> is_aligned w x; x \<ge> y \<rbrakk> \<Longrightarrow> is_aligned w y"
  unfolding is_aligned_def
  by (erule dvd_trans [rotated]) (simp add: le_imp_power_dvd)

lemma nat_power_less_diff:
  assumes lt: "(2::nat) ^ n * q < 2 ^ m"
  shows "q < 2 ^ (m - n)"
  using lt
proof (induct n arbitrary: m)
  case 0
  then show ?case by simp
next
  case (Suc n)

  have ih: "\<And>m. 2 ^ n * q < 2 ^ m \<Longrightarrow> q < 2 ^ (m - n)"
    and prem: "2 ^ Suc n * q < 2 ^ m" by fact+

  show ?case
  proof (cases m)
    case 0
    then show ?thesis using Suc by simp
  next
    case (Suc m')
    then show ?thesis using prem
      by (simp add: ac_simps ih)
  qed
qed

lemma is_alignedE_pre:
  fixes w::"'a::len word"
  assumes aligned: "is_aligned w n"
  shows        rl: "\<exists>q. w = 2 ^ n * (of_nat q) \<and> q < 2 ^ (LENGTH('a) - n)"
proof -
  from aligned obtain q where wv: "unat w = 2 ^ n * q"
    unfolding is_aligned_def ..

  show ?thesis
  proof (rule exI, intro conjI)
    show "q < 2 ^ (LENGTH('a) - n)"
    proof (rule nat_power_less_diff)
      have "unat w < 2 ^ size w" unfolding word_size ..
      then have "unat w < 2 ^ LENGTH('a)" by simp
      with wv show "2 ^ n * q < 2 ^ LENGTH('a)" by simp
    qed

    have r: "of_nat (2 ^ n) = (2::word32) ^ n"
      by (induct n) simp+

    from wv have "of_nat (unat w) = of_nat (2 ^ n * q)" by simp
    then have "w = of_nat (2 ^ n * q)" by (subst word_unat.Rep_inverse [symmetric])
    then show "w = 2 ^ n * (of_nat q)" by (simp add: r)
  qed
qed

lemma is_alignedE:
  "\<lbrakk>is_aligned (w::'a::len word) n;
    \<And>q. \<lbrakk>w = 2 ^ n * (of_nat q); q < 2 ^ (LENGTH('a) - n)\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (auto dest: is_alignedE_pre)

lemma is_aligned_replicate:
  fixes w::"'a::len word"
  assumes aligned: "is_aligned w n"
  and          nv: "n \<le> LENGTH('a)"
  shows   "to_bl w = (take (LENGTH('a) - n) (to_bl w)) @ replicate n False"
proof -
  from nv have rl: "\<And>q. q < 2 ^ (LENGTH('a) - n) \<Longrightarrow>
      to_bl (2 ^ n * (of_nat q :: 'a word)) =
      drop n (to_bl (of_nat q :: 'a word)) @ replicate n False"
    by (metis bl_shiftl le_antisym min_def shiftl_t2n wsst_TYs(3))
  show ?thesis using aligned
    by (auto simp: rl elim: is_alignedE)
qed

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

    from offv show "take (LENGTH('a) - n) (to_bl off) =
                    replicate (LENGTH('a) - n) False"
      by (subst less_is_drop_replicate, assumption) simp
  qed fact
next
  assume "\<not> n \<le> LENGTH('a)"
  with offv show ?thesis by (simp add: power_overflow)
qed

lemma aligned_add_aligned:
  fixes x::"'a::len word"
  assumes aligned1: "is_aligned x n"
  and     aligned2: "is_aligned y m"
  and           lt: "m \<le> n"
  shows   "is_aligned (x + y) m"
proof cases
  assume nlt: "n < LENGTH('a)"
  show ?thesis
    unfolding is_aligned_def dvd_def
  proof -
    from aligned2 obtain q2 where yv: "y = 2 ^ m * of_nat q2"
      and q2v: "q2 < 2 ^ (LENGTH('a) - m)"
      by (auto elim: is_alignedE)

    from lt obtain k where kv: "m + k = n" by (auto simp: le_iff_add)
    with aligned1 obtain q1 where xv: "x = 2 ^ (m + k) * of_nat q1"
      and q1v: "q1 < 2 ^ (LENGTH('a) - (m + k))"
      by (auto elim: is_alignedE)

    have l1: "2 ^ (m + k) * q1 < 2 ^ LENGTH('a)"
      by (rule nat_less_power_trans [OF q1v])
         (subst kv, rule order_less_imp_le [OF nlt])

    have l2: "2 ^ m * q2 < 2 ^ LENGTH('a)"
      by (rule nat_less_power_trans [OF q2v],
          rule order_less_imp_le [OF order_le_less_trans])
         fact+

    have "x = of_nat (2 ^ (m + k) *  q1)" using xv
      by simp

    moreover have "y = of_nat (2 ^ m * q2)" using yv
      by simp

    ultimately have upls: "unat x + unat y = 2 ^ m * (2 ^ k * q1 + q2)"
    proof -
      have f1: "unat x = 2 ^ (m + k) * q1"
        by (metis (no_types) \<open>x = of_nat (2 ^ (m + k) * q1)\<close> l1 nat_mod_lem word_unat.inverse_norm
                             zero_less_numeral zero_less_power)
      have "unat y = 2 ^ m * q2"
        by (metis (no_types) \<open>y = of_nat (2 ^ m * q2)\<close> l2 nat_mod_lem word_unat.inverse_norm
                             zero_less_numeral zero_less_power)
      then show ?thesis
        using f1 by (simp add: power_add semiring_normalization_rules(34))
    qed

    (* (2 ^ k * q1 + q2) *)
    show "\<exists>d. unat (x + y) = 2 ^ m * d"
    proof (cases "unat x + unat y < 2 ^ LENGTH('a)")
      case True

      have "unat (x + y) = unat x + unat y"
        by (subst unat_plus_if', rule if_P) fact

      also have "\<dots> = 2 ^ m * (2 ^ k * q1 + q2)" by (rule upls)
      finally show ?thesis ..
    next
      case False
      then have "unat (x + y) = (unat x + unat y) mod 2 ^ LENGTH('a)"
        by (subst unat_word_ariths(1)) simp

      also have "\<dots> = (2 ^ m * (2 ^ k * q1 + q2)) mod 2 ^ LENGTH('a)"
        by (subst upls, rule refl)

      also
      have "\<dots> = 2 ^ m * ((2 ^ k * q1 +  q2) mod 2 ^ (LENGTH('a) - m))"
      proof -
        have "m \<le> len_of (TYPE('a))"
          by (meson le_trans less_imp_le_nat lt nlt)
        then show ?thesis
          by (metis mult_mod_right ordered_cancel_comm_monoid_diff_class.add_diff_inverse power_add)
      qed

      finally show ?thesis ..
    qed
  qed
next
  assume "\<not> n < LENGTH('a)"
  with assms
  show ?thesis by (simp add: not_less power_overflow is_aligned_mask mask_def)
qed

corollary aligned_sub_aligned:
  "\<lbrakk>is_aligned (x::'a::len word) n; is_aligned y m; m \<le> n\<rbrakk>
   \<Longrightarrow> is_aligned (x - y) m"
  apply (simp del: add_uminus_conv_diff add:diff_conv_add_uminus)
  apply (erule aligned_add_aligned, simp_all)
  apply (erule is_alignedE)
  apply (rule_tac k="- of_nat q" in is_alignedI)
  apply simp
  done

lemma is_aligned_shift:
  fixes k::"'a::len word"
  shows "is_aligned (k << m) m"
proof cases
  assume mv: "m < LENGTH('a)"
  from mv obtain q where mq: "m + q = LENGTH('a)" and "0 < q"
    by (auto dest: less_imp_add_positive)

  have "(2::nat) ^ m dvd unat (k << m)"
  proof
    have kv: "(unat k div 2 ^ q) * 2 ^ q + unat k mod 2 ^ q = unat k"
      by (rule div_mult_mod_eq)

    have "unat (k << m) = unat (2 ^ m * k)" by (simp add: shiftl_t2n)
    also have "\<dots> = (2 ^ m * unat k) mod (2 ^ LENGTH('a))" using mv
      by (subst unat_word_ariths(2))+ simp
    also have "\<dots> = 2 ^ m * (unat k mod 2 ^ q)"
      by (subst mq [symmetric], subst power_add, subst mod_mult2_eq) simp
    finally show "unat (k << m) = 2 ^ m * (unat k mod 2 ^ q)" .
  qed

  then show ?thesis by (unfold is_aligned_def)
next
  assume "\<not> m < LENGTH('a)"
  then show ?thesis
    by (simp add: not_less power_overflow is_aligned_mask mask_def
                  shiftl_zero_size word_size)
qed

lemma word_mod_by_0: "k mod (0::'a::len word) = k"
  by (simp add: word_arith_nat_mod)

lemma aligned_mod_eq_0:
  fixes p::"'a::len word"
  assumes al: "is_aligned p sz"
  shows   "p mod 2 ^ sz = 0"
proof cases
  assume szv: "sz < LENGTH('a)"
  with al
  show ?thesis
    unfolding is_aligned_def
    by (simp add: and_mask_dvd_nat p2_gt_0 word_mod_2p_is_mask)
next
  assume "\<not> sz < LENGTH('a)"
  with al show ?thesis
    by (simp add: not_less power_overflow is_aligned_mask mask_def word_mod_by_0)
qed

lemma is_aligned_triv: "is_aligned (2 ^ n ::'a::len word) n"
  by (rule is_alignedI [where k = 1], simp)

lemma is_aligned_mult_triv1: "is_aligned (2 ^ n * x  ::'a::len word) n"
  by (rule is_alignedI [OF refl])

lemma is_aligned_mult_triv2: "is_aligned (x * 2 ^ n ::'a::len word) n"
  by (subst mult.commute, simp add: is_aligned_mult_triv1)

lemma word_power_less_0_is_0:
  fixes x :: "'a::len word"
  shows "x < a ^ 0 \<Longrightarrow> x = 0" by simp

lemma nat_add_offset_less:
  fixes x :: nat
  assumes yv: "y < 2 ^ n"
  and     xv: "x < 2 ^ m"
  and     mn: "sz = m + n"
  shows   "x * 2 ^ n + y < 2 ^ sz"
proof (subst mn)
  from yv obtain qy where "y + qy = 2 ^ n" and "0 < qy"
    by (auto dest: less_imp_add_positive)

  have "x * 2 ^ n + y < x * 2 ^ n + 2 ^ n" by simp fact+
  also have "\<dots> = (x + 1) * 2 ^ n" by simp
  also have "\<dots> \<le> 2 ^ (m + n)" using xv
    by (subst power_add) (rule mult_le_mono1, simp)
  finally show "x * 2 ^ n + y < 2 ^ (m + n)" .
qed

lemma is_aligned_no_wrap:
  fixes off :: "'a::len word"
  fixes ptr :: "'a::len word"
  assumes al: "is_aligned ptr sz"
  and    off: "off < 2 ^ sz"
  shows  "unat ptr + unat off < 2 ^ LENGTH('a)"
proof -
  have szv: "sz < LENGTH('a)"
  using off p2_gt_0 word_neq_0_conv by fastforce

  from al obtain q where ptrq: "ptr = 2 ^ sz * of_nat q" and
    qv: "q < 2 ^ (LENGTH('a) - sz)" by (auto elim: is_alignedE)

  show ?thesis
  proof (cases "sz = 0")
    case True
    then show ?thesis using off ptrq qv by clarsimp
  next
    case False
    then have sne: "0 < sz" ..

    show ?thesis
    proof -
      have uq: "unat (of_nat q ::'a::len word) = q"
        apply (subst unat_of_nat)
        apply (rule mod_less)
        apply (rule order_less_trans [OF qv])
        apply (rule power_strict_increasing [OF diff_less [OF sne]])
         apply (simp_all)
        done

      have uptr: "unat ptr = 2 ^ sz * q"
        apply (subst ptrq)
        apply (subst iffD1 [OF unat_mult_lem])
         apply (subst unat_power_lower [OF szv])
         apply (subst uq)
         apply (rule nat_less_power_trans [OF qv order_less_imp_le [OF szv]])
        apply (subst uq)
        apply (subst unat_power_lower [OF szv])
        apply simp
        done

      show "unat ptr + unat off < 2 ^ LENGTH('a)" using szv
        apply (subst uptr)
        apply (subst mult.commute, rule nat_add_offset_less [OF _ qv])
        apply (rule order_less_le_trans [OF unat_mono [OF off] order_eq_refl])
         apply simp_all
        done
    qed
  qed
qed

lemma is_aligned_no_wrap':
  fixes ptr :: "'a::len word"
  assumes al: "is_aligned ptr sz"
  and    off: "off < 2 ^ sz"
  shows  "ptr \<le> ptr + off"
  by (subst no_plus_overflow_unat_size, subst word_size, rule is_aligned_no_wrap) fact+

lemma is_aligned_no_overflow':
  fixes p :: "'a::len word"
  assumes al: "is_aligned p n"
  shows "p \<le> p + (2 ^ n - 1)"
proof cases
  assume "n<LENGTH('a)"
  with al
  have "2^n - (1::'a::len word) < 2^n"
    by (simp add: word_less_nat_alt unat_sub_if_size)
  with al
  show ?thesis by (rule is_aligned_no_wrap')
next
  assume "\<not> n<LENGTH('a)"
  with al
  show ?thesis
  by (simp add: not_less power_overflow is_aligned_mask mask_2pm1)
qed

lemma is_aligned_no_overflow:
  "is_aligned ptr sz \<Longrightarrow> ptr \<le> ptr + 2^sz - 1"
  by (drule is_aligned_no_overflow') (simp add: field_simps)

lemma replicate_not_True:
  "\<And>n. xs = replicate n False \<Longrightarrow> True \<notin> set xs"
  by (induct xs) auto

lemma is_aligned_replicateI:
  "to_bl p = addr @ replicate n False \<Longrightarrow> is_aligned (p::'a::len word) n"
  apply (simp add: is_aligned_to_bl word_size)
  apply (subgoal_tac "length addr = LENGTH('a) - n")
   apply (simp add: replicate_not_True)
  apply (drule arg_cong [where f=length])
  apply simp
  done

lemma to_bl_2p:
  "n < LENGTH('a) \<Longrightarrow>
   to_bl ((2::'a::len word) ^ n) =
   replicate (LENGTH('a) - Suc n) False @ True # replicate n False"
  apply (subst shiftl_1 [symmetric])
  apply (subst bl_shiftl)
  apply (simp add: to_bl_1 min_def word_size)
  done

lemma map_zip_replicate_False_xor:
  "n = length xs \<Longrightarrow> map (\<lambda>(x, y). x = (\<not> y)) (zip xs (replicate n False)) = xs"
  by (induct xs arbitrary: n, auto)

lemma drop_minus_lem:
  "\<lbrakk> n \<le> length xs; 0 < n; n' = length xs \<rbrakk> \<Longrightarrow> drop (n' - n) xs = rev xs ! (n - 1)  # drop (Suc (n' - n)) xs"
proof (induct xs arbitrary: n n')
  case Nil then show ?case by simp
next
  case (Cons y ys)
  from Cons.prems
  show ?case
    apply simp
    apply (cases "n = Suc (length ys)")
     apply (simp add: nth_append)
    apply (simp add: Suc_diff_le Cons.hyps nth_append)
    apply clarsimp
    apply arith
    done
qed

lemma drop_minus:
  "\<lbrakk> n < length xs; n' = length xs \<rbrakk> \<Longrightarrow> drop (n' - Suc n) xs = rev xs ! n  # drop (n' - n) xs"
  apply (subst drop_minus_lem)
     apply simp
    apply simp
   apply simp
  apply simp
  apply (cases "length xs", simp)
  apply (simp add: Suc_diff_le)
  done

lemma xor_2p_to_bl:
  fixes x::"'a::len word"
  shows "to_bl (x xor 2^n) =
  (if n < LENGTH('a)
   then take (LENGTH('a)-Suc n) (to_bl x) @ (\<not>rev (to_bl x)!n) # drop (LENGTH('a)-n) (to_bl x)
   else to_bl x)"
proof -
  have x: "to_bl x = take (LENGTH('a)-Suc n) (to_bl x) @ drop (LENGTH('a)-Suc n) (to_bl x)"
    by simp

  show ?thesis
  apply simp
  apply (rule conjI)
   apply (clarsimp simp: word_size)
   apply (simp add: bl_word_xor to_bl_2p)
   apply (subst x)
   apply (subst zip_append)
    apply simp
   apply (simp add: map_zip_replicate_False_xor drop_minus)
  apply (auto simp add: word_size nth_w2p intro!: word_eqI)
  done
qed

lemma aligned_add_xor:
  assumes al: "is_aligned (x::'a::len word) n'" and le: "n < n'"
  shows "(x + 2^n) xor 2^n = x"
proof cases
  assume "n' < LENGTH('a)"
  with assms show ?thesis
  apply -
  apply (rule word_bl.Rep_eqD)
  apply (subst xor_2p_to_bl)
  apply simp
  apply (subst is_aligned_add_conv, simp, simp add: word_less_nat_alt)+
  apply (simp add: to_bl_2p nth_append)
  apply (cases "n' = Suc n")
   apply simp
   apply (subst is_aligned_replicate [where n="Suc n", simplified, symmetric]; simp)
  apply (subgoal_tac "\<not> LENGTH('a) - Suc n \<le> LENGTH('a) - n'")
   prefer 2
   apply arith
  apply (subst replicate_Suc [symmetric])
  apply (subst replicate_add [symmetric])
  apply (simp add: is_aligned_replicate [simplified, symmetric])
  done
next
  assume "\<not> n' < LENGTH('a)"
  with al show ?thesis
    by (simp add: is_aligned_mask mask_def not_less power_overflow)
qed

lemma is_aligned_0 [simp]:
  "is_aligned p 0"
  by (simp add: is_aligned_def)

lemma is_aligned_replicateD:
  "\<lbrakk> is_aligned (w::'a::len word) n; n \<le> LENGTH('a) \<rbrakk>
     \<Longrightarrow> \<exists>xs. to_bl w = xs @ replicate n False
               \<and> length xs = size w - n"
  apply (subst is_aligned_replicate, assumption+)
  apply (rule exI, rule conjI, rule refl)
  apply (simp add: word_size)
  done

lemma is_aligned_add_mult_multI:
  fixes p :: "'a::len word"
  shows "\<lbrakk>is_aligned p m; n \<le> m; n' = n\<rbrakk> \<Longrightarrow> is_aligned (p + x * 2 ^ n * z) n'"
  apply (erule aligned_add_aligned)
  apply (auto intro: is_alignedI [where k="x*z"])
  done

lemma is_aligned_add_multI:
  fixes p :: "'a::len word"
  shows "\<lbrakk>is_aligned p m; n \<le> m; n' = n\<rbrakk> \<Longrightarrow> is_aligned (p + x * 2 ^ n) n'"
  apply (erule aligned_add_aligned)
  apply (auto intro: is_alignedI [where k="x"])
  done

lemma unat_of_nat_len:
  "x < 2 ^ LENGTH('a) \<Longrightarrow> unat (of_nat x :: 'a::len word) = x"
  by (simp add: word_size unat_of_nat)

lemma is_aligned_no_wrap''':
  fixes ptr :: "'a::len word"
  shows"\<lbrakk> is_aligned ptr sz; sz < LENGTH('a); off < 2 ^ sz \<rbrakk>
         \<Longrightarrow> unat ptr + off < 2 ^ LENGTH('a)"
  apply (drule is_aligned_no_wrap[where off="of_nat off"])
   apply (simp add: word_less_nat_alt)
   apply (erule order_le_less_trans[rotated])
   apply (subst unat_of_nat)
   apply (rule mod_less_eq_dividend)
  apply (subst(asm) unat_of_nat_len)
   apply (erule order_less_trans)
   apply (erule power_strict_increasing)
   apply simp
  apply assumption
  done

lemma is_aligned_get_word_bits:
  fixes p :: "'a::len word"
  shows "\<lbrakk> is_aligned p n; \<lbrakk> is_aligned p n; n < LENGTH('a) \<rbrakk> \<Longrightarrow> P;
           \<lbrakk> p = 0; n \<ge> LENGTH('a) \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (cases "n < LENGTH('a)")
   apply simp
  apply simp
  apply (erule meta_mp)
  apply (clarsimp simp: is_aligned_mask mask_def power_add
                        power_overflow)
  done

lemma aligned_small_is_0:
  "\<lbrakk> is_aligned x n; x < 2 ^ n \<rbrakk> \<Longrightarrow> x = 0"
  apply (erule is_aligned_get_word_bits)
   apply (frule is_aligned_add_conv [rotated, where w=0])
    apply (simp add: is_aligned_def)
   apply simp
   apply (drule is_aligned_replicateD)
    apply simp
   apply (clarsimp simp: word_size)
   apply (subst (asm) replicate_add [symmetric])
   apply (drule arg_cong[where f="of_bl :: bool list \<Rightarrow> 'a::len word"])
   apply simp
  apply (simp only: replicate.simps[symmetric, where x=False]
                    drop_replicate)
  done

corollary is_aligned_less_sz:
  "\<lbrakk>is_aligned a sz; a \<noteq> 0\<rbrakk> \<Longrightarrow> \<not> a < 2 ^ sz"
  by (rule notI, drule(1) aligned_small_is_0, erule(1) notE)

lemma aligned_at_least_t2n_diff:
  "\<lbrakk>is_aligned x n; is_aligned y n; x < y\<rbrakk> \<Longrightarrow> x \<le> y - 2 ^ n"
  apply (erule is_aligned_get_word_bits[where p=y])
   apply (rule ccontr)
   apply (clarsimp simp: linorder_not_le)
   apply (subgoal_tac "y - x = 0")
    apply clarsimp
   apply (rule aligned_small_is_0)
    apply (erule(1) aligned_sub_aligned)
    apply simp
   apply unat_arith
  apply simp
  done

lemma word_sub_1_le:
  "x \<noteq> 0 \<Longrightarrow> x - 1 \<le> (x :: ('a :: len) word)"
  apply (subst no_ulen_sub)
  apply simp
  apply (cases "uint x = 0")
   apply (simp add: uint_0_iff)
  apply (insert uint_ge_0[where x=x])
  apply arith
  done

lemma is_aligned_no_overflow'':
  "\<lbrakk>is_aligned x n; x + 2 ^ n \<noteq> 0\<rbrakk> \<Longrightarrow> x \<le> x + 2 ^ n"
  apply (frule is_aligned_no_overflow')
  apply (erule order_trans)
  apply (simp add: field_simps)
  apply (erule word_sub_1_le)
  done

lemma is_aligned_nth:
  "is_aligned p m = (\<forall>n < m. \<not>p !! n)"
  apply (clarsimp simp: is_aligned_mask bang_eq word_size)
  apply (rule iffI)
   apply clarsimp
   apply (case_tac "n < size p")
    apply (simp add: word_size)
   apply (drule test_bit_size)
   apply simp
  apply clarsimp
  done

lemma range_inter:
  "({a..b} \<inter> {c..d} = {}) = (\<forall>x. \<not>(a \<le> x \<and> x \<le> b \<and> c \<le> x \<and> x \<le> d))"
  by auto

lemma aligned_inter_non_empty:
  "\<lbrakk> {p..p + (2 ^ n - 1)} \<inter> {p..p + 2 ^ m - 1} = {};
     is_aligned p n; is_aligned p m\<rbrakk> \<Longrightarrow> False"
  apply (clarsimp simp only: range_inter)
  apply (erule_tac x=p in allE)
  apply simp
  apply (erule impE)
   apply (erule is_aligned_no_overflow')
  apply (erule notE)
  apply (erule is_aligned_no_overflow)
  done

lemma not_aligned_mod_nz:
  assumes al: "\<not> is_aligned a n"
  shows "a mod 2 ^ n \<noteq> 0"
proof cases
  assume "n < LENGTH('a)"
  with al
  show ?thesis
    apply (simp add: is_aligned_def dvd_eq_mod_eq_0 word_arith_nat_mod)
    apply (erule of_nat_neq_0)
    apply (rule order_less_trans)
     apply (rule mod_less_divisor)
     apply simp
    apply simp
    done
next
  assume "\<not> n < LENGTH('a)"
  with al
  show ?thesis
    by (simp add: is_aligned_mask mask_def not_less power_overflow
                  word_less_nat_alt word_mod_by_0)
qed

lemma nat_add_offset_le:
  fixes x :: nat
  assumes yv: "y \<le> 2 ^ n"
  and     xv: "x < 2 ^ m"
  and     mn: "sz = m + n"
  shows   "x * 2 ^ n + y \<le> 2 ^ sz"
proof (subst mn)
  from yv obtain qy where "y + qy = 2 ^ n"
    by (auto simp: le_iff_add)

  have "x * 2 ^ n + y \<le> x * 2 ^ n + 2 ^ n"
    using yv xv by simp
  also have "\<dots> = (x + 1) * 2 ^ n" by simp
  also have "\<dots> \<le> 2 ^ (m + n)" using xv
    by (subst power_add) (rule mult_le_mono1, simp)
  finally show "x * 2 ^ n + y \<le> 2 ^ (m + n)" .
qed

lemma is_aligned_no_wrap_le:
  fixes ptr::"'a::len word"
  assumes al: "is_aligned ptr sz"
  and    szv: "sz < LENGTH('a)"
  and    off: "off \<le> 2 ^ sz"
  shows  "unat ptr + off \<le> 2 ^ LENGTH('a)"
proof -
  from al obtain q where ptrq: "ptr = 2 ^ sz * of_nat q" and
    qv: "q < 2 ^ (LENGTH('a) - sz)" by (auto elim: is_alignedE)

  show ?thesis
  proof (cases "sz = 0")
    case True
    then show ?thesis using off ptrq qv
      apply (clarsimp)
      apply (erule le_SucE)
       apply (simp add: unat_of_nat)
      apply (simp add: less_eq_Suc_le [symmetric] unat_of_nat)
      done
  next
    case False
    then have sne: "0 < sz" ..

    show ?thesis
    proof -
      have uq: "unat (of_nat q :: 'a word) = q"
        apply (subst unat_of_nat)
        apply (rule mod_less)
        apply (rule order_less_trans [OF qv])
        apply (rule power_strict_increasing [OF diff_less [OF sne]])
        apply simp_all
        done

      have uptr: "unat ptr = 2 ^ sz * q"
        apply (subst ptrq)
        apply (subst iffD1 [OF unat_mult_lem])
        apply (subst unat_power_lower [OF szv])
        apply (subst uq)
        apply (rule nat_less_power_trans [OF qv order_less_imp_le [OF szv]])
        apply (subst uq)
        apply (subst unat_power_lower [OF szv])
        apply simp
        done

      show "unat ptr + off \<le> 2 ^ LENGTH('a)" using szv
        apply (subst uptr)
        apply (subst mult.commute, rule nat_add_offset_le [OF off qv])
        apply simp
        done
    qed
  qed
qed

lemma is_aligned_neg_mask:
  "m \<le> n \<Longrightarrow> is_aligned (x && ~~ mask n) m"
  by (metis and_not_mask is_aligned_shift is_aligned_weaken)

lemma unat_minus:
  "unat (- (x :: ('a :: len) word))
    = (if x = 0 then 0 else (2 ^ size x) - unat x)"
  using unat_sub_if_size[where x="2 ^ size x" and y=x]
  by (simp add: unat_eq_0 word_size)

lemma is_aligned_minus:
  "is_aligned p n \<Longrightarrow> is_aligned (- p) n"
  apply (clarsimp simp: is_aligned_def unat_minus word_size word_neq_0_conv)
  apply (rule dvd_diff_nat, simp_all)
  apply (rule le_imp_power_dvd)
  apply (fold is_aligned_def)
  apply (erule_tac Q="0<p" in contrapos_pp)
  apply (clarsimp simp add: is_aligned_mask mask_def power_overflow)
  done

lemma add_mask_lower_bits:
  "\<lbrakk>is_aligned (x :: 'a :: len word) n;
    \<forall>n' \<ge> n. n' < LENGTH('a) \<longrightarrow> \<not> p !! n'\<rbrakk> \<Longrightarrow> x + p && ~~mask n = x"
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
   apply (clarsimp simp: word_size is_aligned_nth)
   apply (erule_tac x=na in allE)+
   apply simp
  apply (rule word_eqI)
  apply (clarsimp simp: word_size is_aligned_nth word_ops_nth_size le_def)
  apply blast
  done

lemma is_aligned_andI1:
  "is_aligned x n \<Longrightarrow> is_aligned (x && y) n"
  by (simp add: is_aligned_nth)

lemma is_aligned_andI2:
  "is_aligned y n \<Longrightarrow> is_aligned (x && y) n"
  by (simp add: is_aligned_nth)

lemma is_aligned_shiftl:
  "is_aligned w (n - m) \<Longrightarrow> is_aligned (w << m) n"
  by (simp add: is_aligned_nth nth_shiftl)

lemma is_aligned_shiftr:
  "is_aligned w (n + m) \<Longrightarrow> is_aligned (w >> m) n"
  by (simp add: is_aligned_nth nth_shiftr)

lemma is_aligned_shiftl_self:
  "is_aligned (p << n) n"
  by (rule is_aligned_shift)

lemma is_aligned_neg_mask_eq:
  "is_aligned p n \<Longrightarrow> p && ~~ mask n = p"
  by (metis add.left_neutral is_aligned_mask word_plus_and_or_coroll2)

lemma is_aligned_shiftr_shiftl:
  "is_aligned w n \<Longrightarrow> w >> n << n = w"
  by (metis and_not_mask is_aligned_neg_mask_eq)

lemma aligned_shiftr_mask_shiftl:
  "is_aligned x n \<Longrightarrow> ((x >> n) && mask v) << n = x && mask (v + n)"
  apply (rule word_eqI)
  apply (simp add: word_size nth_shiftl nth_shiftr)
  apply (subgoal_tac "\<forall>m. x !! m \<longrightarrow> m \<ge> n")
   apply auto[1]
  apply (clarsimp simp: is_aligned_mask)
  apply (drule_tac x=m in word_eqD)
  apply (frule test_bit_size)
  apply (simp add: word_size)
  done

end
