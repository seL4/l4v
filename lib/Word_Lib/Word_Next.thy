(*
 * @TAG(OTHER_BSD)
 *)

section\<open>Increment and Decrement Machine Words Without Wrap-Around\<close>

theory Word_Next
imports
  Aligned
begin

text\<open>Previous and next words addresses, without wrap around.\<close>

definition word_next :: "'a::len word \<Rightarrow> 'a::len word" where
  "word_next a \<equiv> if a = max_word then max_word else a + 1"

definition word_prev :: "'a::len word \<Rightarrow> 'a::len word" where
  "word_prev a \<equiv> if a = 0 then 0 else a - 1"

text\<open>Examples:\<close>

lemma "word_next (2:: 8 word) = 3" by eval
lemma "word_next (255:: 8 word) = 255" by eval
lemma "word_prev (2:: 8 word) = 1" by eval
lemma "word_prev (0:: 8 word) = 0" by eval


lemma plus_one_helper[elim!]:
  "x < n + (1 :: 'a :: len word) \<Longrightarrow> x \<le> n"
  apply (simp add: word_less_nat_alt word_le_nat_alt field_simps)
  apply (case_tac "1 + n = 0")
   apply simp
  apply (subst(asm) unatSuc, assumption)
  apply arith
  done

lemma plus_one_helper2:
  "\<lbrakk> x \<le> n; n + 1 \<noteq> 0 \<rbrakk> \<Longrightarrow> x < n + (1 :: 'a :: len word)"
  by (simp add: word_less_nat_alt word_le_nat_alt field_simps
                unatSuc)

lemma less_x_plus_1:
  fixes x :: "'a :: len word" shows
  "x \<noteq> max_word \<Longrightarrow> (y < (x + 1)) = (y < x \<or> y = x)"
  apply (rule iffI)
   apply (rule disjCI)
   apply (drule plus_one_helper)
   apply simp
  apply (subgoal_tac "x < x + 1")
   apply (erule disjE, simp_all)
  apply (rule plus_one_helper2 [OF order_refl])
  apply (rule notI, drule max_word_wrap)
  apply simp
  done


lemma word_Suc_leq: fixes k::"'a::len word" shows "k \<noteq> max_word \<Longrightarrow> x < k + 1 \<longleftrightarrow> x \<le> k"
  using less_x_plus_1 word_le_less_eq by auto

lemma word_Suc_le: fixes k::"'a::len word" shows "x \<noteq> max_word \<Longrightarrow> x + 1 \<le> k \<longleftrightarrow> x < k"
  by (meson not_less word_Suc_leq)

lemma word_lessThan_Suc_atMost: fixes k::"'a::len word" shows "k \<noteq> max_word \<Longrightarrow> {..< k + 1} = {..k}"
  by(simp add: lessThan_def atMost_def word_Suc_leq)

lemma word_atLeastLessThan_Suc_atLeastAtMost:
  fixes l::"'a::len word" shows "u \<noteq> max_word \<Longrightarrow> {l..< u + 1} = {l..u}"
  by (simp add: atLeastAtMost_def atLeastLessThan_def word_lessThan_Suc_atMost)

lemma word_atLeastAtMost_Suc_greaterThanAtMost: fixes l::"'a::len word"
  shows "m \<noteq> max_word \<Longrightarrow> {m<..u} = {m + 1..u}"
  by(simp add: greaterThanAtMost_def greaterThan_def atLeastAtMost_def atLeast_def word_Suc_le)

lemma word_atLeastLessThan_Suc_atLeastAtMost_union:
  fixes l::"'a::len word"
  assumes "m \<noteq> max_word" and "l \<le> m" and "m \<le> u"
  shows "{l..m} \<union> {m+1..u} = {l..u}"
  proof -
  from ivl_disj_un_two(8)[OF assms(2) assms(3)] have "{l..u} = {l..m} \<union> {m<..u}" by blast
  with assms show ?thesis by(simp add: word_atLeastAtMost_Suc_greaterThanAtMost)
  qed

lemma word_adjacent_union:
  "word_next e = s' \<Longrightarrow> s \<le> e \<Longrightarrow> s' \<le> e' \<Longrightarrow> {s..e} \<union> {s'..e'} = {s .. e'}"
  by (metis Un_absorb2 atLeastatMost_subset_iff ivl_disj_un_two(7) max_word_max
            word_atLeastLessThan_Suc_atLeastAtMost word_le_less_eq word_next_def linorder_not_le)

end
