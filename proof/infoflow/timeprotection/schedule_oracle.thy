(*
 * Copyright 2021, Data61, CSIRO (ABN 41 687 119 230) and UNSW (ABN 57 195 873 179).
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory schedule_oracle
  imports "Lib.EquivValid" 
begin

type_synonym time = nat

type_synonym 'd schedule_list = "(time \<times> 'd) list"

locale schedule_oracle =
  fixes domain_type :: "'d itself"
  fixes sched_list :: "'d schedule_list"
  fixes slice_min :: time
  assumes schedlist_mintime : "\<forall> (t, d) \<in> set sched_list. t > slice_min"
  assumes schedlist_notempty : "length sched_list > 0"
begin



definition
  valid_schedlist :: "'d schedule_list \<Rightarrow> bool" where
 "valid_schedlist lst \<equiv> (\<forall> (t, d) \<in> set lst. t > slice_min) \<and> (length lst > 0)"

lemma valid_schedlist_rotate:
 "valid_schedlist (lst@[e]) = valid_schedlist (e#lst)"
  unfolding valid_schedlist_def apply clarsimp
  done

lemma valid_schedlist_rotate':
 "valid_schedlist (lst@[e]) \<Longrightarrow> valid_schedlist (e#lst)"
  apply (subst (asm) valid_schedlist_rotate, simp)
  done

lemma valid_schedlist_rotate'':
 "valid_schedlist (e#lst) \<Longrightarrow> valid_schedlist (lst@[e])"
  apply (subst (asm) sym [OF valid_schedlist_rotate], simp)
  done

lemma sched_list_is_valid [simp]:
 "valid_schedlist sched_list"
  unfolding valid_schedlist_def
  using schedlist_mintime schedlist_notempty apply auto
  done



\<comment> \<open> unroll the schedule list to the given index, providing each element
     with its time length, current domain, and the clock time at the start
     of that slice. Empty list is for invalid inputs, otherwise always returns
     at least one element. length is k with valid inputs.
     parameters:
     - k:   number of elements left to add
     - tt:  total time 'elapsed' before this list started
     - lst: the schedule list
     valid inputs:
     - list is not empty, and contains no zero times.

     for valid input, the minimum output length is 1
\<close>
fun
  unroll_sched_list_aux :: "nat \<Rightarrow> time \<Rightarrow> 'd schedule_list \<Rightarrow>
                              (time \<times> 'd \<times> time) list" where
 "unroll_sched_list_aux k tt []  = []" |
 "unroll_sched_list_aux k tt ((0, d)#cur)  = []" |
 "unroll_sched_list_aux 0 tt ((t, d)#cur) = [(t, d, tt)]" |
 "unroll_sched_list_aux (Suc k) tt ((t, d)#cur) =
    (t, d, tt)#unroll_sched_list_aux k (tt+t) (cur@[(t, d)])"

\<comment> \<open> given an index, provice sched_list unrolled to that index \<close>
abbreviation
  unroll_sched_list :: "nat \<Rightarrow> (time \<times> 'd \<times> time) list" where
 "unroll_sched_list k \<equiv> unroll_sched_list_aux k 0 sched_list"



\<comment> \<open> similar to unroll_sched_list, but indexed at a current point in time. unrolled list
     contains all slices up to this one and the next one.

     for valid input, the minimum output length is 1     
  \<close>
fun (sequential)
  unroll_sched_list_time_aux :: "time \<Rightarrow> time \<Rightarrow> 'd schedule_list \<Rightarrow>
                              (time \<times> 'd \<times> time) list" where
 "unroll_sched_list_time_aux t tt []            = []" |
 "unroll_sched_list_time_aux t tt ((0, d)#lst)  = []" |
 "unroll_sched_list_time_aux t tt ((ts, d)#lst) = 
                             (if (t<ts)
                            then [(ts, d, tt)]
                            else (ts, d, tt)#unroll_sched_list_time_aux (t-ts) (tt+ts) (lst@[(ts, d)]))"

abbreviation
  unroll_sched_list_time :: "time \<Rightarrow> (time \<times> 'd \<times> time) list" where
 "unroll_sched_list_time t \<equiv> unroll_sched_list_time_aux t 0 sched_list"


\<comment> \<open> get the current slice index from the current time. \<close>
fun              
  index_from_time_aux :: "time \<Rightarrow> 'd schedule_list \<Rightarrow> nat" where
 "index_from_time_aux t []        = 0" |
 "index_from_time_aux t ((0, d)#lst) = 0" |
 "index_from_time_aux t ((ts, d)#lst) = 
                             (if (t<ts)
                            then 0
                            else Suc (index_from_time_aux (t-ts) (lst@[(ts, d)])))"

abbreviation
  index_from_time :: "time \<Rightarrow> nat" where
 "index_from_time t \<equiv> index_from_time_aux t sched_list"

abbreviation
  so_length :: "time \<times> 'd \<times> time \<Rightarrow> time" where
 "so_length z \<equiv> fst z"

abbreviation
  so_domain :: "time \<times> 'd \<times> time \<Rightarrow> 'd" where
 "so_domain z \<equiv> fst $ snd z"

abbreviation
  so_start :: "time \<times> 'd \<times> time \<Rightarrow> time" where
 "so_start z \<equiv> snd $ snd z"

abbreviation
  so_end :: "time \<times> 'd \<times> time \<Rightarrow> time" where
 "so_end z \<equiv> so_start z + so_length z"



\<comment> \<open> getting a list unrolled to a time is the same LENGTH as getting the index from that time \<close>
lemma length_unroll_eq_index [simp]:
 "valid_schedlist lst \<Longrightarrow>
  length (unroll_sched_list_time_aux t tt lst) =
  1+index_from_time_aux t lst"
  apply (induction t tt lst rule:unroll_sched_list_time_aux.induct)
    apply (clarsimp simp:valid_schedlist_def)
   apply (clarsimp simp:valid_schedlist_def)
  apply (clarsimp simp: valid_schedlist_rotate)
  done

lemma length_unroll_eq_input:
 "valid_schedlist lst \<Longrightarrow>
  length (unroll_sched_list_aux k tt lst) = Suc k"
  apply (induction k tt lst rule:unroll_sched_list_aux.induct)
     apply (clarsimp simp:valid_schedlist_def)
    apply (clarsimp simp:valid_schedlist_def)
   apply clarsimp
  apply (clarsimp simp:valid_schedlist_rotate)
  done
  
lemma unroll_index_or_time_aux:
 "unroll_sched_list_time_aux t tt lst =
  unroll_sched_list_aux (index_from_time_aux t lst) tt lst"
  apply (induction t tt lst rule:unroll_sched_list_time_aux.induct; clarsimp)
  done  
  

lemma unroll_index_or_time:
 "unroll_sched_list_time t = unroll_sched_list (index_from_time t)"
  apply (rule unroll_index_or_time_aux)
  done

definition
  same_slice :: "time \<Rightarrow> time \<Rightarrow> bool" where
 "same_slice t1 t2 \<equiv> index_from_time t1 = index_from_time t2"

abbreviation
  slice_start_aux :: "time \<Rightarrow> time \<Rightarrow> 'd schedule_list \<Rightarrow> time" where
 "slice_start_aux t tt lst \<equiv> so_start $ last $ unroll_sched_list_time_aux t tt lst"

definition
  slice_start :: "time \<Rightarrow> time" where
 "slice_start t \<equiv> so_start $ last $ unroll_sched_list_time t"

lemma slice_start_def2:
 "slice_start t = slice_start_aux t 0 sched_list"
  by (simp add: slice_start_def)

abbreviation
  slice_length_aux :: "time \<Rightarrow> time \<Rightarrow> 'd schedule_list \<Rightarrow> time" where
 "slice_length_aux t tt lst \<equiv> so_length $ last $ unroll_sched_list_time_aux t tt lst"

definition
  slice_length :: "time \<Rightarrow> time" where
 "slice_length t \<equiv> so_length $ last $ unroll_sched_list_time t"

lemma slice_length_def2:
 "slice_length t \<equiv> slice_length_aux t 0 sched_list"
  using slice_length_def by auto

lemma unroll_never_empty:
 "valid_schedlist lst \<Longrightarrow>
  unroll_sched_list_time_aux t tt lst \<noteq> []"
  by (metis Zero_not_Suc length_unroll_eq_index list.size(3) plus_1_eq_Suc)

lemma unroll_entries_from_schedlist_aux:
 "valid_schedlist lst \<Longrightarrow>
  i = (index_from_time_aux t lst) \<Longrightarrow>
  (l, d, tt') \<in> set (unroll_sched_list_aux i tt lst) \<Longrightarrow> (l, d) \<in> set lst"
  apply (induction i tt lst arbitrary:t l d tt' rule:unroll_sched_list_aux.induct; clarsimp)
  apply (smt add_Suc_right add_diff_cancel_left' nat.simps(3) plus_1_eq_Suc
             prod.inject set_ConsD unroll_sched_list_aux.simps(4) valid_schedlist_rotate)
  done
  
lemma unroll_entries_from_schedlist:
 "(l, d, tt') \<in> set (unroll_sched_list_time t) \<Longrightarrow> (l, d) \<in> set sched_list"
  apply (subst (asm) unroll_index_or_time)
  apply (rule unroll_entries_from_schedlist_aux; simp)
  done
  
lemma slice_length_gt_slice_min:
 "slice_length t > slice_min"
  unfolding slice_length_def
  apply (prop_tac "(last $ unroll_sched_list_time t) \<in> set (unroll_sched_list_time t)")
   apply (simp add: unroll_never_empty)
  apply (cases "last $ unroll_sched_list_time t", clarsimp)
  apply (drule unroll_entries_from_schedlist)
  using schedlist_mintime apply auto
  done

abbreviation
 "slice_end_aux t tt lst \<equiv> so_end $ last $ unroll_sched_list_time_aux t tt lst"

definition
  slice_end :: "time \<Rightarrow> time" where
 "slice_end t \<equiv> so_end $ last $ unroll_sched_list_time t"

lemma slice_end_def3:
 "slice_end t = slice_end_aux t 0 sched_list"
  apply (clarsimp simp:slice_end_def)
  done

definition
  slice_domain :: "time \<Rightarrow> 'd" where
 "slice_domain t \<equiv> so_domain $ last $ unroll_sched_list_time t"

definition
  slice_next_domain :: "time \<Rightarrow> 'd" where
 "slice_next_domain t \<equiv> slice_domain (slice_end t)"

abbreviation
  time_since_slice_aux :: "time \<Rightarrow> time \<Rightarrow> 'd schedule_list \<Rightarrow> time" where
 "time_since_slice_aux t tt lst \<equiv> t - (slice_start_aux t tt lst - tt)"

definition
  time_since_slice :: "time \<Rightarrow> time" where
 "time_since_slice t \<equiv> t - slice_start t"

lemma time_since_slice_def2:
 "time_since_slice t = time_since_slice_aux t 0 sched_list"
  by (simp add: slice_start_def2 time_since_slice_def)


definition
  next_slice_domain :: "time \<Rightarrow> 'd" where
 "next_slice_domain t \<equiv> so_domain $ last $ unroll_sched_list (1+index_from_time t)"

(* definition ss_start where "ss_start \<equiv> so_start" *)
(* definition ss_end where "ss_end \<equiv> so_end" *)

lemma start_zero_list:
 "valid_schedlist lst \<Longrightarrow>
  so_start (last (unroll_sched_list_aux 0 tt lst)) = tt"
  apply (rule unroll_sched_list_aux.cases [where x="(0, tt, lst)"]; clarsimp)
   apply (clarsimp simp:valid_schedlist_def)
  apply (clarsimp simp:valid_schedlist_def)
  done

lemma start_is_prev_end_aux:
 "valid_schedlist lst \<Longrightarrow>
  sk = Suc k \<Longrightarrow>
  (so_end   $ last $ unroll_sched_list_aux k tt lst) =
  (so_start $ last $ unroll_sched_list_aux sk tt lst)"
  apply (induction k tt lst arbitrary:sk rule:unroll_sched_list_aux.induct; clarsimp)
     apply (clarsimp simp:valid_schedlist_def)
    apply (clarsimp simp:valid_schedlist_def)
   apply (rule conjI; clarsimp)
    using length_unroll_eq_input
    apply (metis list.size(3) nat.simps(3) valid_schedlist_rotate)
   apply (metis Lib.fun_app_def start_zero_list valid_schedlist_rotate)
  apply (metis length_greater_0_conv length_unroll_eq_input nat.simps(3)
               neq0_conv valid_schedlist_rotate)
  done

lemma start_is_prev_end:
 "(so_start $ last $ unroll_sched_list (Suc k)) =
  (so_end   $ last $ unroll_sched_list k)"
  using start_is_prev_end_aux apply simp
  done

lemma end_is_next_start:
 "(so_end   $ last $ unroll_sched_list k) =
  (so_start $ last $ unroll_sched_list (Suc k))"
  using start_is_prev_end apply simp
  done
  

lemma slice_end_def2:
 "slice_end t \<equiv> so_start $ last $ unroll_sched_list (Suc (index_from_time t))"
  apply (subst start_is_prev_end)
  apply (clarsimp simp:slice_end_def)
  using unroll_index_or_time_aux apply auto
  done

lemma slice_end_start_plus_length:
 "slice_end t1 = slice_start t1 + slice_length t1"
  apply (simp add: slice_end_def slice_length_def2 slice_start_def)
  done

lemma same_slice_same_unroll:
 "same_slice t1 t2 \<Longrightarrow>
  unroll_sched_list_time t1 = unroll_sched_list_time t2"
  apply (simp add: same_slice_def unroll_index_or_time)
  done

lemma same_slice_same_domain:
 "same_slice t1 t2 \<Longrightarrow>
  slice_domain t1 = slice_domain t2"
  apply (clarsimp simp:slice_domain_def same_slice_same_unroll)
  done

lemma same_slice_same_length:
 "same_slice t1 t2 \<Longrightarrow>
  slice_length t1 = slice_length t2"
  apply (clarsimp simp:slice_length_def same_slice_same_unroll)
  done

lemma same_slice_same_start:
 "same_slice t1 t2 \<Longrightarrow>
  slice_start t1 = slice_start t2"
  apply (clarsimp simp:slice_start_def same_slice_same_unroll)
  done

lemma same_slice_same_end:
 "same_slice t1 t2 \<Longrightarrow>
  slice_end t1 = slice_end t2"
  apply (clarsimp simp:slice_end_def same_slice_same_start same_slice_same_unroll)
  done

lemma same_slice_same_next_domain:
 "same_slice t1 t2 \<Longrightarrow>
  slice_next_domain t1 = slice_next_domain t2"
  apply (clarsimp simp:slice_next_domain_def same_slice_same_end)
  done

lemma same_slice_refl [simp]:
 "same_slice t t"
  apply (clarsimp simp:same_slice_def)
  done

lemma same_slice_sym [simp]:
 "same_slice t1 t2 = same_slice t2 t1"
  apply (clarsimp simp:same_slice_def)
  apply auto
  done

lemma same_slice_trans:
 "same_slice t1 t2 \<Longrightarrow>
  same_slice t2 t3 \<Longrightarrow>
  same_slice t1 t3"
  apply (clarsimp simp:same_slice_def)
  done

lemma slice_start_fed:
 "so_start $ last $ unroll_sched_list_time t \<equiv> slice_start t"
  unfolding slice_start_def apply simp
  done


lemma unroll_start_more:
 "valid_schedlist lst \<Longrightarrow>
  (so_start $ last $ unroll_sched_list_aux k
                       tt
                       lst) \<ge> tt"
  apply (induction k tt lst rule:unroll_sched_list_aux.induct; clarsimp)
    apply (clarsimp simp:valid_schedlist_def)
   apply (clarsimp simp:valid_schedlist_def)
  apply (simp add: valid_schedlist_rotate)
  done


lemma unroll_time_of_start_unroll:
 "valid_schedlist lst \<Longrightarrow>
  unroll_sched_list_time_aux ((so_start $ last $ unroll_sched_list_aux i tt lst) - tt) tt lst =
  unroll_sched_list_aux i tt lst"
  apply (induction i tt lst rule:unroll_sched_list_aux.induct)
     apply clarsimp
    apply clarsimp
   apply clarsimp
  apply (subgoal_tac "(so_start $ last $ unroll_sched_list_aux k
                                        (Suc (tt + v))
                                        (cur @ [(Suc v, d)])) - tt
                       \<ge> Suc v")
   apply (simp add: valid_schedlist_rotate)
  apply clarsimp
  apply (prop_tac "valid_schedlist (cur @ [(Suc v, d)])")
   using valid_schedlist_rotate apply blast
  apply clarsimp
  apply (metis Lib.fun_app_def diff_diff_left le_simps(3) unroll_start_more zero_less_diff)
  done  

lemma slice_start_of_end:
 "slice_start (slice_end t) = slice_end t"
  unfolding slice_end_def2 slice_start_def
  using unroll_time_of_start_unroll
  apply (metis minus_nat.diff_0 sched_list_is_valid)
  done

lemma time_since_next_slice_zero:
 "time_since_slice (slice_end t) = 0"
  unfolding time_since_slice_def
  apply (subst slice_start_of_end)
  apply linarith
  done

lemma same_slice_def2:
 "same_slice t1 t2 \<equiv> unroll_sched_list_time t1 = unroll_sched_list_time t2"
  by (smt add_left_cancel length_unroll_eq_index same_slice_def
          sched_list_is_valid unroll_index_or_time_aux)


lemma same_slice_plus_right_aux_aux:
 "valid_schedlist lst \<Longrightarrow>
  t1 - (so_start (last (unroll_sched_list_time_aux t1 tt lst))-tt) + td
     < so_length (last (unroll_sched_list_time_aux t1 tt lst)) \<Longrightarrow>
  (unroll_sched_list_time_aux t1 tt lst) = (unroll_sched_list_time_aux (t1+td) tt lst)"
  apply (induction t1 tt lst rule:unroll_sched_list_time_aux.induct)
    apply clarsimp
   apply clarsimp
  apply clarsimp
  apply (rule conjI; clarsimp)
  apply (prop_tac "valid_schedlist (lst @ [(Suc v, d)])")
   apply (subst valid_schedlist_rotate, assumption)
  apply clarsimp
  apply (frule_tac t="t-Suc v" and tt="Suc (tt+v)" and lst="lst@_" in unroll_never_empty)
  apply clarsimp
  done

lemma same_slice_plus_right_aux:
 "time_since_slice t1 + td < slice_length t1 \<Longrightarrow>
  same_slice t1 (t1+td)"
  unfolding time_since_slice_def2
  apply (clarsimp simp:same_slice_def2 slice_start_def slice_length_def)
  using same_slice_plus_right_aux_aux apply auto
  done

lemma same_slice_plus_right:
 "time_since_slice t1 \<le> t1_max \<Longrightarrow>
  td < td_max \<Longrightarrow>
  t1_max+td_max \<le> slice_length t1 \<Longrightarrow>
  same_slice t1 (t1+td)"
  apply (simp add: same_slice_plus_right_aux)
  done

lemma same_slice_plus_right':
 "time_since_slice t1 \<le> t1_max \<Longrightarrow>
  td \<le> td_max \<Longrightarrow>
  t1_max+td_max < slice_length t1 \<Longrightarrow>
  same_slice t1 (t1+td)"
  apply (simp add: same_slice_plus_right_aux)
  done



  

\<comment> \<open> almost the final form of this theorem - just need to turn time_since_slice into
     slice_userend + q form after this \<close>
lemma same_slice_plus_gen:
 "same_slice t1 t1' \<Longrightarrow>
  time_since_slice t1  \<le> t1_max \<Longrightarrow>
  time_since_slice t1' \<le> t1_max \<Longrightarrow>
  td  < td_max \<Longrightarrow>
  td' < td_max \<Longrightarrow>
  t1_max + td_max \<le> slice_length t1 \<Longrightarrow>
  same_slice (t1 + td) (t1' + td')"
  apply (prop_tac "same_slice t1 (t1 + td)")
   apply (erule(2) same_slice_plus_right)
  apply (prop_tac "same_slice t1' (t1' + td')")
   apply (erule(1) same_slice_plus_right)
   apply (drule same_slice_same_length, simp)
  apply (simp add: same_slice_def2)
  done



lemma slice_start_reduces_aux:
 "valid_schedlist lst \<Longrightarrow>
  slice_start_aux t1 tt lst - tt \<le> t1"
  apply (induct t1 tt lst rule:unroll_sched_list_time_aux.induct)
    apply (clarsimp simp:valid_schedlist_def)
   apply (clarsimp simp:valid_schedlist_def)
  using add.left_commute unroll_never_empty valid_schedlist_rotate apply auto
  done

lemma slice_start_reduces:
 "slice_start t1 \<le> t1"
  apply (subst sym [OF diff_zero])
  unfolding slice_start_def2
  apply (rule slice_start_reduces_aux)
  apply (rule sched_list_is_valid)
  done

lemma slice_start_plus_time_since_slice:
 "t1 = slice_start t1 + time_since_slice t1"
  apply (clarsimp simp:time_since_slice_def)
  using slice_start_reduces apply simp
  done

lemma same_slice_time_since_slice_increase:
 "same_slice t1 (t1 + td) \<Longrightarrow>
  td > 0 \<Longrightarrow>
  time_since_slice t1 < time_since_slice (t1 + td)"
  apply (drule same_slice_same_start)
  apply (simp add:time_since_slice_def)
  apply (metis diff_less_mono less_add_same_cancel1 slice_start_reduces)
  done


lemma slice_end_aux_lastcase:
 "valid_schedlist ((v, d) # lst) \<Longrightarrow>
  v > 0 \<Longrightarrow>
  t \<ge> v \<Longrightarrow>
  slice_end_aux t tt ((v, d) # lst) = slice_end_aux (t - v) (tt + v) (lst @ [(v, d)])"
  apply (cases "(t, tt, ((v, d) # lst))" rule:unroll_sched_list_time_aux.cases)
    apply clarsimp
   apply clarsimp
  apply clarsimp
  apply (drule valid_schedlist_rotate'')
  apply (drule_tac t="t-Suc va" and tt="Suc (tt + va)" in unroll_never_empty)
  apply clarsimp
  done


lemma time_since_slice_less_length_aux_helper:
 "xxx > tt+v \<Longrightarrow>
  (t::nat) - Suc (v + (xxx - Suc (tt + v))) = (t - (xxx - tt))"
  apply simp
  done

lemma time_since_slice_less_length_aux:
 "valid_schedlist lst \<Longrightarrow>
  time_since_slice_aux t tt lst < slice_length_aux t tt lst"
  apply (induct t tt lst rule:unroll_sched_list_time_aux.induct)
    apply (clarsimp simp:valid_schedlist_def)
   apply (clarsimp simp:valid_schedlist_def)
  apply (frule valid_schedlist_rotate'')
  apply (case_tac "t < Suc v"; clarsimp)
  apply (intro conjI; clarsimp)
   using unroll_never_empty apply blast
  apply (subst (asm) time_since_slice_less_length_aux_helper)
   defer
   apply clarsimp
  apply (metis Lib.fun_app_def Suc_le_eq unroll_index_or_time_aux unroll_start_more)
  done

lemma time_since_slice_less_length:
 "time_since_slice t < slice_length t"
  unfolding time_since_slice_def2 slice_length_def
  apply (rule time_since_slice_less_length_aux)
  apply (rule sched_list_is_valid)
  done

lemma slice_end_gt:
 "slice_end t > t"
  using time_since_slice_less_length slice_end_start_plus_length
        slice_start_plus_time_since_slice
  apply (metis nat_add_left_cancel_less)
  done

lemma slice_end_flatsteps_aux:
  "\<lbrakk>t + delta < slice_end t\<rbrakk> \<Longrightarrow> slice_end (t+delta) = slice_end t"
  apply (smt (verit, best) Nat.add_diff_assoc2 add_diff_cancel_left'
    canonically_ordered_monoid_add_class.lessE minus_nat.simps(1) nat_add_left_cancel_less
    same_slice_plus_right_aux schedule_oracle.same_slice_def2
    schedule_oracle.slice_end_start_plus_length schedule_oracle.slice_start_def
    schedule_oracle.slice_start_reduces schedule_oracle_axioms slice_end_def3 slice_end_gt
    time_since_slice_def2)
  done

lemma slice_end_flatsteps:
  "\<lbrakk>t \<le> t'; t' < slice_end t\<rbrakk> \<Longrightarrow> slice_end t' = slice_end t"
  using slice_end_flatsteps_aux le_Suc_ex apply blast
  done

end




(* a schedule oracle, but where a slice's start might be delayed by up to
  `max_delay` time units. We therefore offset slices and redefine some properties
  and synchronicities such that the first `max_delay` time units of a slice
  are considered to be part of the previous slice. *)
locale schedule_oracle_delayed = schedule_oracle +
  fixes max_delay :: time
  assumes delay_lt_slice_min: "max_delay \<le> slice_min"
begin

definition next_delayed_start where
  "next_delayed_start t \<equiv> if (time_since_slice t < max_delay)
                        then slice_start t + max_delay
                        else slice_end t"

lemma next_delayed_start_in_future:
  "t < next_delayed_start t"
  apply (metis nat_add_left_cancel_less next_delayed_start_def slice_end_gt
    slice_start_plus_time_since_slice)
  done

lemma lt_slice_start_adjust:
  "t + a < slice_start t + b \<Longrightarrow>
  time_since_slice t + a < b"
  by (metis add.commute less_diff_conv ordered_cancel_comm_monoid_diff_class.diff_diff_right
    slice_start_reduces time_since_slice_def)

lemma next_delayed_start_flatsteps_aux:
  "\<lbrakk>t + delta < next_delayed_start t\<rbrakk> \<Longrightarrow> next_delayed_start (t+delta) = next_delayed_start t"
  unfolding next_delayed_start_def
  apply (smt (verit, ccfv_SIG) add_less_cancel_left delay_lt_slice_min le_add1 le_eq_less_or_eq
    lt_slice_start_adjust order_less_trans same_slice_plus_right_aux same_slice_same_start
    slice_start_plus_time_since_slice schedule_oracle_axioms slice_end_flatsteps_aux
    slice_end_start_plus_length slice_length_gt_slice_min)
  done

lemma next_delayed_start_flatsteps:
  "\<lbrakk>t \<le> t'; t' < next_delayed_start t\<rbrakk> \<Longrightarrow> next_delayed_start t' = next_delayed_start t"
  using le_Suc_ex next_delayed_start_flatsteps_aux apply auto
  done

end






\<comment> \<open>a variation of schedule_oracle where the start of a slice is when a user starts executing,
    and the last section of a slice (contained within switch_WCET) is the domain-switch\<close>
locale schedule_oracle_switch_at_end = schedule_oracle + 
  fixes switch_WCET :: time
  assumes switch_WCET_less_slice_min : "switch_WCET < slice_min"
begin

definition
  slice_userend :: "time \<Rightarrow> time" where
 "slice_userend t \<equiv> slice_end t - switch_WCET"

lemma slice_length_gt_switch_WCET:
  "slice_length t > switch_WCET"
  using order_less_trans slice_length_gt_slice_min switch_WCET_less_slice_min by blast

lemma slice_lt_rearrange:
 "(t1 \<le> slice_userend t1) = (time_since_slice t1 \<le> (slice_length t1 - switch_WCET))"
  unfolding time_since_slice_def slice_userend_def slice_end_start_plus_length
  apply (subgoal_tac "slice_length t1 > switch_WCET")
   apply linarith
  apply (rule slice_length_gt_switch_WCET)
  done

lemma same_slice_plus_right_specific:
 "t1 \<le> slice_userend t1 \<Longrightarrow>
  t2 = t1 + td \<Longrightarrow>
  td < switch_WCET \<Longrightarrow>
  same_slice t1 t2"
  apply (subst (asm) slice_lt_rearrange)
  apply (drule(1) same_slice_plus_right [where t1_max="slice_length t1 - switch_WCET"
                                        and td=td and td_max="switch_WCET"])
   apply (simp add: less_imp_le_nat slice_length_gt_switch_WCET)
  apply simp
  done

lemma slice_lt_rearrange2:
 "(t1 \<le> slice_userend t1 + q) = (time_since_slice t1 \<le> (slice_length t1 - switch_WCET) + q)"
  unfolding time_since_slice_def slice_userend_def slice_end_start_plus_length
  apply (prop_tac "slice_length t1 > switch_WCET")
   apply (rule slice_length_gt_switch_WCET)
  apply linarith
  done

lemma same_slice_plus_right_specific2:
 "t1 \<le> slice_userend t1 + q \<Longrightarrow>
  t2 = t1 + td \<Longrightarrow>
  q + td < switch_WCET \<Longrightarrow>
  same_slice t1 t2"
  apply (subst (asm) slice_lt_rearrange2)
  apply (drule same_slice_plus_right [where t1_max="_"
                                        and td=td and td_max="switch_WCET-q"])
    apply (simp add: less_imp_le_nat slice_length_gt_switch_WCET)
   apply (smt ab_semigroup_add_class.add_ac(1) add.commute diff_add eq_iff
              le_add1 less_imp_le_nat slice_length_gt_switch_WCET)
  apply simp
  done

lemma same_slice_plus:
 "same_slice t1 t1' \<Longrightarrow>
  t1 \<le> slice_userend t1+q \<Longrightarrow>
  t1' \<le> slice_userend t1'+q \<Longrightarrow>
  td \<le> td_max \<Longrightarrow>
  td' \<le> td_max \<Longrightarrow>
  q + td_max < switch_WCET \<Longrightarrow>
  same_slice (t1 + td) (t1' + td')"
  apply (prop_tac "same_slice t1 (t1 + td)")
   apply (erule same_slice_plus_right_specific2, rule refl, linarith)
  apply (prop_tac "same_slice t1' (t1' + td')")
   apply (erule same_slice_plus_right_specific2, rule refl, linarith)
  apply (simp add: same_slice_def2)
  done

lemma same_slice_plus_noq:
 "same_slice t1 t1' \<Longrightarrow>
  t1 \<le> slice_userend t1 \<Longrightarrow>
  t1' \<le> slice_userend t1' \<Longrightarrow>
  td \<le> td_max \<Longrightarrow>
  td' \<le> td_max \<Longrightarrow>
  td_max < switch_WCET \<Longrightarrow>
  same_slice (t1 + td) (t1' + td')"
  apply (erule same_slice_plus [where q=0, simplified]; simp)
  done


lemma step_past_userend_not_new_slice:
 "t1 \<le> slice_userend t1 \<Longrightarrow>
  time_since_slice (t1 + td) = 0 \<Longrightarrow>
  0 < td \<Longrightarrow>
  td < switch_WCET \<Longrightarrow>
  False"
  apply (prop_tac "same_slice t1 t1", clarsimp simp:same_slice_def)
  apply (drule same_slice_plus_right_specific [where td=td], rule refl, assumption)
  apply (frule(1) same_slice_time_since_slice_increase)
  apply linarith
  done

end

end