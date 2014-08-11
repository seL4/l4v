(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory Residual
imports
  Syscall_AC
begin

definition
memory_cleared :: "word32 \<Rightarrow> nat \<Rightarrow> machine_state \<Rightarrow> bool"
where
"memory_cleared ptr bits st \<equiv>
  \<forall>p \<in> {ptr .. ptr + (2 ^ bits) - 1}. underlying_memory st p = 0"

lemma cleanCacheRange_underlying_memory_inv:
  "\<lbrace> \<lambda>s. P (underlying_memory s) \<rbrace>
  cleanCacheRange x y
  \<lbrace> \<lambda>_ s. P (underlying_memory s) \<rbrace>"
  unfolding cleanCacheRange_def machine_op_lift_def 
  apply (simp add: machine_rest_lift_def split_def)
  apply wp
  apply (clarsimp)
  done

lemma memory_cleared_inv_lift:
  assumes underlying_memory_inv: "\<And> P. \<lbrace>\<lambda>s. P (underlying_memory s) \<rbrace> f \<lbrace> \<lambda>_ s. P (underlying_memory s) \<rbrace>"
  shows "\<lbrace> memory_cleared ptr bits \<rbrace> f \<lbrace> \<lambda>_. memory_cleared ptr bits \<rbrace>"
  apply(simp add: valid_def memory_cleared_def)
  apply(cut_tac underlying_memory_inv[simplified valid_def])
  apply(simp)
  done

lemma cleanCacheRange_memory_cleared_inv:
  "\<lbrace> memory_cleared ptr bits \<rbrace>
   cleanCacheRange x y
   \<lbrace> \<lambda>_. memory_cleared ptr bits \<rbrace>"
  by(wp memory_cleared_inv_lift cleanCacheRange_underlying_memory_inv)

definition
  word_cleared :: "machine_word \<Rightarrow> machine_state \<Rightarrow> bool"
  where "word_cleared ptr s \<equiv> let m = underlying_memory s in
    m ptr = 0 \<and> m (ptr + 1) = 0 \<and> m (ptr + 2) = 0 \<and> m (ptr + 3) = 0"

lemma storeWord_zero_word_cleared:
  "\<lbrace> \<top> \<rbrace>
  storeWord x 0
  \<lbrace> \<lambda>_. word_cleared x \<rbrace>"
  unfolding storeWord_def
  by (wp, simp add: word_cleared_def word_rsplit_0)


definition words_cleared :: "word32 set \<Rightarrow> machine_state \<Rightarrow> bool" where
"words_cleared S s \<equiv> \<forall>x\<in>S. word_cleared x s"

lemma storeWord_zero_words_cleared_at:
  "\<lbrace> \<top> \<rbrace>
  storeWord x 0
   \<lbrace>\<lambda>_. words_cleared {x} \<rbrace>"
  apply(rule hoare_strengthen_post)
  apply(rule storeWord_zero_word_cleared)
  apply(simp add: words_cleared_def)
  done

lemma storeWord_zero_words_cleared_other:
  "\<lbrace> words_cleared S \<rbrace>
  storeWord x 0
   \<lbrace> \<lambda>_. words_cleared S \<rbrace>"
  unfolding storeWord_def
  apply wp
  apply (simp add: words_cleared_def word_cleared_def Let_def
                   word_rsplit_0)
  apply auto
  done

lemma words_cleared_union:
  "words_cleared (A \<union> B) = ((words_cleared A) and (words_cleared B))"
  by(auto intro!: ext simp: words_cleared_def pred_conj_def)

lemma storeWord_zero_words_cleared:
  "\<lbrace> words_cleared S \<rbrace>
   storeWord x 0
   \<lbrace> \<lambda>_. words_cleared (S\<union>{x}) \<rbrace>"
  apply(subst words_cleared_union)
  apply(rule hoare_weaken_pre)
   apply(simp add: pred_conj_def)
   apply(rule hoare_vcg_conj_lift)
    apply(rule storeWord_zero_words_cleared_other)
   apply(rule storeWord_zero_words_cleared_at)
  apply simp
  done

lemma mapM_x_storeWord_zero_words_cleared:
  "\<lbrace> words_cleared A \<rbrace>
   mapM_x (\<lambda>p. storeWord p 0) ptrs
   \<lbrace> \<lambda>_. words_cleared (A \<union> (set ptrs)) \<rbrace>"
  apply(induct ptrs arbitrary: A)
   apply(wp mapM_x_wp[OF _ subset_refl] storeWord_zero_words_cleared_other)
   apply simp
  apply(subst mapM_x_Cons)
  apply(wp)
   (* rewrite postcondition to unify with the induction hypothesis *)
   apply(rule_tac Q="\<lambda>_. words_cleared ((A \<union> {a}) \<union> set ptrs)" in hoare_strengthen_post)
    apply assumption
   apply simp
  apply(rule storeWord_zero_words_cleared)
  done


lemma word_range_max:
  "n < word_bits \<Longrightarrow> (p::word32) \<le> (p && ~~ mask n) + (2^n - 1)"
  apply(rule ord_eq_le_trans)
   apply(rule sym)
   apply(rule_tac b="(2 ^ n)::word32" in word_mod_div_equality)
  apply(simp add: neg_mask_is_div)
  apply(rule word_plus_mono_right)
   prefer 2
   apply(rule_tac sz=n in is_aligned_no_wrap')
    apply(rule is_alignedI)
    apply(subst mult.commute, rule refl)
   apply simp
  apply(rule word_less_sub_1)
  apply(rule word_mod_less_divisor)
  apply(rule eq_mask_less)
   apply(simp add: word_log_esimps)
  apply(simp add: word_bits_def)
  done


(* FIXME: cleanup this horrible proof by Toby who hereby takes the blame *)
lemma words_cleared_memory_cleared:
  "\<lbrakk>is_aligned ptr 2; is_aligned ptr bits;
    words_cleared (set [ptr , ptr + word_size .e. ptr + 2 ^ bits - 1]) s\<rbrakk> \<Longrightarrow>
   memory_cleared ptr bits s"
  apply(frule_tac sz=bits in is_aligned_no_overflow)
  apply(simp add: word_size_def upto_enum_step_shift[where m=2, simplified]
             set_upto_enum_step_4 image_def words_cleared_def
            memory_cleared_def)
  apply(rule ballI)
  apply(erule_tac x="p && ~~ mask 2" in allE)
  apply(erule impE)
   apply(rule_tac x="(p && ~~ mask 2) - ptr" in exI)
   apply(rule conjI)
    prefer 2
    apply simp
   apply(rule_tac x="((p && ~~ mask 2) - ptr) >> 2" in bexI)
    apply(simp add: shiftr_shiftl1)
    apply(subgoal_tac "is_aligned ((p && ~~ mask 2) - ptr) 2")
     apply(blast intro: sym is_aligned_neg_mask_eq)
    apply(fastforce intro: aligned_sub_aligned is_aligned_neg_mask le_refl simp: word_bits_def)
   apply(clarsimp)
   apply(rule le_shiftr)
   apply(rule_tac y="((ptr + 2 ^ bits - 1) && ~~ mask 2) - ptr" in order_trans)
    apply(rule word_le_minus_mono_left)
     apply(blast intro: neg_mask_mono_le)
    apply(drule is_aligned_neg_mask_eq[where n=2])
    apply(rule xtr4[rotated], assumption)
    apply(blast intro: neg_mask_mono_le)
   apply(rule order_trans[OF _ word_and_le2[where y="~~ mask 2"]])
   apply(rule word_diff_ls'(4))
    apply(rule_tac y="ptr + (2 ^ bits - 1 && ~~ mask 2)" in order_trans)
     apply(drule_tac n=2 and q="2 ^ bits - 1" in mask_out_add_aligned)
     apply(fastforce intro: neg_mask_mono_le simp: x_power_minus_1 add.commute)
    apply(fastforce simp: add.commute word_order_refl)
   apply(frule is_aligned_neg_mask_eq[where n=2])
   apply(rule xtr4[rotated], assumption)
   apply(blast intro: neg_mask_mono_le dest: order_trans)
  apply(clarsimp simp: word_cleared_def Let_def)
  apply(cut_tac n=2 and p=p in word_range_max, simp add: word_bits_def)
  apply(cut_tac a=p and y="~~ mask 2" in word_and_le2)
  apply(clarsimp)
  apply(case_tac "(p && ~~ mask 2) + 3 = p", simp)
  apply(subgoal_tac "p < (p && ~~ mask 2) + 3")
   apply(drule word_less_sub_1, simp)
   apply(case_tac "(p && ~~ mask 2) + 2 = p", simp)
   apply(subgoal_tac "p < (p && ~~ mask 2) + 2", drule word_less_sub_1, simp)
    apply(case_tac "(p && ~~ mask 2) + 1 = p", simp)
    apply(subgoal_tac "p < (p && ~~ mask 2) + 1", drule word_less_sub_1, simp)
    apply(fastforce simp: word_less_def add.commute)+
  done


(* is_aligned ptr bits is needed to ensure lack of overflow since in the event
   of overflow, clear_memory does nothing.
   We could instead assume "ptr \<le> ptr + 2 ^ bits - 1" directly and pump this
   same assumption into the above lemma. *)
lemma clear_memory_clears_memory:
  "\<lbrakk>is_aligned ptr 2; is_aligned ptr bits\<rbrakk> \<Longrightarrow>
  \<lbrace> \<top> \<rbrace>
  clear_memory ptr bits
  \<lbrace> \<lambda>_. memory_cleared ptr bits \<rbrace>"
  unfolding clear_memory_def
  apply (wp cleanCacheRange_memory_cleared_inv)
   prefer 2
   apply(wp return_sp)
  (* abuse subtoal_tac to rewrite the goal in an equivalent form *)
  apply(subgoal_tac "\<lbrace> \<top> \<rbrace> mapM_x (\<lambda>p. storeWord p 0) [ptr , ptr + word_size .e. ptr + (1 << bits) - 1] \<lbrace>\<lambda>x. memory_cleared ptr bits\<rbrace>")
   apply(fastforce simp: valid_def)
  apply(rule hoare_strengthen_post)
   apply(rule hoare_weaken_pre)
    apply(rule_tac A="{}" in mapM_x_storeWord_zero_words_cleared)
   apply (simp add: words_cleared_def)
  apply(fastforce intro: words_cleared_memory_cleared)
  done

lemma do_machine_op_wp:
  assumes "\<lbrace> P \<rbrace> f \<lbrace> \<lambda>_ s. Q s \<rbrace>"
  shows "\<lbrace> P \<circ> machine_state \<rbrace> do_machine_op f \<lbrace> \<lambda>_ s. Q (machine_state s) \<rbrace>"
  using assms
  apply (simp only: do_machine_op_def split_def)
  apply wp
  apply (simp add: valid_def split_def)
  done

lemma create_word_objects_clears_memory:
  "\<lbrakk>sz \<le> bits; is_aligned ptr 2; is_aligned ptr bits\<rbrakk> \<Longrightarrow>
   \<lbrace> \<top> \<rbrace>
   create_word_objects ptr bits sz
   \<lbrace> \<lambda>_ s. memory_cleared ptr bits (machine_state s) \<rbrace>"
  apply (simp add: create_word_objects_def)
  apply (wp do_machine_op_wp clear_memory_clears_memory)
  apply simp_all
  done

definition "is_page_type new_type \<equiv> case new_type of
  ArchObject SmallPageObj \<Rightarrow> True
| ArchObject LargePageObj \<Rightarrow> True
| ArchObject SectionObj \<Rightarrow> True
| ArchObject SuperSectionObj \<Rightarrow> True
| _ \<Rightarrow> False"

-- "TODO: should work on the other types of objects?"

crunch machine_inv: set_cdt "\<lambda>s. P (machine_state s)"

(* TODO: link the is_aligned stuff to valid_cap somehow *)
lemma "\<lbrakk> bits \<ge> obj_bits_api new_type user_obj_size;
         is_aligned ptr 2; is_aligned ptr bits;
         is_page_type new_type \<rbrakk> \<Longrightarrow>
  \<lbrace> \<top> \<rbrace>
  invoke_untyped (Invocations_A.Retype slot ptr bits new_type user_obj_size slots)
  \<lbrace> \<lambda>_ s. memory_cleared ptr bits (machine_state s) \<rbrace>"
  apply (simp, wp, auto)
    apply (simp add: mapM_x_def [symmetric])
    apply (wp mapM_x_wp_inv)
    apply (auto simp add: create_cap_def, wp)
     apply (auto intro: set_cdt_machine_inv)
   apply (unfold init_arch_objects_def)
   apply (cases new_type, simp_all add: is_page_type_def)
   apply (case_tac aobject_type,
     (simp, (rule create_word_objects_clears_memory), assumption+)+,
       simp_all)
  done

lemma "\<lbrakk> c = Structures_A.ArchObjectCap (ARM_Structs_A.PageCap ptr rs pgsz as) \<rbrakk> \<Longrightarrow>
  \<lbrace> valid_cap c \<rbrace>
  recycle_cap c
  \<lbrace> \<lambda> rv. (\<lambda> s. memory_cleared ptr (pageBitsForSize pgsz) (machine_state s)) \<rbrace>"
  apply (simp add: recycle_cap_def arch_recycle_cap_def)
  apply (rule liftM_wp, simp)
  apply (rule hoare_assume_pre)
  apply (wp do_machine_op_wp)
   apply (clarsimp simp: valid_cap_simps cap_aligned_def)
   apply (rule clear_memory_clears_memory)
    apply (rule is_aligned_weaken, assumption)
    apply (cases pgsz, simp_all)
  done

abbreviation "kernel_entry_pre e \<equiv> invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s) and valid_duplicates"

abbreviation "the_tcb s t \<equiv> case kheap s t of
  Some (TCB tcb) \<Rightarrow> tcb"
abbreviation "the_tcb_context s t \<equiv> tcb_context (the_tcb s t)"

abbreviation "ct_context s \<equiv> the_tcb_context s (cur_thread s)"

lemma thread_get_wp:
  "\<lbrace>\<lambda>s. obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> P (f tcb) s) ptr s\<rbrace>
    thread_get f ptr
   \<lbrace>P\<rbrace>"
  apply (clarsimp simp: valid_def obj_at_def)
  apply (frule in_inv_by_hoareD [OF thread_get_inv])
  apply (clarsimp simp: thread_get_def bind_def gets_the_def
                        assert_opt_def split_def return_def fail_def
                        gets_def get_def
                 split: option.splits
                 dest!: get_tcb_SomeD)
  done

text {*
This can't currently work, because refine has fragmented from
invariant_abstract, and kernel_entry only exists in ADTs in refine,
and importing both creates chaos. Chaos!

lemma kernel_entry_correct_context:
  "\<lbrace> kernel_entry_pre e \<rbrace>
  kernel_entry e tc
  \<lbrace> \<lambda>tc' s. tc' = ct_context s \<rbrace>"
  apply (simp add: kernel_entry_def)
  apply (wp thread_get_wp)
    apply (rule hoare_strengthen_post[OF akernel_invs])
    apply clarsimp
    apply (frule Invariant_AI.tcb_at_invs)
    apply (clarsimp simp add: obj_at_def is_tcb)
  apply (wp thread_set_invs_trivial thread_set_ct_running |
         clarsimp simp add: tcb_cap_cases_def)+
done
*}

text {*
  These are the registers that the kernel might modify in cases other than
  when a thread is blocked on an endpoit
*}
abbreviation "dirty_regs \<equiv>  [LR_svc]"

definition
mask_dirty_regs :: "user_context \<Rightarrow> user_context"
where
"mask_dirty_regs tc \<equiv> foldr (\<lambda>r tc. tc (r := 0)) dirty_regs tc"

lemma mask_dirty_regs_eq_LR_svc_update:
  "mask_dirty_regs tc = mask_dirty_regs (tc(LR_svc := x))"
  apply(simp add: mask_dirty_regs_def)
  done

text {*
  The integrity property from access control ensures that only the dirty regs
  (as defined above) of some other thread can be modified, when that thread
  is not blocked on a receive.
*}
lemma integrity_ensures_only_dirty_regs_modified: "\<not> is_subject aag t \<and> integrity aag X s s' \<and> \<not> (\<exists>ep. receive_blocked_on ep (tcb_state (the_tcb s t))) \<Longrightarrow> 
       (mask_dirty_regs (the_tcb_context s t)) = (mask_dirty_regs (the_tcb_context s' t))"
  apply (clarsimp simp: integrity_def)
  apply (rule integrity_obj.cases, auto simp: mask_dirty_regs_eq_LR_svc_update)
  done


(* The following requires ADTs from refine, see above
lemma access_control_thing:
  "\<lbrace> integrity aag X st \<rbrace>
  kernel_entry e tc
  \<lbrace> K (integrity aag X st) \<rbrace>"


text {*
  From kernel_entry_correct_context, we know that tc' below is the context
  of the currently running thread in the final state, i.e. the context of
  thread t in the final state. From integrity_ensures_only_dirty_regs_modified
  we can infer that the dirty_regs of t in the final state must be equal to
  those in the initial state. This gives us the following result, showing that
  only the dirty regs provide a potential source of residual information in
  this case.
*}
lemma
  "\<lbrace> kernel_entry_pre e and integrity aag X st and
     (\<lambda>s. \<forall>t. the_tcb_state s t = tc \<and>
              \<not> (\<exists>ep. receive_blocked_on ep (tcb_state (the_tcb s t))) \<and>
              \<not> is_subject aag t) \<rbrace>
  kernel_entry e tc
  \<lbrace> \<lambda>tc' s'. cur_thread s = t \<longrightarrow>
               (mask_dirty_regs tc') = (mask_dirty_regs tc) \<rbrace>"

*)

end
