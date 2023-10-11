(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory VSpaceEntries_AI
imports ArchSyscall_AI
begin

definition valid_entries :: " ('b \<Rightarrow> ('a::len) word \<Rightarrow> 'c set) \<Rightarrow> (('a::len) word \<Rightarrow> 'b) \<Rightarrow> bool"
  where "valid_entries \<equiv> \<lambda>range fun. \<forall>x y. x \<noteq> y \<longrightarrow> range (fun x) x \<inter> range (fun y) y = {}"

definition entries_align :: "('b \<Rightarrow> nat ) \<Rightarrow> (('a::len) word \<Rightarrow> 'b) \<Rightarrow> bool"
  where "entries_align \<equiv> \<lambda>sz fun. \<forall>x. is_aligned x (sz (fun x))"

lemma valid_entries_overwrite_0:
  assumes ve: "valid_entries rg tab"
  assumes disjoint: "\<And>p. \<lbrakk>p \<noteq> x\<rbrakk> \<Longrightarrow> rg v x \<inter> rg (tab p) p = {}"
  shows "valid_entries rg (tab (x := v))"
  apply (subst valid_entries_def)
  apply clarsimp
  apply (intro allI impI conjI)
    apply clarsimp
    apply (rule disjoint)
    apply simp
   apply clarsimp
   apply (drule disjoint)
   apply blast
  using ve
  apply (clarsimp simp:valid_entries_def)
  done

lemma vaid_entries_overwrite_0_weak:
  assumes ve: "valid_entries rg tab"
  assumes disjoint: "rg v x \<subseteq> rg (tab x) x"
  shows "valid_entries rg (tab (x := v))"
  using assms
  apply (subst valid_entries_def)
  apply clarsimp
  apply (intro allI impI conjI)
   apply (fastforce simp:valid_entries_def)+
  done

lemma valid_entries_partial_copy:
  "\<lbrakk> valid_entries rg tab; valid_entries rg tab';
  \<forall>v x. P x \<longrightarrow> (rg v x \<subseteq> S);
  \<forall>v x. \<not> P x \<longrightarrow> (rg v x \<inter> S) = {}\<rbrakk>
       \<Longrightarrow> valid_entries rg (\<lambda>x. if P x then tab x else tab' x)"
  apply (subst valid_entries_def, simp)
  apply (intro allI impI conjI)
     apply (fastforce simp:valid_entries_def)
    apply (drule_tac x = "tab x" in spec)
    apply (drule_tac x = x in spec)
    apply (drule_tac x = "tab' y" in spec)
    apply (drule_tac x = y in spec)
    apply clarsimp
    apply blast
   apply (fastforce simp:valid_entries_def)+
  done

lemma valid_entries_overwrite_groups:
  "\<lbrakk>valid_entries rg tab; valid_entries rg (\<lambda>_. v);
    \<forall>v x. P x \<longrightarrow> rg v x \<subseteq> S;
    \<forall>v x. \<not> P x \<longrightarrow> rg v x \<inter> S = {}\<rbrakk>
       \<Longrightarrow> valid_entries rg (\<lambda>x. if P x then v else tab x)"
  by (rule valid_entries_partial_copy)

lemmas valid_entries_overwrite_group
    = valid_entries_overwrite_groups[where S="{y}" for y, simplified]

lemma valid_entriesD:
  "\<lbrakk>x \<noteq> y; valid_entries rg fun\<rbrakk> \<Longrightarrow> rg (fun x) x \<inter> rg (fun y) y = {}"
  by (simp add:valid_entries_def)

lemma aligned_le_sharp:
  "\<lbrakk>a \<le> b;is_aligned a n\<rbrakk> \<Longrightarrow> a \<le> b &&~~ mask n"
  apply (simp add:is_aligned_mask)
  apply (drule neg_mask_mono_le[where n = n])
  apply (simp add:mask_out_sub_mask)
  done

lemma ucast_neg_mask:
  "len_of TYPE('a) \<le> len_of TYPE ('b)
   \<Longrightarrow> ((ucast ptr && ~~ mask n)::('a :: len) word) = ucast ((ptr::('b :: len) word) && ~~ mask n)"
  apply (rule word_eqI)
  apply (auto simp:nth_ucast neg_mask_test_bit word_size)
  done

lemma delete_objects_reduct:
  "valid (\<lambda>s. P (kheap (s :: ('z::state_ext) state))) (modify (detype {ptr..ptr + 2 ^ bits - 1}))
         (\<lambda>_ s. P(kheap (s :: ('z::state_ext) state))) \<Longrightarrow>
   valid (\<lambda>s. P (kheap (s :: ('z::state_ext) state))) (delete_objects ptr bits) (\<lambda>_ s. P (kheap s))"
  apply (clarsimp simp add: delete_objects_def do_machine_op_def split_def)
  apply wp
  apply (clarsimp simp add: valid_def simpler_modify_def)
  done

(* FIXME: move *)
lemma upto_0_to_n:
  "0 < n \<Longrightarrow> tl [0..<n] = [1..<n]"
  apply (erule(1) impE[rotated])
  apply (induct_tac n)
   apply simp
  apply simp
  done

(* FIXME: move *)
lemma upto_0_to_n2:
  "0 < n \<Longrightarrow> [0..<n] = 0 # [1..<n]"
  apply (erule(1) impE[rotated])
  apply (induct_tac n)
   apply simp
  apply simp
  done

(* FIXME: move *)
lemma neg_mask_add_mask:
  "((a && ~~ mask b) + c && mask b) = c && mask b"
  by (subst mask_add_aligned[OF is_aligned_neg_mask],simp+)

lemma all_imp_ko_at_from_ex_strg:
  "((\<exists>v. ko_at (f v) p s \<and> P v) \<and> inj f) \<longrightarrow> (\<forall>v. ko_at (f v) p s \<longrightarrow> P v)"
  apply (clarsimp simp add: obj_at_def)
  apply (auto dest: inj_onD)
  done

lemma set_cap_arch_obj_neg:
  "\<lbrace>\<lambda>s. \<not>ko_at (ArchObj ao) p s \<and> cte_wp_at (\<lambda>_. True) p' s\<rbrace> set_cap cap p' \<lbrace>\<lambda>_ s. \<not>ko_at (ArchObj ao) p s\<rbrace>"
  apply (simp add: set_cap_def split_def)
  apply (wp set_object_neg_ko get_object_wp| wpc)+
  apply (auto simp: pred_neg_def)
  done

lemma mapME_x_Nil:
  "mapME_x f [] = returnOk ()"
  unfolding mapME_x_def sequenceE_x_def
  by simp

lemma mapME_x_mapME:
  "mapME_x m l = (mapME m l >>=E (%_. returnOk ()))"
  apply (simp add: mapME_x_def sequenceE_x_def mapME_def sequenceE_def)
  apply (induct l, simp_all add: Let_def bindE_assoc)
  done

lemma mapME_x_wp:
  assumes x: "\<And>x. x \<in> S \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>rv. P\<rbrace>, \<lbrace>E\<rbrace>"
  shows      "set xs \<subseteq> S \<Longrightarrow> \<lbrace>P\<rbrace> mapME_x f xs \<lbrace>\<lambda>rv. P\<rbrace>, \<lbrace>E\<rbrace>"
  apply (subst mapME_x_mapME)
  apply wp
  apply (rule mapME_wp)
   apply (rule x)
   apply assumption+
  done

lemmas mapME_x_wp' = mapME_x_wp [OF _ subset_refl]

lemmas mapME_x_wp_inv' = mapME_x_wp[where S=UNIV, simplified]

lemma mapME_x_wp2:
  assumes x: "\<And>x. x \<in> S \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>rv. P\<rbrace>"
  shows      "set xs \<subseteq> S \<Longrightarrow> \<lbrace>P\<rbrace> mapME_x f xs \<lbrace>\<lambda>rv. P\<rbrace>"
  by (wpsimp wp: mapME_x_wp x)

lemmas mapME_x_wp_inv = mapME_x_wp2[where S=UNIV, simplified]

lemmas hoare_post_conjE = hoare_validE_pred_conj (* FIXME: eliminate *)

lemma mapME_x_accumulate_checks:
  assumes P:  "\<And>x. x \<in> set xs \<Longrightarrow> \<lbrace>Q\<rbrace> f x \<lbrace>\<lambda>rv. P x\<rbrace>, \<lbrace>E\<rbrace>"
  and Q : "\<And>x. x \<in> set xs \<Longrightarrow> \<lbrace>Q\<rbrace> f x \<lbrace>\<lambda>rv. Q\<rbrace>, \<lbrace>E\<rbrace>"
  and P': "\<And>x y. y \<noteq> x  \<Longrightarrow> \<lbrace>P y\<rbrace> f x \<lbrace>\<lambda>rv. P y\<rbrace>, \<lbrace>E\<rbrace>"
  and distinct: "distinct xs"
  shows       "\<lbrace>Q \<rbrace> mapME_x f xs \<lbrace>\<lambda>rv s. \<forall>x \<in> set xs. P x s\<rbrace>, \<lbrace>E\<rbrace>"
  using assms
  proof (induct xs)
    case Nil
    show ?case
      by (simp add: mapME_x_Nil, wp)
  next
    case (Cons y ys)
    show ?case
      apply (simp add: mapME_x_Cons)
      apply wp
       apply (rule hoare_vcg_conj_liftE_weaker)
        apply (wp mapME_x_wp' P P'
          hoare_vcg_const_Ball_liftE
          | simp add:Q
          | rule hoare_post_impErr[OF P])+
        using Cons.prems
        apply fastforce
      apply (wp Cons.hyps)
         apply (rule Cons.prems,simp)
        apply (wp Cons.prems(2);simp)
       apply (wp Cons.prems(3);simp)
      using Cons.prems
      apply fastforce
     apply (rule hoare_pre)
     apply (rule hoare_vcg_conj_liftE_weaker)
     apply (wp Cons.prems| simp)+
    done
  qed

lemma hoare_vcg_ex_liftE:
  "\<lbrakk> \<And>x. \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. \<exists>x. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<exists>x. Q x rv s\<rbrace>,\<lbrace>E\<rbrace>"
  by (fastforce simp: validE_def valid_def split: sum.splits)

lemma mapME_singleton:
  "mapME_x f [x] = f x"
  by (simp add:mapME_x_def sequenceE_x_def)

end
