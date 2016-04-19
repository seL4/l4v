(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory PDPTEntries_AI
imports Syscall_AI
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
  apply (auto simp:nth_ucast neg_mask_bang word_size)
  done

lemma shiftr_eq_neg_mask_eq:
  "a >> b = c >> b \<Longrightarrow> a && ~~ mask b = c && ~~ mask b"
  apply (rule word_eqI)
   apply (simp add:neg_mask_bang)
  apply (drule_tac f = "\<lambda>x. x !! (n - b)" in arg_cong)
  apply (simp add:nth_shiftr)
  apply (rule iffI)
   apply simp+
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

lemma ucast_pt_index:
  "\<lbrakk>is_aligned (p::word32) 6\<rbrakk>
   \<Longrightarrow> ucast ((pa && mask 4) + (ucast (p && mask 10 >> 2)::word8))
   =  ucast (pa && mask 4) + (p && mask 10 >> 2)"
  apply (simp add:is_aligned_mask mask_def)
  apply word_bitwise
  apply (auto simp:carry_def)
  done

lemma ucast_pd_index:
  "\<lbrakk>is_aligned (p::word32) 6\<rbrakk>
   \<Longrightarrow> ucast ((pa && mask 4) + (ucast (p && mask 14 >> 2)::12 word))
   =  ucast (pa && mask 4) + (p && mask 14 >> 2)"
  apply (simp add:is_aligned_mask mask_def)
  apply word_bitwise
  apply (auto simp:carry_def)
  done

lemma unat_ucast_12_32:
  "unat (ucast (x::(12 word))::word32) = unat x"
  apply (subst unat_ucast)
  apply (rule mod_less)
  apply (rule less_le_trans[OF unat_lt2p])
  apply simp
  done

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

lemma mapME_wp:
  assumes x: "\<And>x. x \<in> S \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>rv. P\<rbrace>, \<lbrace>E\<rbrace>"
  shows      "set xs \<subseteq> S \<Longrightarrow> \<lbrace>P\<rbrace> mapME f xs \<lbrace>\<lambda>rv. P\<rbrace>, \<lbrace>E\<rbrace>"
  apply (induct xs)
   apply (simp add: mapME_def sequenceE_def)
   apply wp
  apply (simp add: mapME_Cons)
  apply wp
   apply simp
  apply (simp add: x)
  done

lemma mapME_x_wp:
  assumes x: "\<And>x. x \<in> S \<Longrightarrow> \<lbrace>P\<rbrace> f x \<lbrace>\<lambda>rv. P\<rbrace>, \<lbrace>E\<rbrace>"
  shows      "set xs \<subseteq> S \<Longrightarrow> \<lbrace>P\<rbrace> mapME_x f xs \<lbrace>\<lambda>rv. P\<rbrace>, \<lbrace>E\<rbrace>"
  apply (subst mapME_x_mapME)
  apply wp
  apply simp
  apply (rule mapME_wp)
   apply (rule x)
   apply assumption+
  done

lemmas mapME_x_wp' = mapME_x_wp [OF _ subset_refl]

lemma hoare_vcg_all_liftE:
  "\<lbrakk> \<And>x. \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. \<forall>x. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x. Q x rv s\<rbrace>,\<lbrace>E\<rbrace>"
  by (fastforce simp: validE_def valid_def split: sum.splits)

lemma hoare_vcg_const_Ball_liftE:
  "\<lbrakk> \<And>x. x \<in> S \<Longrightarrow> \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace>,\<lbrace>E\<rbrace>; \<lbrace>\<lambda>s. True\<rbrace> f \<lbrace>\<lambda>r s. True\<rbrace>, \<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. \<forall>x\<in>S. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x\<in>S. Q x rv s\<rbrace>,\<lbrace>E\<rbrace>"
  by (fastforce simp: validE_def valid_def split: sum.splits)

lemma hoare_post_conjE:
  "\<lbrakk> \<lbrace> P \<rbrace> a \<lbrace> Q \<rbrace>,\<lbrace>E\<rbrace>; \<lbrace> P \<rbrace> a \<lbrace> R \<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace> P \<rbrace> a \<lbrace> Q And R \<rbrace>,\<lbrace>E\<rbrace>"
  by (clarsimp simp: validE_def valid_def split_def bipred_conj_def
              split: sum.splits)

lemma hoare_vcg_conj_liftE:
  assumes x: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  assumes y: "\<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>,\<lbrace>E\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P s \<and> P' s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>,\<lbrace>E\<rbrace>"
  apply (subst bipred_conj_def[symmetric], rule hoare_post_conjE)
   apply (rule hoare_vcg_precond_impE [OF x], simp)
  apply (rule hoare_vcg_precond_impE [OF y], simp)
  done

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
       apply (rule hoare_vcg_conj_liftE)
        apply (wp mapME_x_wp' P P'
          hoare_vcg_const_Ball_liftE
          | simp add:Q
          | rule hoare_post_impErr[OF P])+
        using Cons.prems
        apply fastforce
      apply (wp Cons.hyps)
         apply (rule Cons.prems,simp)
        apply (wp Cons.prems(2),simp)
       apply (wp Cons.prems(3),simp)
      using Cons.prems
      apply fastforce
     apply (rule hoare_pre)
     apply (rule hoare_vcg_conj_liftE)
     apply (wp Cons.prems| simp)+
    done
  qed

lemma hoare_vcg_ex_liftE:
  "\<lbrakk> \<And>x. \<lbrace>P x\<rbrace> f \<lbrace>Q x\<rbrace>,\<lbrace>E\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>\<lambda>s. \<exists>x. P x s\<rbrace> f \<lbrace>\<lambda>rv s. \<exists>x. Q x rv s\<rbrace>,\<lbrace>E\<rbrace>"
  by (fastforce simp: validE_def valid_def split: sum.splits)

lemma mapME_singleton:
  "mapME_x f [x] = f x"
  by (simp add:mapME_x_def sequenceE_x_def)

context ARM begin (*FIXME: arch_split*)

lemma a_type_pdD:
  "a_type ko = AArch APageDirectory \<Longrightarrow> \<exists>pd. ko = ArchObj (PageDirectory pd)"
  by (clarsimp)

primrec
  pde_range_sz :: "pde \<Rightarrow> nat"
where
    "pde_range_sz (InvalidPDE) = 0"
  | "pde_range_sz (SectionPDE ptr x y z) = 0"
  | "pde_range_sz (SuperSectionPDE ptr x z) = 4"
  | "pde_range_sz (PageTablePDE ptr x z) = 0"

primrec
  pte_range_sz :: "pte \<Rightarrow> nat"
where
    "pte_range_sz (InvalidPTE) = 0"
  | "pte_range_sz (LargePagePTE ptr x y) = 4"
  | "pte_range_sz (SmallPagePTE ptr x y) = 0"

primrec
  pde_range :: "pde \<Rightarrow> 12 word \<Rightarrow> 12 word set"
where
    "pde_range (InvalidPDE) p = {}"
  | "pde_range (SectionPDE ptr x y z) p = {p}"
  | "pde_range (SuperSectionPDE ptr x z) p =
     (if is_aligned p 4 then {x. x && ~~ mask 4 = p && ~~ mask 4} else {p})"
  | "pde_range (PageTablePDE ptr x z) p = {p}"

primrec
  pte_range :: "pte \<Rightarrow> word8 \<Rightarrow> word8 set"
where
    "pte_range (InvalidPTE) p = {}"
  | "pte_range (LargePagePTE ptr x y) p =
       (if is_aligned p 4 then {x. x && ~~ mask 4 = p && ~~ mask 4} else {p})"
  | "pte_range (SmallPagePTE ptr x y) p = {p}"

abbreviation "valid_pt_entries \<equiv> \<lambda>pt. valid_entries pte_range pt"

abbreviation "valid_pd_entries \<equiv> \<lambda>pd. valid_entries pde_range pd"

definition
  obj_valid_pdpt :: "kernel_object \<Rightarrow> bool"
where
 "obj_valid_pdpt obj \<equiv> case obj of
    ArchObj (PageTable pt) \<Rightarrow> valid_pt_entries pt \<and> entries_align pte_range_sz pt
  | ArchObj (PageDirectory pd) \<Rightarrow> valid_pd_entries pd \<and> entries_align pde_range_sz pd
  | _ \<Rightarrow> True"

lemmas obj_valid_pdpt_simps[simp]
    = obj_valid_pdpt_def
        [split_simps Structures_A.kernel_object.split
                     arch_kernel_obj.split]

abbreviation
  valid_pdpt_objs :: "'z state \<Rightarrow> bool"
where
 "valid_pdpt_objs s \<equiv> \<forall>x \<in> ran (kheap s). obj_valid_pdpt x"

lemma valid_pdpt_init[iff]:
  "valid_pdpt_objs init_A_st"
proof -
  have P: "valid_pd_entries (global_pd :: 12 word \<Rightarrow> _)"
    apply (clarsimp simp: valid_entries_def global_pd_def)
    done
  also have Q: "entries_align pde_range_sz (global_pd :: 12 word \<Rightarrow> _)"
    apply (clarsimp simp: entries_align_def global_pd_def)
    done
  thus ?thesis using P
    by (auto simp: init_A_st_def init_kheap_def
            elim!: ranE split: split_if_asm)
qed

lemma set_object_valid_pdpt[wp]:
  "\<lbrace>valid_pdpt_objs and K (obj_valid_pdpt obj)\<rbrace>
      set_object ptr obj
   \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: set_object_def, wp)
  apply (auto simp: fun_upd_def[symmetric] del: ballI elim: ball_ran_updI)
  done

crunch valid_pdpt_objs[wp]: cap_insert, cap_swap_for_delete,empty_slot "valid_pdpt_objs"
  (wp: crunch_wps simp: crunch_simps ignore:set_object)

crunch valid_pdpt_objs[wp]: flush_page "valid_pdpt_objs"
  (wp: crunch_wps simp: crunch_simps)

lemma shift_0x3C_set:
  "\<lbrakk> is_aligned p 6; 8 \<le> bits; bits < 32; len_of TYPE('a) = bits - 2 \<rbrakk> \<Longrightarrow>
   (\<lambda>x. ucast (x + p && mask bits >> 2) :: ('a :: len) word) ` set [0 :: word32 , 4 .e. 0x3C]
        = {x. x && ~~ mask 4 = ucast (p && mask bits >> 2)}"
  apply (clarsimp simp: upto_enum_step_def word32_shift_by_2 image_image)
  apply (subst image_cong[where N="{x. x < 2 ^ 4}"])
    apply (safe, simp_all)[1]
     apply (drule plus_one_helper2, simp_all)[1]
    apply (drule minus_one_helper3, simp_all)[1]
   apply (rule_tac f="\<lambda>x. ucast (x && mask bits >> 2)" in arg_cong)
   apply (rule trans[OF add.commute is_aligned_add_or], assumption)
   apply (rule shiftl_less_t2n, simp_all)[1]
  apply safe
   apply (frule upper_bits_unset_is_l2p[THEN iffD2, rotated])
    apply (simp add: word_bits_conv)
   apply (rule word_eqI)
   apply (simp add: word_ops_nth_size word_size nth_ucast nth_shiftr
                    nth_shiftl neg_mask_bang
                    word_bits_conv)
   apply (safe, simp_all add: is_aligned_nth)[1]
   apply (drule_tac x="Suc (Suc n)" in spec)
   apply simp
  apply (rule_tac x="ucast x && mask 4" in image_eqI)
   apply (rule word_eqI)
   apply (drule_tac x=n in word_eqD)
   apply (simp add: word_ops_nth_size word_size nth_ucast nth_shiftr
                    nth_shiftl)
   apply (safe, simp_all)
  apply (rule order_less_le_trans, rule and_mask_less_size)
   apply (simp_all add: word_size)
  done

lemma mapM_x_store_pte_updates:
  "\<forall>x \<in> set xs. f x && ~~ mask pt_bits = p \<Longrightarrow>
   \<lbrace>\<lambda>s. (\<not> page_table_at p s \<longrightarrow> Q s) \<and>
        (\<forall>pt. ko_at (ArchObj (PageTable pt)) p s
           \<longrightarrow> Q (s \<lparr> kheap := (kheap s) (p := Some (ArchObj (PageTable (\<lambda>y. if y \<in> (\<lambda>x.
         ucast (f x && mask pt_bits >> 2)) ` set xs then pte else pt y)))) \<rparr>))\<rbrace>
     mapM_x (\<lambda>x. store_pte (f x) pte) xs
   \<lbrace>\<lambda>_. Q\<rbrace>"
  apply (induct xs)
   apply (simp add: mapM_x_Nil)
   apply wp
   apply (clarsimp simp: obj_at_def)
   apply (simp add: a_type_def fun_upd_idem
             split: Structures_A.kernel_object.split_asm split_if_asm
                    arch_kernel_obj.split_asm)
  apply (simp add: mapM_x_Cons)
  apply (rule hoare_seq_ext, assumption)
  apply (thin_tac "valid P f Q" for P f Q)
  apply (simp add: store_pte_def set_pt_def set_object_def)
  apply (wp get_pt_wp get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_simps)
  apply (erule rsubst[where P=Q])
  apply (rule abstract_state.fold_congs[OF refl refl])
  apply (rule ext, clarsimp)
  apply (rule ext, clarsimp)
  done

lemma valid_pt_entries_invalid[simp]:
  "valid_pt_entries (\<lambda>x. InvalidPTE)"
   by (simp add:valid_entries_def)

lemma valid_pd_entries_invalid[simp]:
  "valid_pd_entries (\<lambda>x. InvalidPDE)"
  by (simp add:valid_entries_def)

lemma entries_align_pte_update:
 "\<lbrakk>entries_align pte_range_sz pt;
  (\<forall>y. (P y) \<longrightarrow> is_aligned y (pte_range_sz pte))\<rbrakk>
  \<Longrightarrow> entries_align pte_range_sz (\<lambda>y. if (P y) then pte else pt y)"
  by (simp add:entries_align_def)

lemma entries_align_pde_update:
 "\<lbrakk>entries_align pde_range_sz pd;
  (\<forall>y. (P y) \<longrightarrow> is_aligned y (pde_range_sz pde))\<rbrakk>
  \<Longrightarrow> entries_align pde_range_sz (\<lambda>y. if (P y) then pde else pd y)"
  by (simp add:entries_align_def)


lemma valid_pdpt_objs_pdD:
  "\<lbrakk>valid_pdpt_objs s;
    kheap s ptr = Some (ArchObj (arch_kernel_obj.PageDirectory pd))\<rbrakk>
   \<Longrightarrow> valid_pd_entries pd \<and> entries_align pde_range_sz pd"
  by (fastforce simp:ran_def)

lemma valid_pdpt_objs_ptD:
  "\<lbrakk>valid_pdpt_objs s;
    kheap s ptr = Some (ArchObj (arch_kernel_obj.PageTable pt))\<rbrakk>
   \<Longrightarrow> valid_pt_entries pt \<and> entries_align pte_range_sz pt"
  by (fastforce simp:ran_def)

lemma mapM_x_store_invalid_pte_valid_pdpt:
  "\<lbrace>valid_pdpt_objs and K (is_aligned p 6) \<rbrace>
     mapM_x (\<lambda>x. store_pte (x + p) InvalidPTE) [0, 4 .e. 0x3C]
   \<lbrace>\<lambda>_. valid_pdpt_objs\<rbrace>"
  apply (rule hoare_gen_asm)+
  apply (rule hoare_pre, rule_tac p="p && ~~ mask pt_bits" in mapM_x_store_pte_updates)
   apply clarsimp
   apply (rule mask_out_first_mask_some[where n=6])
    apply (drule_tac d=x in is_aligned_add_helper)
     apply (drule subsetD[OF upto_enum_step_subset])
     apply simp
     apply (erule order_le_less_trans, simp)
    apply (simp add: field_simps)
   apply (simp add: pt_bits_def pageBits_def)
  apply (clarsimp simp: ranI elim!: ranE split: split_if_asm)
  apply (intro conjI)
   apply (simp add: shift_0x3C_set pt_bits_def pageBits_def)
   apply (rule valid_entries_overwrite_groups
    [where S = "{x. x && ~~ mask 4 = ucast (p && mask 10 >> 2)}"])
      apply (fastforce simp add: obj_at_def ran_def)
     apply simp
    apply clarsimp
    apply (case_tac v)
      apply (simp split:if_splits)+
   apply (clarsimp)
   apply (case_tac v, simp_all split:if_splits)
    apply (intro conjI impI)
     apply (rule disjointI)
     apply (clarsimp)+
  apply (rule entries_align_pte_update)
   apply (clarsimp simp:obj_at_def)
   apply (drule(1) valid_pdpt_objs_ptD)
   apply simp
  apply (simp)
  done

lemma mapM_x_store_pde_updates:
  "\<forall>x \<in> set xs. f x && ~~ mask pd_bits = p \<Longrightarrow>
   \<lbrace>\<lambda>s. (\<not> page_directory_at p s \<longrightarrow> Q s) \<and>
        (\<forall>pd. ko_at (ArchObj (PageDirectory pd)) p s
           \<longrightarrow> Q (s \<lparr> kheap := (kheap s) (p := Some (ArchObj (PageDirectory (\<lambda>y. if y \<in> (\<lambda>x.
         ucast (f x && mask pd_bits >> 2)) ` set xs then pde else pd y)))) \<rparr>))\<rbrace>
     mapM_x (\<lambda>x. store_pde (f x) pde) xs
   \<lbrace>\<lambda>_. Q\<rbrace>"
  apply (induct xs)
   apply (simp add: mapM_x_Nil)
   apply wp
   apply (clarsimp simp: obj_at_def)
   apply (simp add: a_type_def fun_upd_idem
             split: Structures_A.kernel_object.split_asm split_if_asm
                    arch_kernel_obj.split_asm)
  apply (simp add: mapM_x_Cons)
  apply (rule hoare_seq_ext, assumption)
  apply (thin_tac "valid P f Q" for P f Q)
  apply (simp add: store_pde_def set_pd_def set_object_def)
  apply (wp get_pd_wp get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_simps)
  apply (erule rsubst[where P=Q])
  apply (rule abstract_state.fold_congs[OF refl refl])
  apply (rule ext, clarsimp)
  apply (rule ext, clarsimp)
  done

lemma mapM_x_store_pde_valid_pdpt_objs:
  "\<lbrace>valid_pdpt_objs and K (is_aligned p 6)\<rbrace>
     mapM_x (\<lambda>x. store_pde (x + p) InvalidPDE) [0, 4 .e. 0x3C]
   \<lbrace>\<lambda>_. valid_pdpt_objs\<rbrace>"
  apply (rule hoare_gen_asm)+
  apply (rule hoare_pre, rule_tac p="p && ~~ mask pd_bits" in mapM_x_store_pde_updates)
   apply clarsimp
   apply (rule mask_out_first_mask_some[where n=6])
    apply (drule_tac d=x in is_aligned_add_helper)
     apply (drule subsetD[OF upto_enum_step_subset])
     apply simp
     apply (erule order_le_less_trans, simp)
    apply (simp add: field_simps)
   apply (simp add: pd_bits_def pageBits_def)
  apply (clarsimp simp: ranI elim!: ranE split: split_if_asm)
  apply (simp add: shift_0x3C_set pd_bits_def pageBits_def)
  apply (rule conjI)
   apply (rule_tac valid_entries_overwrite_groups
    [where S = "{x. x && ~~ mask 4 = ucast (p && mask 14 >> 2)}"])
      apply (fastforce simp add: obj_at_def ran_def)
     apply fastforce
    apply clarsimp
    apply (case_tac v, simp_all split:if_splits)
    apply clarsimp
    apply (case_tac v, simp_all split:if_splits)
   apply (intro conjI impI allI)
   apply (rule disjointI)
   apply clarsimp
  apply (rule entries_align_pde_update)
   apply (clarsimp simp:obj_at_def)
   apply (drule valid_pdpt_objs_pdD)
    apply (simp add:pd_bits_def pageBits_def)
   apply simp
  apply simp
  done

lemma store_invalid_pde_valid_pdpt:
  "\<lbrace>valid_pdpt_objs and
    (\<lambda>s. \<forall>pd. ko_at (ArchObj (PageDirectory pd)) (p && ~~ mask pd_bits) s
      \<longrightarrow> pde = InvalidPDE)\<rbrace>
       store_pde p pde \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: store_pde_def set_pd_def, wp get_object_wp)
  apply (clarsimp simp: obj_at_def)
   apply (intro conjI)
   apply (rule valid_entries_overwrite_0, simp_all)
   apply (fastforce simp: ran_def)
  apply (simp add:fun_upd_def)
  apply (rule entries_align_pde_update)
   apply (drule(1) valid_pdpt_objs_pdD)
   apply simp
  apply simp
  done

lemma store_pde_non_master_valid_pdpt:
  "\<lbrace>valid_pdpt_objs and
        (\<lambda>s. \<forall>pd. ko_at (ArchObj (PageDirectory pd)) (p && ~~ mask pd_bits) s
        \<longrightarrow> (pde_range_sz (pd (ucast (p && mask pd_bits >> 2) && ~~ mask 4)) = 0
        \<and> pde_range_sz pde = 0))\<rbrace>
       store_pde p pde \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: store_pde_def set_pd_def, wp get_object_wp)
  apply (clarsimp simp: obj_at_def)
  apply (intro conjI)
   apply (rule valid_entries_overwrite_0)
    apply (fastforce simp:ran_def)
   apply (drule bspec)
    apply fastforce
   apply (case_tac "pd pa")
    apply simp_all
     apply (case_tac pde,simp_all)
    apply (case_tac pde,simp_all)
   apply (case_tac pde,simp_all)
    apply (clarsimp simp: is_aligned_neg_mask_eq)+
  apply (simp add:fun_upd_def)
  apply (rule entries_align_pde_update)
   apply (drule(1) valid_pdpt_objs_pdD,simp)
  apply simp
  done

lemma store_invalid_pte_valid_pdpt:
  "\<lbrace>valid_pdpt_objs and
        (\<lambda>s. \<forall>pt. ko_at (ArchObj (PageTable pt)) (p && ~~ mask pt_bits) s
        \<longrightarrow> pte = InvalidPTE)\<rbrace>
       store_pte p pte \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: store_pte_def set_pt_def, wp get_object_wp)
  apply (clarsimp simp: obj_at_def)
   apply (intro conjI)
   apply (rule valid_entries_overwrite_0, simp_all)
   apply (fastforce simp: ran_def)
  apply (simp add:fun_upd_def)
  apply (rule entries_align_pte_update)
   apply (drule (1) valid_pdpt_objs_ptD,simp)
  apply simp
  done

lemma store_pte_non_master_valid_pdpt:
  "\<lbrace>valid_pdpt_objs and
        (\<lambda>s. \<forall>pt. ko_at (ArchObj (PageTable pt)) (p && ~~ mask pt_bits) s
        \<longrightarrow> (pte_range_sz (pt (ucast (p && mask pt_bits >> 2) && ~~ mask 4)) = 0
        \<and> pte_range_sz pte = 0))\<rbrace>
       store_pte p pte \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: store_pte_def set_pt_def, wp get_object_wp)
  apply (clarsimp simp: obj_at_def)
  apply (intro conjI)
   apply (rule valid_entries_overwrite_0)
    apply (fastforce simp:ran_def)
   apply (drule bspec)
    apply fastforce
   apply (case_tac "pt pa")
     apply simp
    apply (case_tac pte,simp_all)
    apply (clarsimp simp: is_aligned_neg_mask_eq)
   apply (case_tac pte,simp_all)
  apply (simp add:fun_upd_def)
  apply (rule entries_align_pte_update)
   apply (drule (1) valid_pdpt_objs_ptD,simp)
  apply simp
  done

lemma unmap_page_valid_pdpt[wp]:
  "\<lbrace>valid_pdpt_objs\<rbrace> unmap_page sz asid vptr pptr \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: unmap_page_def mapM_discarded
             cong: vmpage_size.case_cong)
  apply (wp)
    prefer 2
    apply (rule valid_validE[OF find_pd_for_asid_inv])
  apply (rule hoare_pre)
   apply (wp get_object_wp get_pte_wp get_pde_wp lookup_pt_slot_inv_any
             store_invalid_pte_valid_pdpt
             store_invalid_pde_valid_pdpt
             mapM_x_store_invalid_pte_valid_pdpt mapM_x_store_pde_valid_pdpt_objs
                | simp add: mapM_x_map
                | wpc | simp add: check_mapping_pptr_def)+
  apply (simp add: fun_upd_def[symmetric] is_aligned_mask[symmetric])
  done

crunch valid_pdpt_objs[wp]: flush_table "valid_pdpt_objs"
  (wp: crunch_wps simp: crunch_simps)

crunch kheap[wp]: flush_table "\<lambda>s. P (kheap s)"
  (wp: crunch_wps simp: crunch_simps)

lemma unmap_page_table_valid_pdpt_objs[wp]:
  "\<lbrace>valid_pdpt_objs\<rbrace> unmap_page_table asid vptr pt \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: unmap_page_table_def)
  apply (wp get_object_wp store_invalid_pde_valid_pdpt | wpc)+
  apply (simp add: obj_at_def)
  apply (simp add: page_table_mapped_def)
  apply (wp get_pde_wp | wpc)+
  apply simp
  apply (rule hoare_post_impErr, rule valid_validE,
         rule find_pd_for_asid_inv, simp_all)
  done

crunch valid_pdpt_objs[wp]: finalise_cap, cap_swap_for_delete, empty_slot "valid_pdpt_objs"
  (wp: crunch_wps select_wp preemption_point_inv simp: crunch_simps unless_def ignore:set_object)

lemma preemption_point_valid_pdpt_objs[wp]:
  "\<lbrace>valid_pdpt_objs\<rbrace> preemption_point \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  by (wp preemption_point_inv | simp)+

lemmas cap_revoke_preservation2 = cap_revoke_preservation[OF _,
                                                          where E=valid_pdpt_objs,
                                                          simplified, THEN validE_valid]

lemmas rec_del_preservation2 = rec_del_preservation[OF _ _ _ _,
                                                    where P=valid_pdpt_objs, simplified]

crunch valid_pdpt_objs[wp]: cap_delete, cap_revoke "valid_pdpt_objs"
  (wp: rec_del_preservation2 cap_revoke_preservation2)

crunch valid_pdpt_objs[wp]: invalidate_tlb_by_asid, page_table_mapped
   "valid_pdpt_objs"


lemma mapM_x_copy_pde_updates:
  "\<lbrakk> \<forall>x \<in> set xs. f x && ~~ mask pd_bits = 0; is_aligned p pd_bits;
               is_aligned p' pd_bits \<rbrakk> \<Longrightarrow>
   \<lbrace>\<lambda>s. (\<not> page_directory_at p s \<longrightarrow> Q s) \<and> (\<not> page_directory_at p' s \<longrightarrow> Q s) \<and>
        (\<forall>pd pd'. ko_at (ArchObj (PageDirectory pd)) p s
                \<and> ko_at (ArchObj (PageDirectory pd')) p' s
           \<longrightarrow> Q (s \<lparr> kheap := (kheap s) (p' := Some (ArchObj (PageDirectory (\<lambda>y. if y \<in> (\<lambda>x.
         ucast (f x && mask pd_bits >> 2)) ` set xs then pd y else pd' y)))) \<rparr>))\<rbrace>
     mapM_x (\<lambda>x. get_pde (p + f x) >>= store_pde (p' + f x)) xs
   \<lbrace>\<lambda>_. Q\<rbrace>"
  apply (induct xs)
   apply (simp add: mapM_x_Nil)
   apply wp
   apply (clarsimp simp: obj_at_def fun_upd_idem dest!: a_type_pdD)
  apply (simp add: mapM_x_Cons)
  apply wp
   apply assumption
  apply (thin_tac "valid P f Q" for P f Q)
  apply (simp add: store_pde_def set_pd_def set_object_def
             cong: bind_cong split del: split_if)
  apply (wp get_object_wp get_pde_wp)
  apply (clarsimp simp: obj_at_def a_type_simps mask_out_add_aligned[symmetric]
             split del: split_if)
  apply (simp add: a_type_simps, safe)
   apply (erule rsubst[where P=Q])
   apply (rule abstract_state.fold_congs[OF refl refl])
   apply (rule ext, clarsimp)
   apply (rule ext, simp)
  apply (erule rsubst[where P=Q])
  apply (rule abstract_state.fold_congs[OF refl refl])
  apply (rule ext, clarsimp)
  apply (rule ext, simp add: mask_add_aligned)
  done

lemma copy_global_mappings_valid_pdpt_objs[wp]:
  "\<lbrace>valid_pdpt_objs and valid_arch_state and pspace_aligned
            and K (is_aligned p pd_bits)\<rbrace>
       copy_global_mappings p \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: copy_global_mappings_def)
  apply wp
   apply (rule_tac P="is_aligned global_pd pd_bits" in hoare_gen_asm)
   apply (rule mapM_x_copy_pde_updates, simp_all)
   apply (clarsimp simp: mask_eq_x_eq_0[symmetric])
   apply (rule less_mask_eq, rule shiftl_less_t2n,
          simp_all add: pd_bits_def pageBits_def)[1]
   apply (drule plus_one_helper2, simp+)
  apply wp
  apply (clarsimp simp: invs_aligned_pdD ranI
                 elim!: ranE split: split_if_asm)
  apply (intro conjI)
   apply (rule_tac S="{x. ucast x \<ge> (kernel_base >> 20)}"
                 in valid_entries_partial_copy)
      apply (fastforce simp: obj_at_def ran_def)
     apply (fastforce simp: obj_at_def ran_def)
    apply (clarsimp simp:image_def)
    apply (subst (asm) less_mask_eq)
     apply (rule shiftl_less_t2n)
      apply (simp add:pd_bits_def pageBits_def word_le_make_less)
     apply (simp add:pd_bits_def pageBits_def)
    apply (subst (asm) shiftl_shiftr1)
     apply simp
    apply (simp add:word_size)
    apply (subst (asm) less_mask_eq)
     apply (simp add:pd_bits_def pageBits_def le_less_trans)
    apply (case_tac v)
      apply (simp add:ucast_ucast_len pd_bits_def pageBits_def le_less_trans)+
    apply (clarsimp split:if_splits)
     apply (simp add:kernel_base_shift_cast_le)
     apply (simp add:kernel_base_def)
     apply (cut_tac y1 = xb and x1 = "0xE00::12 word" in ucast_le_migrate[THEN iffD1,rotated -1])
        apply simp
       apply (simp add:word_size le_less_trans)
      apply (simp add:word_size)
     apply (drule aligned_le_sharp[where n = 4 and a = "0xE00::12 word"])
      apply (simp add:kernel_base_def is_aligned_def)
     apply (erule order_trans)
     apply (erule subst)
     apply (simp add:word_and_le2)
    apply (subst ucast_ucast_len)
     apply (simp,word_bitwise)
    apply simp
   apply (clarsimp simp:image_def)
   apply (rule disjointI)
   apply clarsimp
   apply (drule_tac x = "ucast x" in spec)
   apply (erule impE)
    apply (simp add:pd_bits_def pageBits_def)
    apply word_bitwise
   apply (subgoal_tac "kernel_base >> 20 \<le> ucast x")
    apply simp
    apply (subst (asm) less_mask_eq)
     apply (rule shiftl_less_t2n)
      apply (simp add:pd_bits_def pageBits_def word_le_make_less)
      apply word_bitwise
     apply (simp add:pd_bits_def pageBits_def)
    apply (subst (asm) shiftl_shiftr1)
     apply simp
    apply (simp add:word_size)
    apply (subst (asm) less_mask_eq)
     apply (rule less_le_trans[OF ucast_less])
      apply simp
     apply simp
    apply word_bitwise
   apply (case_tac v,simp_all)
   apply (clarsimp split:if_splits)
   apply (drule aligned_le_sharp[where n = 4])
    apply (simp add:kernel_base_def is_aligned_def)
   apply (simp add:word_size kernel_base_def pd_bits_def pageBits_def)
   apply word_bitwise
   apply simp
  apply (clarsimp simp:obj_at_def)
  apply (subst (asm) is_aligned_neg_mask_eq
    [where p = p and n = pd_bits,symmetric])
   apply simp
  apply (drule(1) valid_pdpt_objs_pdD[rotated])+
  apply (clarsimp simp:entries_align_def)
  done

lemma in_pte_rangeD:
  "x \<in> pte_range v y \<Longrightarrow> x && ~~ mask 4 = y && ~~ mask 4"
  by (case_tac v,simp_all split:if_splits)

lemma in_pde_rangeD:
  "x \<in> pde_range v y \<Longrightarrow> x && ~~ mask 4 = y && ~~ mask 4"
  by (case_tac v,simp_all split:if_splits)

lemma mapM_x_store_pte_valid_pdpt2:
  "\<lbrace>valid_pdpt_objs and K (is_aligned ptr pt_bits)\<rbrace>
     mapM_x (\<lambda>x. store_pte x InvalidPTE) [ptr, ptr + 4 .e. ptr + 2 ^ pt_bits - 1]
   \<lbrace>\<lambda>_. valid_pdpt_objs\<rbrace>"
  apply (rule hoare_gen_asm)+
  apply (rule mapM_x_wp')
  apply (simp add:store_pte_def set_pt_def)
  apply (wp get_pt_wp get_object_wp)
  apply (clarsimp simp: mask_in_range
    split:Structures_A.kernel_object.splits
    arch_kernel_obj.splits)
  apply (rule conjI)
   apply (rule valid_entries_overwrite_0)
    apply (fastforce simp:ran_def obj_at_def)
   apply simp
  apply (simp add:fun_upd_def obj_at_def)
  apply (rule entries_align_pte_update)
   apply (drule (1) valid_pdpt_objs_ptD,simp)
  apply simp
  done

lemma mapM_x_store_pde_valid_pdpt2:
  "\<lbrace>valid_pdpt_objs and K (is_aligned pd pd_bits)\<rbrace>
       mapM_x (\<lambda>x. store_pde ((x << 2) + pd) pde.InvalidPDE)
        [0.e.(kernel_base >> 20) - 1]
       \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule mapM_x_wp')
  apply (simp add:store_pde_def set_pd_def)
  apply (wp get_pd_wp get_object_wp)
  apply (clarsimp simp: mask_in_range
    split:Structures_A.kernel_object.splits
    arch_kernel_obj.splits)
  apply (rule conjI)
   apply (rule valid_entries_overwrite_0)
    apply (fastforce simp:ran_def obj_at_def)
   apply simp
  apply (simp add:fun_upd_def obj_at_def)
  apply (rule entries_align_pde_update)
   apply (drule (1) valid_pdpt_objs_pdD,simp)
  apply simp
  done

lemma non_invalid_in_pde_range:
  "pde \<noteq> InvalidPDE
  \<Longrightarrow> x \<in> pde_range pde x"
  by (case_tac pde,simp_all)

lemma non_invalid_in_pte_range:
  "pte \<noteq> InvalidPTE
  \<Longrightarrow> x \<in> pte_range pte x"
  by (case_tac pte,simp_all)

lemma arch_recycle_cap_valid_pdpt[wp]:
  "\<lbrace>valid_pdpt_objs and valid_cap (cap.ArchObjectCap cap)
         and pspace_aligned and valid_arch_state\<rbrace>
      arch_recycle_cap is_final cap \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: arch_recycle_cap_def
             cong: arch_cap.case_cong split del: split_if)
  apply (rule hoare_pre)
   apply (wp |wpc | simp)+
     apply (simp add:swp_def)
     apply (wp mapM_x_store_pte_valid_pdpt2 static_imp_wp)
    apply (simp add:swp_def)
    apply (wp hoare_drop_imp
        mapM_x_store_pte_valid_pdpt2
      | wpc | simp)+
   apply (clarsimp simp:mapM_x_map)
   apply (wp mapM_x_store_pde_valid_pdpt2 static_imp_wp)
  apply (auto simp: valid_cap_def cap_aligned_def pt_bits_def
                    pageBits_def pd_bits_def)
  done

crunch valid_pdpt_objs[wp]: cancel_badged_sends "valid_pdpt_objs"
  (simp: crunch_simps filterM_mapM wp: crunch_wps ignore: filterM)

lemma recycle_cap_valid_pdpt[wp]:
  "\<lbrace>valid_pdpt_objs and invs and valid_cap cap\<rbrace>
        recycle_cap is_final cap \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: recycle_cap_def)
  apply (rule hoare_pre)
   apply (wp | wpc | simp | wp_once hoare_drop_imps)+
  apply auto
  done

lemma cap_recycle_valid_pdpt[wp]:
  "\<lbrace>invs and valid_pdpt_objs and real_cte_at slot\<rbrace> cap_recycle slot \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: cap_recycle_def unless_def)
  apply (wp get_cap_wp)
   apply (rule_tac Q="\<lambda>rv. invs and valid_pdpt_objs"
              and E="\<lambda>rv. valid_pdpt_objs" in hoare_post_impErr)
     apply (simp add: finalise_slot_def)
     apply (wp rec_del_invs)
    apply (clarsimp simp: cte_wp_at_caps_of_state caps_of_state_valid)
   apply simp
  apply simp
  apply (rule hoare_pre, wp)
   apply (strengthen real_cte_emptyable_strg)
   apply (wp cap_revoke_invs)
  apply simp
  done

crunch valid_pdpt_objs[wp]: cap_move, cap_insert "valid_pdpt_objs"

lemma invoke_cnode_valid_pdpt_objs[wp]:
  "\<lbrace>valid_pdpt_objs and invs and valid_cnode_inv i\<rbrace> invoke_cnode i \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: invoke_cnode_def)
  apply (rule hoare_pre)
   apply (wp get_cap_wp | wpc | simp split del: split_if)+
  apply (clarsimp)
  done

lemma as_user_valid_pdpt_objs[wp]:
  "\<lbrace>valid_pdpt_objs\<rbrace> as_user t m \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: as_user_def split_def)
  apply wp
  apply simp
  done

crunch valid_pdpt_objs[wp]: invoke_tcb "valid_pdpt_objs"
  (wp: check_cap_inv crunch_wps simp: crunch_simps
       ignore: check_cap_at)

lemma invoke_domain_valid_pdpt_objs[wp]:
  "\<lbrace>valid_pdpt_objs\<rbrace> invoke_domain t d \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  by (simp add: invoke_domain_def | wp)+

crunch valid_pdpt_objs[wp]: set_extra_badge, transfer_caps_loop "valid_pdpt_objs"
  (wp: transfer_caps_loop_pres)

crunch valid_pdpt_objs[wp]: send_ipc, send_signal,
    do_reply_transfer, invoke_irq_control, invoke_irq_handler "valid_pdpt_objs"
  (wp: crunch_wps simp: crunch_simps
         ignore: clearMemory const_on_failure set_object)

lemma valid_pdpt_objs_trans_state[simp]: "valid_pdpt_objs (trans_state f s) = valid_pdpt_objs s"
  apply (simp add: obj_valid_pdpt_def)
  done

lemma retype_region_valid_pdpt[wp]:
  "\<lbrace>valid_pdpt_objs\<rbrace> retype_region ptr bits o_bits type \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: retype_region_def split del: split_if)
  apply (wp | simp only: valid_pdpt_objs_trans_state trans_state_update[symmetric])+
  apply (clarsimp simp: retype_addrs_fold foldr_upd_app_if ranI
                 elim!: ranE split: split_if_asm simp del:fun_upd_apply)
  apply (simp add: default_object_def default_arch_object_def
            split: Structures_A.kernel_object.splits
    Structures_A.apiobject_type.split aobject_type.split)+
  apply (simp add:entries_align_def)
  done

lemma detype_valid_pdpt[elim!]:
  "valid_pdpt_objs s \<Longrightarrow> valid_pdpt_objs (detype S s)"
  by (auto simp add: detype_def ran_def)

crunch valid_pdpt_objs[wp]: create_word_objects, create_cap "valid_pdpt_objs"
  (ignore: clearMemory simp: crunch_simps)

lemma init_arch_objects_valid_pdpt:
  "\<lbrace>valid_pdpt_objs and pspace_aligned and valid_arch_state
           and K (orefs = retype_addrs ptr type n us)
           and K (range_cover ptr sz (obj_bits_api type us) n)\<rbrace>
     init_arch_objects type ptr n obj_sz orefs
   \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (rule hoare_gen_asm)+
  apply (simp add: init_arch_objects_def)
  apply (rule hoare_pre)
   apply (wp | wpc)+
     apply (rule_tac Q="\<lambda>rv. valid_pdpt_objs and pspace_aligned and valid_arch_state"
                  in hoare_post_imp, simp)
     apply (rule mapM_x_wp')
     apply (rule hoare_pre, wp copy_global_mappings_valid_pdpt_objs)
     apply clarsimp
     apply (drule retype_addrs_aligned[where sz = sz])
        apply (simp add:range_cover_def)
       apply (drule range_cover.sz,simp add:word_bits_def)
      apply (simp add:range_cover_def)
     apply (clarsimp simp:obj_bits_api_def pd_bits_def pageBits_def
       arch_kobj_size_def default_arch_object_def range_cover_def)+
   apply wp
  apply simp
  done

lemma delete_objects_valid_pdpt:
  "\<lbrace>valid_pdpt_objs\<rbrace> delete_objects ptr bits \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  by (rule delete_objects_reduct) (wp detype_valid_pdpt)

lemma invoke_untyped_valid_pdpt[wp]:
  "\<lbrace>valid_pdpt_objs and invs and ct_active and valid_untyped_inv uinv\<rbrace>
       invoke_untyped uinv \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (cases uinv)
  apply (clarsimp simp del:invoke_untyped.simps)
  apply (rename_tac s cref oref ptr tp us slots sz idx)
  proof -
    fix s cref oref ptr tp us slots sz idx
    assume cte_wp_at : "cte_wp_at (\<lambda>c. c = cap.UntypedCap (ptr && ~~ mask sz) sz idx) (cref,oref) s"
     have cte_at: "cte_wp_at (op = (cap.UntypedCap (ptr && ~~ mask sz) sz idx)) (cref,oref) s" (is "?cte_cond s")
       using cte_wp_at by (simp add:cte_wp_at_caps_of_state)
    assume desc_range: "ptr = ptr && ~~ mask sz \<longrightarrow> descendants_range_in {ptr..ptr + 2 ^ sz - 1} (cref,oref) s"
    assume  misc     : "distinct slots" "tp = CapTableObject \<longrightarrow> 0 < (us::nat)"
      " tp = Untyped \<longrightarrow> 4 \<le> (us::nat)"
      " idx \<le> unat (ptr && mask sz) \<or> ptr = ptr && ~~ mask sz"
      " invs s" "tp \<noteq> ArchObject ASIDPoolObj"
      " \<forall>slot\<in>set slots. cte_wp_at (op = cap.NullCap) slot s \<and> ex_cte_cap_wp_to is_cnode_cap slot s \<and> real_cte_at slot s"
      " ct_active s" "valid_pdpt_objs s"
    assume cover : "range_cover ptr sz (obj_bits_api tp us) (length slots)"
    assume vslot : "slots\<noteq> []"

    have pf : "invoke_untyped_proofs s (cref,oref) ptr tp us slots sz idx"
      using  cte_wp_at desc_range misc cover vslot
      apply (clarsimp simp:invoke_untyped_proofs_def cte_wp_at_caps_of_state)
      apply (drule(1) bspec)
      apply (clarsimp elim!:ex_cte_cap_wp_to_weakenE)
      done

    have of_nat_length: "(of_nat (length slots)::word32) - (1::word32) < (of_nat (length slots)::word32)"
       using vslot
       using range_cover.range_cover_le_n_less(1)[OF cover,where p = "length slots"]
       apply -
       apply (case_tac slots)
        apply clarsimp
       apply clarsimp
       apply (subst add.commute)
       apply (subst word_le_make_less[symmetric])
       apply (rule less_imp_neq)
       apply (simp add:minus_one_norm)
       apply (rule word_of_nat_less)
       apply auto
       done

    have sz_simp[simp]: "2 \<le> sz \<and> sz <word_bits"
       using misc cte_at cover
       apply -
       apply (clarsimp simp:cte_wp_at_caps_of_state)
       apply (drule caps_of_state_valid_cap,fastforce)
       apply (drule range_cover.sz)
       apply (clarsimp simp:valid_cap_def word_bits_conv)
       done

   have subset_stuff[simp]:
       "{ptr..ptr + of_nat (length slots) * 2 ^ obj_bits_api tp us - 1}
       \<subseteq> {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}" (is "?retype_range \<subseteq> ?usable_range")
      apply (rule range_cover_subset'[OF cover])
      apply (simp add:vslot)
      done

    note blah[simp del] = untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex

    note descendants_range[simp] = invoke_untyped_proofs.descendants_range[OF pf]
    note caps_no_overlap[simp] = invoke_untyped_proofs.caps_no_overlap[OF pf]

    -- "pspace_no_overlap :"
    have ps_no_overlap[simp]: "ptr && ~~ mask sz \<noteq> ptr \<Longrightarrow> pspace_no_overlap ptr sz s"
      using misc cte_wp_at cover
      apply clarsimp
      apply (erule(3) cte_wp_at_pspace_no_overlapI[OF _ _ _
                        range_cover.sz(1)[where 'a=32, folded word_bits_def]])
      done

    note ex_cte_no_overlap = invoke_untyped_proofs.ex_cte_no_overlap[OF pf]
    note cref_inv = invoke_untyped_proofs.cref_inv[OF pf]

    have slots_invD: "\<And>x. x \<in> set slots
      \<Longrightarrow> fst x \<notin> ?usable_range \<and> caps_of_state s x = Some cap.NullCap
          \<and> ex_cte_cap_wp_to is_cnode_cap x s
          \<and> real_cte_at x s"
      using cte_at misc
      apply -
      apply (drule(1) bspec)+
      apply (clarsimp simp: cte_wp_at_caps_of_state)+
      apply (drule ex_cte_no_overlap)
       apply simp
      done

    note kernel_window_inv[simp] = invoke_untyped_proofs.kernel_window_inv[OF pf]

    have nidx[simp]: "\<And>m. ptr + m - (ptr && ~~ mask sz)
      = (ptr && mask sz) + m"
       apply (subst word_plus_and_or_coroll2[symmetric,where w = "mask sz" and t = ptr])
       apply simp
       done

    have non_detype_idx_le[simp]: "ptr \<noteq>  ptr && ~~ mask sz \<Longrightarrow> idx < 2^sz"
       using misc cover
       apply clarsimp
       apply (frule le_mask_le_2p)
       apply (simp add:range_cover_def)+
       done

    have idx_compare:
      "\<lbrakk>unat ((ptr && mask sz) + of_nat (length slots) * 2 ^ obj_bits_api tp us) < 2^ sz;
        ptr \<noteq> ptr && ~~ mask sz \<rbrakk>
      \<Longrightarrow> (ptr && ~~ mask sz) + of_nat idx
      \<le> ptr + (of_nat (length slots) << obj_bits_api tp us)"
       apply (rule range_cover_idx_compare[OF cover ])
         apply assumption+
       apply (frule non_detype_idx_le)
       apply (erule less_imp_le)
       using misc
       apply simp
      done

    have idx_compare'[simp]:"unat ((ptr && mask sz) + (of_nat (length slots)<< obj_bits_api tp us)) \<le> 2 ^ sz"
      apply (rule le_trans[OF unat_plus_gt])
      apply (simp add:range_cover.unat_of_nat_n_shift[OF cover] range_cover_unat)
      apply (insert range_cover.range_cover_compare_bound[OF cover])
      apply simp
      done

    note neg_mask_add_mask = word_plus_and_or_coroll2[symmetric,where w = "mask sz" and t = ptr,symmetric]

    have usable_range_subset:
      "ptr && ~~ mask sz \<noteq> ptr
      \<Longrightarrow>usable_untyped_range
                     (cap.UntypedCap (ptr && ~~ mask sz) sz
                       (unat (ptr + (of_nat (length slots) << obj_bits_api tp us) - (ptr && ~~ mask sz))))
                    \<subseteq> usable_untyped_range (cap.UntypedCap (ptr && ~~ mask sz) sz idx)"
      apply (simp_all add:blah field_simps)
      apply (clarsimp simp:shiftl_t2n  add.assoc[symmetric] neg_mask_add_mask )
      apply (simp add:field_simps)
      apply (subst add.commute)
      apply (erule order_trans[OF idx_compare])
      apply (simp add:shiftl_t2n field_simps)+
      done

    have [simp]:"ptr \<noteq> 0"
      using cte_wp_at misc
      apply (clarsimp simp:cte_wp_at_caps_of_state)
      apply (drule(1) caps_of_state_valid)+
      apply (simp add:valid_cap_def)
      done

    have idx_compare''[simp]:
       "unat ((ptr && mask sz) + (of_nat (length slots) * (2::word32) ^ obj_bits_api tp us)) < 2 ^ sz
        \<Longrightarrow> ptr + of_nat (length slots) * 2 ^ obj_bits_api tp us - 1
        < ptr + of_nat (length slots) * 2 ^ obj_bits_api tp us"
      apply (rule minus_one_helper,simp)
      apply (rule neq_0_no_wrap)
      apply (rule word32_plus_mono_right_split)
      apply (simp add:shiftl_t2n range_cover_unat[OF cover] field_simps)
      apply (simp add:range_cover.sz[OF cover])+
      done

    note neg_mask_add_mask = word_plus_and_or_coroll2[symmetric,where w = "mask sz" and t = ptr,symmetric]

    have idx_compare'''[simp]:
      "\<lbrakk>unat (of_nat (length slots) * (2::word32) ^ obj_bits_api tp us) < 2 ^ sz;
       ptr && ~~ mask sz = ptr\<rbrakk>
      \<Longrightarrow> ptr + of_nat (length slots) * 2 ^ obj_bits_api tp us - 1
      < ptr + of_nat (length slots) * 2 ^ obj_bits_api tp us "
      apply (rule minus_one_helper,simp)
      apply (simp add:is_aligned_neg_mask_eq'[symmetric])
      apply (rule neq_0_no_wrap)
      apply (rule word32_plus_mono_right_split[where sz = sz])
       apply (simp add:is_aligned_mask)+
      done

    have detype_locale:"ptr && ~~ mask sz = ptr \<Longrightarrow> detype_locale (cap.UntypedCap (ptr && ~~ mask sz) sz idx) (cref,oref) s"
      using cte_at descendants_range misc
      by (simp add:detype_locale_def cte_at descendants_range_def2 blah invs_untyped_children)

    have detype_descendants_range_in:
      "ptr && ~~ mask sz = ptr \<Longrightarrow> descendants_range_in ?usable_range (cref,oref) (detype ?usable_range s)"
      using misc cte_at
      apply -
      apply (frule detype_invariants)
          apply simp
         using descendants_range
         apply (clarsimp simp:blah descendants_range_def2)
         apply (simp add: invs_untyped_children blah
               invs_valid_reply_caps invs_valid_reply_masters)+
      apply (subst valid_mdb_descendants_range_in)
       apply (clarsimp dest!:invs_mdb simp:detype_clear_um_independent)
      apply (frule detype_locale)
      apply (drule detype_locale.non_filter_detype[symmetric])
      apply (simp add:blah)
      using descendants_range(1)
      apply -
      apply (subst (asm)valid_mdb_descendants_range_in)
      apply (simp add:invs_mdb)
      apply simp
      done

    have detype_invs:
      "ptr && ~~ mask sz = ptr \<Longrightarrow> invs (detype ?usable_range  (clear_um {ptr..ptr + 2 ^ sz - 1} s))"
      apply (insert misc cte_at descendants_range)
      apply clarsimp
      apply (frule detype_invariants)
         apply simp
        apply (clarsimp simp:blah descendants_range_def2)
       apply ((simp add: invs_untyped_children blah
               invs_valid_reply_caps invs_valid_reply_masters)+)[6]
      done

      have delete_objects_rewrite:
      "ptr && ~~ mask sz = ptr \<Longrightarrow> delete_objects ptr sz =
      do y \<leftarrow> modify (clear_um {ptr + of_nat k |k. k < 2 ^ sz});
              modify (detype {ptr && ~~ mask sz..ptr + 2 ^ sz - 1})
      od"
      using cover
      apply (clarsimp simp:delete_objects_def freeMemory_def word_size_def)
      apply (subgoal_tac "is_aligned (ptr &&~~ mask sz) sz")
       apply (subst mapM_storeWord_clear_um)
          apply (simp)
         apply simp
        apply (simp add:less_imp_le)
       apply clarsimp
      apply (rule is_aligned_neg_mask)
      apply simp
      done

    note set_cap_free_index_invs_spec = set_free_index_invs[where cap = "cap.UntypedCap (ptr && ~~ mask sz) sz idx"
      ,unfolded free_index_update_def free_index_of_def,simplified]

    note msimp[simp add] =  misc neg_mask_add_mask
    show
      "\<lbrace>op = s\<rbrace>
          invoke_untyped (Invocations_A.untyped_invocation.Retype (cref, oref) (ptr && ~~ mask sz) ptr tp us slots)
      \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
    apply (clarsimp simp:mapM_x_def[symmetric])
    apply (case_tac "ptr && ~~ mask sz \<noteq> ptr ")
    -- "none detype case:"
    apply simp
    apply (wp mapM_x_wp'
      init_arch_objects_valid_pdpt[where sz = sz]
      retype_region_invs_extras[where sz = sz]
      retype_region_ret_folded | simp)+
    apply (rule_tac P = "cap = cap.UntypedCap (ptr && ~~ mask sz) sz idx" in hoare_gen_asm)
    apply (clarsimp simp:conj_comms bits_of_def region_in_kernel_window_def)
    apply (wp set_cap_no_overlap hoare_vcg_ball_lift set_cap_free_index_invs_spec
              set_cap_cte_wp_at set_cap_descendants_range_in set_cap_caps_no_overlap
              set_untyped_cap_caps_overlap_reserved set_cap_cte_cap_wp_to get_cap_wp)
   apply (insert cte_wp_at)
   apply (clarsimp simp:cte_wp_at_caps_of_state untyped_range.simps)
   apply (insert misc cover)
   apply (intro conjI)
      apply (clarsimp simp:field_simps range_cover_unat shiftl_t2n)
     apply simp
    apply (erule subset_trans[OF range_cover_subset'])
    apply (simp add:vslot)
   apply (clarsimp simp:blah word_and_le2)
   apply (clarsimp simp:blah field_simps add.assoc[symmetric] add.commute shiftl_t2n
                    dest!:idx_compare'')
   apply simp
  apply (wp mapM_x_wp'
      init_arch_objects_valid_pdpt[where sz = sz]
      retype_region_invs_extras[where sz = sz]
      retype_region_ret_folded | simp)+
    apply (rule_tac P = "cap = cap.UntypedCap (ptr && ~~ mask sz) sz idx" in hoare_gen_asm)
    apply (clarsimp simp:conj_comms bits_of_def region_in_kernel_window_def)
    apply (wp set_cap_no_overlap set_untyped_cap_invs_simple
              set_cap_cte_wp_at set_cap_caps_no_overlap
              set_untyped_cap_caps_overlap_reserved get_cap_wp)
   apply (rule_tac P = "cap = cap.UntypedCap ptr sz idx" in hoare_gen_asm)
   apply (clarsimp simp:bits_of_def delete_objects_rewrite)
   apply (wp get_cap_wp)
  apply (clarsimp simp:cte_wp_at_caps_of_state untyped_range.simps)
  apply (insert misc descendants_range cref_inv cte_at subset_stuff
      detype_locale detype_descendants_range_in detype_invs kernel_window_inv)
  apply (frule(1) valid_global_refsD2[OF _ invs_valid_global_refs])
  apply (clarsimp simp:cte_wp_at_caps_of_state invs_valid_objs
      untyped_range.simps bits_of_def conj_comms)
  apply (frule caps_of_state_valid_cap)
   apply (simp add:invs_valid_objs)
  apply (frule valid_cap_aligned)
  apply (clarsimp simp:cap_aligned_def)
  apply (frule intvl_range_conv)
   apply (drule range_cover.sz)
   apply (simp add:less_imp_le)
  apply (simp add:detype_clear_um_independent)
  apply (intro conjI)
      apply (rule pspace_no_overlap_detype)
        apply (rule caps_of_state_valid)
         apply simp+
      apply (simp add:invs_psp_aligned invs_valid_objs)+
     apply (rule caps_no_overlap_detype[OF caps_no_overlap])
    apply (simp add:detype_clear_um_independent[symmetric])
    apply (rule detype_valid_pdpt)
    apply (simp add:clear_um.pspace)
   apply (cut_tac invoke_untyped_proofs.usable_range_disjoint[OF pf])
   apply (simp add:shiftl_t2n field_simps)
  apply (simp add:clear_um_def)
 apply (erule descendants_range_in_subseteq)
 apply simp
 done
qed

crunch valid_pdpt_objs[wp]: perform_asid_pool_invocation,
     perform_asid_control_invocation "valid_pdpt_objs"
  (ignore: delete_objects wp: delete_objects_valid_pdpt static_imp_wp)

abbreviation (input)
  "safe_pt_range \<equiv> \<lambda>slots s. obj_at (\<lambda>ko. \<exists>pt. ko = ArchObj (PageTable pt)
                                    \<and> (\<forall>x\<in>set (tl slots). pt (ucast (x && mask pt_bits >> 2))
                                      = pte.InvalidPTE))
                              (hd slots && ~~ mask pt_bits) s"

abbreviation (input)
  "safe_pd_range \<equiv> \<lambda>slots s. obj_at (\<lambda>ko. \<exists>pd. ko = ArchObj (PageDirectory pd)
                                    \<and> (\<forall>x\<in>set (tl slots). pd (ucast (x && mask pd_bits >> 2))
                                      = pde.InvalidPDE))
                              (hd slots && ~~ mask pd_bits) s"

definition
  "page_inv_entries_pre entries \<equiv>
   let slots = (case entries of Inl (pte, slots) \<Rightarrow> slots | Inr (pde, slots) \<Rightarrow> slots)
   in (if \<exists>sl. slots = [sl]
    then case entries of
        Inl (pte, _) \<Rightarrow> obj_at (\<lambda>ko. \<exists>pt pte. ko = ArchObj (PageTable pt)
                     \<and> pt (ucast (hd slots && mask pt_bits >> 2) && ~~ mask 4) = pte
                     \<and> pte_range_sz pte = 0)
                 (hd slots && ~~ mask pt_bits)
            and K (pte_range_sz pte = 0)
      | Inr (pde, _) \<Rightarrow> obj_at (\<lambda>ko. \<exists>pd pde. ko = ArchObj (PageDirectory pd)
                     \<and> pd (ucast (head slots && mask pd_bits >> 2) && ~~ mask 4)
                            = pde \<and> pde_range_sz pde = 0)
                 (hd slots && ~~ mask pd_bits)
           and K (pde_range_sz pde = 0)
    else  (\<lambda>s. (\<exists>p. is_aligned p 6 \<and> slots = map (\<lambda>x. x + p) [0, 4 .e. 0x3C])))
   and K (case entries of Inl (pte,slots) \<Rightarrow> pte \<noteq> InvalidPTE
     | Inr (pde,slots) \<Rightarrow> pde \<noteq> InvalidPDE)"

definition
  "page_inv_entries_safe entries \<equiv>
   let slots = (case entries of Inl (pte, slots) \<Rightarrow> slots | Inr (pde, slots) \<Rightarrow> slots)
   in if \<exists>sl. slots = [sl]
    then case entries of
        Inl (pte, _) \<Rightarrow> obj_at (\<lambda>ko. \<exists>pt pte. ko = ArchObj (PageTable pt)
                     \<and> pt (ucast (hd slots && mask pt_bits >> 2) && ~~ mask 4) = pte
                     \<and> pte_range_sz pte = 0)
                 (hd slots && ~~ mask pt_bits)
            and K (pte_range_sz pte = 0)
      | Inr (pde, _) \<Rightarrow> obj_at (\<lambda>ko. \<exists>pd pde. ko = ArchObj (PageDirectory pd)
                     \<and> pd (ucast (head slots && mask pd_bits >> 2) && ~~ mask 4)
                            = pde \<and> pde_range_sz pde = 0)
                 (hd slots && ~~ mask pd_bits)
           and K (pde_range_sz pde = 0)
    else  (\<lambda>s. (\<exists>p. is_aligned p 6 \<and> slots = map (\<lambda>x. x + p) [0, 4 .e. 0x3C]
                  \<and> (case entries of
                     Inl (pte, _) \<Rightarrow> safe_pt_range slots s
                   | Inr (pde, _) \<Rightarrow> safe_pd_range slots s
                     )))"

definition
  "page_inv_duplicates_valid iv \<equiv> case iv of
         PageMap asid cap ct_slot entries \<Rightarrow>
            page_inv_entries_safe entries
       | PageRemap asid entries \<Rightarrow>
            page_inv_entries_safe entries
       | _ \<Rightarrow> \<top>"

lemma pte_range_interD:
 "pte_range pte p \<inter> pte_range pte' p' \<noteq> {}
  \<Longrightarrow> pte \<noteq> InvalidPTE \<and> pte' \<noteq> InvalidPTE
      \<and> p && ~~ mask 4 = p' && ~~ mask 4"
  apply (drule WordLemmaBucket.int_not_emptyD)
  apply (case_tac pte,simp_all split:if_splits)
   apply (case_tac pte',simp_all split:if_splits)
   apply clarsimp
   apply (case_tac pte',simp_all split:if_splits)
  apply (case_tac pte', simp_all split:if_splits)
  done

lemma pde_range_interD:
 "pde_range pde p \<inter> pde_range pde' p' \<noteq> {}
  \<Longrightarrow> pde \<noteq> InvalidPDE \<and> pde' \<noteq> InvalidPDE
      \<and> p && ~~ mask 4 = p' && ~~ mask 4"
  apply (drule WordLemmaBucket.int_not_emptyD)
  apply (case_tac pde,simp_all split:if_splits)
     apply (case_tac pde',simp_all split:if_splits)
    apply (case_tac pde',simp_all split:if_splits)
   apply clarsimp
   apply (case_tac pde', simp_all split:if_splits)
  apply (case_tac pde', simp_all split:if_splits)
  done

lemma pte_range_sz_le:
  "(pte_range_sz pte) \<le> 4"
  by (case_tac pte,simp_all)

lemma pde_range_sz_le:
  "(pde_range_sz pde) \<le> 4"
  by (case_tac pde,simp_all)

(* BUG , revisit the following lemmas , moved from ArchAcc_R.thy *)
lemma mask_pd_bits_shift_ucast_align[simp]:
  "is_aligned (ucast (p && mask pd_bits >> 2)::12 word) 4 =
   is_aligned ((p::word32) >> 2) 4"
  by (clarsimp simp: is_aligned_mask mask_def pd_bits) word_bitwise

lemma mask_pt_bits_shift_ucast_align[simp]:
  "is_aligned (ucast (p && mask pt_bits >> 2)::word8) 4 =
   is_aligned ((p::word32) >> 2) 4"
  by (clarsimp simp: is_aligned_mask mask_def pt_bits_def pageBits_def)
     word_bitwise

lemma store_pte_valid_pdpt:
  "\<lbrace>valid_pdpt_objs and page_inv_entries_safe (Inl (pte, slots))\<rbrace>
       store_pte (hd slots) pte \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp:page_inv_entries_safe_def split:if_splits)
   apply (clarsimp simp:store_pte_def set_pt_def)
   apply (wp get_pt_wp get_object_wp)
   apply (clarsimp simp:obj_at_def
     split:pte.splits arch_kernel_obj.splits)
  apply (rule conjI)
    apply (drule(1) valid_pdpt_objs_ptD)
    apply (rule valid_entries_overwrite_0)
     apply simp
    apply (case_tac pte)
     apply simp+
    apply (case_tac "pta p",simp_all)
    apply (clarsimp simp: is_aligned_neg_mask_eq)
   apply (simp add:fun_upd_def)
   apply (rule entries_align_pte_update)
    apply (drule (1) valid_pdpt_objs_ptD,simp)
   apply simp
  apply (simp add:hd_map_simp upto_enum_def upto_enum_step_def)
  apply (clarsimp simp:store_pte_def set_pt_def)
  apply (wp get_pt_wp get_object_wp)
  apply (clarsimp simp:obj_at_def
     split:pte.splits arch_kernel_obj.splits)
  apply (drule(1) valid_pdpt_objs_ptD)
  apply (rule conjI)
   apply (rule valid_entries_overwrite_0)
    apply simp
   apply (rule ccontr)
   apply (drule pte_range_interD)
   apply clarsimp
   apply (simp add:ucast_neg_mask)
   apply (subst (asm) is_aligned_neg_mask_eq[where n = 4])
    apply (rule is_aligned_shiftr[OF is_aligned_andI1])
    apply simp
   apply (drule_tac x = "((p && ~~ mask pt_bits)  + ((ucast pa) << 2))" in bspec)
    apply (clarsimp simp: tl_map_simp upto_0_to_n2 image_def)
    apply (rule_tac x = "unat (((ucast pa)::word32) - (p && mask pt_bits >> 2))" in bexI)
     apply (simp add:ucast_nat_def shiftl_t2n mask_out_sub_mask)
     apply (subst shiftl_t2n[where n = 2,simplified field_simps,simplified,symmetric])
     apply (subst shiftr_shiftl1)
      apply simp+
     apply (subst is_aligned_neg_mask_eq)
      apply (erule is_aligned_andI1[OF is_aligned_weaken])
      apply simp
     apply simp
    apply simp
    apply (drule_tac s = "ucast (p && mask pt_bits >> 2)" in sym)
    apply (simp add:mask_out_sub_mask field_simps)
    apply (drule_tac f = "ucast::(word8\<Rightarrow>word32)" in arg_cong)
    apply (simp add:ucast_pt_index pt_bits_def pageBits_def)
    apply (simp add:unat_ucast_8_32)
    apply (rule conjI)
     apply (subgoal_tac "unat (pa && mask 4)\<noteq> 0")
      apply simp
     apply (simp add:unat_gt_0)
    apply (rule unat_less_helper)
    apply (rule le_less_trans[OF word_and_le1])
    apply (simp add:mask_def)
   apply (simp add:field_simps neg_mask_add_mask)
   apply (thin_tac "ucast y = x" for y x)
   apply (subst (asm) less_mask_eq[where n = pt_bits])
    apply (rule shiftl_less_t2n)
     apply (simp add:pt_bits_def pageBits_def)
     apply word_bitwise
    apply (simp add:pt_bits_def pageBits_def)
   apply (subst (asm) shiftl_shiftr_id)
    apply simp
   apply (simp,word_bitwise)
   apply (simp add:ucast_ucast_id)
  apply (simp add:fun_upd_def entries_align_def)
  apply (rule is_aligned_weaken[OF _ pte_range_sz_le])
  apply (simp add:is_aligned_shiftr)
  done

lemma store_pde_valid_pdpt:
  "\<lbrace>valid_pdpt_objs and page_inv_entries_safe (Inr (pde, slots))\<rbrace>
       store_pde (hd slots) pde \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp:page_inv_entries_safe_def split:if_splits)
   apply (clarsimp simp:store_pde_def set_pd_def)
   apply (wp get_pd_wp get_object_wp)
   apply (clarsimp simp:obj_at_def
     split:pde.splits arch_kernel_obj.splits)
   apply (drule(1) valid_pdpt_objs_pdD)
   apply (rule conjI)
    apply (rule valid_entries_overwrite_0)
     apply simp
    apply (case_tac pde,simp_all)
     apply (case_tac "pda p",simp_all)
     apply (clarsimp simp: is_aligned_neg_mask_eq)
    apply (case_tac "pda p",simp_all)
    apply (clarsimp simp: is_aligned_neg_mask_eq)
   apply (simp add:fun_upd_def)
   apply (rule entries_align_pde_update)
    apply simp+
  apply (simp add:hd_map_simp upto_enum_def upto_enum_step_def)
  apply (clarsimp simp:store_pde_def set_pd_def)
  apply (wp get_pd_wp get_object_wp)
  apply (clarsimp simp:obj_at_def
     split:pde.splits arch_kernel_obj.splits)
  apply (drule(1) valid_pdpt_objs_pdD)
  apply (rule conjI)
   apply (rule valid_entries_overwrite_0)
    apply simp
   apply (rule ccontr)
   apply (drule pde_range_interD)
   apply clarsimp
   apply (simp add:ucast_neg_mask)
   apply (subst (asm) is_aligned_neg_mask_eq[where n = 4])
    apply (rule is_aligned_shiftr[OF is_aligned_andI1])
    apply simp
   apply (drule_tac x = "((p && ~~ mask pd_bits)  + ((ucast pa) << 2))" in bspec)
    apply (clarsimp simp: tl_map_simp upto_0_to_n2 image_def)
    apply (rule_tac x = "unat (((ucast pa)::word32) - (p && mask pd_bits >> 2))" in bexI)
     apply (simp add:ucast_nat_def shiftl_t2n mask_out_sub_mask)
     apply (subst shiftl_t2n[where n = 2,simplified field_simps,simplified,symmetric])
     apply (subst shiftr_shiftl1)
      apply simp+
     apply (subst is_aligned_neg_mask_eq)
      apply (erule is_aligned_andI1[OF is_aligned_weaken])
      apply simp
     apply simp
    apply simp
    apply (drule_tac s = "ucast (p && mask pd_bits >> 2)" in sym)
    apply (simp add:mask_out_sub_mask field_simps)
    apply (drule_tac f = "ucast::(12 word\<Rightarrow>word32)" in arg_cong)
    apply (simp add:ucast_pd_index pd_bits_def pageBits_def)
    apply (simp add:unat_ucast_12_32)
    apply (rule conjI)
     apply (subgoal_tac "unat (pa && mask 4)\<noteq> 0")
      apply simp
     apply (simp add:unat_gt_0)
    apply (rule unat_less_helper)
    apply (rule le_less_trans[OF word_and_le1])
    apply (simp add:mask_def)
   apply (simp add:field_simps neg_mask_add_mask)
   apply (thin_tac "ucast y = x" for y x)
   apply (subst (asm) less_mask_eq[where n = pd_bits])
    apply (rule shiftl_less_t2n)
     apply (simp add:pd_bits_def pageBits_def)
     apply word_bitwise
    apply (simp add:pd_bits_def pageBits_def)
   apply (subst (asm) shiftl_shiftr_id)
     apply simp
    apply (simp,word_bitwise)
   apply (simp add:ucast_ucast_id)
  apply (simp add:entries_align_def)
  apply (rule is_aligned_weaken[OF _ pde_range_sz_le])
  apply (simp add:is_aligned_shiftr)
  done

lemma set_cap_page_inv_entries_safe:
  "\<lbrace>page_inv_entries_safe x\<rbrace> set_cap y z \<lbrace>\<lambda>_. page_inv_entries_safe x\<rbrace>"
  apply (simp add:page_inv_entries_safe_def set_cap_def split_def
    get_object_def set_object_def)
  apply (wp | wpc)+
  apply (case_tac x)
  apply (auto simp:obj_at_def
    Let_def split:if_splits option.splits)
  done

crunch valid_pdpt[wp]: pte_check_if_mapped, pde_check_if_mapped "valid_pdpt_objects"

lemma perform_page_valid_pdpt[wp]:
  "\<lbrace>valid_pdpt_objs and valid_page_inv pinv and page_inv_duplicates_valid pinv\<rbrace>
        perform_page_invocation pinv \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: perform_page_invocation_def page_inv_duplicates_valid_def)
  apply (cases pinv,
         simp_all add: mapM_discarded page_inv_entries_safe_def
            split: sum.split arch_cap.split option.split,
         safe intro!: hoare_gen_asm hoare_gen_asm[unfolded K_def],
         simp_all add: mapM_x_Nil mapM_x_Cons mapM_x_map)
            apply (wp store_pte_valid_pdpt store_pde_valid_pdpt get_master_pte_wp get_master_pde_wp
                      store_pte_non_master_valid_pdpt store_pde_non_master_valid_pdpt
                      mapM_x_wp'[OF store_invalid_pte_valid_pdpt
                        [where pte=pte.InvalidPTE, simplified]]
                      mapM_x_wp'[OF store_invalid_pde_valid_pdpt
                        [where pde=pde.InvalidPDE, simplified]]
                      set_cap_page_inv_entries_safe
                      hoare_vcg_imp_lift[OF set_cap_arch_obj_neg] hoare_vcg_all_lift
                 | clarsimp simp: valid_page_inv_def cte_wp_at_weakenE[OF _ TrueI] obj_at_def
                                  pte_range_sz_def pde_range_sz_def swp_def valid_page_inv_def
                                  valid_slots_def page_inv_entries_safe_def pte_check_if_mapped_def
                                  pde_check_if_mapped_def
                           split: pte.splits pde.splits
                 | wp_once hoare_drop_imps)+
  done

definition
  "pti_duplicates_valid iv \<equiv>
   case iv of PageTableMap cap ct_slot pde pd_slot
     \<Rightarrow> obj_at (\<lambda>ko. \<exists>pd pde. ko = ArchObj (PageDirectory pd)
                     \<and> pd (ucast (pd_slot && mask pd_bits >> 2) && ~~ mask 4)
                            = pde \<and> pde_range_sz pde = 0)
                 (pd_slot && ~~ mask pd_bits)

           and K (pde_range_sz pde = 0)
  | _ \<Rightarrow> \<top>"


definition
  "invocation_duplicates_valid i \<equiv>
   case i of
     InvokeArchObject (InvokePage pi) \<Rightarrow> page_inv_duplicates_valid pi
   | InvokeArchObject (InvokePageTable pti) \<Rightarrow> pti_duplicates_valid pti
   | _ \<Rightarrow> \<top>"

lemma perform_page_table_valid_pdpt[wp]:
  "\<lbrace>valid_pdpt_objs and valid_pti pinv and pti_duplicates_valid pinv\<rbrace>
      perform_page_table_invocation pinv \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: perform_page_table_invocation_def split_def
             cong: page_table_invocation.case_cong
                   option.case_cong cap.case_cong arch_cap.case_cong)
  apply (rule hoare_pre)
   apply (wp store_pde_non_master_valid_pdpt hoare_vcg_ex_lift
             set_cap_arch_obj mapM_x_store_pte_valid_pdpt2
              | wpc
              | simp add: swp_def
              | strengthen all_imp_ko_at_from_ex_strg)+
  apply (clarsimp simp: pti_duplicates_valid_def valid_pti_def)
  apply (auto simp: obj_at_def cte_wp_at_caps_of_state valid_cap_simps
                    cap_aligned_def pt_bits_def pageBits_def
            intro!: inj_onI)
  done

lemma perform_page_directory_valid_pdpt[wp]:
  "\<lbrace>valid_pdpt_objs and valid_pdi pinv\<rbrace>
      perform_page_directory_invocation pinv \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: perform_page_directory_invocation_def split_def)
  apply (rule hoare_pre)
   apply (wp | wpc | simp)+
  done

lemma perform_invocation_valid_pdpt[wp]:
  "\<lbrace>invs and ct_active and valid_invocation i and valid_pdpt_objs
           and invocation_duplicates_valid i\<rbrace>
      perform_invocation blocking call i
         \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (cases i, simp_all)
  apply (wp send_signal_interrupt_states | simp)+
  apply (clarsimp simp: invocation_duplicates_valid_def)
  apply (wp | wpc | simp)+
  apply (simp add: arch_perform_invocation_def)
  apply (rule hoare_pre)
  apply (wp | wpc | simp)+
  apply (auto simp: valid_arch_inv_def invocation_duplicates_valid_def)
  done

lemma neg_mask_pt_6_4:
  "(ptr && mask pt_bits >> 2) && ~~ mask 4 =
   (ptr::word32) && ~~ mask 6 && mask pt_bits >> 2"
  apply (simp add:pt_bits_def pageBits_def)
  apply word_bitwise
  apply (simp add:word_size)
  done

lemma neg_mask_pd_6_4:
  "(ptr && mask pd_bits >> 2) && ~~ mask 4 =
   (ptr::word32) && ~~ mask 6 && mask pd_bits >> 2"
  apply (simp add:pd_bits_def pageBits_def)
  apply word_bitwise
  apply (simp add:word_size)
  done

lemma mask_out_same_pt:
  "\<lbrakk>is_aligned p 6; x < 2 ^ 6 \<rbrakk> \<Longrightarrow> p + x && ~~ mask pt_bits = p && ~~ mask pt_bits"
  apply (subst mask_lower_twice[symmetric,where n = 6])
   apply (simp add:pt_bits_def pageBits_def)
  apply (simp add:is_aligned_add_helper)
  done

lemma mask_out_same_pd:
  "\<lbrakk>is_aligned p 6; x < 2 ^ 6 \<rbrakk> \<Longrightarrow> p + x && ~~ mask pd_bits = p && ~~ mask pd_bits"
  apply (subst mask_lower_twice[symmetric,where n = 6])
   apply (simp add:pd_bits_def pageBits_def)
  apply (simp add:is_aligned_add_helper)
  done

lemma ensure_safe_mapping_ensures[wp]:
  "\<lbrace>valid_pdpt_objs and (case entries of (Inl (SmallPagePTE _ _ _, [_])) \<Rightarrow> \<top>
                  | (Inl (SmallPagePTE _ _ _, _)) \<Rightarrow> \<bottom>
                  | (Inl (LargePagePTE _ _ _, [])) \<Rightarrow> \<bottom>
                  | (Inr (SectionPDE _ _ _ _, [_])) \<Rightarrow> \<top>
                  | (Inr (SuperSectionPDE _ _ _, [])) \<Rightarrow> \<bottom>
                  | (Inr (SectionPDE _ _ _ _, _)) \<Rightarrow> \<bottom>
                  | _ \<Rightarrow> page_inv_entries_pre entries)\<rbrace>
     ensure_safe_mapping entries
   \<lbrace>\<lambda>rv. page_inv_entries_safe entries\<rbrace>,-"
  proof -
    have [simp]:
      "\<And>s a. page_inv_entries_pre (Inl (pte.InvalidPTE, a)) s \<Longrightarrow>
      page_inv_entries_safe (Inl (pte.InvalidPTE, a)) s"
      apply (clarsimp simp:page_inv_entries_pre_def page_inv_entries_safe_def
        split:if_splits)
      done
    have name_pre:
      "\<And>F P Q. (\<And>s. P s \<Longrightarrow> \<lbrace>op = s \<rbrace> F \<lbrace>Q\<rbrace>, -) \<Longrightarrow> \<lbrace>P\<rbrace> F \<lbrace>Q\<rbrace>,-"
      apply (simp add:validE_R_def validE_def)
      apply (rule hoare_name_pre_state)
      apply assumption
      done
    have mask_neg_mask_order[simp]:
      "\<And>a m n. a && ~~ mask m && mask n = a && mask n && ~~ mask m"
       by (simp add:word_bw_comms word_bw_lcs)
    have align_entry_ptD:
      "\<And>pt m x xb xc. \<lbrakk>pt m = pte.LargePagePTE x xb xc; entries_align pte_range_sz pt\<rbrakk>
       \<Longrightarrow> is_aligned m 4"
      apply (simp add:entries_align_def)
      apply (drule_tac x = m in spec,simp)
      done
    have align_entry_pdD:
      "\<And>pd m x xb xc. \<lbrakk>pd m = pde.SuperSectionPDE x xb xc; entries_align pde_range_sz pd\<rbrakk>
       \<Longrightarrow> is_aligned m 4"
      apply (simp add:entries_align_def)
      apply (drule_tac x = m in spec,simp)
      done
    have pt_offset_bitwise[simp]:"\<And>a. (ucast ((a::word32) && mask pt_bits && ~~ mask 6  >> 2)::word8)
      = (ucast (a  && mask pt_bits >> 2)::word8) && ~~ mask 4"
    apply (simp add:pt_bits_def pageBits_def mask_def)
    apply word_bitwise
    done
    have pd_offset_bitwise[simp]:"\<And>a. (ucast ((a::word32) && mask pd_bits && ~~ mask 6  >> 2)::12 word)
      = (ucast (a  && mask pd_bits >> 2)::12 word) && ~~ mask 4"
    apply (simp add:pt_bits_def pageBits_def mask_def pd_bits_def)
    apply word_bitwise
    done
    have mask_neq_0:
      "\<And>z zs xa p g. \<lbrakk>[0 :: word32, 4 .e. 0x3C] = z # zs; xa \<in> set zs; is_aligned p 6; 6 \<le> g\<rbrakk>
         \<Longrightarrow> (p + xa && mask g >> 2) && mask 4 \<noteq> 0"
     apply (rule ccontr)
      apply (simp add:is_aligned_mask[symmetric])
       apply (drule is_aligned_shiftl[where n = 6 and m = 2,simplified])
      apply (subst (asm) shiftr_shiftl1)
       apply simp+
      apply (subst (asm) is_aligned_neg_mask_eq)
       apply (rule is_aligned_andI1)
       apply (erule aligned_add_aligned)
        apply (clarsimp simp :upto_enum_def upto_enum_step_def
         Fun.comp_def upto_0_to_n2 is_aligned_mult_triv2[where n = 2,simplified])
       apply simp
      apply (simp add:is_aligned_mask mask_twice
        pt_bits_def pageBits_def min_def)
      apply (subst (asm) is_aligned_mask[symmetric])
      apply (subst (asm) is_aligned_add_helper)
       apply simp
      apply (clarsimp simp :upto_enum_def upto_enum_step_def
         Fun.comp_def upto_0_to_n2)
      apply (subst shiftl_t2n
        [where n = 2,simplified field_simps,simplified,symmetric])+
      apply (rule shiftl_less_t2n[where m = 6,simplified])
       apply (rule word_of_nat_less)
       apply simp
      apply simp
     apply (clarsimp simp :upto_enum_def upto_enum_step_def
         Fun.comp_def upto_0_to_n2)
     apply (cut_tac x = "of_nat x" and n = 2 in word_power_nonzero)
        apply (simp add:word_of_nat_less word_bits_def)+
      apply (simp add: of_nat_neq_0)
     apply simp
     done 
    have neq_pt_offset: "\<And>z zs xa (p::word32). \<lbrakk>[0 , 4 .e. 0x3C] = z # zs;
        xa \<in> set zs;is_aligned p 6 \<rbrakk> \<Longrightarrow>
        ucast (p + xa && mask pt_bits >> 2) && ~~ mask 4 \<noteq> ((ucast (p + xa && mask pt_bits >> 2))::word8)"
      apply (rule ccontr)
      apply (simp add:mask_out_sub_mask ucast_and_mask[symmetric])
      apply (drule arg_cong[where f = unat])
      apply (simp add:unat_ucast)
      apply (subst (asm) mod_less)
       apply (rule unat_less_helper)
       apply (rule le_less_trans[OF word_and_le1])
       apply (simp add:mask_def)
      apply (simp add:unat_eq_0)
      apply (drule(2) mask_neq_0[of _ _ _ _ pt_bits])
       apply (simp add:pt_bits_def pageBits_def)+
      done
    have neq_pd_offset: "\<And>z zs xa (p::word32). \<lbrakk>[0 , 4 .e. 0x3C] = z # zs;
        xa \<in> set zs;is_aligned p 6 \<rbrakk> \<Longrightarrow>
        ucast (p + xa && mask pd_bits >> 2) && ~~ mask 4 \<noteq> ((ucast (p + xa && mask pd_bits >> 2)) :: 12 word)"
      apply (simp add:mask_out_sub_mask)
      apply (rule ccontr)
      apply (simp add:mask_out_sub_mask ucast_and_mask[symmetric])
      apply (drule arg_cong[where f = unat])
      apply (simp add:unat_ucast)
      apply (subst (asm) mod_less)
       apply (rule unat_less_helper)
       apply (rule le_less_trans[OF word_and_le1])
       apply (simp add:mask_def)
      apply (simp add:unat_eq_0)
      apply (drule(2) mask_neq_0[of _ _ _ _ pd_bits])
       apply (simp add:pd_bits_def pageBits_def)+
      done
    have invalid_pteI:
      "\<And>a pt x y z. \<lbrakk>valid_pt_entries pt; (a && ~~ mask 4) \<noteq> a;
       pt (a && ~~ mask 4) = pte.LargePagePTE x y z \<rbrakk>
       \<Longrightarrow> pt a = pte.InvalidPTE"
      apply (drule(1) valid_entriesD[rotated])
      apply (case_tac "pt a"; simp add:mask_lower_twice is_aligned_neg_mask split:if_splits)
      apply fastforce
      done
    have invalid_pdeI:
      "\<And>a pd x y z. \<lbrakk>valid_pd_entries pd; (a && ~~ mask 4) \<noteq> a;
       pd (a && ~~ mask 4) = pde.SuperSectionPDE x y z \<rbrakk>
       \<Longrightarrow> pd a = pde.InvalidPDE"
      apply (drule(1) valid_entriesD[rotated])
      apply (case_tac "pd a",
        simp_all add:mask_lower_twice is_aligned_neg_mask
        split:if_splits)
      apply fastforce
      done
    have inj[simp]:
      "\<And>p. is_aligned (p::word32) 6 \<Longrightarrow> inj_on (\<lambda>x. toEnum x * 4 + p) {Suc 0..<16}"
      apply (clarsimp simp:inj_on_def)
      apply (subst (asm) shiftl_t2n[where n = 2,simplified field_simps,simplified,symmetric])+
      apply (drule arg_cong[where f = "\<lambda>x. x >> 2"])
      apply (simp add:shiftl_shiftr_id word_of_nat_less)
      apply (simp add:of_nat_inj)
      done

  show ?thesis
  apply (rule name_pre)
  apply (case_tac entries)
   apply (case_tac a, case_tac aa)
     apply (simp add:page_inv_entries_pre_def page_inv_entries_safe_def
       | wp | intro conjI impI)+
     apply (simp split:list.splits add:page_inv_entries_pre_def)+
    apply (rename_tac obj_ref vm_attributes cap_rights slot slots)
    apply (elim conjE exE)
    apply (subst mapME_x_Cons)
    apply simp
    apply wp
     apply (rule_tac Q' = "\<lambda>r s. \<forall>x \<in> set slots. obj_at
                (\<lambda>ko. \<exists>pt. ko = ArchObj (PageTable pt) \<and>
                 pt (ucast (x && mask pt_bits >> 2)) = pte.InvalidPTE)
                (hd (slot # slots) && ~~ mask pt_bits) s" in hoare_post_imp_R)
      apply (wp mapME_x_accumulate_checks[where Q = "\<lambda>s. valid_pdpt_objs s"] )
          apply (wp get_master_pte_wp| wpc | simp)+
         apply clarsimp
         apply (frule_tac x = xa in mask_out_same_pt)
          apply (clarsimp simp:upto_enum_def upto_enum_step_def upto_0_to_n2)
          apply (erule notE)
          apply (subst shiftl_t2n[where n = 2,simplified field_simps,simplified,symmetric])
          apply (rule shiftl_less_t2n[where m = 6,simplified])
           apply (simp add:word_of_nat_less)
          apply simp
         apply (frule_tac x = z in mask_out_same_pt)
          apply (clarsimp simp:upto_enum_def upto_enum_step_def upto_0_to_n2)
         apply (clarsimp simp:field_simps obj_at_def
           split:pte.splits)
         apply (intro conjI impI)
           apply (clarsimp)
           apply (drule(1) valid_pdpt_objs_ptD)
           apply (frule align_entry_ptD,simp)
           apply (simp add:is_aligned_neg_mask_eq)
          apply clarsimp
          apply (drule(1) valid_pdpt_objs_ptD,clarify)
          apply (erule(4) invalid_pteI[OF _ neq_pt_offset])
         apply clarsimp
         apply (drule(1) valid_pdpt_objs_ptD,clarify)
         apply (frule align_entry_ptD,simp)
         apply (simp add:is_aligned_neg_mask_eq)
        apply (wp hoare_drop_imps |wpc|simp)+
      apply (clarsimp simp:upto_enum_def upto_enum_step_def
        upto_0_to_n2 Fun.comp_def distinct_map)
     apply (intro exI conjI,fastforce+)
     apply (simp add:obj_at_def hd_map_simp
         upto_0_to_n2 upto_enum_def upto_enum_step_def)
     apply (frule_tac x = 1 in bspec,fastforce+)
    apply ((wp hoare_drop_imps |wpc|simp)+)[1]
   apply (simp add:page_inv_entries_pre_def page_inv_entries_safe_def
       | wp | intro conjI impI)+
    apply (simp split:list.splits add:page_inv_entries_pre_def mapME_singleton)
    apply (wp get_master_pte_wp |wpc | simp)+
    apply (clarsimp simp:obj_at_def split:pte.splits)
   apply (clarsimp simp:page_inv_entries_safe_def split:list.splits)
  apply (simp split:list.splits add:page_inv_entries_pre_def mapME_singleton)
  apply (case_tac b,case_tac a)
     apply ((simp add:page_inv_entries_pre_def page_inv_entries_safe_def
       | wp | intro conjI impI)+)[1]
    apply simp
    apply wp[1]
   apply (simp split:list.splits add:page_inv_entries_pre_def mapME_singleton)
   apply (wp get_master_pde_wp | wpc | simp)+
   apply (clarsimp simp:obj_at_def page_inv_entries_safe_def
     split:pde.splits)
  apply (simp split:list.splits if_splits
    add:page_inv_entries_pre_def Let_def page_inv_entries_safe_def)
  apply (elim conjE exE)
  apply (subst mapME_x_Cons)
  apply simp
  apply wp
   apply (rule_tac Q' = "\<lambda>r s. \<forall>x \<in> set x22. obj_at
       (\<lambda>ko. \<exists>pd. ko = ArchObj (PageDirectory pd) \<and>
       pd (ucast (x && mask pd_bits >> 2)) = pde.InvalidPDE)
       (hd (x21 # x22) && ~~ mask pd_bits) s" in hoare_post_imp_R)
    apply (wp mapME_x_accumulate_checks[where Q = "\<lambda>s. valid_pdpt_objs s"] )
        apply (wp get_master_pde_wp| wpc | simp)+
       apply clarsimp
       apply (frule_tac x = xa in mask_out_same_pd)
        apply (clarsimp simp:upto_enum_def upto_enum_step_def upto_0_to_n2)
        apply (erule notE)
        apply (subst shiftl_t2n[where n = 2,simplified field_simps,simplified,symmetric])
        apply (rule shiftl_less_t2n[where m = 6,simplified])
         apply (simp add:word_of_nat_less)
        apply simp
       apply (frule_tac x = z in mask_out_same_pd)
        apply (clarsimp simp:upto_enum_def upto_enum_step_def upto_0_to_n2)
       apply (clarsimp simp:field_simps obj_at_def
           split:pde.splits)
       apply (drule(1) valid_pdpt_objs_pdD)
       apply (intro conjI impI)
          apply clarsimp
          apply (frule(1) align_entry_pdD)
          apply (simp add:is_aligned_neg_mask_eq)
         apply clarsimp
         apply (frule(1) align_entry_pdD)
         apply (simp add:is_aligned_neg_mask_eq)
        apply clarsimp
        apply (frule(1) align_entry_pdD)
        apply (simp add:is_aligned_neg_mask_eq)
       apply clarsimp
       apply (erule(4) invalid_pdeI[OF _ neq_pd_offset])
      apply (wp hoare_drop_imps |wpc|simp)+
    apply (clarsimp simp:upto_enum_def upto_enum_step_def
        upto_0_to_n2 Fun.comp_def distinct_map)
   apply (intro exI conjI,fastforce+)
   apply (simp add:obj_at_def hd_map_simp
     upto_0_to_n2 upto_enum_def upto_enum_step_def)
   apply (frule_tac x = 1 in bspec,fastforce+)
  apply (wp get_master_pde_wp | simp | wpc)+
  done
qed

lemma create_mapping_entries_safe[wp]:
  "\<lbrace>\<exists>\<rhd>pd and K (vmsz_aligned vptr sz) and K (is_aligned pd pd_bits)
          and K (vptr < kernel_base)
          and valid_arch_objs and pspace_aligned and
          (\<exists>\<rhd> (lookup_pd_slot pd vptr && ~~ mask pd_bits))\<rbrace>
      create_mapping_entries ptr vptr sz rights attrib pd
   \<lbrace>\<lambda>entries. case entries of (Inl (SmallPagePTE _ _ _, [_])) \<Rightarrow> \<top>
                  | (Inl (SmallPagePTE _ _ _, _)) \<Rightarrow> \<bottom>
                  | (Inl (LargePagePTE _ _ _, [])) \<Rightarrow> \<bottom>
                  | (Inr (SectionPDE _ _ _ _, [_])) \<Rightarrow> \<top>
                  | (Inr (SectionPDE _ _ _ _, _)) \<Rightarrow> \<bottom>
                  | (Inr (SuperSectionPDE _ _ _, [])) \<Rightarrow> \<bottom>
                  | _ \<Rightarrow> page_inv_entries_pre entries\<rbrace>,-"
  apply (cases sz, simp_all)
     defer 2
     apply (wp | simp)+
   apply (simp split:list.split)
   apply (subgoal_tac "lookup_pd_slot pd vptr \<le> lookup_pd_slot pd vptr + 0x3C")
    apply (clarsimp simp:upto_enum_def not_less upto_enum_step_def
      page_inv_entries_pre_def Let_def)
    apply (clarsimp simp:upto_enum_step_def upto_enum_def
                     map_eq_Cons_conv upt_eq_Cons_conv)
    apply (drule_tac x = "lookup_pd_slot pd vptr" in spec)
    apply (subst (asm) upto_0_to_n2)
     apply simp
    apply clarsimp
    apply (drule lookup_pd_slot_aligned_6)
     apply (simp add:pd_bits_def pageBits_def)
    apply simp
   apply clarsimp
   apply (erule is_aligned_no_wrap'[OF lookup_pd_slot_aligned_6])
    apply (simp add:pd_bits pageBits_def)
   apply simp
  apply (wp get_pde_wp | simp add:lookup_pt_slot_def | wpc)+
  apply (clarsimp simp:upto_enum_def upto_enum_step_def
    page_inv_entries_pre_def Let_def )
  apply (drule_tac ref = refa in valid_arch_objsD)
    apply (simp add:obj_at_def)
   apply simp
  apply (simp add:valid_arch_obj.simps)
  apply (drule_tac x = "ucast (lookup_pd_slot pd vptr && mask pd_bits >> 2)"
    in bspec)
   apply simp
   apply (erule(1) less_kernel_base_mapping_slots)
  apply (clarsimp simp:not_less[symmetric] split:list.splits)
  apply (clarsimp simp:page_inv_entries_pre_def
    Let_def upto_enum_step_def upto_enum_def)
  apply (subst (asm) upto_0_to_n2)
   apply simp
  apply (clarsimp simp:not_less[symmetric])
  apply (subgoal_tac
    "(\<exists>xa xb. pda (ucast (lookup_pd_slot pd vptr && mask pd_bits >> 2))
     = pde.PageTablePDE x xa xb)
     \<longrightarrow> is_aligned (ptrFromPAddr x + ((vptr >> 12) && 0xFF << 2)) 6")
   apply clarsimp
   apply (subgoal_tac "
     ptrFromPAddr x + ((vptr >> 12) && 0xFF << 2) \<le>
     ptrFromPAddr x + ((vptr >> 12) && 0xFF << 2) + 0x3C")
    apply (clarsimp simp:not_less[symmetric])
   apply (erule is_aligned_no_wrap')
   apply simp
  apply clarsimp
  apply (rule aligned_add_aligned)
    apply (erule(1) pt_aligned)
   apply (rule is_aligned_shiftl[OF is_aligned_andI1])
   apply (rule is_aligned_shiftr)
   apply (simp add:vmsz_aligned_def)
  apply simp
  done

lemma arch_decode_invocation_valid_pdpt[wp]:
  notes find_pd_for_asid_inv[wp del]
  shows
  "\<lbrace>invs and valid_cap (cap.ArchObjectCap cap) and valid_pdpt_objs \<rbrace>
   arch_decode_invocation label args cap_index slot cap excaps
   \<lbrace>invocation_duplicates_valid o Invocations_A.InvokeArchObject\<rbrace>,-"
  proof -
    have bitwise:"\<And>a. (ucast (((a::word32) && ~~ mask 6) && mask 14 >> 2)::12 word)
      = (ucast (a  && mask 14 >> 2)::12 word) && ~~ mask 4"
      apply (simp add:mask_def)
      apply word_bitwise
      done
    have sz:
      "\<And>vmpage_size. \<lbrakk>args ! 0 + 2 ^ pageBitsForSize vmpage_size - 1 < kernel_base;
        vmsz_aligned (args ! 0) vmpage_size\<rbrakk>
       \<Longrightarrow> args ! 0 < kernel_base"
      apply (rule le_less_trans[OF is_aligned_no_overflow])
       apply (simp add:vmsz_aligned_def)
      apply simp
      done
  show ?thesis
  apply (simp add: arch_decode_invocation_def
              Let_def split_def get_master_pde_def
              split del: split_if
                   cong: arch_cap.case_cong if_cong cap.case_cong
                         option.case_cong)
  apply (rule hoare_pre)
   apply ((wp get_pde_wp
             ensure_safe_mapping_ensures[THEN hoare_post_imp_R]
             create_mapping_entries_safe check_vp_wpR
             find_pd_for_asid_aligned_pd_bits
               [unfolded pd_bits_def pageBits_def,simplified]
             | wpc
             | simp add: invocation_duplicates_valid_def unlessE_def whenE_def
                         pti_duplicates_valid_def page_inv_duplicates_valid_def
                         mask_lower_twice pd_bits_def bitwise pageBits_def
                         not_le sz
                    del: hoare_post_taut hoare_True_E_R
                     split del: split_if
             | simp only: obj_at_def)+)
         apply (rule_tac Q'="\<lambda>rv. \<exists>\<rhd> rv and K (is_aligned rv pd_bits) and
                  (\<exists>\<rhd> (lookup_pd_slot rv (args ! 0) && ~~ mask pd_bits)) and
                     valid_arch_objs and pspace_aligned and valid_pdpt_objs"
                     and f="find_pd_for_asid p" for p
                    in hoare_post_imp_R)
          apply (wp| simp)+
         apply (fastforce simp:pd_bits_def pageBits_def)
        apply ((wp get_pde_wp
             ensure_safe_mapping_ensures[THEN hoare_post_imp_R]
             create_mapping_entries_safe check_vp_wpR
             find_pd_for_asid_aligned_pd_bits
               [unfolded pd_bits_def pageBits_def,simplified]
             | wpc
             | simp add: invocation_duplicates_valid_def unlessE_def whenE_def
                         pti_duplicates_valid_def page_inv_duplicates_valid_def
                         mask_lower_twice pd_bits_def bitwise pageBits_def
                         not_le sz
                    del: hoare_post_taut hoare_True_E_R
                     split del: split_if
             | simp only: obj_at_def)+)
         apply (rule_tac Q'="\<lambda>rv. \<exists>\<rhd> rv and K (is_aligned rv pd_bits) and
                  (\<exists>\<rhd> (lookup_pd_slot rv (snd pa) && ~~ mask pd_bits)) and
                     valid_arch_objs and pspace_aligned and valid_pdpt_objs and
                     K ((snd pa) < kernel_base)"
                     and f="find_pd_for_asid p" for p
                    in hoare_post_imp_R)
          apply (wp| simp)+
         apply (auto simp:pd_bits_def pageBits_def)[1]
        apply ((wp get_pde_wp
             ensure_safe_mapping_ensures[THEN hoare_post_imp_R]
             create_mapping_entries_safe check_vp_wpR
             find_pd_for_asid_aligned_pd_bits
               [unfolded pd_bits_def pageBits_def,simplified]
             | wpc
             | simp add: invocation_duplicates_valid_def unlessE_def whenE_def
                         pti_duplicates_valid_def page_inv_duplicates_valid_def
                         mask_lower_twice pd_bits_def bitwise pageBits_def
                         not_le sz
                    del: hoare_post_taut hoare_True_E_R
                     split del: split_if
             | simp only: obj_at_def)+)
         apply (rule hoare_post_imp_R[where P=\<top>])
          apply (rule hoare_True_E_R)
         apply auto[1]
        apply ((wp
             | wpc
             | simp add: invocation_duplicates_valid_def unlessE_def whenE_def
                         pti_duplicates_valid_def page_inv_duplicates_valid_def
                     del: hoare_post_taut hoare_True_E_R
                     split del: split_if
             | simp only: obj_at_def)+)
  apply (auto simp:valid_cap_simps)
  done
qed

lemma decode_invocation_valid_pdpt[wp]:
  "\<lbrace>invs and valid_cap cap and valid_pdpt_objs\<rbrace> decode_invocation label args cap_index slot cap excaps
   \<lbrace>invocation_duplicates_valid\<rbrace>,-"
  apply (simp add: decode_invocation_def split del: split_if)
  apply (rule hoare_pre)
   apply (wp | wpc
            | simp only: invocation_duplicates_valid_def o_def uncurry_def split_def
                         Invocations_A.invocation.simps)+
  apply clarsimp
  done

crunch valid_pdpt_objs[wp]: handle_fault, reply_from_kernel "valid_pdpt_objs"
  (simp: crunch_simps wp: crunch_wps)


lemma invocation_duplicates_valid_exst_update[simp]:
  "invocation_duplicates_valid i (trans_state f s) = invocation_duplicates_valid i s"
  apply (clarsimp simp add: invocation_duplicates_valid_def pti_duplicates_valid_def page_inv_duplicates_valid_def page_inv_entries_safe_def split: sum.splits invocation.splits arch_invocation.splits kernel_object.splits page_table_invocation.splits page_invocation.splits)+
  done


lemma set_thread_state_duplicates_valid[wp]:
  "\<lbrace>invocation_duplicates_valid i\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. invocation_duplicates_valid i\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def)
  apply (wp|simp)+
  apply (clarsimp simp: invocation_duplicates_valid_def pti_duplicates_valid_def
                        page_inv_duplicates_valid_def page_inv_entries_safe_def
                        Let_def
                 dest!: get_tcb_SomeD
                 split: Invocations_A.invocation.split arch_invocation.split_asm
                        page_table_invocation.split
                        page_invocation.split sum.split
                        )
  apply (auto simp add: obj_at_def page_inv_entries_safe_def)
  done

lemma handle_invocation_valid_pdpt[wp]:
  "\<lbrace>valid_pdpt_objs and invs and ct_active\<rbrace>
        handle_invocation calling blocking \<lbrace>\<lambda>rv. valid_pdpt_objs\<rbrace>"
  apply (simp add: handle_invocation_def)
  apply (wp syscall_valid set_thread_state_ct_st
               | simp add: split_def | wpc
               | wp_once hoare_drop_imps)+
  apply (auto simp: ct_in_state_def elim: st_tcb_ex_cap)
  done


crunch valid_pdpt[wp]: handle_event, activate_thread,switch_to_thread,
       switch_to_idle_thread "valid_pdpt_objs"
  (simp: crunch_simps wp: crunch_wps alternative_valid select_wp OR_choice_weak_wp select_ext_weak_wp
      ignore: without_preemption getActiveIRQ resetTimer ackInterrupt
              getFAR getDFSR getIFSR OR_choice set_scheduler_action
              clearExMonitor)

lemma schedule_valid_pdpt[wp]: "\<lbrace>valid_pdpt_objs\<rbrace> schedule :: (unit,unit) s_monad \<lbrace>\<lambda>_. valid_pdpt_objs\<rbrace>"
  apply (simp add: schedule_def allActiveTCBs_def)
  apply (wp alternative_wp select_wp)
  apply simp
  done

lemma call_kernel_valid_pdpt[wp]:
  "\<lbrace>invs and (\<lambda>s. e \<noteq> Interrupt \<longrightarrow> ct_running s) and valid_pdpt_objs\<rbrace>
      (call_kernel e) :: (unit,unit) s_monad
   \<lbrace>\<lambda>_. valid_pdpt_objs\<rbrace>"
  apply (cases e, simp_all add: call_kernel_def)
      apply (rule hoare_pre)
       apply (wp | simp | wpc
                 | rule conjI | clarsimp simp: ct_in_state_def
                 | erule pred_tcb_weakenE
                 | wp_once hoare_drop_imps)+
  done

end

end
