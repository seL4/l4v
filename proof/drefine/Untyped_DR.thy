(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Untyped_DR
imports CNode_DR
begin

context begin interpretation Arch . (*FIXME: arch_split*)

lemma detype_dcorres:
  "S = {ptr..ptr + 2 ^ sz - 1}
 \<Longrightarrow> dcorres dc \<top> (\<lambda>s. invs s \<and> (\<exists>cref. cte_wp_at ((=) (cap.UntypedCap dev ptr sz idx)) cref s) \<and> valid_etcbs s)
        (modify (Untyped_D.detype S))
        (modify (Retype_A.detype S))"
  apply (rule corres_modify)
  apply (clarsimp simp: transform_def Untyped_D.detype_def
                        transform_cdt_def
             split del: if_split
              simp del: untyped_range.simps)
  apply (simp add: Untyped_D.detype_def transform_def
                   transform_current_thread_def Retype_A.detype_def transform_asid_table_def
                   detype_ext_def wrap_ext_det_ext_ext_def)
  apply (rule ext)
  apply (clarsimp simp: map_option_case restrict_map_def transform_objects_def
                        map_add_def cte_wp_at_caps_of_state
                 split: option.split)
  apply (drule valid_global_refsD2)
   apply clarsimp
  apply (clarsimp simp: global_refs_def transform_object_def detype_ext_def)
  done

(* FIXME: move *)
lemma evalMonad_loadWords:
  "evalMonad (mapM loadWord xs) ms =
  (if (\<forall>x\<in>set xs. is_aligned x 2) then
     Some (map (\<lambda>x. word_rcat [underlying_memory ms (x + 3),
                               underlying_memory ms (x + 2),
                               underlying_memory ms (x + 1),
                               underlying_memory ms x]) xs)
   else None)"
proof (induct xs)
  case Nil thus ?case
    by (simp add: evalMonad_def mapM_simps return_def)
next
  note mapM_simps[simp]

  (* FIXME: could be generalized. *)
  have evalMonad_bind_return:
    "\<And>f g s. \<forall>x\<in>fst (f s). snd x = s \<Longrightarrow> \<exists>r. \<forall>x\<in>fst (f s). fst x = r \<Longrightarrow>
              \<exists>r. \<forall>x\<in>fst (g s). fst x = r \<Longrightarrow>
              evalMonad (do r \<leftarrow> f; rs \<leftarrow> g; return (r#rs) od) s =
              (case evalMonad f s of None \<Rightarrow> None
               | Some r \<Rightarrow> (case evalMonad g s of None \<Rightarrow> None
                            | Some rs \<Rightarrow> Some (r#rs)))"
    apply (simp add: evalMonad_def bind_def split_def return_def)
    apply safe
      apply auto[2]
    apply (rule sym)
    apply (rule someI2_ex, fastforce)
    apply (clarsimp split: if_split_asm)
    apply (rule conjI)
     apply (rule someI2_ex, fastforce+)+
    done

  (* FIXME: For some reason Nondet_In_Monad.in_fail doesn't fire below. This version would probably
            have been better in the first place. *)
  have [simp]: "\<And>s. fst (fail s) = {}" by (simp add: fail_def)

  have loadWord_const:
   "\<And>a s. \<forall>x\<in>fst (loadWord a s). snd x = s"
    apply (case_tac "is_aligned a 2")
     apply (simp add: loadWord_def is_aligned_mask exec_gets)
     apply (simp add: return_def)
    apply (simp add: loadWord_def exec_gets is_aligned_mask)
    done

  have loadWord_atMostOneResult:
    "\<And>a s. \<exists>r. \<forall>x\<in>fst (loadWord a s). fst x = r"
    apply (case_tac "is_aligned a 2")
     apply (simp add: loadWord_def is_aligned_mask exec_gets)
     apply (simp add: return_def)
    apply (simp add: loadWord_def exec_gets is_aligned_mask)
    done

  have mapM_loadWord_atMostOneResult[rule_format]:
    "\<And>as s. \<exists>rs. \<forall>x\<in>fst (mapM loadWord as s). fst x = rs"
    apply (induct_tac as)
     apply (simp add: return_def)
    using loadWord_const loadWord_atMostOneResult
    by (fastforce simp: bind_def split_def return_def)

  case Cons thus ?case
    by (simp add: evalMonad_bind_return[OF loadWord_const
                    loadWord_atMostOneResult mapM_loadWord_atMostOneResult]
                  evalMonad_loadWord is_aligned_mask
             split: option.splits)
qed

(* FIXME: change definition! *)
lemma get_ipc_buffer_words_def2:
  "get_ipc_buffer_words ms tcb ns \<equiv>
   (case tcb_ipcframe tcb of
      cap.ArchObjectCap (arch_cap.PageCap dev buf rights sz mapdata) \<Rightarrow>
        if AllowRead \<in> rights then
          (if ns = Nil \<or> is_aligned (buf + tcb_ipc_buffer tcb) 2 then
            map ((\<lambda>x. word_rcat [underlying_memory ms (x + 3),
                                 underlying_memory ms (x + 2),
                                 underlying_memory ms (x + 1),
                                 underlying_memory ms x]) \<circ>
                 (\<lambda>n. buf + (tcb_ipc_buffer tcb && mask (pageBitsForSize sz)) +
                      of_nat n * of_nat word_size))
              ns
          else the None)
        else []
    | _ \<Rightarrow> [])"
proof -

  (* FIXME: extract *)
  have mask_eq:
    "\<And>p q m n. m\<ge>n \<Longrightarrow> p + (q && mask m) && mask n = p + q && mask n"
    by (subst mask_eqs(2)[of p "q && mask m" for p q m, symmetric])
       (simp add: mask_twice min_def mask_eqs)

  have eq: "\<And>x p b sz. is_aligned (p + (b && mask (pageBitsForSize sz)) +
                                    of_nat x * of_nat word_size) 2
                \<longleftrightarrow> is_aligned (p + b) 2"
    apply (rule iffI)
     apply (drule is_aligned_addD2)
     apply (simp add: word_size_def is_aligned_mult_triv2[where n=2,
                                      simplified word_bits_def, simplified])
     apply (simp add: is_aligned_mask mask_eq)
    apply (rule is_aligned_add)
     apply (simp add: is_aligned_mask mask_eq)
    apply (simp add: word_size_def is_aligned_mult_triv2[where n=2,
                                     simplified word_bits_def, simplified])
    done

  show "PROP ?thesis"
    apply (rule eq_reflection)
    apply (auto simp: get_ipc_buffer_words_def evalMonad_loadWords eq
               split: cap.splits arch_cap.splits)
    done
qed

lemma is_arch_page_cap_def2:
  "is_arch_page_cap cap \<longleftrightarrow>
   (\<exists>dev buf rights sz mapdata.
      cap = cap.ArchObjectCap (arch_cap.PageCap dev buf rights sz mapdata))"
  by (simp add: is_arch_page_cap_def  split: cap.splits arch_cap.splits)

lemma transform_full_intent_machine_state_eq:
  assumes 3: "tcb_ipcframe tcb =
              cap.ArchObjectCap (arch_cap.PageCap dev buf rights sz opt)"
  assumes 4: "is_aligned buf (pageBitsForSize sz)"
  assumes 1: "is_aligned (tcb_ipc_buffer tcb) msg_align_bits"
  assumes 5: "(\<forall>p. buf = (p && ~~ mask (pageBitsForSize sz)) \<longrightarrow>
                   underlying_memory ms' p = underlying_memory ms p)"
  shows "transform_full_intent ms tref tcb = transform_full_intent ms' tref tcb"
proof -
  have 2: "valid_message_info (get_tcb_message_info tcb)"
    by (simp add: get_tcb_message_info_def data_to_message_info_valid)

  let ?p = "%x. buf + (tcb_ipc_buffer tcb && mask (pageBitsForSize sz)) +
                of_nat x * of_nat word_size"
  have word_rcat_eq:
    "\<And>x. x<128 \<Longrightarrow>
       word_rcat [underlying_memory ms (?p x + 3),
                  underlying_memory ms (?p x + 2),
                  underlying_memory ms (?p x + 1),
                  underlying_memory ms (?p x)] =
       word_rcat [underlying_memory ms'(?p x + 3),
                  underlying_memory ms'(?p x + 2),
                  underlying_memory ms'(?p x + 1),
                  underlying_memory ms'(?p x)]"
  proof -
    fix x :: nat
    assume x: "x<128"
    have y: "!!y. y<4 \<Longrightarrow> ?p x + y && ~~ mask (pageBitsForSize sz) = buf"
      apply (simp add: add.assoc)
      apply (rule is_aligned_add_helper[OF 4, THEN conjunct2])
      apply (rule_tac n=msg_align_bits in is_aligned_add_less_t2n)
         apply (rule is_aligned_andI1[OF 1])
        apply (rule_tac n=2 in is_aligned_add_less_t2n)
           apply (simp add: word_size_def)
           apply (rule is_aligned_mult_triv2[where n=2, simplified])
          apply simp
         apply (simp add: msg_align_bits)
        apply (simp add: word_size_def)
        apply (rule word_less_power_trans_ofnat[where k=2, simplified],
               simp_all add: x msg_align_bits word_bits_def)[1]
       apply (case_tac sz, simp_all add: msg_align_bits)[1]
      apply (rule and_mask_less_size)
      apply (case_tac sz, simp_all add: word_size)[1]
      done

    note 6 = 5[rule_format, OF y[symmetric]]
    show "?thesis x"
      apply (rule arg_cong[where f=word_rcat])
      using 6[of 3] 6[of 2] 6[of 1] 6[of 0]
      by simp
  qed

  show ?thesis
  apply (clarsimp simp: transform_full_intent_def Let_def get_tcb_mrs_def
                        get_ipc_buffer_words_def2 3
                        Suc_leI[OF msg_registers_lt_msg_max_length]
                  simp del: upt_Suc
                  split del: if_split)
  apply (case_tac "AllowRead \<in> rights",
         simp_all del: upt_Suc  split del: if_split)
  apply (cut_tac y=2 in is_aligned_weaken[OF 1])
   apply (simp add: msg_align_bits)
  apply (cut_tac y=2 in is_aligned_weaken[OF 4])
   apply (case_tac sz, simp_all)[1]
  apply (frule (1) is_aligned_add[of buf 2 "tcb_ipc_buffer tcb"])
  apply (simp add: o_def del: upt_Suc)
  apply (intro conjI)
    apply (rule arg_cong2[where f=transform_intent, OF refl])
    apply (rule arg_cong2[where f="(@)", OF refl])
    apply (rule arg_cong2[where f=take, OF refl])
    apply (rule map_cong[OF refl])
    apply (rule word_rcat_eq)
    apply (clarsimp simp: atLeastAtMost_upt[symmetric] msg_max_length_def
                    simp del: upt_Suc)
   apply clarsimp
   apply (rule word_rcat_eq)
   using 2
   apply (clarsimp simp: buffer_cptr_index_def msg_max_length_def
              valid_message_info_def msg_max_extra_caps_def word_le_nat_alt)
  apply (rule arg_cong2[where f="case_list None", OF refl])
  apply (rule map_cong[OF refl])
   apply (rule word_rcat_eq)
  apply (clarsimp simp: atLeastAtMost_upt[symmetric]  simp del: upt_Suc)
  apply (simp add: msg_max_length_def msg_max_extra_caps_def)
  done
qed

lemma valid_page_cap_imp_valid_buf:
  "s \<turnstile> cap.ArchObjectCap (arch_cap.PageCap False buf rights sz mapdata) \<Longrightarrow>
   is_aligned buf (pageBitsForSize sz) \<and> typ_at (AArch (AUserData sz)) buf s"
  by (clarsimp simp add: valid_cap_simps cap_aligned_def)

lemma freeMemory_dcorres:
  "is_aligned ptr bits \<Longrightarrow> 2 \<le> bits \<Longrightarrow> bits < word_bits \<Longrightarrow>
   dcorres dc (\<lambda>_. True)
     (pspace_no_overlap_range_cover ptr bits and valid_objs and valid_etcbs)
     (return rv) (do_machine_op (freeMemory ptr bits))"
  apply (clarsimp simp add: corres_underlying_def split_def return_def)
  apply (rename_tac s t)
  apply (drule_tac P="(=) s" and
                   Q="%_ u. (\<exists>ms. u=s\<lparr>machine_state := ms\<rparr>) \<and>
                            (\<forall>p\<in>UNIV-{ptr..ptr + 2 ^ bits - 1}.
                                underlying_memory (machine_state s) p =
                                underlying_memory (machine_state u) p)"
                in use_valid)
    apply (simp add: do_machine_op_def split_def)
    apply wp
    apply (clarsimp simp: freeMemory_def mapM_x_storeWord_step[simplified word_size_bits_def]
                          intvl_range_conv')
    apply (rule conjI, fastforce)
    apply clarsimp
    apply (erule use_valid[where P=P and Q="%_. P" for P])
     apply wp
     apply (clarsimp simp: is_aligned_no_wrap' of_nat_less_pow_32 word_bits_def
                           x_power_minus_1 word_plus_mono_right)
    apply (rule refl)
   apply (rule refl)
  apply (clarsimp simp: transform_def transform_current_thread_def)
  apply (rule ext)
  apply (clarsimp simp: transform_objects_def map_add_def)
  apply (clarsimp simp: option_map_def split: option.splits)
  apply (clarsimp simp: transform_object_def transform_tcb_def
                 split: Structures_A.kernel_object.split option.splits)
  apply (rename_tac s ms tref etcb tcb)
  apply (clarsimp simp: restrict_map_def split: if_split_asm)
  apply (frule(1) valid_etcbs_tcb_etcb)
  apply (case_tac "\<not> is_arch_page_cap (tcb_ipcframe tcb)")
   apply (erule transform_full_intent_no_ipc_buffer)
  apply (clarsimp simp: is_arch_page_cap_def2)
  apply (simp add: valid_objs_def)
  apply (drule_tac x=tref in bspec, clarsimp+)
  apply (clarsimp simp: valid_obj_def valid_tcb_def)
    (* FIXME: extract a sensible lemma for that *)
  apply (drule_tac x="(tcb_ipcframe, tcb_ipcframe_update,
                        \<lambda>_ _. is_nondevice_page_cap or (=) cap.NullCap)" in bspec)
   apply (simp add: ran_tcb_cap_cases)
  apply clarsimp
  apply (thin_tac "case_option x y z" for x y z)
  apply (clarsimp simp add: valid_ipc_buffer_cap_def is_nondevice_page_cap_def split: bool.split_asm)
  apply (drule valid_page_cap_imp_valid_buf)
  apply (frule_tac transform_full_intent_machine_state_eq, simp_all)
  apply clarsimp
  apply (erule_tac x=p in bspec)
  apply (frule is_aligned_no_overflow')
  apply (clarsimp simp: pspace_no_overlap_def typ_at_eq_kheap_obj obj_at_def
                        mask_2pm1[symmetric])
  apply (erule_tac x="(p && ~~ mask (pageBitsForSize sz))" in allE)
  apply clarsimp
  apply (thin_tac "length xs = y" for xs y)
  apply (erule impE)
   apply (simp add:mask_def[unfolded shiftl_t2n,simplified,symmetric] p_assoc_help)
   apply (erule order_trans[OF word_and_le2])
  apply (erule impE)
   apply (rule_tac y = p in order_trans)
    apply simp
   apply (cut_tac ptr = p and n = "pageBitsForSize sz" in word_neg_and_le)
   apply (simp add:mask_def[unfolded shiftl_t2n,simplified,symmetric] p_assoc_help)
  apply (thin_tac "x\<noteq>y" for x y)
  apply (erule notE)+
  apply (rule is_aligned_no_wrap'[OF is_aligned_neg_mask])
   apply (rule le_refl)
  apply (simp add:mask_def not_le pbfs_less_wb'[unfolded word_bits_def, simplified])
  done

declare wrap_ext_det_ext_ext_def[simp]

(* Strictly speaking, we would not need ct_active, here.  Proving that,
   however, requires a stronger version of lemma detype_invariants. *)
lemma delete_objects_dcorres:
  notes order_class.Icc_eq_Icc [simp del]
        is_aligned_neg_mask_eq[simp del]
        is_aligned_neg_mask_weaken[simp del]
  assumes S: "S = {ptr..ptr + 2 ^ bits - 1}"
  shows "dcorres dc \<top>
      (\<lambda>s. invs s \<and> ct_active s \<and> (\<exists>cref dev idx.
        cte_wp_at ((=) (cap.UntypedCap dev ptr bits idx)) cref s
         \<and> descendants_range (cap.UntypedCap dev ptr bits idx) cref s) \<and> valid_etcbs s)
      (modify (Untyped_D.detype S))
      (delete_objects ptr bits)"
  apply (clarsimp simp: S)
  apply (unfold delete_objects_def2 K_bind_def)
  apply (rule corres_bind_return)
  apply (rule_tac F="is_aligned ptr bits \<and> 2 \<le> bits \<and> bits < word_bits"
                  in corres_req)
   apply clarsimp
   apply (drule cte_wp_valid_cap, clarsimp)
   apply (simp add: valid_cap_def cap_aligned_def untyped_min_bits_def)
  apply (rule corres_name_pre, clarify)
  apply (rule corres_guard_imp)
    apply (rule corres_split)
       apply (rule detype_dcorres; simp)
      apply (rule freeMemory_dcorres, simp+)
    apply wp
   apply clarsimp
   apply (rule TrueI)?
  apply clarsimp
  apply (rule conjI)
   apply fastforce
  apply (frule cte_wp_valid_cap, clarsimp)
  apply (intro conjI)
    apply (erule pspace_no_overlap_detype)
     apply clarsimp+
   apply (frule invs_untyped_children)
   apply (drule_tac detype_invariants, simp_all)
   apply (clarsimp simp: empty_descendants_range_in descendants_range_def2 invs_def valid_state_def
                         valid_pspace_def detype_clear_um_independent valid_etcbs_def)
  apply (simp add: invs_def valid_state_def valid_pspace_def detype_clear_um_independent valid_etcbs_def
                   is_etcb_at_def detype_def detype_ext_def st_tcb_at_kh_def obj_at_kh_def obj_at_def)
  done

lemma unat_ptr_range_end:
  "\<lbrakk> is_aligned (ptr :: 'a :: len word) sz; sz < len_of TYPE('a)\<rbrakk>
       \<Longrightarrow> unat (ptr + 2 ^ sz - 1) = unat ptr + 2 ^ sz - 1"
  apply (simp only: add_diff_eq[symmetric])
  apply (subst unat_plus_simple[THEN iffD1])
   apply (simp add: add_diff_eq)
  apply (subst unat_minus_one)
   apply simp_all
  done

definition
  translate_object_type :: "Structures_A.apiobject_type \<Rightarrow> cdl_object_type"
where
 "translate_object_type type \<equiv> case type of
    Structures_A.Untyped \<Rightarrow> UntypedType
  | Structures_A.TCBObject \<Rightarrow> TcbType
  | Structures_A.EndpointObject \<Rightarrow> EndpointType
  | Structures_A.NotificationObject \<Rightarrow> NotificationType
  | Structures_A.CapTableObject \<Rightarrow> CNodeType
  | ArchObject SmallPageObj \<Rightarrow> FrameType 12
  | ArchObject LargePageObj \<Rightarrow> FrameType 16
  | ArchObject SectionObj \<Rightarrow> FrameType 20
  | ArchObject SuperSectionObj \<Rightarrow> FrameType 24
  | ArchObject PageTableObj \<Rightarrow> PageTableType
  | ArchObject PageDirectoryObj \<Rightarrow> PageDirectoryType
  | ArchObject ASIDPoolObj \<Rightarrow> AsidPoolType"

definition
  translate_untyped_invocation :: "Invocations_A.untyped_invocation \<Rightarrow> cdl_untyped_invocation"
where
 "translate_untyped_invocation x \<equiv>
  case x of Invocations_A.Retype cref reset ptr_base ptr tp us slots dev
    \<Rightarrow> cdl_untyped_invocation.Retype
           (transform_cslot_ptr cref )
           (translate_object_type tp)
           us
           (map transform_cslot_ptr slots)
           (\<not> reset) (length slots)"

definition
 "retype_transform_obj_ref type sz ptr
     \<equiv> if type = Structures_A.Untyped then {ptr .. ptr + 2^sz - 1}
       else {ptr}"

lemma transform_empty_cnode:
  "transform_cnode_contents o_bits (empty_cnode o_bits) = empty_cap_map o_bits"
  apply (simp add: transform_cnode_contents_def dom_empty_cnode)
  apply (rule ext, simp add: option_map_join_def empty_cap_map_def
                             nat_to_bl_def len_bin_to_bl_aux empty_cnode_def)
  done

lemma transform_default_tcb:
  "transform_tcb ms x default_tcb (default_etcb\<lparr>tcb_domain := domain\<rparr>)
        = Tcb (Types_D.default_tcb domain)"
  apply (simp add: transform_tcb_def default_tcb_def Types_D.default_tcb_def default_arch_tcb_def)
  apply (simp add: transform_full_intent_def Let_def new_context_def cap_register_def capRegister_def
                   get_tcb_mrs_def Suc_le_eq get_tcb_message_info_def msg_info_register_def
                   msgInfoRegister_def data_to_message_info_def arch_tcb_context_get_def
                   get_ipc_buffer_words_def)
  apply (simp add: transform_intent_def invocation_type_def fromEnum_def enum_invocation_label
                   enum_gen_invocation_labels toEnum_def)
  apply (simp add: fun_eq_iff tcb_slot_defs infer_tcb_pending_op_def infer_tcb_bound_notification_def
                   guess_error_def default_etcb_def default_domain_def)
  done

lemma transform_unat_map_empty:
  "unat_map (\<lambda>_ :: ('a :: len) word. Some cdl_cap.NullCap)
      = empty_cap_map (len_of TYPE('a))"
  by (rule ext, simp add: unat_map_def empty_cap_map_def)

lemma transform_default_object:
  "\<lbrakk>type \<noteq> Structures_A.Untyped; type = Structures_A.CapTableObject \<longrightarrow> 0 < o_bits\<rbrakk> \<Longrightarrow>
   transform_object ms word (default_ext type domain) (Retype_A.default_object type dev o_bits)
     = the (Types_D.default_object (translate_object_type type) o_bits domain)"
  by (cases type, simp_all add: translate_object_type_def default_object_def
              Types_D.default_object_def transform_default_tcb default_ext_def
              transform_unat_map_empty transform_empty_cnode
              Types_D.empty_cnode_def dom_empty_cnode
              transform_object_def default_arch_object_def
              transform_page_table_contents_def o_def transform_pte_def
              transform_page_directory_contents_def transform_pde_def kernel_pde_mask_def
              transform_asid_pool_contents_def transform_asid_pool_entry_def asid_low_bits_def
           split: aobject_type.split nat.splits)

lemma obj_bits_bound32:
  "\<lbrakk>type = Structures_A.Untyped \<longrightarrow> us < 32; type = Structures_A.CapTableObject \<longrightarrow> us < 28\<rbrakk>
  \<Longrightarrow> obj_bits_api type us < word_bits"
  apply (case_tac type; simp add: obj_bits_api_def word_bits_def slot_bits_def)
  apply (rename_tac aobject_type)
  apply (case_tac aobject_type; simp add: arch_kobj_size_def default_arch_object_def pageBits_def)
  done

lemma obj_bits_bound4:
  "\<lbrakk>type = Structures_A.Untyped \<longrightarrow> untyped_min_bits \<le> us\<rbrakk> \<Longrightarrow>
    untyped_min_bits \<le> obj_bits_api type us"
  apply (case_tac type; simp add: obj_bits_api_def word_bits_def slot_bits_def untyped_min_bits_def)
  apply (rename_tac aobject_type)
  apply (case_tac aobject_type; simp add:arch_kobj_size_def default_arch_object_def pageBits_def)
  done

lemma distinct_retype_addrs:
  "\<lbrakk>type = Structures_A.Untyped \<longrightarrow> untyped_min_bits \<le> us;
    range_cover ptr sz (obj_bits_api type us) n\<rbrakk>
    \<Longrightarrow> distinct (retype_addrs ptr type n us)"
  supply untyped_min_bits_def[simp]
  apply (clarsimp simp:retype_addrs_def distinct_map ptr_add_def inj_on_def)
  apply (simp only: shiftl_t2n[symmetric, simplified field_simps, simplified])
  apply (drule shiftl_inj_if)
    apply (rule shiftl_shiftr_id)
     apply (simp add:range_cover_def)
    apply (rule word_of_nat_less)
    apply (subst unat_power_lower)
     apply (rule diff_less)
      apply (cut_tac obj_bits_bound4[where us = us and type = type])
       apply simp
      apply simp
     apply (simp add:word_bits_def)
    apply (erule Retype_AI.range_cover.range_cover_le_n_less(2))
    apply simp
   apply (rule shiftl_shiftr_id)
    apply (simp add:range_cover_def)
   apply (rule word_of_nat_less)
   apply (subst unat_power_lower)
    apply (rule diff_less)
     apply (cut_tac obj_bits_bound4[where us = us and type = type])
      apply simp
     apply simp
    apply (simp add:word_bits_def)
   apply (erule Retype_AI.range_cover.range_cover_le_n_less(2))
   apply simp
  apply (rule of_nat_inj[where 'a=32, THEN iffD1])
    apply (simp add:range_cover.range_cover_le_n_less[where 'a=32, simplified])+
  done

lemma length_retype_addrs[simp]:
  "length (retype_addrs ptr type n us) = n"
  by (simp add:retype_addrs_def)

lemma retype_transform_obj_ref_ut:
 "(p \<in> (retype_transform_obj_ref Structures_A.Untyped sz ptr)) = (p \<in> {ptr .. ptr + 2^sz - 1})"
  by (clarsimp simp:retype_transform_obj_ref_def)

lemma transform_none_to_untyped:
  "\<lbrakk>valid_idle s'; kheap s' obj_id = None\<rbrakk>
   \<Longrightarrow> cdl_objects (transform s') obj_id = Some Types_D.Untyped"
  apply (clarsimp simp: transform_def restrict_map_def map_add_def transform_objects_def)
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
  done

lemma retype_transform_obj_ref_available:
  "\<lbrakk>pspace_no_overlap_range_cover ptr sz s'; s = transform s'; valid_pspace s'; valid_idle s';
    range_cover ptr sz (obj_bits_api ty us) n;
    y \<in> set (retype_addrs ptr ty n us)\<rbrakk>
  \<Longrightarrow> retype_transform_obj_ref ty us y \<subseteq>
    (cdl_objects s) -` {Some Types_D.Untyped}"
  apply (clarsimp simp:retype_transform_obj_ref_def | rule conjI)+
  apply (rule transform_none_to_untyped, simp)
  apply (rule ccontr, clarsimp)
   apply (drule(1) retype_addrs_range_subset[where p = y])
   apply (drule(1) pspace_no_overlap_obj_range)
   apply (simp only: field_simps)
   apply (drule(1) disjoint_subset2)
   apply (clarsimp simp:obj_bits_api_def)
   apply (drule p_in_obj_range)
     apply clarsimp+
   apply auto[1]
  apply (drule(2) pspace_no_overlap_into_Int_none)
  apply (clarsimp simp: transform_def restrict_map_def map_add_def transform_objects_def
                 split: if_splits option.splits)
  apply (fastforce simp: valid_idle_def pred_tcb_at_def obj_at_def)
  done

lemma retype_transform_obj_ref_pick_id:
  "type \<noteq> Structures_A.Untyped
   \<Longrightarrow> map (\<lambda>x. {pick x}) (map (retype_transform_obj_ref type us) xs)
   = map (retype_transform_obj_ref type us) xs"
  by (simp add:retype_transform_obj_ref_def)

lemma translate_object_type_not_untyped:
  "type \<noteq> Structures_A.Untyped
   \<Longrightarrow>  Some (the (Types_D.default_object (translate_object_type type) us current_domain))
    = Types_D.default_object (translate_object_type type) us current_domain"
  by (clarsimp simp:translate_object_type_def Types_D.default_object_def
    split:Structures_A.apiobject_type.splits aobject_type.splits)

lemma retype_transform_obj_ref_not_untyped:
  "\<lbrakk>type \<noteq> Structures_A.Untyped\<rbrakk>
   \<Longrightarrow>
    {x} \<in> retype_transform_obj_ref type us ` set xs = (x \<in> set xs)"
  apply (rule iffI)
  apply (clarsimp simp:retype_transform_obj_ref_def)+
  done

lemma retype_transform_obj_ref_in_untyped_range:
  notes [simp del] = atLeastAtMost_iff atLeastatMost_subset_iff
  shows "\<lbrakk>y \<in> set (retype_addrs ptr type n us);
  range_cover ptr sz (obj_bits_api type us) n\<rbrakk>
  \<Longrightarrow> retype_transform_obj_ref type us y \<subseteq>
  {ptr &&~~ mask sz ..(ptr && ~~ mask sz) + (2 ^ sz - 1)}"
  apply (frule retype_addrs_subset_ptr_bits)
  apply (clarsimp simp:retype_transform_obj_ref_def)
  apply (rule conjI)
   apply (drule(1) set_mp)
   apply clarsimp
   apply (erule set_mp[rotated])
   apply (frule(1) retype_addrs_range_subset)
   apply (simp add:obj_bits_api_def)
   apply (erule subset_trans)
   apply (clarsimp simp: atLeastatMost_subset_iff field_simps)
   apply (rule word_and_le2)
  apply clarsimp
  apply (erule set_mp[rotated])
  apply (erule subset_trans)
  apply (clarsimp simp: atLeastatMost_subset_iff field_simps)
  apply (rule word_and_le2)
  done

lemma retype_region_dcorres:
  "dcorres (\<lambda>rv rv'. rv = map (retype_transform_obj_ref type us) rv'
                       \<and> rv' = retype_addrs ptr type n us)
       \<top>
  (\<lambda>s. pspace_no_overlap_range_cover ptr sz s \<and> invs s
  \<and> range_cover ptr sz (obj_bits_api type us) n
  \<and> (type = Structures_A.Untyped \<longrightarrow> untyped_min_bits \<le> us)
  \<and> (type = Structures_A.CapTableObject \<longrightarrow> us \<noteq> 0))
  (Untyped_D.retype_region
  us (translate_object_type type) (map (retype_transform_obj_ref type us) (retype_addrs ptr type n us)))
  (Retype_A.retype_region ptr n us type dev)"
  supply if_cong[cong]
  apply (simp add: retype_region_def Untyped_D.retype_region_def
              split del: if_split)
  apply (clarsimp simp:when_def generate_object_ids_def bind_assoc
                  split del:if_split)
  apply (simp add:retype_addrs_fold split del:if_split)
  apply (case_tac "type = Structures_A.Untyped")
   apply (rule corres_guard_imp)
     apply (simp add:translate_object_type_def)
    apply (intro conjI impI ballI | simp)+
   apply (simp add:gets_fold_into_modify retype_addrs_fold retype_region_ext_def modify_modify
                   create_objects_def)
   apply (rule dcorres_expand_pfx)
   apply clarsimp
   apply (rule corres_guard_imp)
     apply (rule corres_split)
        apply (rule_tac r = dc and Q = \<top> and Q' = "(=) s'" in corres_guard_imp)
          apply (clarsimp simp: transform_def bind_def simpler_modify_def corres_underlying_def
           transform_current_thread_def transform_cdt_def transform_asid_table_def)
          apply (rule ext)
          apply (clarsimp simp:foldr_upd_app_if foldr_fun_upd_value restrict_map_def map_add_def
                              transform_objects_def retype_transform_obj_ref_def image_def)
          apply (subgoal_tac "idle_thread s' \<notin> set (retype_addrs ptr type n us)")
           apply (subgoal_tac "type = Structures_A.CapTableObject \<longrightarrow> us \<noteq> 0")
            apply (clarsimp simp:transform_default_object translate_object_type_not_untyped)
           defer
           apply clarsimp
           apply (frule invs_valid_idle,clarsimp simp:valid_idle_def pred_tcb_at_def obj_at_def)
           apply (erule(3) pspace_no_overlapC)
           apply clarsimp
          apply simp
         apply assumption
        apply (rule corres_trivial)
        apply simp
       apply wp+
     apply fastforce
    apply simp
   apply (case_tac type, simp_all add:translate_object_type_def)
  apply (rename_tac aobject_type)
  apply (case_tac aobject_type,simp_all)
  done

lemma page_objects_default_object:
  "ty \<in> ArchObject ` {SmallPageObj, LargePageObj, SectionObj, SuperSectionObj}
     \<Longrightarrow> \<exists>vmsz. (default_object ty dev us = ArchObj (DataPage dev vmsz) \<and> pageBitsForSize vmsz = obj_bits_api ty us)"
  by (auto simp: default_object_def default_arch_object_def obj_bits_api_def pageBitsForSize_def)

crunch cleanByVA, cleanCacheRange_RAM
  for mem[wp]: "\<lambda>s. P (underlying_memory s)"
  (ignore_del: cleanByVA cleanL2Range)

lemma clearMemory_unused_corres_noop:
  "\<lbrakk> ty \<in> ArchObject ` {SmallPageObj, LargePageObj, SectionObj, SuperSectionObj};
       range_cover ptr sz (obj_bits_api ty us) n;
       p \<in> set (retype_addrs ptr ty n us)\<rbrakk>
   \<Longrightarrow> dcorres dc \<top>
     (\<lambda>s. (\<forall>x \<in> set (retype_addrs ptr ty n us).
      obj_at (\<lambda>ko. ko = Retype_A.default_object ty dev us) x s
      \<and> (\<forall>cap\<in>ran (caps_of_state s). x \<notin> (obj_refs cap)))
      \<and> valid_objs s \<and> pspace_aligned s \<and> pspace_distinct s \<and> valid_idle s \<and> valid_etcbs s)
     (return ())
     (do_machine_op (clearMemory p (2 ^ (obj_bits_api ty us))))"
  (is "\<lbrakk> ?def; ?szv; ?in \<rbrakk> \<Longrightarrow> dcorres dc \<top> ?P ?f ?g")
  supply empty_fail_cond[simp]
  apply (drule page_objects_default_object[where us=us and dev = dev], clarsimp)
  apply (rename_tac pgsz)
  apply (simp add: clearMemory_def do_machine_op_bind cleanCacheRange_PoC_def
                   cleanCacheRange_RAM_def cleanL2Range_def dsb_def mapM_x_mapM)
  apply (subst do_machine_op_bind)
    apply (clarsimp simp:  ef_storeWord)
   apply (clarsimp simp: cacheRangeOp_def cleanByVA_def split_def)
  apply (simp add: dom_mapM ef_storeWord)
  apply (rule corres_guard_imp, rule corres_split_noop_rhs)
      apply (rule corres_mapM_to_mapM_x)
      apply (rule_tac P=\<top> and P'="?P"
                   and S="Id \<inter> ({p .. p + 2 ^ (obj_bits_api ty us) - 1} \<times> UNIV)"
                 in corres_mapM_x[where f="\<lambda>_. return ()", OF _ _ _ refl,
                                   simplified mapM_x_return])
         apply clarsimp
         apply (rule stronger_corres_guard_imp,
                rule_tac sz=pgsz in dcorres_store_word_safe[where dev = dev])
           apply (simp add: within_page_def)
          apply simp
         apply (clarsimp simp: obj_at_def)
         apply (subgoal_tac "x && ~~ mask (obj_bits_api ty us) = p")
          apply (clarsimp simp: ipc_frame_wp_at_def obj_at_def ran_null_filter
                         split: cap.split_asm arch_cap.split_asm)
          apply (cut_tac t="(t, tcb_cnode_index 4)" and P="(=) cap" for t cap
                     in cte_wp_at_tcbI, simp, fastforce, simp)
          apply (clarsimp simp: cte_wp_at_caps_of_state)
          apply (drule(1) bspec)
          apply clarsimp
          apply (drule(1) bspec[OF _ ranI])
          apply simp
         apply (drule(2) retype_addrs_aligned
           [OF _ range_cover.aligned range_cover_sz'
             [where 'a=32, folded word_bits_def] le_refl])
         apply (simp add:mask_in_range)
        apply wp
       apply (simp | wp hoare_vcg_ball_lift)+
      apply (simp add:zip_same_conv_map)
      apply (rule conjI)
       apply clarsimp
      apply (clarsimp simp: word_size_def)
      apply (drule subsetD[OF upto_enum_step_subset])
      apply simp
     apply (rule dcorres_machine_op_noop, wp)
    apply (wp | simp)+
  done

lemma init_arch_objects_corres_noop:
  notes [simp del] = atLeastAtMost_iff atLeastatMost_subset_iff
  shows
  "\<lbrakk> \<forall>x \<in> set refs. is_aligned x (obj_bits_api ty obj_sz);
       range_cover ptr sz (obj_bits_api ty obj_sz) n; 0 < n \<rbrakk>
   \<Longrightarrow> dcorres dc \<top>
        (\<lambda>s. (ty \<noteq> Structures_A.Untyped \<longrightarrow>
                (\<forall>x\<in>set (retype_addrs ptr ty n obj_sz).
                    obj_at (\<lambda>ko. ko = Retype_A.default_object ty dev obj_sz) x s))
            \<and> (\<forall>cap \<in> ran (null_filter (caps_of_state s)).
                     obj_refs cap \<inter> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1} = {})
               \<and> valid_objs s \<and> pspace_aligned s \<and> pspace_distinct s \<and> valid_idle s \<and> valid_etcbs s)
        (return ())
        (init_arch_objects ty ptr n obj_sz refs)"
  apply (simp add: init_arch_objects_def
            split: Structures_A.apiobject_type.split aobject_type.split)
  apply (simp add: dcorres_machine_op_noop[THEN corres_guard_imp]
                   cleanCacheRange_PoU_def machine_op_lift)
  apply safe
  apply (simp add:mapM_x_mapM)
  apply (rule corres_guard_imp)
    apply (rule corres_split_noop_rhs)
      apply (rule corres_noop[where P=\<top> and P'=valid_idle])
       apply simp
       apply (rule hoare_strengthen_post, rule mapM_wp')
        apply (subst eq_commute, wp copy_global_mappings_dwp)
          apply (simp add: obj_bits_api_def arch_kobj_size_def
                           default_arch_object_def pd_bits_def pageBits_def)
         apply (wp mapM_wp' dmo_dwp | simp)+
     apply (rule corres_noop[where P=\<top> and P'=valid_idle])
      apply (simp add: clearMemory_def do_machine_op_bind
                   cleanCacheRange_PoU_def ef_storeWord
                   mapM_x_mapM dom_mapM)
      apply (wp mapM_wp' dmo_dwp | simp)+
  done

lemma monad_commute_set_cap_cdt:
  "monad_commute \<top> (KHeap_D.set_cap ptr cap) (modify (\<lambda>s. s\<lparr>cdl_cdt := (cdl_cdt s)(ptr2 \<mapsto> ptr3)\<rparr>))"
  apply (clarsimp simp:monad_commute_def)
  apply (rule sym)
  apply (subst bind_assoc[symmetric])
  apply (subst oblivious_modify_swap)
   apply (simp add: KHeap_D.set_cap_def split_def gets_the_def
     KHeap_D.set_object_def)
   apply (intro oblivious_bind oblivious_assert impI conjI allI oblivious_select |
          simp split: cdl_object.split)+
  apply (clarsimp simp:bind_assoc)
  done

lemma monad_commute_set_cap_assert:
  "monad_commute \<top> (KHeap_D.set_cap ptr cap) (assert F)"
   apply (simp add: monad_commute_def
     assert_def fail_def bind_def return_def)
   apply (subgoal_tac "empty_fail (KHeap_D.set_cap ptr cap)")
    apply (clarsimp simp:empty_fail_def)
    apply fastforce
   apply (simp add:KHeap_D.set_cap_def split_def)
   apply (wp|wpc|clarsimp split:cdl_object.splits)+
   apply (simp add:KHeap_D.set_object_def)
   done

lemma monad_commute_set_cap_gets_cdt:
  "monad_commute \<top> (KHeap_D.set_cap ptr cap) (gets cdl_cdt)"
   apply (simp add: monad_commute_def gets_def get_def
     assert_def fail_def bind_def return_def)
   apply auto[1]
   apply (rule bexI[rotated])
     apply simp
    apply simp
    apply (drule use_valid)
      apply (rule KHeap_D_set_cap_cdl_cdt)
     prefer 2
     apply (fastforce +)[2]
   apply (rule bexI[rotated])
     apply simp
    apply simp
    apply (drule use_valid)
      apply (rule KHeap_D_set_cap_cdl_cdt)
     prefer 2
     apply (fastforce +)[2]
   done

lemma set_cap_set_parent_swap:
  "do _ \<leftarrow> KHeap_D.set_cap ptr cap; set_parent ptr2 ptr3 od
   = do _ \<leftarrow> set_parent ptr2 ptr3; KHeap_D.set_cap ptr cap od"
  apply (rule bind_return_eq)
  apply (subst bind_assoc)+
  apply (rule ext)
  apply (subst monad_commute_simple)
    apply (simp add:set_parent_def)
    apply (rule monad_commute_split)+
        apply (rule monad_commute_set_cap_cdt)
       apply (rule monad_commute_set_cap_assert)
      apply wp
     apply (rule monad_commute_set_cap_gets_cdt)
    apply clarsimp
   apply fastforce
  apply fastforce
  done

lemma transform_default_cap:
  "transform_cap (default_cap type ptr sz dev)
       = Types_D.default_cap (translate_object_type type)
             (retype_transform_obj_ref type sz ptr) sz dev"
  by (cases type,
      simp_all add: translate_object_type_def Types_D.default_cap_def
                    free_range_of_untyped_def
                    transform_cap_def arch_default_cap_def transform_mapping_def
                    retype_transform_obj_ref_def vm_read_write_def Nitpick.The_psimp
                    transform_asid_def asid_high_bits_of_def asid_low_bits_def
             split: aobject_type.split)

crunch create_cap_ext
  for valid_etcbs[wp]: valid_etcbs

lemma create_cap_dcorres:
  "dcorres dc \<top> (cte_at parent and cte_wp_at ((=) cap.NullCap) slot
                       and not_idle_thread (fst slot) and valid_idle and valid_etcbs
                       and (\<lambda>s. mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)))
        (Untyped_D.create_cap (translate_object_type type) sz (transform_cslot_ptr parent) dev
                 (transform_cslot_ptr slot, retype_transform_obj_ref type sz ptr))
        (Retype_A.create_cap type sz parent dev (slot, ptr))"
  supply if_cong[cong]
  apply (simp add: Untyped_D.create_cap_def Retype_A.create_cap_def)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_gets_the_bind)
    apply (rule corres_underlying_gets_pre_lhs)
    apply (rule corres_assert_lhs)
    apply (simp add: set_cap_set_parent_swap bind_assoc[symmetric])
    apply (rule corres_split_nor)
       apply (simp add: bind_assoc set_original_def create_cap_ext_def
                        set_cdt_modify gets_fold_into_modify update_cdt_list_def
                        modify_modify set_cdt_list_modify)
       apply (rule dcorres_set_parent_helper)
       apply (rule_tac P'="\<lambda>s. mdb_cte_at (swp cte_at s) (cdt s)
                                \<and> cte_at parent s \<and> cte_at slot s"
                      in corres_modify[where P=\<top>])
       apply (clarsimp simp: transform_def transform_current_thread_def
                             transform_asid_table_def transform_objects_def)
       apply (simp add: transform_cdt_def fun_upd_def[symmetric])
       apply (subst map_lift_over_upd)
        apply (rule_tac P=\<top> and s=s' in transform_cdt_slot_inj_on_cte_at)
        apply (auto dest: mdb_cte_atD[rotated] elim!: ranE)[1]
       apply simp
      apply (fold dc_def)
      apply (rule set_cap_corres, simp_all add: transform_default_cap)[1]
     apply (wp|simp)+
   apply (clarsimp simp: cte_wp_at_caps_of_state caps_of_state_transform_opt_cap not_idle_thread_def)
  apply (clarsimp simp: swp_def not_idle_thread_def cte_wp_at_caps_of_state)
  apply (drule mdb_cte_at_cdt_null)
   apply (clarsimp simp:cte_wp_at_caps_of_state swp_def)
  apply (fastforce simp:mdb_cte_at_def)
  done

lemma set_cap_default_not_none:
  "\<lbrace>\<lambda>s. cte_wp_at (\<lambda>x. slot \<noteq> ptr \<longrightarrow> x \<noteq> cap.NullCap) slot s\<rbrace> CSpaceAcc_A.set_cap (Retype_A.default_cap type a b dev) ptr
  \<lbrace>\<lambda>rv s. cte_wp_at ((\<noteq>) cap.NullCap) slot s\<rbrace>"
  apply (clarsimp simp:cte_wp_at_caps_of_state valid_def)
  apply (drule set_cap_caps_of_state_monad)
  apply clarsimp
  done

lemma create_cap_mdb_cte_at:
  "\<lbrace>\<lambda>s. mdb_cte_at (swp (cte_wp_at ((\<noteq>)cap.NullCap)) s) (cdt s)
  \<and> cte_wp_at ((\<noteq>)cap.NullCap) parent s \<and> cte_at (fst tup) s\<rbrace>
      create_cap type sz parent dev tup \<lbrace>\<lambda>rv s. mdb_cte_at (swp (cte_wp_at ((\<noteq>)cap.NullCap)) s) (cdt s)\<rbrace>"
  apply (simp add: create_cap_def split_def mdb_cte_at_def)
  apply (wp hoare_vcg_all_lift set_cap_default_not_none set_cdt_cte_wp_at hoare_weak_lift_imp dxo_wp_weak
          | simp | wps)+
  apply (fastforce simp: cte_wp_at_caps_of_state)
  done

lemma neg_mask_add_2p_helper:
  "\<lbrakk>is_aligned (b::word32) us;us < 32\<rbrakk> \<Longrightarrow> b + 2 ^ us - 1 && ~~ mask us = b"
  apply (simp add:p_assoc_help)
  apply (rule is_aligned_add_helper[THEN conjunct2]; simp add:less_1_helper)
  done

lemma retype_transform_ref_subseteq_strong:
  "\<lbrakk>p \<in> set (retype_addrs ptr ty n us);range_cover ptr sz (obj_bits_api ty us) n \<rbrakk>
  \<Longrightarrow> retype_transform_obj_ref ty us p \<subseteq> {ptr..ptr + of_nat n * (2::word32) ^ obj_bits_api ty us - 1}"
   apply (subgoal_tac "{p .. p + 2 ^ obj_bits_api ty us - 1}
     \<subseteq> {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1}")
   apply (erule subset_trans[rotated])
    apply (clarsimp simp:retype_transform_obj_ref_def)
    apply (rule conjI)
     apply (clarsimp simp:obj_bits_api_def)
    apply clarsimp
    apply (rule is_aligned_no_overflow)
    apply (erule retype_addrs_aligned)
      apply (erule range_cover.aligned)
     apply (drule range_cover.sz,simp add:word_bits_def)
    apply (erule range_cover.sz)
   apply (case_tac "n = 0")
    apply (clarsimp simp:retype_addrs_def)
   apply (frule(1) retype_addrs_range_subset)
   apply clarsimp
  proof -
    assume cover:"range_cover ptr sz (obj_bits_api ty us) n"
      and  mem_p:"p \<in> set (retype_addrs ptr ty n us)"
      and  not_0:"0 < n"
    note n_less = range_cover.range_cover_n_less[OF cover]
    have unat_of_nat_m1: "unat (of_nat n - (1::word32)) < n"
      using not_0 n_less
       by (simp add:unat_of_nat_minus_1)
    have decomp:"of_nat n * 2 ^ obj_bits_api ty us = of_nat (n - 1) * 2 ^ obj_bits_api ty us
      + (2 :: word32) ^ obj_bits_api ty us"
      apply (simp add:distrib_right[where b = "1::'a::len word",simplified,symmetric])
      using not_0 n_less
      apply (simp add:unat_of_nat_minus_1 obj_bits_api_def3)
      done
    show  "p + 2 ^ obj_bits_api ty us - 1 \<le> ptr + of_nat n * 2 ^ obj_bits_api ty us - 1"
      apply (subst decomp)
      apply (simp add:add.assoc[symmetric])
      apply (simp add:p_assoc_help)
      apply (rule order_trans[OF word_plus_mono_left word_plus_mono_right])
       using mem_p not_0
         apply (clarsimp simp:retype_addrs_def ptr_add_def shiftl_t2n)
         apply (rule word_plus_mono_right)
          apply (rule word_mult_le_mono1[OF word_of_nat_le])
          using n_less not_0
            apply (subst unat_of_nat_minus_1)
              apply simp
             apply simp
            apply (simp add:Set_Interval.ord_class.atLeastLessThan_def)
           apply (rule p2_gt_0[THEN iffD2])
           using cover
           apply (simp add:word_bits_def range_cover_def)
          apply (simp only: word_bits_def[symmetric])
          using not_0 n_less
          apply (clarsimp simp: unat_of_nat_minus_1)
          apply (subst unat_power_lower)
            using cover
            apply (simp add:range_cover_def)
          apply (rule nat_less_power_trans2[OF range_cover.range_cover_le_n_less(2),OF cover, folded word_bits_def])
          apply (simp add:unat_of_nat_m1 less_imp_le)
         using cover
         apply (simp add:range_cover_def word_bits_def)
        apply (rule machine_word_plus_mono_right_split[where sz = sz])
        using range_cover.range_cover_compare[OF cover,where p = "unat (of_nat n - (1::word32))"]
        apply (clarsimp simp:unat_of_nat_m1)
       using cover
       apply (simp add:range_cover_def word_bits_def)
      apply (rule olen_add_eqv[THEN iffD2])
      apply (subst add.commute[where a = "2^(obj_bits_api ty us) - 1"])
     apply (subst p_assoc_help[symmetric])
     apply (rule is_aligned_no_overflow)
     apply (insert cover)
     apply (clarsimp simp:range_cover_def)
     apply (erule aligned_add_aligned[OF _  is_aligned_mult_triv2])
       apply (simp add:range_cover_def)+
     by (metis is_aligned_add is_aligned_mult_triv2 is_aligned_no_overflow_mask mask_2pm1)
  qed

lemma generate_object_ids_exec:
  notes [simp del] = order_class.Icc_eq_Icc
  shows
  "dcorres r P P' (f  (map (retype_transform_obj_ref ty us) (retype_addrs ptr ty n us))) g
   \<Longrightarrow> dcorres r  P
  (K ((ty = Structures_A.Untyped \<longrightarrow> (untyped_min_bits \<le> us))
   \<and> range_cover ptr sz (obj_bits_api ty us) n
   \<and> is_aligned ptr (obj_bits_api ty us)
   \<and> {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1} \<subseteq> free_range )
  and (pspace_no_overlap_range_cover ptr sz) and valid_pspace and valid_idle and P')
  (do
    t \<leftarrow> generate_object_ids n (translate_object_type ty) free_range;
    f t
  od) g"
  apply (clarsimp simp: generate_object_ids_def bind_assoc)
  apply (rule dcorres_absorb_get_l)
  apply (rule corres_guard_imp)
    apply (rule_tac x = "(map (retype_transform_obj_ref ty us) (retype_addrs ptr ty n us))"
                    in select_pick_corres_asm[rotated])
     apply (rule corres_symb_exec_l)
        apply (rule_tac F = "rv = map (retype_transform_obj_ref ty us) (retype_addrs ptr ty n us)"
                        in corres_gen_asm)
        apply clarify
        apply assumption
       apply (clarsimp simp:return_def exs_valid_def)
      apply (rule hoare_vcg_if_split)
       apply (wp|simp)+
    apply (intro conjI impI)
      apply (clarsimp simp:distinct_map distinct_retype_addrs)
      apply (clarsimp simp:inj_on_def)
      apply (clarsimp simp:retype_transform_obj_ref_def split: if_split_asm)
      apply (frule range_cover.sz(1))
      apply (drule(1) retype_addrs_aligned[where sz = sz])
        apply (clarsimp simp:word_bits_def)
       apply (erule range_cover.sz)
      apply (drule(1) retype_addrs_aligned[where sz = sz])
        apply (clarsimp simp:word_bits_def)
       apply (erule range_cover.sz)
      apply (subst (asm) range_eq)
       apply (clarsimp simp: obj_bits_api_def)
      apply simp
     apply (clarsimp simp:retype_transform_obj_ref_def split:if_splits)
     apply (frule range_cover.sz(1))
     apply (drule(1) retype_addrs_aligned[where sz = sz])
       apply (clarsimp simp:word_bits_def)
      apply (erule range_cover.sz)
     apply (drule(1) retype_addrs_aligned[where sz = sz])
       apply (clarsimp simp:word_bits_def)
      apply (erule range_cover.sz)
     apply (clarsimp simp:obj_bits_api_def order_class.Icc_eq_Icc)
     apply (drule_tac x = b in neg_mask_mono_le[where n = us])
     apply (drule_tac x = a in neg_mask_mono_le[where n = us])
     apply (clarsimp simp: neg_mask_add_2p_helper dest!: range_cover_sz')
    apply (clarsimp)
    apply (intro conjI)
      apply (clarsimp simp:retype_transform_obj_ref_def)
      apply (rule is_aligned_no_overflow)
      apply (drule(1) retype_addrs_aligned[where sz = sz])
        apply (clarsimp simp:word_bits_def dest!:range_cover.sz(1))
       apply (erule range_cover.sz)
      apply (simp add:obj_bits_api_def)
     apply (erule(2) subset_trans[OF retype_transform_ref_subseteq_strong])
    apply (rule retype_transform_obj_ref_available)
         apply simp+
   apply (clarsimp simp:retype_transform_obj_ref_def translate_object_type_def)
  apply simp
  done

lemma create_caps_loop_dcorres:
  "dcorres dc \<top>
      (\<lambda>s. cte_wp_at ((\<noteq>) cap.NullCap) parent s \<and> valid_idle s \<and> mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)
            \<and> idle_thread s \<notin> fst ` fst ` set targets
            \<and> distinct (parent # map fst targets)
            \<and> (\<forall>tup \<in> set targets. cte_wp_at ((=) cap.NullCap) (fst tup) s) \<and> valid_etcbs s)
      (mapM_x
          (\<lambda>x. Untyped_D.create_cap (translate_object_type type) sz
                (transform_cslot_ptr parent) dev
                (transform_cslot_ptr (fst x), retype_transform_obj_ref type sz (snd x)))
          targets)
      (mapM_x (Retype_A.create_cap type sz parent dev) targets)"
  apply (induct targets)
   apply (simp add: mapM_x_Nil)
  apply (clarsimp simp: mapM_x_Cons)
  apply (rule corres_guard_imp)
    apply (rule corres_split_nor)
       apply (rule create_cap_dcorres)
      apply assumption
     apply (wp create_cap_invs hoare_vcg_const_Ball_lift create_cap_mdb_cte_at[unfolded swp_def])+
   apply simp
  apply (clarsimp simp: not_idle_thread_def swp_def)
  apply (auto simp: cte_wp_at_caps_of_state image_def)
  done

crunch init_arch_objects
  for valid_idle[wp]: "valid_idle"
  (wp: crunch_wps unless_wp ignore: clearMemory)

lemma update_available_range_dcorres:
  "dcorres dc \<top> ( K(\<exists>idx. untyped_cap = transform_cap (cap.UntypedCap dev ptr sz idx)
    \<and> free_range_of_untyped idx' sz ptr \<subseteq> new_range - set oids)
   and valid_idle and (\<lambda>s. fst cref \<noteq> idle_thread s) and valid_etcbs)
  (update_available_range new_range oids
    (transform_cslot_ptr cref) untyped_cap)
  (CSpaceAcc_A.set_cap
    (cap.UntypedCap dev ptr sz idx')
    cref)"
  apply (rule dcorres_expand_pfx)
  apply (clarsimp simp:update_available_range_def)
  apply (rule corres_guard_imp)
   apply (rule select_pick_corres)
    apply (rule set_cap_corres)
    apply clarsimp
    apply simp+
  done

lemma subseteq_set_minus:
  "\<lbrakk>A \<subseteq> B; A\<inter> C = {}\<rbrakk> \<Longrightarrow> A \<subseteq> B - C"
  by auto

lemma free_range_of_untyped_subseteq:
  "range_cover (ptr::word32) sz us n \<Longrightarrow>
  free_range_of_untyped (unat ((ptr && mask sz) + (of_nat n * 2^us))) sz (ptr &&~~ mask sz)
       \<subseteq> {ptr.. (ptr &&~~ mask sz) + 2 ^ sz - 1}"
  unfolding free_range_of_untyped_def
  apply clarsimp
  apply (subst AND_NOT_mask_plus_AND_mask_eq[symmetric,where n = sz])
  apply (rule word_plus_mono_right)
   apply (drule range_cover.range_cover_base_le)
   apply (clarsimp simp:shiftl_t2n field_simps)
  apply (rule is_aligned_no_wrap'[OF is_aligned_neg_mask])
   apply (rule le_refl)
  apply (rule word32_less_sub_le[THEN iffD1])
   apply (simp add: range_cover_def word_bits_def)
  apply (simp add: word_le_nat_alt range_cover_def unat_2p_sub_1)
  done

lemma retype_addrs_range_subset_strong:
  notes [simp del] = atLeastAtMost_iff atLeastatMost_subset_iff
  shows "\<lbrakk>p \<in> set (retype_addrs ptr ty n us); range_cover ptr sz (obj_bits_api ty us) n\<rbrakk>
  \<Longrightarrow> {p..p + 2 ^ obj_bits_api ty us - 1} \<subseteq> {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1}"
  apply (clarsimp simp: retype_addrs_def ptr_add_def)
  apply (drule_tac p = x in range_cover_subset)
   apply clarsimp+
  apply blast
  done

lemma le_p2_minus_1:
  "a \<le> (2^z - (Suc 0::nat)) \<Longrightarrow> a < 2^z"
   apply (subgoal_tac "(0 :: nat)< 2^z")
    apply arith
   apply simp
   done

lemma free_range_of_untyped_subseteq':
  "\<lbrakk>a \<le> a'; is_aligned ptr sz; sz < size (ptr)\<rbrakk>
    \<Longrightarrow> free_range_of_untyped a' sz ptr \<subseteq>free_range_of_untyped a sz ptr"
  apply (clarsimp simp:free_range_of_untyped_def)
  apply (rule word_plus_mono_right)
  apply (drule le_p2_minus_1)
   apply (rule of_nat_mono_maybe_le[THEN iffD1,rotated -1])
     apply simp
    apply (erule less_le_trans)
    apply (simp add: word_size)
   apply (drule(1) le_less_trans)
   apply (erule less_le_trans)
   apply (simp add: word_size)
  apply (erule is_aligned_no_wrap')
  apply (rule word_of_nat_less)
  apply (drule le_p2_minus_1)
  apply (simp add: word_size)
  done

lemma retype_transform_obj_ref_not_empty:
  "\<lbrakk>range_cover ptr sz (obj_bits_api tp us) n;
  is_aligned ptr (obj_bits_api tp us);
  y \<in> set (retype_addrs ptr tp n us)\<rbrakk>
   \<Longrightarrow> (retype_transform_obj_ref tp us y) \<noteq> {}"
  apply (frule(1) retype_addrs_aligned)
    apply (drule range_cover.sz,simp add:word_bits_def)
   apply (erule range_cover.sz)
  apply (clarsimp simp:retype_addrs_def retype_transform_obj_ref_def ptr_add_def)
  apply (rule is_aligned_no_overflow)
  apply (simp add:obj_bits_api_def)
  done

lemma in_empty_setE:
  "\<lbrakk>x\<in> A;x\<in> B; A\<inter> B = {}\<rbrakk> \<Longrightarrow> Q"
  by blast

lemma free_range_of_untyped_pick_retype_addrs:
  notes [simp del] = atLeastAtMost_iff
  shows "\<lbrakk>range_cover ptr sz (obj_bits_api tp us) (length slots) ; slots \<noteq> []\<rbrakk> \<Longrightarrow>
  free_range_of_untyped (unat ((ptr && mask sz) + (of_nat (length slots) << obj_bits_api tp us))) sz (ptr && ~~ mask sz) \<inter>
  (\<lambda>a. pick (retype_transform_obj_ref tp us a)) ` set (retype_addrs ptr tp (length slots) us) =
  {}"
  apply (clarsimp simp:image_def free_range_of_untyped_def)
  apply (rule disjointI)
  apply (drule CollectD)
  apply clarsimp
  apply (frule retype_transform_obj_ref_not_empty)
    apply (erule range_cover.aligned)
   apply simp
  apply (drule(1) retype_transform_ref_subseteq_strong)
  apply (drule nonempty_pick_in)
  apply (drule(1) set_mp[rotated])
  apply (clarsimp simp:shiftl_t2n field_simps)
  apply (erule(1) in_empty_setE)
  apply clarsimp
  apply (drule leD[where y = "(ptr && mask sz) + ((ptr && ~~ mask sz)
    + of_nat (length slots) * 2 ^ obj_bits_api tp us)"])
  apply (subgoal_tac " ptr + of_nat (length slots) * 2 ^ obj_bits_api tp us - 1 <
    (ptr && mask sz) + ((ptr && ~~ mask sz) + of_nat (length slots) * 2 ^ obj_bits_api tp us)")
   apply simp
  apply (subst group_add_class.add_diff_eq[symmetric])
  apply (frule range_cover_not_zero_shift[rotated,OF _ le_refl])
   apply simp
  apply (thin_tac "\<not>P" for P)
  apply (subst add.assoc[symmetric])
  apply (subst AND_NOT_mask_plus_AND_mask_eq[symmetric,where n = sz])
  apply (subst add.commute[where a = "(ptr && mask sz)"])
  apply (rule word_plus_strict_mono_right)
   apply (rule word_leq_le_minus_one)
    apply simp
   apply (simp add:shiftl_t2n field_simps)
   apply (subst add.assoc)
  apply (rule word_plus_mono_right)
   apply (simp add:word_le_nat_alt)
   apply (simp add: range_cover_unat)
  apply (rule is_aligned_no_wrap'[OF is_aligned_neg_mask])
   apply (rule le_refl)
  apply (drule le_p2_minus_1)
  apply (simp add:word_less_nat_alt)
  apply (subst unat_power_lower32[unfolded word_bits_def])
   apply (erule range_cover.sz)
  apply simp
  done

lemma clearMemory_corres_noop:
  "full_sz = 2 ^ sz \<Longrightarrow> is_aligned p sz \<Longrightarrow> 2 \<le> sz
    \<Longrightarrow> sz < word_bits
    \<Longrightarrow> dcorres dc \<top>
     (pspace_no_overlap {p .. p + 2 ^ sz - 1} and valid_objs and valid_etcbs)
     (return ())
     (do_machine_op (clearMemory p full_sz))"
  apply (simp add: clearMemory_def freeMemory_def[symmetric]
                   do_machine_op_bind empty_fail_freeMemory)
  apply (rule corres_guard_imp)
    apply (rule corres_add_noop_lhs)
    apply (rule corres_split_nor)
       apply (rule freeMemory_dcorres; simp)
      apply (rule dcorres_machine_op_noop)
      apply (wp | simp)+
  apply (clarsimp simp: field_simps)
  done

lemma mapME_x_upt_length_ys:
  "mapME_x (\<lambda>_. f) [0 ..< length ys]
    = mapME_x (\<lambda>_. f) ys"
  by (metis mapME_x_map_simp[where f="\<lambda>_. ()" and m="\<lambda>_. m" for m,
            unfolded o_def] map_replicate_const length_upt minus_nat.diff_0)

(* FIXME: move *)
lemma mapME_x_append:
  "mapME_x f (xs @ ys) = (doE mapME_x f xs; mapME_x f ys odE)"
  apply (induct xs)
   apply (simp add: mapME_x_Nil)
  apply (simp add: mapME_x_Cons bindE_assoc)
  done

lemma hd_filter_eq:
  "P (hd xs) \<Longrightarrow> hd (filter P xs) = hd xs"
  by (cases xs, simp_all)

lemma free_range_of_untyped_subset'[rule_format]:
  assumes al: "is_aligned ptr sz"
    and sz: "sz < size (ptr)"
  shows "a < a' \<longrightarrow> a < 2 ^ sz \<longrightarrow> free_range_of_untyped a' sz ptr \<subset> free_range_of_untyped a sz ptr"
proof -
  note no_ov = is_aligned_no_overflow'[OF al]
  note mono = word_plus_mono_right[OF _ no_ov, simplified field_simps]
  note sz_len = sz[unfolded word_size]
(*
  note sz_simp[simp] = unat_2p_sub_1[OF sz_len] unat_power_lower[OF sz_len]
*)
  show ?thesis using sz
    apply (intro impI psubsetI)
     apply (rule free_range_of_untyped_subseteq', simp_all add: al)
    apply (clarsimp simp:free_range_of_untyped_def)
    apply (strengthen mono word_of_nat_le)+
    apply (simp add: sz_len unat_2p_sub_1)
    apply (intro conjI impI; (clarsimp dest!: le_p2_minus_1)?)
     apply (drule word_unat.Abs_eqD, simp_all add: unats_def word_size
           less_trans[OF _ power_strict_increasing[OF sz_len]])
    done
qed

lemma delete_objects_invs2:
  "\<lbrace>(\<lambda>s. \<exists>slot dev f. cte_wp_at ((=) (cap.UntypedCap dev ptr bits f)) slot s
    \<and> descendants_range (cap.UntypedCap dev ptr bits f) slot s) and
    invs and ct_active\<rbrace>
    delete_objects ptr bits \<lbrace>\<lambda>_. invs\<rbrace>"
  by (rule hoare_name_pre_state, clarsimp, wp delete_objects_invs, fast)

lemma reset_untyped_cap_corres:
  notes delete_objects_invs[wp del]
  shows
  "dcorres (dc \<oplus> dc) \<top> (invs and valid_etcbs and ct_active
          and cte_wp_at (\<lambda>cap. is_untyped_cap cap \<and> free_index_of cap = idx) cref
          and (\<lambda>s. descendants_of cref (cdt s) = {}))
     (Untyped_D.reset_untyped_cap (transform_cslot_ptr cref))
     (Retype_A.reset_untyped_cap cref)"
  supply if_cong[cong]
  apply (rule dcorres_expand_pfx)
  apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps)
  apply (simp add: Untyped_D.reset_untyped_cap_def reset_untyped_cap_def
                   liftE_bindE)
  apply (rule corres_guard_imp)
    apply (rule corres_split)
       apply (rule get_cap_corres; simp)
      apply (rule_tac F="is_untyped_cap capa \<and> cap_aligned capa
                \<and> bits_of capa > 2 \<and> free_index_of capa \<le> 2 ^ bits_of capa"
            in corres_gen_asm2)
      apply (simp add: whenE_def if_flip split del: if_split)
      apply (rule corres_if)
        apply (clarsimp simp: is_cap_simps free_range_of_untyped_def
                              cap_aligned_def free_index_of_def
                        simp del: word_of_nat_eq_0_iff)
        apply (simp add: word_unat.Rep_inject[symmetric])
        apply (subst unat_of_nat_eq, erule order_le_less_trans,
          rule power_strict_increasing, simp_all add: word_bits_def bits_of_def)[1]
       apply (rule corres_trivial, rule corres_returnOk, simp)
      apply (rule_tac F="free_index_of capa \<noteq> 0" in corres_gen_asm2)
      apply (rule corres_split_nor)
         apply (rule delete_objects_dcorres)
         apply (clarsimp simp: is_cap_simps bits_of_def)
        apply (rule corres_if_rhs)
         apply (rule_tac x="[cap_objects (transform_cap capa)]" in select_pick_corres_asm)
          apply (clarsimp simp: is_cap_simps cap_aligned_def free_index_of_def)
          apply (rule order_less_le_trans, rule free_range_of_untyped_subset'[where a=0],
            simp_all)[1]
           apply (simp add: word_size word_bits_def)
          apply (simp add: free_range_of_untyped_def)

         apply (simp add: mapME_x_Nil mapME_x_Cons liftE_def bind_assoc)
         apply (rule corres_add_noop_lhs)
         apply (rule corres_split_nor)
            apply (rule dcorres_unless_r)
             apply (rule clearMemory_corres_noop[OF refl])
               apply (clarsimp simp: is_cap_simps cap_aligned_def bits_of_def)
              apply (clarsimp simp: is_cap_simps bits_of_def free_range_of_untyped_def)
             apply (clarsimp simp: is_cap_simps cap_aligned_def bits_of_def)
            apply (rule corres_trivial, simp)
           apply (rule corres_split_nor)
              apply (rule set_cap_corres)
               apply (clarsimp simp: is_cap_simps bits_of_def free_range_of_untyped_def)
              apply simp
             apply (rule corres_alternate1)
             apply (rule corres_trivial, simp add: returnOk_def)
            apply (wp | simp add: unless_def)+
        apply (rule_tac F="\<not> (is_device_untyped_cap capa \<or> bits_of capa < resetChunkBits)
                  \<and> (\<exists>s. s \<turnstile> capa)"
              in corres_gen_asm2)
        apply (rule_tac x="map (\<lambda>i. free_range_of_untyped (i * 2 ^ resetChunkBits)
                  (bits_of capa) (obj_ref_of capa)) xs" for xs
          in select_pick_corres_asm)
         prefer 2
         apply (simp add: mapME_x_map_simp o_def)
         apply (rule_tac P="\<top>\<top>" and P'="\<lambda>_. valid_objs
                 and valid_etcbs and pspace_no_overlap (untyped_range capa)
                 and valid_idle and (\<lambda>s. idle_thread s \<noteq> fst cref)
                 and cte_wp_at (\<lambda>cp. \<exists>idx. cp = free_index_update (\<lambda>_. idx) capa) cref"
                 in mapME_x_corres_same_xs[OF _ _ _ refl])
           apply (rule corres_guard_imp)
             apply (rule corres_add_noop_lhs)
             apply (rule corres_split_nor)
                apply (rule clearMemory_corres_noop[OF refl])
                  apply (clarsimp simp add: is_cap_simps cap_aligned_def bits_of_def
                                            aligned_add_aligned is_aligned_shiftl)
                 apply (simp add: Kernel_Config.resetChunkBits_def)
                apply (simp add: Kernel_Config.resetChunkBits_def word_bits_def)
               apply (rule corres_split)
                  apply (rule set_cap_corres; simp)
                  apply (clarsimp simp: is_cap_simps bits_of_def)
                 apply (subst alternative_com)
                 apply (rule throw_or_return_preemption_corres[where P=\<top> and P'=\<top>])
                apply wp+
            apply (wp hoare_vcg_all_lift hoare_vcg_const_imp_lift
                      preemption_point_inv' set_cap_no_overlap
                      update_untyped_cap_valid_objs set_cap_idle
                       | simp)+
           apply (clarsimp simp: is_cap_simps bits_of_def cap_aligned_def)
           apply (erule pspace_no_overlap_subset)
           apply (rule aligned_range_offset_subset, simp_all add: is_aligned_shiftl)[1]
           apply (rule shiftl_less_t2n[OF word_of_nat_less])
            apply simp
           apply (simp add: word_bits_def)
          apply wpsimp
         apply (wp hoare_vcg_all_lift hoare_vcg_const_imp_lift
                   update_untyped_cap_valid_objs set_cap_no_overlap
                   set_cap_idle preemption_point_inv'
                   set_cap_cte_wp_at
                | simp)+
         apply (clarsimp simp: cte_wp_at_caps_of_state exI
                               is_cap_simps bits_of_def)
         apply (frule(1) cte_wp_at_valid_objs_valid_cap[OF caps_of_state_cteD])
         apply (clarsimp simp: valid_cap_simps cap_aligned_def
                               valid_untyped_pspace_no_overlap
                               free_index_of_def)

        apply (clarsimp simp: is_cap_simps bits_of_def)
        apply (strengthen order_trans[OF free_range_of_untyped_subseteq'[where a=0]]
                          free_range_of_untyped_subset')
        apply (clarsimp simp: conj_comms)
        apply (clarsimp simp: filter_empty_conv bexI[where x=0]
                              last_rev hd_map hd_filter_eq
                              is_cap_simps bits_of_def cap_aligned_def
                              word_bits_def word_size exI
                              rev_map[symmetric])
        apply (clarsimp simp: free_index_of_def free_range_of_untyped_def)
       apply (simp del: hoare_TrueI)
       apply wp
      apply (wp add: hoare_vcg_const_imp_lift get_cap_wp delete_objects_invs2
         | simp
         | strengthen invs_valid_objs invs_valid_idle
         | rule impI)+
  apply (clarsimp simp: cte_wp_at_caps_of_state
                        descendants_range_def2)
  apply (strengthen empty_descendants_range_in
    subst[where P="\<lambda>x. descendants_of x c = {}" for c, mk_strg I _ E]
    | simp add: prod_eq_iff)+
  apply (cases cref)
  apply (clarsimp simp: is_cap_simps bits_of_def free_index_of_def
                        )
  apply (frule cte_wp_at_valid_objs_valid_cap[OF caps_of_state_cteD],
    clarsimp+)
  apply (clarsimp simp: valid_cap_simps)
  apply (frule if_unsafe_then_capD[OF caps_of_state_cteD], clarsimp+)
  apply (frule(1) ex_cte_cap_protects[OF _ caps_of_state_cteD _ _ order_refl],
    simp add: empty_descendants_range_in, clarsimp+)
  apply (auto simp: not_idle_thread_def untyped_min_bits_def
             dest!: valid_idle_has_null_cap[rotated -1],
    auto intro: caps_of_state_valid)[1]
  done

lemma range_le_free_range_of_untyped:
  "range_cover (ptr::word32) sz sbit n
    \<Longrightarrow> n \<noteq> 0
    \<Longrightarrow> idx \<le> unat (ptr && mask sz)
    \<Longrightarrow> {ptr..ptr + of_nat n * 2 ^ sbit - 1}
             \<subseteq> free_range_of_untyped idx sz (ptr && ~~ mask sz)"
  apply (rule order_trans, erule(1) range_cover_subset')
  apply (clarsimp simp: free_range_of_untyped_def
             split del: if_split del: subsetI)
  apply (subst if_P)
   prefer 2
   apply (rule range_subsetI, simp_all)
   apply (subst word_plus_and_or_coroll2[symmetric,where w = "mask sz" and t = ptr],
     subst add.commute,
     rule word_add_le_mono2)
    apply (simp add: word_of_nat_le)
   apply (simp only: no_olen_add_nat[symmetric] word_plus_and_or_coroll2 word_and_le2)
  apply (erule order_trans)
  apply (rule nat_le_Suc_less_imp)
  apply (rule word_unat_mask_lt)
  apply (simp add: range_cover_def word_size)
  done

lemma invoke_untyped_corres:
  "dcorres (dc \<oplus> dc) (\<lambda>_. True)
             (invs and ct_active and valid_untyped_inv untyped_invocation and valid_etcbs)
             (Untyped_D.invoke_untyped (translate_untyped_invocation untyped_invocation))
             (Retype_A.invoke_untyped untyped_invocation)"
  apply (rule dcorres_expand_pfx)
  apply (clarsimp simp only: valid_untyped_inv_wcap)
  apply (cases untyped_invocation)
  apply (rename_tac s s' sz idx creforef reset ptr ptr' tp us slots dev)
  proof -
    fix s cref reset ptr ptr' tp us slots sz idx dev
    assume vui1: "valid_untyped_inv_wcap untyped_invocation
         (Some (case untyped_invocation of
                Invocations_A.untyped_invocation.Retype slot reset ptr_base ptr ty us slots dev \<Rightarrow>
                  cap.UntypedCap dev (ptr && ~~ mask sz) sz idx)) s"
    and ui: "untyped_invocation =
        Invocations_A.Retype cref reset ptr' ptr tp us slots dev"
    and etc: "valid_etcbs s" "invs s" "ct_active s"

  note vui = vui1[simplified ui Invocations_A.untyped_invocation.simps]

  have ptrs: "ptr' = ptr && ~~ mask sz"
    using vui
    by (auto simp: ui cte_wp_at_caps_of_state word_bw_assocs)

  have cover: "range_cover ptr sz (obj_bits_api tp us) (length slots)"
   and vslot: "slots \<noteq> []" "distinct slots"
    and misc: "tp = Structures_A.apiobject_type.CapTableObject \<longrightarrow> 0 < us"
              "tp = Structures_A.apiobject_type.Untyped \<longrightarrow> untyped_min_bits \<le> us"
    using vui
    by (auto simp: ui cte_wp_at_caps_of_state)

  have vcap: "s \<turnstile> cap.UntypedCap dev (ptr && ~~ mask sz) sz idx"
    using vui etc
    by (auto simp: ui cte_wp_at_caps_of_state
            dest!: caps_of_state_valid[rotated])

  note [simp del] = usable_untyped_range.simps atLeastAtMost_iff
                    atLeastatMost_subset_iff split_paired_Ex

  show  "dcorres (dc \<oplus> dc) ((=) (transform s)) ((=) s)
           (Untyped_D.invoke_untyped
             (translate_untyped_invocation untyped_invocation))
           (Retype_A.invoke_untyped untyped_invocation)"
    supply option.case_cong[cong] if_cong[cong]
    apply (clarsimp simp: Untyped_D.invoke_untyped_def mapM_x_def translate_untyped_invocation_def
                          ui ptrs invoke_untyped_def unlessE_whenE)
    apply (rule corres_guard_imp)
      apply (rule corres_split_norE)
         apply (rule corres_whenE, simp)
          apply (rule reset_untyped_cap_corres[where idx=idx])
         apply simp
        apply simp
        apply (rule corres_split)
           apply (rule get_cap_corres; simp)
          apply simp
          apply (rule generate_object_ids_exec[where ptr = ptr and us = us and sz = sz])
          apply simp
          apply (rule corres_split[OF update_available_range_dcorres])
            apply simp
            apply (rule corres_split[OF retype_region_dcorres[where sz = sz]])
              apply (rule corres_split_noop_rhs)
                apply (rule init_arch_objects_corres_noop[where sz =sz])
                  apply clarsimp
                  apply (erule retype_addrs_aligned[OF _ range_cover.aligned _ le_refl])
                   apply (rule cover)
                  apply (rule range_cover_sz'[where 'a=32, folded word_bits_def, OF cover])
                 apply (rule cover)
                apply (simp add: vslot)
               apply (simp add: liftM_def[symmetric] mapM_x_def[symmetric]
                                zip_map1 zip_map2 o_def split_beta dc_def[symmetric])
               apply (rule_tac F = " (untyped_is_device (transform_cap cap)) = dev" in corres_gen_asm2)
               apply clarify
               apply (rule create_caps_loop_dcorres)
              apply ((wp | simp add: mdb_cte_at_def | rule hoare_vcg_conj_lift, wps)+)[2]
            supply send_signal_interrupt_states[wp_unsafe del] validNF_prop[wp_unsafe del]
            apply (wp retype_region_aligned_for_init[where sz = sz]
                    retype_region_obj_at[THEN hoare_vcg_const_imp_lift]
                    retype_region_caps_of[where sza = "\<lambda>_. sz"]
                 | simp add: misc)+
            apply (rule_tac Q="\<lambda>rv s. cte_wp_at ((\<noteq>) cap.NullCap) cref s
                                      \<and> post_retype_invs tp rv s
                                      \<and> idle_thread s \<notin> fst ` set slots
                                      \<and> untyped_is_device (transform_cap cap) = dev
                                      \<and> (\<forall>slot\<in>set slots. cte_wp_at ((=) cap.NullCap) slot s)
                                      \<and> valid_etcbs s"
                            in hoare_post_imp)
             apply (simp add:post_retype_invs_def split:if_split_asm)
              apply ((clarsimp dest!: set_zip_leftD
                                simp: vslot image_def invs_def valid_state_def valid_mdb_def
                                      cte_wp_at_caps_of_state
                     | intro conjI | drule (1) bspec | drule(1) mdb_cte_atD[rotated])+)[2]
            apply (wp retype_region_cte_at_other'[where sz= sz]
                      retype_region_post_retype_invs[where sz = sz]
                      hoare_vcg_const_Ball_lift retype_region_aligned_for_init)+
          apply (clarsimp simp:conj_comms misc cover)
          apply (rule_tac Q="\<lambda>r s.
               cte_wp_at (\<lambda>cp. \<exists>idx. cp = (cap.UntypedCap dev ptr' sz idx)) cref s \<and>
               invs s \<and> pspace_no_overlap_range_cover ptr sz s \<and> caps_no_overlap ptr sz s \<and>
               region_in_kernel_window {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1} s \<and>
               caps_overlap_reserved {ptr..ptr + of_nat (length slots) * 2 ^ obj_bits_api tp us - 1} s \<and>
               idle_thread s \<notin> fst ` set slots
               \<and> untyped_is_device (transform_cap cap) = dev
               \<and> (\<forall>x\<in>set slots. cte_wp_at ((=) cap.NullCap) x s) \<and> valid_etcbs s"
               in hoare_strengthen_post[rotated])
           apply (clarsimp simp: invs_mdb invs_valid_pspace cte_wp_at_caps_of_state misc split_paired_Ex)
           apply (rule conjI,clarsimp)
            apply (erule ranE)
            apply (clarsimp simp:null_filter_def split:if_splits)
            apply (frule_tac cap = capa in caps_of_state_ko[OF caps_of_state_valid])
             apply assumption
            apply (elim disjE)
              apply (clarsimp simp:cap_range_def is_cap_simps)+
            apply (rule disjointI)
            apply clarsimp
            apply (drule bspec,fastforce,clarsimp)
            apply (drule(1) pspace_no_overlap_obj_range)
            apply (drule p_in_obj_range)
              apply clarsimp+
            apply (auto simp: field_simps)[1]
           apply (cases cref, simp, intro exI, rule conjI, assumption,
                  simp add: atLeastatMost_subset_iff word_and_le2 ptrs field_simps)
          apply (rule_tac P="bits_of cap = sz" in hoare_gen_asm)
          apply (simp add:bits_of_def)
          apply (strengthen caps_region_kernel_window_imp[where p=cref] invs_cap_refs_in_kernel_window)+
          apply (wp set_cap_no_overlap hoare_vcg_ball_lift
                    set_free_index_invs[where 'a=det_ext and
                                               cap = "cap.UntypedCap dev (ptr && ~~ mask sz) sz
                                                                     (if reset then 0 else idx)",
                                               simplified]
                    set_cap_cte_wp_at set_cap_descendants_range_in set_cap_caps_no_overlap
                    set_untyped_cap_caps_overlap_reserved set_cap_cte_cap_wp_to hoare_vcg_ex_lift)
         apply wp
        apply (simp split del: if_split)
        apply (wp get_cap_wp)+
       apply (wp (once) hoare_drop_imps)
       apply wp
      apply ((rule validE_validE_R)?,
             rule_tac E="\<top>\<top>" and
                      Q="\<lambda>_. valid_etcbs and invs and valid_untyped_inv_wcap untyped_invocation
                                (Some (cap.UntypedCap dev ptr' sz (if reset then 0 else idx))) and ct_active
                             and (\<lambda>s. reset \<longrightarrow> pspace_no_overlap {ptr' .. ptr' + 2 ^ sz - 1} s)"
                      in hoare_strengthen_postE)
        apply (wp whenE_wp)
        apply (rule validE_validE_R, rule hoare_strengthen_postE, rule reset_untyped_cap_invs_etc)
         apply (clarsimp simp only: if_True simp_thms ptrs, intro conjI, assumption+)
        apply simp
       apply (clarsimp simp only: ui ptrs)
       apply (frule(2) invoke_untyped_proofs.intro)
       apply (clarsimp simp: ui cte_wp_at_caps_of_state bits_of_def empty_descendants_range_in exI
                             free_index_of_def untyped_range_def if_split[where P="\<lambda>x. x \<le> unat v" for v]
                  split del: if_split)
       apply (frule(1) valid_global_refsD2[OF _ invs_valid_global_refs])
       apply (strengthen refl subseteq_set_minus free_range_of_untyped_subseteq'
                         range_le_free_range_of_untyped[mk_strg I E]
                         caps_region_kernel_window_imp[where p=cref])+
       apply (simp only: word_size word_bits_def[symmetric])
       apply (clarsimp simp: conj_comms invoke_untyped_proofs.simps range_le_free_range_of_untyped
                             if_split[where P="\<lambda>x. x \<le> unat v" for v]
                  split del: if_split)
       apply (simp add: arg_cong[OF mask_out_sub_mask, where f="\<lambda>y. x - y" for x]
                        field_simps invoke_untyped_proofs.idx_le_new_offs
                        invoke_untyped_proofs.idx_compare'
                        untyped_range_def invs_valid_idle invs_valid_pspace
                        is_aligned_neg_mask invoke_untyped_proofs.szw
                        free_range_of_untyped_pick_retype_addrs vslot
             split del: if_split)
       apply (clarsimp simp: detype_clear_um_independent conj_comms not_idle_thread_def
                             misc invs_valid_idle invs_valid_objs word_bits_def word_and_le2
                             atLeastatMost_subset_iff[where b=x and d=x for x]
                 split del: if_split)
       apply (clarsimp simp: range_cover.aligned bits_of_def field_simps split del: if_split)
       apply (intro conjI)
            apply (cases cref, fastforce dest: valid_idle_has_null_cap[rotated -1])
           apply (fastforce dest: ex_cte_cap_to_not_idle)
          apply (cases reset)
           apply (simp, erule pspace_no_overlap_subset)
           apply (simp add: atLeastatMost_subset_iff word_and_le2)
          apply (clarsimp simp: field_simps dest!: invoke_untyped_proofs.ps_no_overlap)
         apply (auto dest: invoke_untyped_proofs.idx_le_new_offs)[1]
        apply (strengthen invoke_untyped_proofs.subset_stuff[THEN order_trans, mk_strg I E])
        apply (simp add: atLeastatMost_subset_iff word_and_le2)
       apply (drule invoke_untyped_proofs.usable_range_disjoint)
       apply (clarsimp simp: field_simps mask_out_sub_mask shiftl_t2n)
      apply simp
     apply simp
    apply (cut_tac vui1)
    apply (clarsimp simp add: etc ptrs)
    apply (clarsimp simp: ui cte_wp_at_caps_of_state valid_cap_simps free_index_of_def)
    apply auto
    done
qed

lemma transform_translate_type:
  "transform_type n = Some tp
      \<Longrightarrow> \<exists>v. data_to_obj_type n = returnOk v \<and> tp = translate_object_type v"
  apply (simp add: transform_type_def
            split: if_split_asm)
  apply (simp_all add: data_to_obj_type_def arch_data_to_obj_type_def)
  apply (auto simp add: translate_object_type_def)
  done

lemma corres_whenE_throwError_split_rhs:
  "corres_underlying sr nf nf' r P Q a (whenE G (throwError e) >>=E (\<lambda>_. b))
     = ((G \<longrightarrow> corres_underlying sr nf nf' r P Q a (throwError e))
           \<and> (\<not> G \<longrightarrow> corres_underlying sr nf nf' r P Q a b))"
  by (simp add: whenE_bindE_throwError_to_if)


lemma nat_bl_to_bin_nat_to_cref:
  assumes asms: "x < 2 ^ bits" "bits < word_bits"
  shows "nat (bl_to_bin (nat_to_cref bits x)) = x"
proof -
  note of_bl = of_bl_nat_to_cref[OF asms]
  have lt_bl: "bl_to_bin (nat_to_cref bits x) < 2 ^ 32"
    apply (rule order_less_le_trans, rule bl_to_bin_lt2p)
    apply (rule power_increasing)
     apply (simp add: nat_to_cref_def)
    apply simp
    done
  have lt_x: "x < 2 ^ 32"
    apply (rule order_less_le_trans, rule asms)
    apply (rule power_increasing, simp_all)
    apply (insert asms word_bits_conv, simp)
    done
  show ?thesis using of_bl lt_bl lt_x
    apply (simp add: of_bl_def)
    apply (erule word_of_int_word_of_nat_eqD; simp add: bl_to_bin_ge0)
    done
qed

context
notes if_cong[cong]
begin
crunch "CSpace_D.ensure_empty"
  for inv[wp]: "P"
end

lemma mapME_x_inv_wp2:
  "(\<And>x. \<lbrace>P and E\<rbrace> f x \<lbrace>\<lambda>rv. P and E\<rbrace>,\<lbrace>\<lambda>rv. E\<rbrace>)
      \<Longrightarrow> \<lbrace>P and E\<rbrace> mapME_x f xs \<lbrace>\<lambda>rv. P\<rbrace>,\<lbrace>\<lambda>rv. E\<rbrace>"
  apply (rule hoare_strengthen_postE)
  apply (rule mapME_x_inv_wp[where E="\<lambda>_. E"])
    apply (rule hoare_strengthen_postE, assumption)
     apply simp_all
  done

lemma gets_get:
  "get = gets id "
  by (simp add:gets_def)

lemma transform_cdt_dom_standard:
  "transform_cdt s' slot' = Some (transform_cslot_ptr b)
   \<Longrightarrow> \<exists>slot. slot' = transform_cslot_ptr slot"
  apply (case_tac b)
  apply (fastforce simp:transform_cdt_def map_lift_over_def split:if_split_asm)
  done

lemma descendants_of_empty_lift :
  "\<lbrakk>cte_at slot' s; valid_mdb s\<rbrakk> \<Longrightarrow>
  (CSpaceAcc_A.descendants_of slot' (cdt s) = {})
   = (\<not> (\<exists>slot. transform_cdt s slot = Some (transform_cslot_ptr slot')))"
  apply (rule iffI)
   apply clarsimp
   apply (frule transform_cdt_dom_standard)
   apply (clarsimp simp:descendants_of_def)
   apply (thin_tac "(a,b) = P" for P)
   apply (drule(1) transform_cdt_some_rev)
    apply (clarsimp simp:valid_mdb_def)
   apply clarsimp
   apply (drule_tac x = a in spec,drule_tac x = b in spec)
   apply (subgoal_tac "cdt s \<Turnstile> slot' \<rightarrow> (a, b)")
    apply simp
   apply (rule r_into_trancl')
   apply (simp add:cdt_parent_rel_def is_cdt_parent_def)
  apply (rule ccontr)
  apply (clarsimp simp:descendants_of_def)
  apply (drule tranclD)
  apply clarsimp
   apply (drule_tac x = aa in spec,drule_tac x = "nat (bl_to_bin ba)" in spec)
   apply (frule descendants_of_cte_at[rotated])
    apply (simp add:descendants_of_def)
    apply (rule r_into_trancl')
    apply simp
  apply (drule_tac slot = "(aa,ba)" in mdb_cte_transform_cdt_lift)
   apply (simp add:valid_mdb_def)
  apply (clarsimp simp:cdt_parent_rel_def is_cdt_parent_def transform_cslot_ptr_def)
  done

lemma alignUp_gt_0:
  "\<lbrakk>is_aligned (x :: 'a :: len word) n; n < len_of TYPE('a); x \<noteq> 0 ; a \<le> x\<rbrakk> \<Longrightarrow> (0 < alignUp a n) = (a \<noteq> 0)"
  apply (rule iffI)
   apply (rule ccontr)
   apply (clarsimp simp:not_less alignUp_def2 mask_def)
  apply (frule(1) alignUp_is_aligned_nz[where a = a])
    apply (simp add:unat_1_0)
   apply simp
  apply (simp add:word_neq_0_conv)
  done

lemma of_nat_0:
  "free_index < 2^word_bits - 1
   \<Longrightarrow> ((of_nat free_index::word32) = 0) = (free_index = 0)"
  apply (subst word_unat.inverse_norm)
  apply (subst word_bits_def[symmetric])
  apply simp
  done

lemma range_cover_sz_less':
  "range_cover (ptr :: word32) sz us n \<Longrightarrow> (2::nat) ^ sz < 2 ^ word_bits - 1"
  apply (simp add:range_cover_def)
  apply (rule le_less_trans[where y = "2^31"])
    apply (rule power_increasing)
    apply (clarsimp simp:word_bits_def)
   apply simp
  apply (simp add:word_bits_def)
  done

lemma decode_untyped_corres:
  "\<lbrakk> Some (UntypedIntent ui) = transform_intent (invocation_type label') args';
     cap = transform_cap cap';
     cap' = cap.UntypedCap dev ptr sz idx;
     slot = transform_cslot_ptr slot';
     excaps = transform_cap_list excaps' \<rbrakk> \<Longrightarrow>
   dcorres (dc \<oplus> (\<lambda>x y. x = translate_untyped_invocation y))
       \<top> (cte_wp_at ((=) cap') slot' and invs
           and (\<lambda>s. \<forall>x \<in> set (map fst excaps'). s \<turnstile> x)
           and (\<lambda>s. \<forall>x \<in> set excaps'. cte_wp_at ((=) (fst x)) (snd x) s) and valid_etcbs)
     (Untyped_D.decode_untyped_invocation cap slot excaps ui)
     (Decode_A.decode_untyped_invocation label' args' slot' cap' (map fst excaps'))"
  supply if_cong[cong]
  apply (simp add: transform_intent_def map_option_Some_eq2
                   transform_intent_untyped_retype_def
            split: invocation_label.split_asm gen_invocation_labels.split_asm
                   arch_invocation_label.split_asm list.split_asm option.split_asm)
  apply (cases ui)
  apply (drule transform_translate_type[where 'a=det_ext])
  apply (clarsimp simp: Untyped_D.decode_untyped_invocation_def
                        Decode_A.decode_untyped_invocation_def
                        unlessE_whenE
             split del: if_split
                 split: invocation_label.split_asm)
  apply (rename_tac a list w1 w2 w3 w4 w5 apiobject_type)
  apply (cases excaps')
   apply (simp add: get_index_def transform_cap_list_def
                    alternative_refl gen_invocation_type_eq)
  apply (simp add: get_index_def transform_cap_list_def throw_on_none_def
                   split_beta
               split del: if_split)
  apply (clarsimp simp: corres_whenE_throwError_split_rhs
                        corres_alternate2
             split del: if_split)
  apply (simp add: bindE_assoc[symmetric] split del: if_split)
  apply (rule_tac r'="\<lambda>rv rv'. rv = transform_cap rv'"
              in corres_alternative_throw_splitE)
       apply (rule corres_guard_imp, rule corres_alternate1)
         apply (rule corres_if)
           apply (simp add: unat_eq_0)
          apply (rule corres_trivial, simp add: returnOk_def)
         apply (rule corres_splitEE)
            apply (rule lookup_slot_for_cnode_op_corres; simp)
           apply clarsimp
           apply (rule get_cap_corres)
           apply simp
          apply (wp lsfco_not_idle | simp)+
       apply (clarsimp simp: cte_wp_at_caps_of_state)
       apply auto[1]
      apply (rename_tac cnode_cap cnode_cap')
      apply (simp add: bindE_assoc split del: if_split)
      apply (simp add: if_to_top_of_bindE is_cnode_cap_transform_cap[symmetric]
                  split del: if_split)
      apply (rule corres_if_rhs[rotated])
       apply (rule corres_trivial, simp add: alternative_refl)
      apply (simp add: corres_whenE_throwError_split_rhs
                       corres_alternate2)
      apply (intro impI)
      apply (rule_tac r'=dc in corres_alternative_throw_splitE[rotated])
           apply (simp add:liftE_bindE)
           apply (rule corres_symb_exec_r)
              apply (clarsimp simp: corres_whenE_throwError_split_rhs corres_alternate2
                         split del: if_split)
              apply (rule corres_alternate1)
              apply (simp add:gets_get split del: if_split)
              apply (rule corres_underlying_gets_pre_lhs)
              apply (rule_tac P' = "\<lambda>s. valid_mdb s \<and> cte_at slot' s \<and> is_cnode_cap cnode_cap' \<and>
                cap_aligned cnode_cap' \<and> invs s \<and> not_idle_thread (obj_ref_of cnode_cap') s \<and>
                is_aligned ptr sz \<and> idx \<le> 2 ^ sz \<and> sz < word_bits \<and>
                reset = (descendants_of slot' (cdt s) ={} ) \<and> valid_etcbs s"
                and P = "\<lambda>s. s = x" in corres_returnOk)
              apply (simp add: translate_untyped_invocation_def transform_def get_free_ref_def)
              apply (simp add:has_children_def KHeap_D.is_cdt_parent_def
                descendants_of_empty_lift word_neq_0_conv)
              apply (clarsimp simp: not_less is_cap_simps bits_of_def)
              apply (clarsimp simp: is_cap_simps transform_cslot_ptr_def bits_of_def
                                    cap_aligned_def nat_bl_to_bin_nat_to_cref)
             apply (wp check_children_wp)
            apply simp
           apply (simp add:const_on_failure_def)
          apply clarsimp
          apply wp+
         apply (clarsimp simp:conj_comms)
         apply (wp mapME_x_inv_wp[OF hoare_pre(2)] | simp split del: if_split)+
       apply (simp split del: if_split add: if_apply_def2)
      apply (rule corres_alternate1)
      apply (rule corres_guard_imp)
        apply (rule_tac F="cap_aligned cnode_cap' \<and> is_cnode_cap cnode_cap'" in corres_gen_asm2)
        apply (subgoal_tac "map (Pair (cap_object (transform_cap cnode_cap')))
             [unat w3 ..< unat w3 + unat w4]
             = map (\<lambda>x. transform_cslot_ptr (obj_ref_of (cnode_cap'),
             (nat_to_cref (bits_of cnode_cap') x)))
             [unat w3 ..< unat w3 + unat w4]")
         apply (simp del: map_eq_conv)
         apply (simp add: mapME_x_map_simp)
         apply (rule mapME_x_corres_inv)
            apply (simp add: dc_def[symmetric])
            apply (rule dcorres_ensure_empty)
           apply (wp mapME_x_inv_wp[OF hoare_pre(2)] | simp)+
        apply (clarsimp simp: is_cap_simps transform_cslot_ptr_def bits_of_def cap_aligned_def
                              nat_bl_to_bin_nat_to_cref)
       apply simp
      apply clarsimp
     apply (rule hoare_pre)
      apply wpsimp
     apply fastforce
    apply (clarsimp simp: conj_comms is_cnode_cap_transform_cap split del: if_split)
    apply (rule validE_R_validE)
    apply (rule_tac Q' = "\<lambda>a s. invs s \<and> valid_etcbs s \<and> valid_cap a s \<and> cte_wp_at ((=) (cap.UntypedCap dev ptr sz idx)) slot' s
      \<and> (Structures_A.is_cnode_cap a \<longrightarrow> not_idle_thread (obj_ref_of a) s)"
      in hoare_strengthen_postE_R)
     apply (rule hoare_pre)
      apply (wp get_cap_wp)
      apply (rule_tac Q' = "\<lambda>a s. invs s \<and> valid_etcbs s \<and> cte_wp_at ((=) (cap.UntypedCap dev ptr sz idx)) slot' s"
      in hoare_strengthen_postE_R)
       apply wp
      apply (clarsimp simp: cte_wp_at_caps_of_state)
      apply (frule_tac p = "(x,y)" for x y in caps_of_state_valid[rotated])
       apply simp
      apply (clarsimp simp:valid_cap_def obj_at_def valid_idle_def pred_tcb_at_def
        is_cap_simps not_idle_thread_def is_cap_table_def dest!:invs_valid_idle)
     apply (clarsimp simp:valid_cap_def obj_at_def valid_idle_def pred_tcb_at_def
       is_cap_simps not_idle_thread_def is_cap_table_def dest!:invs_valid_idle)
    apply (clarsimp simp:invs_mdb cte_wp_at_caps_of_state valid_cap_aligned)
    apply (frule(1) caps_of_state_valid)
    apply (rule ccontr)
    apply (clarsimp simp:valid_cap_simps cap_aligned_def)
   apply (rule hoare_pre,wp,simp)
  apply (wp hoare_drop_imp mapME_x_inv_wp2 | simp add:if_apply_def2 split del:if_split)+
  done

lemma decode_untyped_label_not_match:
  "\<lbrakk>Some intent = transform_intent (invocation_type label) args; \<forall>ui. intent \<noteq> UntypedIntent ui\<rbrakk>
    \<Longrightarrow> \<lbrace>(=) s\<rbrace> Decode_A.decode_untyped_invocation label args ref (cap.UntypedCap dev a b idx) e
             \<lbrace>\<lambda>r. \<bottom>\<rbrace>, \<lbrace>\<lambda>e. (=) s\<rbrace>"
  apply (case_tac "invocation_type label = GenInvocationLabel UntypedRetype")
   apply (clarsimp simp:Decode_A.decode_untyped_invocation_def transform_intent_def)+
   apply (clarsimp simp:transform_intent_untyped_retype_def split:option.splits list.splits)
  apply (simp add:Decode_A.decode_untyped_invocation_def unlessE_def gen_invocation_type_eq)
  apply wp
  done

end

end
