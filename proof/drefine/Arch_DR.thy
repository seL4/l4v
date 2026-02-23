(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Arch_DR
imports Untyped_DR
begin

context begin interpretation Arch . (*FIXME: arch-split*)

definition
 "make_arch_duplicate cap \<equiv> case cap of
    cdl_cap.PageTableCap oid _ mp \<Rightarrow> cdl_cap.PageTableCap oid Fake None
  | cdl_cap.FrameCap dev oid rghts sz _ mp \<Rightarrow> cdl_cap.FrameCap dev oid rghts sz Fake None"

definition
  "get_pt_mapped_addr cap \<equiv>
    case cap of (cap.ArchObjectCap (arch_cap.PageTableCap p asid)) \<Rightarrow> transform_mapping asid
    | _ \<Rightarrow> None"

definition
 "transform_page_table_inv invok \<equiv> case invok of
    ARM_A.PageTableMap cap slot pde slot' \<Rightarrow>
      if (\<exists>oref attribs. pde = ARM_A.PageTablePDE (addrFromPPtr oref) attribs 0
                \<and> is_pt_cap cap \<and> oref \<in> obj_refs cap)
      then Some (cdl_page_table_invocation.PageTableMap (transform_cap cap)
                      (make_arch_duplicate (transform_cap cap))
                      (transform_cslot_ptr slot) (transform_pd_slot_ref slot'))
      else None
  | ARM_A.PageTableUnmap cap slot \<Rightarrow>
         Some (cdl_page_table_invocation.PageTableUnmap (get_pt_mapped_addr cap)
                 (obj_ref_of cap) (transform_cslot_ptr slot))"

definition flush_type_map :: "ARM_A.flush_type \<Rightarrow> flush"
 where "flush_type_map f \<equiv> case f of
          ARM_A.Unify \<Rightarrow> flush.Unify
        | ARM_A.Clean \<Rightarrow> flush.Clean
        | ARM_A.Invalidate \<Rightarrow> flush.Invalidate
        | ARM_A.CleanInvalidate \<Rightarrow> flush.CleanInvalidate"

definition transform_page_dir_inv :: "ARM_A.page_directory_invocation \<Rightarrow> cdl_page_directory_invocation option"
where "transform_page_dir_inv invok \<equiv> case invok of
     ARM_A.page_directory_invocation.PageDirectoryFlush flush _ _ _ _ _ \<Rightarrow>
                       Some (cdl_page_directory_invocation.PageDirectoryFlush (flush_type_map flush))
    |ARM_A.page_directory_invocation.PageDirectoryNothing  \<Rightarrow>
                       Some (cdl_page_directory_invocation.PageDirectoryNothing) "


definition transform_page_inv :: "ARM_A.page_invocation \<Rightarrow> cdl_page_invocation option"
where "transform_page_inv invok \<equiv> case invok of
  ARM_A.page_invocation.PageMap asid cap ct_slot entries \<Rightarrow>
   Some (cdl_page_invocation.PageMap (transform_cap cap)
        (case_sum (transform_pte \<circ> fst) (transform_pde \<circ> fst) entries)
        (transform_cslot_ptr ct_slot)
        (case_sum (\<lambda>pair. [ (transform_pt_slot_ref \<circ> hd \<circ> snd) pair])
          (\<lambda>pair. [(transform_pd_slot_ref \<circ> hd \<circ> snd) pair]) entries))
| ARM_A.page_invocation.PageUnmap (arch_cap.PageCap _ a _ sz asid) ref \<Rightarrow>
    Some (cdl_page_invocation.PageUnmap (transform_mapping asid) a (transform_cslot_ptr ref) (pageBitsForSize sz))
| ARM_A.page_invocation.PageFlush flush _ _ _ _ _ \<Rightarrow>
    Some (cdl_page_invocation.PageFlushCaches (flush_type_map flush))
| ARM_A.page_invocation.PageGetAddr base \<Rightarrow> Some (cdl_page_invocation.PageGetAddress)
| _ \<Rightarrow> None"

definition transform_sgi_inv :: "sgi_signal_invocation \<Rightarrow> cdl_sgi_signal_invocation" where
  "transform_sgi_inv iv \<equiv> cdl_sgi_signal_invocation.SGISignalGenerate"

definition translate_arch_invocation :: "arch_invocation \<Rightarrow> cdl_invocation option"
where "translate_arch_invocation invo \<equiv> case invo of
    arch_invocation.InvokePageTable oper \<Rightarrow> option_map cdl_invocation.InvokePageTable (transform_page_table_inv oper)
  | arch_invocation.InvokePage oper \<Rightarrow> option_map cdl_invocation.InvokePage (transform_page_inv oper)
  | arch_invocation.InvokePageDirectory oper \<Rightarrow> option_map cdl_invocation.InvokePageDirectory (transform_page_dir_inv oper)
  | arch_invocation.InvokeSGISignal oper \<Rightarrow> Some (cdl_invocation.InvokeSGISignal (transform_sgi_inv oper))
  | arch_invocation.InvokeASIDControl oper \<Rightarrow>
      Some (case oper of ARM_A.MakePool frame slot parent base
        \<Rightarrow> cdl_invocation.InvokeAsidControl
               (cdl_asid_control_invocation.MakePool
                             (cdl_cap.UntypedCap False {frame..frame + 2 ^ pageBits - 1} {})
                             (transform_cslot_ptr parent)
                             {frame..frame + 2 ^ pageBits - 1}
                             (transform_cslot_ptr slot)
                             (fst $ transform_asid base)))
  | arch_invocation.InvokeASIDPool oper \<Rightarrow>
      Some (case oper of ARM_A.Assign asid pool_ptr ct_slot
        \<Rightarrow> cdl_invocation.InvokeAsidPool
               (cdl_asid_pool_invocation.Assign
                             (transform_asid asid)
                             (transform_cslot_ptr ct_slot)
                             (pool_ptr, snd (transform_asid asid))))"

definition arch_invocation_relation :: "cdl_invocation \<Rightarrow> arch_invocation \<Rightarrow> bool"
where "arch_invocation_relation cdl_invok arch_invok \<equiv>
  translate_arch_invocation arch_invok = Some cdl_invok"

lemma corres_symb_exec_in_gets:
  "corres_underlying sr nf nf' r P P' f (gets g >>= j)
    = (\<forall>v. corres_underlying sr nf nf' r P (P' and (\<lambda>s. g s = v)) f (j v))"
  "corres_underlying sr nf nf' r P P' (gets g' >>= j') f'
    = (\<forall>v. corres_underlying sr nf nf' r (P and (\<lambda>s. g' s = v)) P' (j' v) f')"
  by (auto simp add: corres_underlying_def exec_gets split_def)

lemma select_ignored:
  "select S >>= (\<lambda>_. f) = (if S = {} then select {} else f)"
  apply (intro ext)
  apply (simp add: select_def bind_def cart_singleton_image
                   image_image image_constant_conv)
  done

lemma liftM_select:
  "liftM f (select S) = select (f ` S)"
  apply (rule ext)
  apply (auto simp add: select_def bind_def liftM_def return_def split_def
                        cart_singleton_image image_image)
  done

lemma gets_bind_alternative:
  "((gets f >>= g) \<sqinter> h) = gets f >>= (\<lambda>x. g x \<sqinter> h)"
  by (rule ext, simp add: alternative_def exec_gets)

lemma corres_from_rdonly:
  assumes rdonly: "\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. P\<rbrace>" "\<And>P. \<lbrace>P\<rbrace> g \<lbrace>\<lambda>rv. P\<rbrace>"
  assumes rv: "\<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> sr \<rbrakk>
                     \<Longrightarrow> \<lbrace>(=) s'\<rbrace> g \<lbrace>\<lambda>rv s''. \<exists>rv' s'''. (rv', s''') \<in> fst (f s) \<and> r rv' rv\<rbrace>"
  assumes nfl: "fl' \<Longrightarrow> no_fail P' g"
  shows "corres_underlying sr fl fl' r P P' f g"
  apply (clarsimp simp: corres_underlying_def no_failD[OF nfl])
  apply (frule in_inv_by_hoareD[OF rdonly(2)], simp)
  apply (frule(3) use_valid[OF _ rv], simp)
  apply clarsimp
  apply (frule in_inv_by_hoareD[OF rdonly(1)], simp)
  apply fastforce
  done

lemma get_pde_sp:
  "\<lbrace>P\<rbrace> get_pde p \<lbrace>\<lambda>pde s. \<exists>pd. ko_at (ArchObj (arch_kernel_obj.PageDirectory pd)) (p && ~~ mask pd_bits) s
                                   \<and> pde = (pd (ucast (p && mask pd_bits >> 2))) \<and> P s\<rbrace>"
  apply (wp get_pde_wp)
  apply auto
  done

lemmas less_kernel_base_mapping_slots = less_kernel_base_mapping_slots_both[where x=0, simplified]

lemma dcorres_lookup_pt_slot:
  "dcorres (dc \<oplus> (\<lambda>r r'. r = transform_pt_slot_ref r')) \<top>
  ( valid_vspace_objs
  and (\<exists>\<rhd> (lookup_pd_slot pd vptr && ~~ mask pd_bits))
  and valid_idle and pspace_aligned
  and K (is_aligned pd 14 \<and> ucast (lookup_pd_slot pd vptr && mask pd_bits >> 2) \<notin> kernel_mapping_slots))
  (cdl_lookup_pt_slot pd vptr) (lookup_pt_slot pd vptr)"
  apply (rule dcorres_expand_pfx)
  apply (clarsimp simp:cdl_lookup_pt_slot_def
    lookup_pt_slot_def liftE_bindE dcorres_lookup_pd_slot)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF dcorres_get_pde])
      apply (rule_tac F = "case rv' of ARM_A.pde.PageTablePDE ptab x xa \<Rightarrow>
        is_aligned (ptrFromPAddr ptab) 10 | _ \<Rightarrow> True"
        in corres_gen_asm2)
      apply (case_tac rv')
         prefer 2
         apply (clarsimp simp:transform_pde_def)
         apply (rename_tac pt rights w)
         apply (rule dcorres_returnOk)
         apply (clarsimp simp:transform_pt_slot_ref_def
         vaddr_segment_nonsense3 vaddr_segment_nonsense4)
         apply (subst shiftl_shiftr_id)
           apply simp
          apply (rule le_less_trans)
           apply (rule word_and_le1)
          apply simp
         apply simp
     apply (simp add: transform_pde_def)+
    apply (rule hoare_strengthen_post[where Q'="\<lambda>r. valid_pde r and pspace_aligned"] )
     apply (wp get_pde_valid)
    apply (clarsimp simp:valid_pde_def dest!:pt_aligned
      split:ARM_A.pde.splits)
   apply simp
  apply auto
  done

lemma lookup_pt_slot_aligned_6':
  "\<lbrace> valid_vspace_objs
  and (\<exists>\<rhd> (lookup_pd_slot pd vptr && ~~ mask pd_bits))
  and valid_idle and pspace_aligned
  and K (is_aligned pd 14 \<and> is_aligned vptr 16 \<and> ucast (lookup_pd_slot pd vptr && mask pd_bits >> 2) \<notin> kernel_mapping_slots)\<rbrace>
  lookup_pt_slot pd vptr \<lbrace>\<lambda>rv s. is_aligned rv 6\<rbrace>, -"
  apply (rule hoare_gen_asmE)
  apply (simp add:lookup_pt_slot_def)
  apply (wp|wpc)+
   apply clarsimp
   apply (rule hoare_strengthen_post[where Q'="\<lambda>r. valid_pde r and pspace_aligned"] )
    apply wp
   apply simp+
   apply (clarsimp simp:valid_pde_def dest!:pt_aligned split:ARM_A.pde.splits)
   apply (erule aligned_add_aligned)
    apply (rule is_aligned_shiftl)
    apply (rule is_aligned_andI1)
    apply (rule is_aligned_shiftr)
    apply simp+
  done

lemma create_mapping_entries_dcorres:
  assumes pdid: "pdid = pd_ptr"
      and pd_aligned: "is_aligned pd_ptr pd_bits"
      and vp_aligned: "vmsz_aligned vptr pgsz"
      and kb: "vptr < kernel_base"
  shows
  "dcorres (dc \<oplus> (\<lambda>rv rv'. rv = case_sum (\<lambda>pair. [ (transform_pt_slot_ref \<circ> hd \<circ> snd) pair])
                                 (\<lambda>pair. [(transform_pd_slot_ref \<circ> hd \<circ> snd) pair]) rv'
                     \<and> case_sum (transform_pte \<circ> fst) (transform_pde \<circ> fst) rv'
                           = FrameCap False (ptrFromPAddr base)
                               vm_rights (pageBitsForSize pgsz) Fake None))
     \<top>
     (page_directory_at pd_ptr and valid_idle and valid_vspace_objs and pspace_aligned
             and (\<exists>\<rhd> (lookup_pd_slot pd_ptr vptr && ~~ mask pd_bits)))
     (cdl_page_mapping_entries vptr (pageBitsForSize pgsz) pd_ptr)
     (create_mapping_entries base vptr pgsz vm_rights attrib pd_ptr)"
proof -

  have aligned_4_hd:
    "\<And>r :: word32. is_aligned r 6 \<Longrightarrow> hd (map (\<lambda>x. x + r) [0 , 4 .e. 0x3C]) = r"
    apply (subgoal_tac "r \<le> r + 0x3C")
     apply (clarsimp simp: upto_enum_step_def o_def | intro conjI)+
     apply (subst hd_map)
      apply (clarsimp simp:upto_enum_def)
     apply (clarsimp simp:upto_enum_def hd_map)
    apply (rule is_aligned_no_wrap')
     apply simp
    apply simp
    done


  show ?thesis using pdid vp_aligned
    apply hypsubst_thin
    proof (induct pgsz)
      case ARMSmallPage
      show ?case using ARMSmallPage.prems
        apply (simp add: liftME_def[symmetric] o_def transform_pte_def
                                     lookup_error_injection dc_def[symmetric])
        apply (rule dcorres_injection_handler_rhs)
        apply (simp add:liftE_bindE cdl_page_mapping_entries_def)
        apply (rule corres_dummy_returnOk_r)
        apply (rule corres_guard_imp)
          apply (rule corres_splitEE)
             apply (rule dcorres_lookup_pt_slot)
            apply (rule dcorres_returnOk; simp)
           apply wp+
         apply simp
        apply (clarsimp simp:
          dest!:page_directory_at_aligned_pd_bits )
        apply (frule less_kernel_base_mapping_slots_both[OF kb,where x = 0])
         apply simp
        apply (simp add:pageBits_def pd_bits_def)
      done
    next
      case ARMLargePage
      show ?case using ARMLargePage.prems
        apply (simp add: liftME_def[symmetric] o_def transform_pte_def pd_bits_def pageBits_def
                                     lookup_error_injection dc_def[symmetric])
        apply (rule dcorres_injection_handler_rhs)
        apply (simp add:liftE_bindE cdl_page_mapping_entries_def largePagePTE_offsets_def)
        apply (rule corres_dummy_returnOk_r)
        apply (rule corres_guard_imp)
          apply (rule corres_splitEE)
             apply (rule dcorres_lookup_pt_slot)
            apply (rule_tac F = "is_aligned rv' 6" in corres_gen_asm2)
            apply (rule dcorres_returnOk)
            apply (subst aligned_4_hd)
             apply clarsimp
            apply (clarsimp)
           apply (wpsimp wp: lookup_pt_slot_aligned_6')+
        apply (clarsimp dest!:page_directory_at_aligned_pd_bits)
        apply (frule less_kernel_base_mapping_slots_both[OF kb,where x = 0])
         apply simp
        apply (clarsimp simp:pageBits_def pd_bits_def vmsz_aligned_def)
        apply (rule_tac x=ref in exI, simp)
      done
    next
      case ARMSection
      show ?case using ARMSection.prems
        apply (simp add: liftME_def[symmetric] o_def transform_pte_def
                                     lookup_error_injection dc_def[symmetric])
        apply (simp add:liftE_bindE cdl_page_mapping_entries_def)
        apply (rule corres_guard_imp)
          apply (rule_tac F = "is_aligned pd_ptr 14" in corres_gen_asm2)
          apply (rule dcorres_returnOk)
          apply (clarsimp simp:transform_pde_def vmsz_aligned_def)
          apply (simp add: dcorres_lookup_pd_slot)
         apply simp
        apply (clarsimp simp: pd_bits_def pageBits_def
          dest!:page_directory_at_aligned_pd_bits )
      done
    next
      case ARMSuperSection
      show ?case using ARMSuperSection.prems
        using pd_aligned
        apply (simp add: liftME_def[symmetric] o_def transform_pte_def
                                     lookup_error_injection dc_def[symmetric])
        apply (simp add:liftE_bindE cdl_page_mapping_entries_def superSectionPDE_offsets_def)
        apply (rule corres_guard_imp)
          apply (rule_tac F = "is_aligned pd_ptr 14" in corres_gen_asm2)
          apply (rule dcorres_returnOk)
          apply (clarsimp simp:transform_pde_def vmsz_aligned_def)
          apply (subst aligned_4_hd)
           apply (rule lookup_pd_slot_aligned_6)
            apply (simp add:vmsz_aligned_def)+
          apply (simp add: dcorres_lookup_pd_slot)
         apply simp
        apply (clarsimp simp: pd_bits_def pageBits_def
          dest!:page_directory_at_aligned_pd_bits )
        done
    qed
  qed

lemma create_mapping_entries_dcorres_select:
  assumes pdid: "pdid = pd_ptr"
      and pd_aligned: "is_aligned pd_ptr pd_bits"
      and vp_aligned: "vmsz_aligned vptr pgsz"
      and kb: "vptr < kernel_base"
  shows
  "dcorres (dc \<oplus> (\<lambda>rv rv'. rv = case_sum (\<lambda>pair. [ (transform_pt_slot_ref \<circ> hd \<circ> snd) pair])
                                 (\<lambda>pair. [(transform_pd_slot_ref \<circ> hd \<circ> snd) pair]) rv'
                     \<and> case_sum (transform_pte \<circ> fst) (transform_pde \<circ> fst) rv'
                           = FrameCap False (ptrFromPAddr base)
                               vm_rights (pageBitsForSize pgsz) Fake None))
     (\<lambda>s. frslots = all_pd_pt_slots pd pdid s
              \<and> cdl_objects s pdid = Some pd)
     (page_directory_at pd_ptr and valid_idle and valid_vspace_objs and pspace_aligned
             and (\<exists>\<rhd> (lookup_pd_slot pd_ptr vptr && ~~ mask pd_bits)))
     (liftE (select {M. set M \<subseteq> frslots \<and> distinct M}) \<sqinter> Monads_D.throw)
     (create_mapping_entries base vptr pgsz vm_rights attrib pd_ptr)"
proof -
  have lookup_pd_slot_offs_times_4_mask_2[simp]:
    "\<And>x. lookup_pd_slot pd_ptr vptr + of_nat x * 4 && mask 2 = 0"
    apply (subst is_aligned_mask[symmetric])
    apply (rule aligned_add_aligned[where n=2], simp_all add: word_bits_conv)
     apply (simp add: lookup_pd_slot_def)
     apply (rule aligned_add_aligned[OF pd_aligned],
            simp_all add: pd_bits_def pageBits_def word_bits_conv)
     apply (simp_all add: is_aligned_shiftl word_shift_by_2)
    done
  have inj_on_pd:
    "inj_on (\<lambda>x. transform_pd_slot_ref (lookup_pd_slot pd_ptr vptr + toEnum x * 4)) {0 ..< 16}"
    apply (rule inj_onI, clarsimp simp: transform_pd_slot_ref_def)
    apply (drule bits_low_high_eq[rotated])
     apply (simp add: mask_twice pd_bits_def pageBits_def)
    apply (drule(1) mask_eqI[rotated])
    apply (simp add: word_shift_by_2)
    apply (rule ccontr, erule(3) of_nat_shift_distinct_helper)
     apply (simp_all add: word_bits_conv)
    done

  have map_includedI:
   "\<And>S g xs. \<lbrakk>set (map g xs) \<subseteq> S;xs \<noteq> []\<rbrakk> \<Longrightarrow> g (hd xs) \<in> S"
    by (clarsimp simp:hd_map_simp neq_Nil_conv)

  show ?thesis using pdid vp_aligned
    apply clarsimp
    proof (induct pgsz)
      case ARMSmallPage
      show ?case using ARMSmallPage.prems
        apply (simp add: liftME_def[symmetric] o_def transform_pte_def
                                     lookup_error_injection dc_def[symmetric])
        apply (rule dcorres_injection_handler_rhs)
        apply (simp add: lookup_pt_slot_def liftE_bindE)
        apply (rule corres_symb_exec_r[OF _ get_pde_sp get_pde_inv], simp_all)[1]
        apply (clarsimp simp add: corres_alternate2 split: ARM_A.pde.split)
        apply (rule corres_alternate1)
        apply (rule corres_from_rdonly, simp_all)[1]
          apply (wp | simp)+
        apply (simp add: returnOk_def in_monad select_def, wp)
        apply (clarsimp simp: transform_pt_slot_ref_def all_pd_pt_slots_def
                              opt_object_page_directory
                              obj_at_def object_slots_def transform_page_directory_contents_def
                              unat_map_def kernel_pde_mask_def lookup_pd_slot_pd
                              pd_aligned
                       dest!: a_type_pdD
                         del: disjCI)
        apply (drule valid_vspace_objsD, simp add: obj_at_def, simp+)
        apply (cut_tac less_kernel_base_mapping_slots[OF kb pd_aligned])
        apply (drule_tac x="ucast (lookup_pd_slot pd_ptr vptr && mask pd_bits >> 2)" in bspec)
         apply simp
        apply (drule_tac t="pda v" for v in sym, simp)
        apply (clarsimp simp: obj_at_def del: disjCI)
        apply (frule_tac p="ptrFromPAddr v" for v in pspace_alignedD, simp+)
        apply (rule disjI2, rule conjI)
         apply (rule_tac x="unat (lookup_pd_slot pd_ptr vptr && mask pd_bits >> 2)"
                    in exI)
         apply (simp add: transform_pde_def ucast_nat_def)
         apply (subst is_aligned_add_helper, simp add: pt_bits_def pageBits_def)
          apply (rule shiftl_less_t2n)
           apply (rule order_le_less_trans, rule word_and_le1, simp add: pt_bits_def pageBits_def)
          apply (simp add: pt_bits_def pageBits_def)
         apply simp
         apply (simp add: kernel_mapping_slots_def)
        apply (subst is_aligned_add_helper, simp add: pt_bits_def pageBits_def)
         apply (rule shiftl_less_t2n)
          apply (rule order_le_less_trans, rule word_and_le1, simp add: pt_bits_def pageBits_def)
         apply (simp add: pt_bits_def pageBits_def)
        apply (simp add: dom_def transform_def transform_objects_def
                         restrict_map_def map_add_def)
        apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
        done
    next
      case ARMLargePage
      show ?case using ARMLargePage.prems
        apply (simp add: liftME_def[symmetric] o_def transform_pte_def largePagePTE_offsets_def
                                     lookup_error_injection dc_def[symmetric])
        apply (rule dcorres_injection_handler_rhs)
        apply (simp add: lookup_pt_slot_def liftE_bindE)
        apply (rule corres_symb_exec_r[OF _ get_pde_sp get_pde_inv], simp_all)[1]
        apply (clarsimp simp add: corres_alternate2 split: ARM_A.pde.split)
        apply (rename_tac word1 set word2)
        apply (rule corres_alternate1)
        apply (rule corres_from_rdonly, simp_all)[1]
          apply (wp | simp)+
        apply (simp add: returnOk_def in_monad select_def, wp)
        apply (clarsimp simp: pd_aligned obj_at_def lookup_pd_slot_pd
                              a_type_simps)
        apply (drule valid_vspace_objsD, simp add: obj_at_def, simp+)
        apply (cut_tac less_kernel_base_mapping_slots[OF kb pd_aligned])
        apply (drule_tac x="ucast (lookup_pd_slot pd_ptr vptr && mask pd_bits >> 2)" in bspec)
         apply simp
        apply (drule_tac t="pda v" for v in sym, simp)
        apply (clarsimp simp: obj_at_def del: disjCI)
        apply (frule_tac p="ptrFromPAddr v" for v in pspace_alignedD, simp+)
        apply (rule map_includedI)
         apply (clarsimp simp: transform_pt_slot_ref_def all_pd_pt_slots_def
                               opt_object_page_directory
                               object_slots_def transform_page_directory_contents_def
                               unat_map_def kernel_pde_mask_def
                          del: disjCI UnCI)
         apply (subgoal_tac "x + (ptrFromPAddr word1 + ((vptr >> 12) && 0xFF << 2)) && ~~ mask pt_bits = ptrFromPAddr word1")
          apply (rule disjI2, rule conjI)
           apply (rule_tac x="unat (lookup_pd_slot pd_ptr vptr && mask pd_bits >> 2)"
                      in exI)
           apply (simp add: transform_pde_def ucast_nat_def)
           apply (simp add: kernel_mapping_slots_def)
          apply (simp add: dom_def transform_def transform_objects_def
                           restrict_map_def)
          apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
         apply (clarsimp simp: upto_enum_step_def pt_bits_def pageBits_def
                        split: if_split_asm)
         apply (subst add.commute, subst add.assoc, subst is_aligned_add_helper, assumption)
          apply (simp only: word_shift_by_2 word_shiftl_add_distrib[symmetric])
          apply (rule shiftl_less_t2n)
           apply (rule is_aligned_add_less_t2n[where n=4])
              apply (rule is_aligned_andI1)
              apply (rule is_aligned_shiftr)
              apply (simp add: vmsz_aligned_def)
             apply (simp add: word_leq_minus_one_le)
            apply simp
           apply (rule order_le_less_trans, rule word_and_le1, simp)
          apply simp
         apply simp
        apply (simp add: upto_enum_step_def not_less upto_enum_def)
        done
    next
      case ARMSection
      show ?case using ARMSection.prems
        apply (simp add: liftME_def[symmetric] o_def transform_pte_def
                                     lookup_error_injection dc_def[symmetric])
        apply (rule corres_alternate1)
        apply (rule corres_from_rdonly, simp_all)[1]
          apply (wp | simp)+
        apply (simp add: returnOk_def in_monad select_def, wp)
        apply (clarsimp simp: transform_pde_def obj_at_def
                              opt_object_page_directory
                       dest!: a_type_pdD)
        apply (simp add: transform_pd_slot_ref_def lookup_pd_slot_def
                         all_pd_pt_slots_def object_slots_def
                         transform_page_directory_contents_def
                         dom_def unat_map_def)
        done

    next
      case ARMSuperSection
      show ?case using ARMSuperSection.prems
        using pd_aligned
        apply (simp add: liftME_def[symmetric] o_def transform_pte_def
                                     lookup_error_injection dc_def[symmetric])
        apply (rule corres_alternate1)
        apply (rule corres_from_rdonly, simp_all)[1]
          apply (wp | simp)+
        apply (simp add: returnOk_def in_monad select_def, wp)
        apply (clarsimp simp: transform_pde_def obj_at_def
                              opt_object_page_directory
                       dest!: a_type_pdD)
        apply (rule map_includedI)
         apply clarsimp
         apply (clarsimp simp: all_pd_pt_slots_def transform_pd_slot_ref_def
                               object_slots_def transform_page_directory_contents_def
                               dom_def unat_map_def)
        apply (simp add: not_less upto_enum_step_def upto_enum_def superSectionPDE_offsets_def)
        done
    qed
qed

schematic_goal get_master_pde_invalid_sp:
  "\<lbrace>P\<rbrace> get_master_pde p
  \<lbrace>\<lambda>pde s. pde = ARM_A.pde.InvalidPDE \<longrightarrow>
    (\<exists>pd. ko_at (ArchObj (arch_kernel_obj.PageDirectory pd)) (?p && ~~ mask pd_bits) s \<and>
     pde = pd (ucast (?p && mask pd_bits >> 2))) \<and> P s\<rbrace>"
  apply (simp add:get_master_pde_def)
  apply (wp get_pde_wp |wpc)+
   apply (clarsimp simp:obj_at_def)
  apply (auto simp add:mask_lower_twice pd_bits_def pageBits_def)
  done

lemma shiftl_mod:
  "\<lbrakk> n < 32; (x :: word32) < 2 ^ (32 - n) \<rbrakk> \<Longrightarrow> unat (x << n) mod 2 ^ n = 0"
  apply (subst shiftl_t2n)
  apply (clarsimp simp:unat_word_ariths)
  apply (subgoal_tac "2 ^ n * unat x < 2 ^ 32")
   apply (clarsimp)
  apply (subst (asm) word_unat_power)
  apply (drule unat_less_helper)
  apply (rule_tac y="2^n * 2 ^(32-n)" in less_le_trans)
   apply simp
  apply (simp add:power_add[symmetric])
  done

definition
  select_ret_or_throw :: "'a set \<Rightarrow> 'x set \<Rightarrow> ('s, ('x + 'a)) nondet_monad"
where
  "select_ret_or_throw S X = alternative (select S >>= returnOk) (select X >>= throwError)"

lemma to_select_ret_or_throw:
  "returnOk x = select_ret_or_throw {x} {}"
  "throwError e = select_ret_or_throw {} {e}"
  "alternative (select_ret_or_throw S X) (select_ret_or_throw S' X')
    = select_ret_or_throw (S \<union> S') (X \<union> X')"
  apply (simp_all add: select_ret_or_throw_def alternative_def returnOk_def return_def
                       select_def bind_def throwError_def)
  apply (simp add: Sigma_def return_def Un_ac)
  done

lemma whenE_to_select_ret_or_throw:
  "whenE P (select_ret_or_throw S X)
    = select_ret_or_throw ({x. P \<longrightarrow> x \<in> S}) ({x. P \<and> x \<in> X})"
  apply (simp add: whenE_def to_select_ret_or_throw UNIV_unit)
  apply (strengthen arg_cong2[where f=select_ret_or_throw])
  apply (simp add: set_eq_iff)
  done

lemma select_ret_or_throw_twice:
  "(do _ \<leftarrow> select_ret_or_throw S X; select_ret_or_throw S X od)
    = select_ret_or_throw S X"
  apply (simp add: select_ret_or_throw_def alternative_def returnOk_def return_def
                       select_def bind_def throwError_def Sigma_def)
  apply (rule ext, auto)
  done

lemma select_ret_or_throw_twiceE:
  "(doE _ \<leftarrow> select_ret_or_throw S X; select_ret_or_throw S X odE)
    = select_ret_or_throw S X"
  apply (simp add: select_ret_or_throw_def alternative_def returnOk_def return_def
                       select_def bind_def throwError_def Sigma_def
                       bindE_def)
  apply (rule ext, auto simp: throwError_def return_def)
  done

crunch select_ret_or_throw
  for inv[wp]: "P"

lemma corres_initial_bindE_rdonly_select_ret_or_throw:
  assumes y: "\<And>rv'. corres_underlying sr nf nf' (e \<oplus> r) P P' (select_ret_or_throw S X) (d rv')"
  assumes x: "corres_underlying sr nf nf' (e \<oplus> dc) P P' (select_ret_or_throw S X) c"
  assumes z: "\<lbrace>P'\<rbrace> c \<lbrace>\<lambda>_. P'\<rbrace>,-"
  shows      "corres_underlying sr nf nf' (e \<oplus> r) P P' (select_ret_or_throw S X) (c >>=E (\<lambda>rv'. d rv'))"
  apply (subst select_ret_or_throw_twiceE[symmetric])
  apply (rule corres_initial_splitE[OF x y])
   apply wp
  apply (wp z)
  done

lemma corres_select_ret_or_throw:
  "\<forall>v \<in> S'. \<exists>v' \<in> S. r v' v
    \<Longrightarrow> \<forall>x \<in> X'. \<exists>x' \<in> X. e x' x
    \<Longrightarrow> corres_underlying sr nf nf' (e \<oplus> r) \<top> \<top>
        (select_ret_or_throw S X) (select_ret_or_throw S' X')"
  apply (simp add: select_ret_or_throw_def)
  apply (rule corres_alternate_match)
   apply (simp add: returnOk_def liftM_def[symmetric] o_def)
   apply (rule corres_select, simp)
  apply (simp add: throwError_def liftM_def[symmetric] o_def)
  apply (rule corres_select, simp)
  done

(*
 * Decoding Arch invocations is equivalent.
 *)

lemmas isPageFlushLabel_simps =
    isPageFlushLabel_def[split_simps invocation_label.split arch_invocation_label.split]

lemma decode_invocation_archcap_corres:
  notes label_split_asm = invocation_label.split_asm gen_invocation_labels.split_asm
                          arch_invocation_label.split_asm
  shows
  "\<lbrakk> Some intent = transform_intent (invocation_type label') args';
     invoked_cap_ref = transform_cslot_ptr invoked_cap_ref';
     invoked_cap = transform_cap invoked_cap';
     excaps = transform_cap_list excaps';
     invoked_cap' = cap.ArchObjectCap x \<rbrakk> \<Longrightarrow>
    dcorres (dc \<oplus> (\<lambda>rv rv'. \<exists>ai. rv' = Invocations_A.InvokeArchObject ai
                       \<and> arch_invocation_relation rv ai))
         \<top> (invs and valid_cap invoked_cap'
                 and (\<lambda>s. \<forall>x \<in> set (map fst excaps'). s \<turnstile> x)
                 and (\<lambda>s. \<forall>x \<in> set excaps'. cte_wp_at ((=) (fst x)) (snd x) s))
        (Decode_D.decode_invocation invoked_cap invoked_cap_ref excaps intent)
        (Decode_A.decode_invocation label' args' cap_index' invoked_cap_ref' invoked_cap' excaps')"
  apply (rule_tac F="\<forall>x \<in> set (map fst excaps'). cap_aligned x" in corres_req)
   apply (fastforce simp add: valid_cap_aligned)
  apply clarsimp
proof (induct x)
  case (ASIDPoolCap ap_ptr asid)
  thus ?case
    apply (simp add: Decode_D.decode_invocation_def
                     decode_invocation_def arch_decode_invocation_def
               split del: if_split)
    apply (clarsimp simp: get_asid_pool_intent_def transform_intent_def
                          map_option_Some_eq2 throw_opt_def
                          decode_asid_pool_invocation_def
               split del: if_split split: label_split_asm list.split_asm)
    apply (simp add: split_beta corres_alternate2
                     liftE_bindE corres_symb_exec_in_gets
                     corres_whenE_throwError_split_rhs
                     split: cap.split arch_cap.split option.split)
    apply (clarsimp simp: get_index_def transform_cap_list_def
                          throw_on_none_def split_beta bindE_assoc
                          dc_def[symmetric])
    apply (rule corres_guard_imp)
      apply (rule corres_symb_exec_r)
         apply (clarsimp simp: corres_whenE_throwError_split_rhs
                               corres_alternate2)
         apply (rule corres_alternate1)
         apply (simp add: select_ext_def bind_assoc)
         apply (rule dcorres_symb_exec_r)
           apply (rule corres_assert_rhs)
           apply (rule_tac x="unat (free_asid_pool_select pool asid)" in select_pick_corres_asm)
            apply (rule CollectI)
            apply (elim conjE)
            apply (rule le_p2_minus_1)
            apply (rule unat_le_helper)
            apply (simp add: p2_low_bits_max)
           apply (rule corres_returnOk[where P=\<top> and P'="\<lambda>rv. is_aligned asid asid_low_bits"])
           apply (clarsimp simp:arch_invocation_relation_def translate_arch_invocation_def
                                transform_asid_def asid_high_bits_of_def shiftr_irrelevant
                                up_ucast_inj_eq)
           apply (erule impE)
            apply (rule arg_cong[where f=ucast])
            apply (subst shiftr_irrelevant)
              apply (rule word_leq_minus_one_le)
               apply (simp add: asid_low_bits_def)
              apply (subst ucast_le_migrate)
                apply (simp add: asid_low_bits_def word_size)
               apply (simp add: word_size)
              apply (subst ucast_down_minus)
               apply (simp add: is_down_def target_size_def source_size_def word_size)
              apply (simp add: asid_low_bits_def)
             apply simp
            apply simp
           apply (simp add: ucast_ucast_add)
           apply (erule_tac P="ucast asid = 0" in notE)
           apply (rule ucast_up_inj[where 'b=32])
            apply (simp add: ucast_ucast_mask is_aligned_mask asid_low_bits_def)
           apply simp
          apply (wp | simp add:valid_cap_def split del: if_split)+
    done
next
  case ASIDControlCap
  thus ?case
    apply (simp add: Decode_D.decode_invocation_def
                     decode_invocation_def arch_decode_invocation_def
                     bindE_assoc
               split del: if_split)
    apply (clarsimp simp: get_asid_control_intent_def transform_intent_def
                          map_option_Some_eq2 throw_opt_def
                          decode_asid_control_invocation_def
                          transform_cnode_index_and_depth_def
               split del: if_split split: label_split_asm list.split_asm)
    apply (simp add: split_beta corres_alternate2
                     liftE_bindE corres_symb_exec_in_gets
                     corres_whenE_throwError_split_rhs
                     transform_cnode_index_and_depth_def
                     select_ignored
              split: cap.split arch_cap.split option.split)
    apply (clarsimp simp: get_index_def transform_cap_list_def
                          throw_on_none_def split_beta bindE_assoc
                          dc_def[symmetric])
    apply (intro conjI impI allI)
               apply (rule corres_symb_exec_r[OF dcorres_alternative_throw],
                      (wp | simp)+)
              defer
              apply ((rule corres_symb_exec_r[OF dcorres_alternative_throw],
                     (wp | simp)+)+)[11]
    apply (rename_tac dev ptr sz v)
    apply (case_tac dev)
     apply simp
     apply (rule corres_alternate2)
     apply (rule corres_guard_imp)
       apply (rule corres_symb_exec_r)
          apply (rule dcorres_throw)
         apply ((wp|simp)+)[5]
    apply clarsimp
    apply (rule conjI[rotated])
     apply clarsimp
     apply (rule corres_alternate2)
     apply (rule corres_guard_imp)
       apply (rule corres_symb_exec_r)
          apply (rule dcorres_throw)
         apply ((wp|simp)+)[5]
    apply clarsimp
    apply (rule corres_guard_imp)
      apply (rule corres_alternate1)
      apply (clarsimp simp: select_ext_def bind_assoc)
      apply (rule dcorres_symb_exec_r)
        apply (rule corres_assert_rhs)
        apply (rule_tac x="unat (free_asid_select v)" in select_pick_corres_asm)
         apply (rule CollectI)
         apply (elim conjE)
         apply (rule le_p2_minus_1)
         apply (rule unat_le_helper)
         apply simp
        apply (simp add:bindE_assoc)
        apply (rule corres_splitEE[OF dcorres_ensure_no_children[where P="(\<noteq>) cap.NullCap"]])
          apply (rule corres_splitEE)
             apply (rule lookup_slot_for_cnode_op_corres; simp)
            apply (simp, elim conjE)
            apply (rule corres_splitEE[OF dcorres_ensure_empty])
              apply (rule corres_returnOk[where P=\<top> and P'=\<top>])
              apply (simp add:transform_def arch_invocation_relation_def
                              translate_arch_invocation_def)
              apply (simp add:transform_asid_def unat_ucast asid_high_bits_def asid_low_bits_def
                              unat_lt2p[where 'a=8, simplified])
              apply (thin_tac "free_asid_select v \<notin> dom v")
              apply clarsimp
              apply (subgoal_tac "unat ((ucast (free_asid_select v) :: word32) << 10) mod 1024=0")
               apply (simp add: asid_high_bits_of_shift[simplified asid_low_bits_def[simplified]])
              apply (rule shiftl_mod[where n=10, simplified])
              apply (cut_tac x="free_asid_select v" and 'a=32 in ucast_less)
               apply simp
              apply (rule less_trans)
               apply simp
              apply simp
             apply (wp lsfco_not_idle select_inv | simp)+
    apply (simp add: cte_wp_at_caps_of_state neq_Nil_conv invs_mdb_cte mdb_cte_at_rewrite)
    apply auto
    done
next
  case (PageCap dev base rights pgsz asid)
  thus ?case
    supply option.case_cong[cong] if_cong[cong] isPageFlushLabel_simps[simp]
    apply (simp add: Decode_D.decode_invocation_def
                     decode_invocation_def arch_decode_invocation_def
               split del: if_split)
    apply (clarsimp simp: get_page_intent_def transform_intent_def
                          map_option_Some_eq2 throw_opt_def
                          decode_page_invocation_def
                          transform_intent_page_map_def
               split del: if_split split: label_split_asm list.split_asm,
            simp_all add: split_beta corres_alternate2
                          liftE_bindE corres_symb_exec_in_gets
                          corres_whenE_throwError_split_rhs
                          transform_cnode_index_and_depth_def
                          select_ignored throw_on_none_def
                          get_index_def transform_cap_list_def
                          dc_def[symmetric]
                   split: cap.split arch_cap.split option.split)
          (* 7 subgoals *)
          (* PageMap *)
          apply (clarsimp simp: transform_mapping_def)
          apply (clarsimp simp: neq_Nil_conv valid_cap_simps obj_at_def opt_object_page_directory
                                invs_valid_idle label_to_flush_type_def isPageFlushLabel_def
                         dest!: a_type_pdD)
          apply (intro conjI; clarsimp)
              (* Unmapped *)
           apply (rule_tac
                    r'=dc and P'="I" and Q'="\<lambda>rv. I and (\<exists>\<rhd> (lookup_pd_slot rv x21 && ~~ mask pd_bits))"
                    for I
                    in corres_alternative_throw_splitE[OF _ _ returnOk_wp[where x="()"], simplified])
               apply (rule corres_from_rdonly, simp_all)[1]
                 apply (wp+ | simp)+
               apply (rule hoare_strengthen_post, rule hoare_TrueI)
               apply (rename_tac rv s)
               apply (case_tac rv, auto simp add: in_monad)[1]
              apply (simp add: corres_whenE_throwError_split_rhs corres_alternate2
                               check_vp_alignment_def unlessE_whenE)
              apply (clarsimp simp add: liftE_bindE[symmetric])
              apply (rule corres_alternative_throw_splitE)
                   apply (rule corres_alternate1)
                   apply (rule corres_guard_imp,
                          rule create_mapping_entries_dcorres[OF refl])
                       apply (clarsimp simp: neq_Nil_conv cap_aligned_def
                                             pd_bits_def pageBits_def)
                      apply (simp add: vmsz_aligned_def)
                     apply (simp only: linorder_not_le, erule order_le_less_trans[rotated])
                     apply simp
                    apply simp
                   apply (fastforce simp: neq_Nil_conv valid_cap_simps dest!: page_directory_at_rev)
                  apply (rule corres_from_rdonly[where P=\<top> and P'=\<top>], simp_all)[1]
                    apply (wp+ | simp)+
                  apply (rule validE_cases_valid, rule hoare_pre)
                   apply (wp+ | simp)+
                  apply (clarsimp simp add: in_monad conj_disj_distribR[symmetric])
                  apply (simp add: conj_disj_distribR cong: conj_cong)
                  apply (simp add: arch_invocation_relation_def translate_arch_invocation_def
                                   transform_page_inv_def update_cap_rights_def
                                   update_mapping_cap_status_def Types_D.cap_rights_def
                                   mask_vm_rights_def transform_mapping_def)
                 apply wp+
              apply simp
             apply (rule hoare_pre, wp, auto)[1]
            apply ((wpsimp simp: whenE_def split_del: if_split)+)[2]
             (* Mapped *)
          apply (clarsimp simp: bindE_assoc)
          apply (clarsimp simp: corres_whenE_throwError_split_rhs corres_alternate2)
          apply (rule_tac
                   r'=dc and P'="I" and Q'="\<lambda>rv. I and (\<exists>\<rhd> (lookup_pd_slot rv x21 && ~~ mask pd_bits))"
                   for I
                   in corres_alternative_throw_splitE[OF _ _ returnOk_wp[where x="()"], simplified])
              apply (rule corres_from_rdonly, simp_all)[1]
                apply (wp+ | simp)+
              apply (rule hoare_strengthen_post, rule hoare_TrueI)
              apply (rename_tac rv s)
              apply (case_tac rv, auto simp add: in_monad)[1]
             apply (simp add: corres_whenE_throwError_split_rhs corres_alternate2
                              check_vp_alignment_def unlessE_whenE)
             apply (clarsimp simp add: liftE_bindE[symmetric])
             apply (rule corres_alternative_throw_splitE)
                  apply (rule corres_alternate1)
                  apply (rule corres_guard_imp[where P=P and Q=P and Q'="P' and _" and P'=P' for P P'])
                    apply (rule_tac F="x21 < kernel_base" in corres_gen_asm2)
                    apply (rule corres_guard_imp,
                           rule create_mapping_entries_dcorres[OF refl])
                        apply (clarsimp simp: neq_Nil_conv cap_aligned_def
                                              pd_bits_def pageBits_def)
                       apply (simp add: vmsz_aligned_def)
                      apply simp
                     apply simp
                    apply simp
                    apply (fastforce simp: neq_Nil_conv valid_cap_simps dest!:page_directory_at_rev)
                   apply presburger
                  apply blast
                 apply (rule corres_from_rdonly[where P=\<top> and P'=\<top>], simp_all)[1]
                   apply (wp+ | simp)+
                 apply (rule validE_cases_valid, rule hoare_pre)
                  apply (wp+ | simp)+
                 apply (clarsimp simp add: in_monad conj_disj_distribR[symmetric])
                 apply (simp add: conj_disj_distribR cong: conj_cong)
                 apply (simp add: arch_invocation_relation_def translate_arch_invocation_def
                                  transform_page_inv_def update_cap_rights_def
                                  update_mapping_cap_status_def Types_D.cap_rights_def
                                  mask_vm_rights_def transform_mapping_def)
                apply wp+
             apply (simp)
            apply (rule hoare_pre, wp, auto)[1]
           apply (wp | simp add: whenE_def split del: if_split)+
         (* PageUnmap *)
         apply (rule corres_alternate1)
         apply (simp add: returnOk_def arch_invocation_relation_def
                          translate_arch_invocation_def transform_page_inv_def)
        (* PageClean *)
        apply (clarsimp)
        apply (rule corres_from_rdonly)
           apply (wp, clarsimp)
          apply (simp only: Let_unfold, (wp whenE_inv)+, clarsimp)
         apply (rule validE_cases_valid, rule hoare_pre)
          apply (wpsimp simp: Let_unfold arch_invocation_relation_def
                              translate_arch_invocation_def transform_page_inv_def)+
         apply (clarsimp simp: in_monad conj_disj_distribR[symmetric])
         apply safe
         apply blast
        apply (metis flush.exhaust)
       (* PageInvalidate *)
       apply (rule corres_from_rdonly)
          apply (wp, clarsimp)
         apply (simp only: Let_unfold, (wp whenE_inv)+, clarsimp)
        apply (rule validE_cases_valid, rule hoare_pre)
         apply (wpsimp simp: Let_unfold arch_invocation_relation_def
                             translate_arch_invocation_def transform_page_inv_def)+
        apply (clarsimp simp: in_monad conj_disj_distribR[symmetric])
        apply safe
        apply blast
       apply (metis flush.exhaust)
      (* PageCleanInvalidate *)
      apply (rule corres_from_rdonly)
         apply (wp, clarsimp)
        apply (simp only: Let_unfold, (wp whenE_inv)+, clarsimp)
       apply (rule validE_cases_valid, rule hoare_pre)
        apply (wpsimp simp: Let_unfold arch_invocation_relation_def
                            translate_arch_invocation_def transform_page_inv_def)+
       apply (clarsimp simp: in_monad conj_disj_distribR[symmetric])
       apply safe
       apply blast
      apply (metis flush.exhaust)
     (* PageUnify *)
     apply (rule corres_from_rdonly)
        apply (wp, clarsimp)
       apply (simp only: Let_unfold, (wp whenE_inv)+, clarsimp)
      apply (rule validE_cases_valid, rule hoare_pre)
       apply (wpsimp simp: Let_unfold arch_invocation_relation_def
                           translate_arch_invocation_def transform_page_inv_def)+
      apply (clarsimp simp: in_monad conj_disj_distribR[symmetric])
      apply safe
      apply blast
     apply (metis flush.exhaust)
    (* PageGetAddress *)
    apply (rule corres_returnOk,clarsimp simp:arch_invocation_relation_def
                translate_arch_invocation_def transform_page_inv_def |
           clarsimp simp: isPageFlushLabel_def)+
    done
next
  case (PageTableCap ptr asid)
  thus ?case
    supply if_cong[cong]
    apply (simp add: Decode_D.decode_invocation_def
                     decode_invocation_def arch_decode_invocation_def
               split del: if_split)
    apply (clarsimp simp: get_page_table_intent_def transform_intent_def
                          map_option_Some_eq2 throw_opt_def cdl_get_pt_mapped_addr_def
                          decode_page_table_invocation_def
                          transform_intent_page_table_map_def
               split del: if_split
               split: label_split_asm list.split_asm)
     apply (simp add: throw_on_none_def transform_cap_list_def
       get_index_def split_beta alternative_refl
       transform_mapping_def corres_whenE_throwError_split_rhs corres_alternate2
       split: cap.split arch_cap.split option.split cdl_frame_cap_type.splits)
     apply (clarsimp simp: dc_def[symmetric] liftE_bindE
       gets_the_def bind_assoc transform_mapping_def
       corres_symb_exec_in_gets gets_bind_alternative)
      apply (rule_tac r'=dc and P'="I" and Q'="\<lambda>rv. I and (\<exists>\<rhd> (lookup_pd_slot rv ab && ~~ mask pd_bits))"
               for I in corres_alternative_throw_splitE[OF _ _ returnOk_wp[where x="()"], simplified])
         apply (rule corres_from_rdonly, simp_all)[1]
           apply (wp | simp)+
         apply (rule hoare_strengthen_post, rule hoare_TrueI)
         apply (rename_tac rv s)
         apply (case_tac rv, auto simp add: in_monad)[1]
        apply (simp add: corres_whenE_throwError_split_rhs corres_alternate2
                         check_vp_alignment_def unlessE_whenE)
        apply clarsimp
        apply (rule corres_symb_exec_r
          [OF _ get_master_pde_invalid_sp get_master_pde_inv],simp_all)[1]
        apply (clarsimp simp add: corres_whenE_throwError_split_rhs
             corres_alternate2)
        apply (rule corres_alternate1)
        apply (rule corres_from_rdonly,simp_all)[1]
          apply (wp | simp)+
        apply (simp add: returnOk_def, wp)
        apply (clarsimp simp: in_monad select_def arch_invocation_relation_def
          translate_arch_invocation_def transform_page_table_inv_def
          addrFromPPtr_def is_cap_simps cap_object_def
          cdl_lookup_pd_slot_def cap_has_object_def
          neq_Nil_conv cap_aligned_def)
        apply (simp add: make_arch_duplicate_def transform_pd_slot_ref_def)
        apply (clarsimp simp add: free_pd_slots_def opt_object_page_directory
                                  obj_at_def invs_valid_idle pd_shifting
                                  object_slots_def transform_page_directory_contents_def
                                  unat_map_def kernel_pde_mask_def
                                  transform_pde_def transform_mapping_def)
        apply (simp add: pd_shifting_dual ucast_nat_def shiftr_20_less triple_shift_fun
                         le_shiftr linorder_not_le)
       apply (rule hoare_pre, wp, auto)[1]
      apply (wp weak_if_wp | simp)+
    apply (clarsimp simp: is_final_cap'_def
      is_final_cap_def split:list.splits)
    apply (simp add: liftE_bindE is_final_cap_def corres_symb_exec_in_gets
                     unlessE_whenE corres_whenE_throwError_split_rhs
                     corres_alternate2)
    apply (rule corres_alternate1, simp add: returnOk_def)
    apply (clarsimp simp: arch_invocation_relation_def translate_arch_invocation_def get_pt_mapped_addr_def
                          transform_page_table_inv_def is_cap_simps)
    done
next
  case (PageDirectoryCap pd_ptr asid)
  thus ?case
  (* abandon hope, all who enter here *)
  apply (simp add: Decode_D.decode_invocation_def
  decode_invocation_def arch_decode_invocation_def
  get_page_directory_intent_def transform_intent_def
  isPDFlushLabel_def
  split del: if_split)
  apply (clarsimp simp: get_page_directory_intent_def transform_intent_def
           map_option_Some_eq2 throw_opt_def decode_page_directory_invocation_def
    split: label_split_asm  cdl_intent.splits
           InvocationLabels_H.invocation_label.splits arch_invocation_label.splits)
     apply (simp_all add: Let_def)
     apply (all \<open>(intro conjI impI allI)\<close>)
         apply (all \<open>(simp add: to_select_ret_or_throw whenE_to_select_ret_or_throw split_def
                           del: Collect_const;
            intro corres_initial_bindE_rdonly_select_ret_or_throw
                  corres_select_ret_or_throw[THEN corres_guard_imp];
            (wpsimp simp: if_apply_def2 ex_disj_distrib)?)?\<close>)

  (* 20-odd subgoals, not going to indent *)

    apply (all \<open>(simp split: option.split)?;
        (intro conjI impI allI corres_initial_bindE_rdonly_select_ret_or_throw
                  corres_select_ret_or_throw[THEN corres_guard_imp])?;
        (wpsimp simp: arch_invocation_relation_def translate_arch_invocation_def
                  transform_page_dir_inv_def flush_type_map_def
                  label_to_flush_type_def
                  ex_disj_distrib)?\<close>)

           apply ((rule corres_from_rdonly; wpsimp?),
              rule validE_cases_valid, wpsimp,
              simp add: ex_disj_distrib split_sum_ex
                        select_ret_or_throw_def in_monad in_select)+
    done

next
  case (SGISignalCap irq target)
  thus ?case
    apply (simp add: Decode_D.decode_invocation_def
                     Decode_A.decode_invocation_def arch_decode_invocation_def
                     decode_sgi_signal_invocation_def)
    apply (rule corres_returnOk)
    apply (simp add: arch_invocation_relation_def translate_arch_invocation_def
                     transform_sgi_inv_def)
    done
qed


lemma set_object_simple_corres:
  "\<lbrakk> obj = transform_object undefined 0 obj' \<rbrakk> \<Longrightarrow>
   dcorres dc \<top> (not_idle_thread ptr
             and obj_at (\<lambda>obj. \<not> is_tcb obj \<and> same_caps obj' obj \<and> obj_bits obj = obj_bits obj') ptr)
      (KHeap_D.set_object ptr obj) (KHeap_A.set_object ptr obj')"
  apply (clarsimp simp: KHeap_D.set_object_def set_object_def)
  apply (rule dcorres_symb_exec_r)
    apply (rule corres_assert_rhs[where P'="not_idle_thread ptr and
           obj_at (\<lambda>obj. \<not> is_tcb obj \<and> same_caps obj' obj \<and> obj_bits obj = obj_bits obj') ptr"])
    apply (fold modify_def)
    apply (rule corres_modify)
    apply (clarsimp simp: transform_def transform_objects_def not_idle_thread_def obj_at_def
                          transform_current_thread_def
                    cong: if_cong)
    apply (rule ext, simp split: if_split)
    apply (intro conjI impI allI)
     apply (clarsimp simp: transform_object_def
                    split: Structures_A.kernel_object.split)
    apply (clarsimp simp: restrict_map_def map_add_def)
   apply (wpsimp wp: get_object_wp)+
  done

lemma pde_unat_less_helper[simplified]:
  "unat ((p && mask pd_bits >> 2) :: word32) < 2 ^ 12"
  apply (rule unat_less_helper, simp only: word_unat_power[symmetric],
         rule shiftr_less_t2n)
  apply (rule order_less_le_trans, rule and_mask_less_size,
         simp_all add: pd_bits_def pageBits_def word_size)
  done

lemma store_pte_set_cap_corres:
  "\<lbrakk> slot = transform_pt_slot_ref ptr; cap = transform_pte pte\<rbrakk> \<Longrightarrow>
   dcorres dc \<top> valid_idle (KHeap_D.set_cap slot cap)
      (store_pte ptr pte)"
  apply (clarsimp simp:store_pte_def get_pt_def set_pt_def get_object_def gets_def bind_assoc)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp simp:corres_free_fail assert_def split:Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp:transform_pt_slot_ref_def)
  apply (rule corres_guard_imp[OF dcorres_set_pte_cap])
     apply (simp add: obj_at_def)+
  done

lemma store_pde_set_cap_corres:
  "\<lbrakk> slot = transform_pd_slot_ref ptr; cap = transform_pde pde ; ucast (ptr && mask pd_bits >> 2) \<notin> kernel_mapping_slots\<rbrakk> \<Longrightarrow>
   dcorres dc \<top> valid_idle (KHeap_D.set_cap slot cap)
      (store_pde ptr pde)"
  apply (clarsimp simp:store_pde_def get_pd_def set_pd_def get_object_def gets_def bind_assoc)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp simp:corres_free_fail assert_def split:Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp:transform_pd_slot_ref_def)
  apply (rule corres_guard_imp[OF dcorres_set_pde_cap])
      apply (simp add: obj_at_def)+
  done

lemma pde_opt_cap_eq:
  "\<lbrakk> ko_at (ArchObj (arch_kernel_obj.PageDirectory pd)) (x && ~~ mask pd_bits) s;
         valid_idle s \<rbrakk>
       \<Longrightarrow> opt_cap (transform_pd_slot_ref x) (transform s)
         = Some (transform_pde ((kernel_pde_mask pd) (ucast (x && mask pd_bits >> 2))))"
  apply (simp add: opt_cap_def transform_pd_slot_ref_def
                   slots_of_def transform_def
                   obj_at_def object_slots_def restrict_map_def map_add_def
                   transform_page_directory_contents_def transform_objects_def
                   unat_map_def ucast_nat_def
                   pde_unat_less_helper)
  apply (clarsimp simp: valid_idle_def st_tcb_at_def obj_at_def pred_tcb_at_def)
  done

lemma gets_the_noop_dcorres:
  "dcorres dc (\<lambda>s. f s \<noteq> None) \<top> (gets_the f) (return x)"
  by (clarsimp simp: gets_the_def corres_underlying_def exec_gets
                     assert_opt_def return_def)

lemma dget_object_sp:
  "\<lbrace>P\<rbrace> KHeap_D.get_object p \<lbrace>\<lambda>r s. P s \<and> cdl_objects s p = Some r\<rbrace>"
  apply wp
  apply auto
  done

lemma set_cap_opt_cap':
  "\<lbrace>\<lambda>s. P ((\<lambda>p. opt_cap p s) (slot \<mapsto> cap))\<rbrace> KHeap_D.set_cap slot cap \<lbrace>\<lambda>rv s. P (\<lambda>p. opt_cap p s)\<rbrace>"
  apply (cases slot)
  apply (clarsimp simp add:KHeap_D.set_cap_def split_def)
  apply (rule bind_wp [OF _ dget_object_sp])
  apply (case_tac obj; simp add: KHeap_D.set_object_def has_slots_def update_slots_def object_slots_def
                            split del: if_split cong: if_cong bind_cong;
                       wpsimp)
       by (auto elim!:rsubst[where P=P] simp: opt_cap_def slots_of_def object_slots_def)

lemma set_cap_opt_cap:
  "\<lbrace>\<lambda>s. if slot = slot' then P (Some cap) else P (opt_cap slot s)\<rbrace>
  KHeap_D.set_cap slot' cap
  \<lbrace>\<lambda>uu s. P (opt_cap slot s)\<rbrace>"
  apply (wp set_cap_opt_cap')
  apply clarsimp
  done

lemma set_cap_corres_stronger:
assumes rules: "\<And>s.  P cap' s \<Longrightarrow> cap = transform_cap cap'"  "slot = transform_cslot_ptr slot'"
shows "dcorres dc \<top>
           (\<lambda>s. P cap' s \<and> valid_idle s \<and> fst slot' \<noteq> idle_thread s)
           (KHeap_D.set_cap slot cap)
           (CSpaceAcc_A.set_cap cap' slot')"
(* corres_req2 *)
  apply (rule corres_req[rotated])
  apply (rule corres_req[rotated])
  apply (rule stronger_corres_guard_imp, erule(1) set_cap_corres)
  apply (auto simp add: rules)
  done

lemma invoke_page_table_corres:
  "transform_page_table_inv ptinv' = Some ptinv \<Longrightarrow>
   dcorres dc \<top> (valid_pti ptinv' and invs)
    (invoke_page_table ptinv) (perform_page_table_invocation ptinv')"
  apply (simp add: invoke_page_table_def perform_page_table_invocation_def)
  apply (clarsimp simp: transform_page_table_inv_def
            split: ARM_A.page_table_invocation.split_asm
                   if_split_asm)
   apply (rename_tac word oref attribs)
   apply (clarsimp simp: is_pt_cap_def valid_pti_def make_arch_duplicate_def)
   apply (rule stronger_corres_guard_imp)
     apply (rule corres_split)
        apply (rule set_cap_corres; simp)
       apply (rule corres_split_noop_rhs2)
          apply (simp add:insert_cap_orphan_def)
          apply (rule corres_add_noop_rhs)
          apply (rule corres_split[OF gets_the_noop_dcorres])
            apply (rule corres_assert_lhs)
            apply (rule_tac F ="ucast (word && mask pd_bits >> 2) \<notin> kernel_mapping_slots" in corres_gen_asm2)
            apply (rule store_pde_set_cap_corres)
              apply (simp add:transform_pde_def addrFromPPtr_def)+
             apply (wp | clarsimp simp: ptrFromPAddr_def)+
         apply (rule dcorres_machine_op_noop)
         apply (wp set_cap_opt_cap)+
    apply (clarsimp simp: empty_pde_at_def)
    apply (frule pde_opt_cap_eq, clarsimp+)
    apply (clarsimp simp:transform_pde_def kernel_pde_mask_def pde_at_def
                         transform_pd_slot_ref_def transform_cslot_ptr_def)
    apply (drule page_directory_not_in_cdt, simp+)
   apply (clarsimp simp: cte_wp_at_caps_of_state is_arch_update_def
                         cap_master_cap_simps
                  dest!: cap_master_cap_eqDs)
   apply (clarsimp simp: invs_valid_idle not_idle_thread_def)
   apply (intro conjI)
    apply (rule ccontr)
    apply (clarsimp)
    apply (drule valid_idle_has_null_cap[rotated -1])
        apply (clarsimp simp:invs_def valid_state_def)+
   apply (clarsimp simp:kernel_vsrefs_kernel_mapping_slots)
  apply (clarsimp simp: get_pt_mapped_addr_def bind_assoc)
  apply (rule dcorres_expand_pfx)
  apply (clarsimp simp:valid_pti_def transform_mapping_def is_pt_cap_def)
  apply (case_tac asid)
   apply (clarsimp simp: liftM_def)
   apply (rule corres_guard_imp)
    apply (rule corres_split)
        apply (rule get_cap_corres; simp)
       apply (rule_tac P="\<lambda>y s. cte_wp_at ((=) x) (a,b) s \<and> s = s'" in set_cap_corres_stronger)
        apply clarsimp
        apply (drule cte_wp_at_eqD2, simp)
        apply (clarsimp simp: transform_mapping_def update_map_data_def)
       apply (wp get_cap_cte_wp_at_rv | clarsimp)+
   apply (clarsimp simp:cte_wp_at_def is_arch_cap_def is_pt_cap_def)
   apply (clarsimp simp:invs_def valid_state_def not_idle_thread_def)
   apply (frule valid_idle_has_null_cap,simp+)
    apply (rule sym)
    apply (simp add:get_cap_caps_of_state)+
  apply (clarsimp simp:bind_assoc liftM_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split)
       apply (rule dcorres_unmap_page_table;
              clarsimp simp: valid_cap_def vmsz_aligned_def mask_2pm1)
      apply (rule_tac a2 = a and b2 = b and option2 = "Some (aa,ba)" in
                 corres_split[OF corres_alternate1[OF dcorres_clear_object_caps_pt]])
        apply (rule dcorres_symb_exec_r)
          apply (rule corres_split)
             apply (rule get_cap_corres; simp)
            apply (rule_tac P="\<lambda>y s. cte_wp_at ((=) xb) (a,b) s \<and>
                                caps_of_state s' = caps_of_state s" in set_cap_corres_stronger)
             apply (clarsimp simp:cte_wp_at_caps_of_state)
             apply (clarsimp simp: transform_mapping_def update_map_data_def)
            apply (wp get_cap_cte_wp_at_rv | clarsimp)+
         apply (wp do_machine_op_wp | clarsimp simp:not_idle_thread_def)+
      apply (wp mapM_x_wp)
       apply clarsimp
       apply (wp store_pte_cte_wp_at)
      apply fastforce
     apply wpsimp+
    apply (rule_tac Q'="\<lambda>rv s. invs s \<and> a \<noteq> idle_thread s \<and> cte_wp_at \<top> (a,b) s \<and>
                              caps_of_state s' = caps_of_state s" in hoare_strengthen_post)
     apply wp
    apply (clarsimp simp:invs_def valid_state_def)
   apply simp
  apply (simp add:valid_cap_def vmsz_aligned_def mask_2pm1)
  apply (simp add:cte_wp_at_def transform_cap_def update_map_data_def transform_mapping_def
                  is_arch_cap_def mask_cap_def cap_rights_update_def is_pt_cap_def cap_aligned_def)
  apply (rule ccontr,clarsimp simp:invs_def valid_state_def)
  apply (drule valid_idle_has_null_cap,simp+)
   apply (clarsimp simp:get_cap_caps_of_state)
   apply (rule sym, simp+)
  done

lemma case_sum_eq: "case_sum a a x = a (case x of Inl a \<Rightarrow> a | Inr a \<Rightarrow> a)"
  apply (case_tac x)
  apply (clarsimp)+
done

lemma set_vm_root_for_flush_dwp[wp]:
  "\<lbrace>\<lambda>ps. transform ps = cs\<rbrace> set_vm_root_for_flush word1 word2 \<lbrace>\<lambda>r s. transform s = cs\<rbrace>"
  apply (simp add:set_vm_root_for_flush_def)
  apply (wp do_machine_op_wp|clarsimp simp:arm_context_switch_def get_hw_asid_def)+
        apply (wpc)
         apply wp+
       apply (rule hoare_conjI,rule hoare_drop_imp)
        apply (wp do_machine_op_wp|clarsimp simp:load_hw_asid_def)+
     apply (wpc|wp)+
    apply (rule_tac Q'="\<lambda>rv s. transform s = cs" in hoare_strengthen_post)
     apply (wp|clarsimp)+
  done

lemma ucast_add: (* FIXME: move to Word_Lib *)
  "len_of TYPE('a) \<le> len_of TYPE('b)
   \<Longrightarrow> (ucast (a + b) :: (('a::len)word)) = ucast (a :: (('b ::len) word)) + (ucast b)"
  apply (rule word_unat.Rep_eqD)
  apply (simp add:unat_ucast unat_word_ariths mod_exp_eq min_def mod_add_eq)
  done

lemma store_pte_page_inv_entries_safe:
  "\<lbrace>page_inv_entries_safe (Inl (ab, bb)) and valid_pdpt_objs\<rbrace>
   store_pte (hd bb) ab
   \<lbrace>\<lambda>rv s. (\<exists>f. ko_at (ArchObj (arch_kernel_obj.PageTable f)) (hd bb && ~~ mask pt_bits)  s
    \<and> (\<forall>slot\<in>set (tl bb). f (ucast (slot && mask pt_bits >> 2)) = ARM_A.pte.InvalidPTE))
    \<and> (\<forall>sl\<in>set (tl bb). sl && ~~ mask pt_bits = hd bb && ~~ mask pt_bits)\<rbrace>"
  apply (simp add:store_pte_def set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp:obj_at_def page_inv_entries_safe_def split:if_splits)
  apply (intro conjI impI)
   apply (clarsimp simp: hd_map_simp upto_enum_def upto_enum_step_def tl_map_simp
                         map_eq_Cons_conv upt_eq_Cons_conv upto_0_to_n)
   apply (simp add:field_simps)
   apply (subst (asm) shiftl_t2n[where n = 2,simplified field_simps,simplified,symmetric])+
   apply (rename_tac s ptr pt slot)
   apply (subst (asm) and_mask_plus[where a = "of_nat slot << 2"])
       apply (simp add:pt_bits_def pageBits_def)+
    apply (rule shiftl_less_t2n[where m = 6,simplified])
     apply (rule word_of_nat_less,simp)
    apply simp
   apply (subst (asm) is_aligned_shiftr_add)
        apply (erule is_aligned_after_mask)
        apply (simp add:pt_bits_def pageBits_def)+
       apply (simp add:is_aligned_shiftl_self)
      apply (rule shiftl_less_t2n)
       apply (rule word_of_nat_less,simp)
      apply simp+
   apply (subst (asm) ucast_add)
    apply simp
   apply simp
   apply (subst (asm) shiftl_shiftr_id)
     apply simp
    apply (rule word_of_nat_less)
    apply simp
   apply (simp add:ucast_of_nat_small of_nat_neq_0 del: word_of_nat_eq_0_iff)
  apply (clarsimp simp: hd_map_simp upto_enum_def upto_enum_step_def tl_map_simp
                        map_eq_Cons_conv upt_eq_Cons_conv upto_0_to_n image_def)
  apply (simp add:field_simps)
  apply (erule page_table_address_eq[symmetric])
  apply (fastforce simp:upto_enum_def upto_enum_step_def image_def)
  done

lemma store_pde_page_inv_entries_safe:
  "\<lbrace>page_inv_entries_safe (Inr (ab, bb)) and valid_pdpt_objs\<rbrace>
   store_pde (hd bb) ab
   \<lbrace>\<lambda>rv s. (\<exists>f. ko_at (ArchObj (arch_kernel_obj.PageDirectory f)) (hd bb && ~~ mask pd_bits)  s
    \<and> (\<forall>slot\<in>set (tl bb). f (ucast (slot && mask pd_bits >> 2)) = ARM_A.pde.InvalidPDE))
    \<and> (\<forall>sl\<in>set (tl bb). sl && ~~ mask pd_bits = hd bb && ~~ mask pd_bits)\<rbrace>"
  apply (simp add:store_pde_def set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp:obj_at_def page_inv_entries_safe_def split:if_splits)
  apply (intro conjI impI)
   apply (clarsimp simp: hd_map_simp upto_enum_def upto_enum_step_def drop_map
                         tl_map_simp map_eq_Cons_conv upt_eq_Cons_conv upto_0_to_n)
   apply (clarsimp simp add:field_simps)
   apply (subst (asm) shiftl_t2n[where n = 2,simplified field_simps,simplified,symmetric])+
   apply (subst (asm) and_mask_plus[where a = "of_nat slot << 2"])
       apply (simp add:pd_bits_def pageBits_def)+
    apply (rule shiftl_less_t2n[where m = 6,simplified])
     apply (rule word_of_nat_less,simp)
    apply simp
   apply (subst (asm) is_aligned_shiftr_add)
        apply (erule is_aligned_after_mask)
        apply (simp add:pd_bits_def pageBits_def)+
       apply (simp add:is_aligned_shiftl_self)
      apply (rule shiftl_less_t2n)
       apply (rule word_of_nat_less,simp)
      apply simp+
   apply (subst (asm) ucast_add)
    apply simp
   apply simp
   apply (subst (asm) shiftl_shiftr_id)
     apply simp
    apply (rule word_of_nat_less)
    apply simp
   apply (simp add:ucast_of_nat_small of_nat_neq_0 del: word_of_nat_eq_0_iff)
  apply (clarsimp simp: hd_map_simp upto_enum_def upto_enum_step_def tl_map_simp map_eq_Cons_conv
                        upt_eq_Cons_conv upto_0_to_n image_def)
  apply (simp add: field_simps)
  apply (erule page_directory_address_eq[symmetric])
  apply (fastforce simp:upto_enum_def upto_enum_step_def image_def)
  done

lemma cleanL2Range_underlying_memory[wp]:
  "cleanL2Range word3 w \<lbrace>\<lambda>ms. underlying_memory ms = m\<rbrace>"
  by (clarsimp simp: cleanL2Range_def, wp)

lemma invalidateL2Range_underlying_memory[wp]:
  "invalidateL2Range word3 w \<lbrace>\<lambda>ms. underlying_memory ms = m\<rbrace>"
  by (clarsimp simp: invalidateL2Range_def, wp)

lemma cleanInvalidateL2Range_underlying_memory[wp]:
  "cleanInvalidateL2Range word3 w \<lbrace>\<lambda>ms. underlying_memory ms = m\<rbrace>"
  by (clarsimp simp: cleanInvalidateL2Range_def, wp)

lemma cleanByVA_underlying_memory[wp]:
  "\<lbrace>\<lambda>ms. underlying_memory ms = m\<rbrace> cleanByVA a b \<lbrace>\<lambda>y ms. underlying_memory ms = m\<rbrace>"
  by (clarsimp simp: cleanByVA_def, wp)

lemma invalidateByVA_underlying_memory[wp]:
  "\<lbrace>\<lambda>ms. underlying_memory ms = m\<rbrace> invalidateByVA a b \<lbrace>\<lambda>y ms. underlying_memory ms = m\<rbrace>"
  by (clarsimp simp: invalidateByVA_def, wp)

lemma invalidateByVA_I_underlying_memory[wp]:
  "\<lbrace>\<lambda>ms. underlying_memory ms = m\<rbrace> invalidateByVA_I a b \<lbrace>\<lambda>y ms. underlying_memory ms = m\<rbrace>"
  by (clarsimp simp: invalidateByVA_I_def, wp)

lemma cleanInvalByVA_underlying_memory[wp]:
  "\<lbrace>\<lambda>ms. underlying_memory ms = m\<rbrace> cleanInvalByVA a b \<lbrace>\<lambda>y ms. underlying_memory ms = m\<rbrace>"
  by (clarsimp simp: cleanInvalByVA_def, wp)

lemma cleanCacheRange_PoC_underlying_memory[wp]:
  "cleanCacheRange_PoC word1 word2 word3 \<lbrace>\<lambda>ms. underlying_memory ms = m\<rbrace>"
  by (clarsimp simp: cleanCacheRange_PoC_def, wp)

lemma cleanCacheRange_RAM_underlying_memory[wp]:
  "cleanCacheRange_RAM word1 word2 word3 \<lbrace>\<lambda>ms. underlying_memory ms = m\<rbrace>"
  by (clarsimp simp: cleanCacheRange_RAM_def,wp)

lemma branchFlush_underlying_memory[wp]:
  "\<lbrace>\<lambda>ms. underlying_memory ms = m\<rbrace> branchFlush a b \<lbrace>\<lambda>rv ms. underlying_memory ms = m\<rbrace>"
  by (clarsimp simp: branchFlush_def, wp)

lemma branchFlushRange_underlying_memory[wp]:
  "branchFlushRange word1 word2 word3 \<lbrace>\<lambda>ms. underlying_memory ms = m\<rbrace>"
  by (clarsimp simp: branchFlushRange_def,wp)

lemma invalidateCacheRange_RAM_underlying_memory[wp]:
  "invalidateCacheRange_RAM word1 word2 word3 \<lbrace>\<lambda>ms. underlying_memory ms = m\<rbrace>"
  by (clarsimp simp: invalidateCacheRange_RAM_def, wp, clarsimp, wp, clarsimp)

lemma invalidateCacheRange_I_underlying_memory[wp]:
  "invalidateCacheRange_I word1 word2 word3 \<lbrace>\<lambda>ms. underlying_memory ms = m\<rbrace>"
  by (clarsimp simp: invalidateCacheRange_I_def, wp)

lemma cleanInvalidateCacheRange_RAM_underlying_memory[wp]:
  "cleanInvalidateCacheRange_RAM word1 word2 word3 \<lbrace>\<lambda>ms. underlying_memory ms = m\<rbrace>"
  by (clarsimp simp: cleanInvalidateCacheRange_RAM_def,wp)

lemma isb_underlying_memory[wp]:
  "\<lbrace>\<lambda>ms. underlying_memory ms = m\<rbrace> isb \<lbrace>\<lambda>rv ms. underlying_memory ms = m\<rbrace>"
  by (clarsimp simp: isb_def, wp)

lemma do_flush_underlying_memory[wp]:
  "do_flush flush_type word1 word2 word3 \<lbrace>\<lambda>ms. underlying_memory ms = m\<rbrace>"
  unfolding do_flush_def by wpsimp

declare cleanCacheRange_PoU_underlying_memory[wp]

lemma invoke_page_directory_corres:
  "transform_page_dir_inv ip' = Some ip  \<Longrightarrow>
   dcorres dc \<top> (invs  and valid_pdpt_objs)
    (invoke_page_directory ip) (perform_page_directory_invocation ip')"
  apply (clarsimp simp:invoke_page_directory_def)
  apply (case_tac ip')
   apply (simp_all add:perform_page_invocation_def)
   apply (simp_all add: when_def  transform_page_dir_inv_def)
   apply safe
   apply (clarsimp)
   apply (rule corres_dummy_return_r)
   apply (rule dcorres_symb_exec_r[OF corres_free_return[where P=\<top> and P'=\<top>]])
    apply wp
   apply (clarsimp simp: perform_page_directory_invocation_def)
   apply (wp)
       apply (rule dcorres_to_wp, rule dcorres_set_vm_root)
      apply (wp)
     apply (clarsimp cong: if_cong)
     apply (wp do_machine_op_wp, clarsimp, wp+)
   apply (clarsimp)
  apply (rule corres_dummy_return_r)
  apply (rule dcorres_symb_exec_r[OF corres_free_return[where P=\<top> and P'=\<top>]])
   apply wp
  apply (clarsimp simp: perform_page_directory_invocation_def)
  done

lemma pte_check_if_mapped_corres:
  "dcorres dc \<top> \<top> (return a) (pte_check_if_mapped pte)"
  apply (clarsimp simp add: pte_check_if_mapped_def get_master_pte_def get_pte_def get_pt_def
                            bind_assoc in_monad get_object_def corres_underlying_def return_def)
  apply (case_tac y; simp add: in_monad)
  by (simp add: get_pte_def get_pt_def get_object_def in_monad bind_assoc
         split: pte.splits kernel_object.splits arch_kernel_obj.splits)

lemma pde_check_if_mapped_corres:
  "dcorres dc \<top> \<top> (return a) (pde_check_if_mapped pde)"
  apply (clarsimp simp add: pde_check_if_mapped_def get_master_pde_def get_pde_def get_pd_def
                            in_monad get_object_def corres_underlying_def return_def)
  apply (case_tac y; simp add: in_monad)
  by (simp add: get_pde_def get_pd_def get_object_def in_monad bind_assoc
         split: pde.splits kernel_object.splits arch_kernel_obj.splits)

lemma if_invalidate_equiv_return:
  "dcorres dc \<top> \<top> (return a) (if b then invalidate_tlb_by_asid asid else return ())"
  apply (cases b, simp_all)
  apply (rule wp_to_dcorres)
  apply (wp invalidate_tlb_by_asid_dwp)
  apply clarsimp
  done

lemma ct_active_not_idle_etc:
  "\<lbrakk> invs s; ct_active s \<rbrakk> \<Longrightarrow> not_idle_thread (cur_thread s) s"
  apply (simp add: not_idle_thread_def ct_in_state_def)
  apply (subgoal_tac "valid_idle s")
   apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
  apply (clarsimp simp: invs_def valid_state_def)
  done

lemma invoke_page_corres:
  "transform_page_inv ip' = Some ip  \<Longrightarrow>
   dcorres dc \<top> (valid_page_inv ip' and invs and page_inv_duplicates_valid ip' and valid_pdpt_objs and ct_active)
    (invoke_page ip) (perform_page_invocation ip')"
  supply if_cong[cong]
  apply (clarsimp simp:invoke_page_def)
  apply (case_tac ip')
     apply (simp_all add:perform_page_invocation_def)
     apply (rename_tac word cap prod sum)
     apply (simp_all add:perform_page_invocation_def transform_page_inv_def)
    apply (rule dcorres_expand_pfx)
    apply (clarsimp simp:valid_page_inv_def)
    apply (clarsimp simp:empty_refs_def)
    apply (case_tac sum)
     apply (clarsimp simp: mapM_x_singleton)
     apply (simp add:page_inv_duplicates_valid_def split:if_splits)
     apply (rule corres_guard_imp)
       apply (rule corres_split)
          apply (rule set_cap_corres; simp)
         apply (rule corres_bind_return_r, rule corres_rel_imp[rotated], simp)
         apply (rule corres_dummy_return_pl[where b ="()"])
         apply (rule corres_split[OF pte_check_if_mapped_corres])
           apply (simp split del: if_split)
           apply (rule corres_dummy_return_l)
           apply (rule corres_split)
              apply (rule store_pte_set_cap_corres; simp)
             apply (rule corres_dummy_return_l)
             apply (rule_tac corres_split[OF dcorres_store_invalid_pte_tail_large_page])
               apply (rule corres_dummy_return_l)
               apply (rule corres_split[OF _ if_invalidate_equiv_return])
                 apply (rule wp_to_dcorres[where Q=\<top>])
                 apply (wp do_machine_op_wp mapM_wp' set_cap_idle
                           store_pte_page_inv_entries_safe set_cap_page_inv_entries_safe
                        | clarsimp simp:cleanCacheRange_PoU_def)+
     apply (clarsimp simp:invs_def valid_state_def cte_wp_at_caps_of_state)
     apply (frule_tac v = b in valid_idle_has_null_cap,simp+)
     apply (clarsimp simp:is_arch_update_def is_arch_cap_def cap_master_cap_def split:cap.split_asm)
    apply (clarsimp simp:mapM_x_singleton)
    apply (rule corres_guard_imp)
      apply (rule corres_split)
         apply (rule set_cap_corres; simp)
        apply (rule corres_bind_return_r, rule corres_rel_imp[rotated], simp)
        apply (rule corres_dummy_return_pl[where b="()"])
        apply (rule corres_split[OF pde_check_if_mapped_corres])
          apply (simp split del: if_split)
          apply (rule corres_dummy_return_l)
          apply (rule corres_split)
             apply (rule store_pde_set_cap_corres; clarsimp simp: valid_slots_def)
            apply (rule corres_dummy_return_l)
            apply (rule_tac corres_split[OF dcorres_store_invalid_pde_tail_super_section])
              apply (rule corres_dummy_return_l)
              apply (rule corres_split[OF _ if_invalidate_equiv_return])
                apply (rule wp_to_dcorres[where Q=\<top>])
                apply (wp do_machine_op_wp mapM_wp' set_cap_idle
                          set_cap_page_inv_entries_safe store_pde_page_inv_entries_safe
                       | clarsimp simp:cleanCacheRange_PoU_def)+
    apply (simp add:page_inv_duplicates_valid_def valid_slots_def
                    page_inv_entries_safe_def split:if_splits)
     apply (clarsimp simp:invs_def valid_state_def cte_wp_at_caps_of_state)
     apply (frule_tac v = b in valid_idle_has_null_cap,simp+)
     apply (clarsimp simp:is_arch_update_def is_arch_cap_def cap_master_cap_def split:cap.split_asm)
    apply (clarsimp simp:invs_def valid_state_def cte_wp_at_caps_of_state)
    apply (frule_tac v = b in valid_idle_has_null_cap,simp+)
    apply (clarsimp simp:is_arch_update_def is_arch_cap_def cap_master_cap_def split:cap.split_asm)

   \<comment> \<open>PageUnmap\<close>
   apply (rule dcorres_expand_pfx)
   apply (clarsimp simp: valid_page_inv_def transform_mapping_def liftM_def
     split:arch_cap.splits option.splits)
    apply (rule corres_guard_imp)
      apply (rule corres_split)
         apply (rule get_cap_corres; simp)
        apply (rule corres_bind_return_r, rule corres_rel_imp[rotated], simp)
        apply (rule_tac P="\<lambda>y s. cte_wp_at ((=) x) (a,b) s \<and> s = s'" in set_cap_corres_stronger)
         apply clarsimp
         apply (drule cte_wp_at_eqD2, simp)
         apply (clarsimp simp: transform_mapping_def update_map_data_def)
        apply (wp get_cap_cte_wp_at_rv | clarsimp)+
    apply (clarsimp simp:cte_wp_at_def is_arch_cap_def is_pt_cap_def)
    apply (clarsimp simp:invs_def valid_state_def not_idle_thread_def)
    apply (frule valid_idle_has_null_cap,simp+)
     apply (rule sym)
     apply (simp add:get_cap_caps_of_state)+
   apply (rule corres_guard_imp)
     apply (rule corres_split[OF dcorres_unmap_page])
       apply (rule corres_split)
          apply (rule get_cap_corres; simp)
         apply (rule corres_bind_return_r, rule corres_rel_imp[rotated], simp)
         apply (rule_tac P="\<lambda>y s. cte_wp_at ((=) x) (a,b) s \<and>
                                   caps_of_state s' = caps_of_state s"
           in set_cap_corres_stronger)
          apply (clarsimp simp:cte_wp_at_caps_of_state)
          apply (clarsimp simp: transform_mapping_def update_map_data_def)
         apply (wp get_cap_cte_wp_at_rv unmap_page_pred_tcb_at |
                clarsimp simp:valid_idle_def not_idle_thread_def)+
     apply (rule_tac Q'="\<lambda>rv s. idle_tcb_at (\<lambda>(st, ntfn, arch). idle st \<and> ntfn = None \<and> valid_arch_idle arch)
                                           (idle_thread s) s \<and>
                               a \<noteq> idle_thread s \<and> idle_thread s = idle_thread_ptr \<and> cte_wp_at \<top> (a,b) s \<and>
                               caps_of_state s' = caps_of_state s" in hoare_strengthen_post)
      apply (wps, wp unmap_page_pred_tcb_at, clarsimp simp: invs_def valid_state_def valid_idle_def)
    apply simp
   apply (clarsimp simp: cte_wp_at_def is_arch_cap_def is_pt_cap_def)
   apply (rule conjI, simp)
   apply (rule conjI, simp add:invs_def valid_state_def valid_idle_def)
    apply (clarsimp simp:invs_def valid_state_def not_idle_thread_def)
   apply (clarsimp simp:invs_def valid_state_def not_idle_thread_def valid_idle_def)
   apply (frule valid_idle_has_null_cap, (simp add: valid_idle_def)+)
    apply (rule sym)
    apply (simp add:get_cap_caps_of_state)+

  \<comment> \<open>PageFlush\<close>
  apply (clarsimp simp:invoke_page_def)
  apply (clarsimp simp: when_def split: if_splits)
  apply (rule corres_bind_return_r, rule corres_rel_imp[rotated], simp)
  apply (rule corres_guard_imp)
    apply (rule dcorres_symb_exec_r)+
        apply (simp only: if_split_asm)
        apply (safe)
         apply (erule notE)
         apply (rule dcorres_symb_exec_r)+
           apply (rule dcorres_set_vm_root)
          apply (wp)+
        apply (erule notE)+
        apply (clarsimp)
       apply (wp do_machine_op_wp | clarsimp)+
  done

declare tl_drop_1[simp]

lemma unat_map_upd:
  "unat_map (Some \<circ> transform_asid_table_entry \<circ> (asid_table as)(asid_high_bits_of base \<mapsto> frame)) =
   (unat_map (Some \<circ> transform_asid_table_entry \<circ> asid_table as))
     (unat (asid_high_bits_of base) \<mapsto> AsidPoolCap frame 0)"
  apply (rule ext)
  apply (clarsimp simp:unat_map_def asid_high_bits_of_def transform_asid_table_entry_def)
  apply (intro impI conjI)
    apply (subgoal_tac "x<256")
     apply (clarsimp simp: unat_map_def asid_high_bits_of_def asid_low_bits_def
                           transform_asid_table_entry_def transform_asid_def)
     apply (drule_tac x="of_nat x" in unat_cong)
     apply (subst (asm) word_unat.Abs_inverse)
      apply (clarsimp simp:unats_def unat_ucast)+
  done

declare descendants_of_empty[simp]

lemma invoke_asid_control_corres:
  assumes "arch_invocation_relation (cdl_invocation.InvokeAsidControl asid_inv)
      (arch_invocation.InvokeASIDControl asid_inv')"
  notes is_aligned_neg_mask_eq[simp del]
        is_aligned_neg_mask_weaken[simp del]
  shows
  "dcorres dc \<top>
    (invs and ct_active and valid_aci asid_inv')
    (invoke_asid_control asid_inv)
    (perform_asid_control_invocation asid_inv')"
  using assms
  apply -
  apply (rule dcorres_expand_pfx)
  apply (case_tac asid_inv')
  apply (simp add:valid_aci_def)
  apply (simp add: cte_wp_at_caps_of_state)
  apply (elim conjE exE)
  apply (rename_tac frame cnode_ref cref base cap idx)
proof -
  fix s s' frame cnode_ref cref base cap idx
  note retype_dc = retype_region_dcorres[where type="ArchObject ASIDPoolObj",
          unfolded translate_object_type_def, simplified]
  note insert_dc = insert_cap_child_corres
  [where cap="cap.ArchObjectCap (arch_cap.ASIDPoolCap x y)" for x y,
    simplified transform_cap_simps]
  note [simp del] = untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex

  have p2bits: "2 ^ pageBits \<le> 2 ^ pageBits - Suc 0 \<Longrightarrow> False"
    by (simp add:pageBits_def)

  assume misc: "invs (s' :: det_ext state)" "ct_active s'"
        "caps_of_state s' cnode_ref = Some cap.NullCap"
        "ex_cte_cap_wp_to Structures_A.is_cnode_cap cnode_ref s'"
        "cnode_ref \<noteq> cref"
        "CSpaceAcc_A.descendants_of cref (cdt s') = {}"
        "caps_of_state s' cref = Some cap"
        "cap = cap.UntypedCap False frame pageBits idx"
        "is_aligned (base::word32) asid_low_bits"
        "base < 2 ^ asid_bits"
  assume relation:"arch_invocation_relation (InvokeAsidControl asid_inv)
         (arch_invocation.InvokeASIDControl (asid_control_invocation.MakePool frame cnode_ref cref base))"
  assume asid_para: "asid_inv' = asid_control_invocation.MakePool frame cnode_ref cref base"
  show "dcorres dc ((=) (transform s')) ((=) s') (invoke_asid_control asid_inv)
           (perform_asid_control_invocation (asid_control_invocation.MakePool frame cnode_ref cref base))"
    using relation asid_para
    supply if_cong[cong]
    apply (clarsimp simp:invoke_asid_control_def)
    apply (clarsimp simp:perform_asid_control_invocation_def)
    apply (simp add:arch_invocation_relation_def translate_arch_invocation_def)
    apply (cases asid_inv, clarsimp)
    apply (rule corres_guard_imp)
      apply (rule corres_split)
         apply (rule delete_objects_dcorres)
         apply (intro set_eqI)
         apply (case_tac x)
         apply (clarsimp simp: image_def)
         apply (clarsimp simp: page_bits_def)
        apply (rule corres_symb_exec_r)
           apply (rule_tac F = "cdl_cap.UntypedCap False {frame..frame + 2 ^ pageBits - 1} {} =
                                transform_cap (max_free_index_update pcap)" in corres_gen_asm2)
           apply (rule corres_split)
              apply (rule set_cap_corres; simp)
             apply (rule generate_object_ids_exec[where ty = "ArchObject ASIDPoolObj" and
                                                        ptr = frame and us = 0 and sz = pageBits,
                                                  unfolded translate_object_type_def ,simplified])
             apply (rule corres_split[OF retype_dc[where ptr = frame and sz = pageBits]])
               apply (simp add: retype_addrs_def obj_bits_api_def default_arch_object_def
                                retype_transform_obj_ref_def)
               apply (rule corres_split[OF insert_dc[unfolded fun_app_def], where R="\<lambda>rv. \<top>"])
                 apply (rule corres_assert_rhs[where P'=\<top>])
                 apply (simp add: gets_fold_into_modify dc_def[symmetric])
                 apply (clarsimp simp: simpler_modify_def put_def bind_def corres_underlying_def)
                 apply (clarsimp simp: transform_def transform_objects_def transform_cdt_def
                                       transform_current_thread_def)
                 apply (clarsimp simp: transform_asid_table_def transform_asid_def
                                       fun_upd_def[symmetric] unat_map_upd)
                apply wp+
             apply (rule_tac Q'="\<lambda>rv s. cte_wp_at (\<lambda>c. \<exists>idx. c = (cap.UntypedCap False frame pageBits idx)) cref s
                                       \<and> asid_pool_at frame s
                                       \<and> cte_wp_at ((=) cap.NullCap) cnode_ref s
                                       \<and> ex_cte_cap_to cnode_ref s \<and> invs s"
                             in hoare_post_imp)
              apply (clarsimp simp: cte_wp_at_caps_of_state)
              apply (frule(1) caps_of_state_valid[where p = cref])
              apply (clarsimp simp: valid_cap_simps cap_aligned_def)
              apply (drule ex_cte_cap_to_not_idle, auto simp: not_idle_thread_def)[1]
               apply (subst safe_parent_is_parent[where m=Map.empty],
                      auto simp: safe_parent_for_def is_physical_def arch_is_physical_def)[1]
              apply (case_tac cref,clarsimp)
              apply (drule valid_idle_has_null_cap[rotated - 1])
                  apply clarsimp+
             apply (wp retype_cte_wp_at[where sz = pageBits] retype_region_ap'[simplified]
                       retype_region_ex_cte_cap_to[where sz = pageBits and ptr = frame]
                       retype_region_plain_invs[where sz = pageBits and ptr = frame])
            apply (rule hoare_strengthen_post[OF hoare_TrueI[where P = \<top>]])
            apply simp
           apply (clarsimp simp: conj_comms pred_conj_def
                  | strengthen invs_valid_pspace invs_valid_idle)+
           apply (rule_tac P = "pcap = cap.UntypedCap False frame pageBits idx \<and>
                                is_aligned frame (obj_bits_api (ArchObject ASIDPoolObj) 0)"
                           in hoare_gen_asm)
           apply (wp max_index_upd_invs_simple set_cap_idle set_cap_caps_no_overlap set_cap_no_overlap
                     set_cap_cte_wp_at set_cap_cte_cap_wp_to)
           apply (simp add:region_in_kernel_window_def obj_bits_api_def default_arch_object_def)
           apply (wp set_untyped_cap_caps_overlap_reserved get_cap_wp
                     set_cap_no_overlap set_cap_cte_wp_at
                   | strengthen exI[where x=cref])+
         apply clarsimp
        apply clarsimp
       apply (clarsimp simp: image_def)
      apply (rule_tac P = "is_aligned frame page_bits \<and> page_bits \<le> word_bits \<and> 2 \<le> page_bits"
                      in hoare_gen_asm)
      apply (simp add: delete_objects_rewrite[unfolded word_size_bits_def] is_aligned_neg_mask_eq)
      apply (rule_tac Q'="\<lambda>_ s.
             invs s \<and> pspace_no_overlap_range_cover frame pageBits s \<and>
             descendants_range_in (untyped_range (cap.UntypedCap False frame pageBits idx)) cref s \<and>
             cte_wp_at ((=) (cap.UntypedCap False frame pageBits idx)) cref s \<and>
             cte_wp_at ((=) cap.NullCap) cnode_ref s \<and>
             ex_cte_cap_wp_to (\<lambda>_. True) cnode_ref s \<and>
             region_in_kernel_window {frame..frame + 2 ^ pageBits - 1} s \<and>
             is_aligned frame pageBits" in hoare_post_imp)
       apply (clarsimp simp: cte_wp_at_caps_of_state default_arch_object_def invs_valid_idle
                             obj_bits_api_def arch_kobj_size_def page_bits_def max_free_index_def
                             usable_untyped_range.simps is_aligned_neg_mask_eq untyped_range.simps
                             region_in_kernel_window_def not_idle_thread_def field_simps)
       apply (rule context_conjI,clarsimp+)
       apply (intro conjI)
          apply (case_tac cref,clarsimp)
          apply (drule valid_idle_has_null_cap[rotated -1]; clarsimp)
         apply (erule descendants_range_caps_no_overlapI)
          apply (fastforce simp:cte_wp_at_caps_of_state is_aligned_neg_mask_eq)+
        apply (erule range_cover_full)
        apply (simp add:pageBits_def word_bits_conv)
       apply (clarsimp dest!:p2bits simp:free_range_of_untyped_def)
      apply wp
     apply fastforce
    using misc
    apply (clarsimp simp:cte_wp_at_caps_of_state page_bits_def)
    apply (subgoal_tac "descendants_range (cap.UntypedCap False frame pageBits idx) cref s'")
     prefer 2
     apply (simp add: descendants_range_def2 empty_descendants_range_in)
    apply (rule conjI)
     apply (erule ex_cte_cap_protects)
         apply (simp add: cte_wp_at_caps_of_state)
        apply ((clarsimp simp: descendants_range_def2 untyped_range.simps)+)[4]
    apply clarsimp
    apply (rule conjI)
     apply (rule ex_cte_cap_protects)
          apply (rule_tac P = "\<lambda>cap. cap = cap.UntypedCap False frame pageBits idx" in if_unsafe_then_capD)
            apply (fastforce simp:cte_wp_at_caps_of_state)+
        apply ((clarsimp simp:descendants_range_def2 untyped_range.simps)+)[4]
    apply clarsimp
    apply (rule conjI)
     apply (intro exI conjI,assumption)
     apply (simp add:descendants_range_def2)
    apply (frule_tac p = cref in caps_of_state_valid, assumption)
    apply (frule valid_cap_aligned)
    apply (clarsimp simp: cap_aligned_def)
    apply (frule detype_invariants[rotated 2]; clarsimp?)
     apply (clarsimp simp: cte_wp_at_caps_of_state)
    apply (frule intvl_range_conv[where ptr = frame])
     apply (simp add: pageBits_def word_bits_conv asid_low_bits_def)
    apply (clarsimp simp: untyped_range.simps detype_clear_um_independent)
    apply (intro conjI)
         apply (erule pspace_no_overlap_detype; clarsimp)
        apply (clarsimp simp: descendants_range_in_def)
       apply (erule cap_to_protected[OF ex_cte_cap_wp_to_weakenE]; fastforce simp:cte_wp_at_caps_of_state)
      apply (drule_tac p = cref in cap_refs_in_kernel_windowD2[OF caps_of_state_cteD], fastforce)
      apply (clarsimp simp: region_in_kernel_window_def valid_cap_def cap_range_def cap_aligned_def
                            untyped_range.simps clear_um_def)
     apply (simp add: pageBits_def word_bits_def)
    apply (simp add: pageBits_def word_bits_conv)
    done
qed

lemma corres_return_r:
  "corres_underlying st nf nf' dc P P' a (do b; return () od) \<Longrightarrow> corres_underlying st nf nf' dc P P' a b"
  by (fastforce simp: bind_def dc_def return_def corres_underlying_def)

lemma dcorres_assert_assume:
  "\<lbrakk> P' \<Longrightarrow> dcorres rr P Q f (g ()) \<rbrakk> \<Longrightarrow> dcorres rr P Q f (assert P' >>= g)"
  by (clarsimp simp: assert_def) (rule corres_free_fail)

lemma invoke_asid_pool_corres:
  "arch_invocation_relation (InvokeAsidPool ap_inv)
                            (arch_invocation.InvokeASIDPool ap_inv') \<Longrightarrow>
   dcorres dc \<top> (invs and valid_apinv ap_inv')
    (invoke_asid_pool ap_inv)
    (perform_asid_pool_invocation ap_inv')"
  apply (rule dcorres_expand_pfx)
  apply (clarsimp simp:invoke_asid_pool_def perform_asid_pool_invocation_def)
  apply (clarsimp split:asid_pool_invocation.splits cdl_asid_pool_invocation.splits)
  apply (clarsimp simp:valid_apinv_def arch_invocation_relation_def
                       translate_arch_invocation_def)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (rule corres_guard_imp)
    apply (rule corres_split)
       apply (rule get_cap_corres; simp)
      apply (clarsimp split: cap.splits arch_cap.splits simp: corres_free_fail)
      apply (rule dcorres_symb_exec_r)
        apply (rule_tac F = "rv = pool" in corres_gen_asm2)
        apply (rule corres_split)
           apply (rule set_cap_corres; simp)
          apply (rule dcorres_set_asid_pool[unfolded fun_upd_def])
            apply fastforce
           apply (clarsimp simp:transform_asid_pool_entry_def transform_cap_def)+
        apply (wp set_cap_idle set_cap_arch_obj | clarsimp)+
  apply (clarsimp simp:not_idle_thread_def invs_def valid_state_def
                       cte_wp_at_caps_of_state obj_at_def)
  apply (frule(1) valid_idle_has_null_cap,simp+)
  done

lemma invoke_arch_corres:
  "arch_invocation_relation invok arch_invok
   \<Longrightarrow> dcorres (dc \<oplus> dc) (\<lambda>_. True)
   (invs and ct_active and valid_arch_inv arch_invok
         and invocation_duplicates_valid (Invocations_A.InvokeArchObject arch_invok)
         and valid_pdpt_objs)
   (Syscall_D.perform_invocation block call_m invok)
    (arch_perform_invocation arch_invok)"
  apply (clarsimp simp: arch_perform_invocation_def valid_arch_inv_def)
  apply (case_tac arch_invok)
       apply (simp_all add:arch_invocation_relation_def translate_arch_invocation_def)
       apply (clarsimp simp:liftE_def bind_assoc)
       apply (rule corres_guard_imp)
         apply (rule corres_split)
            apply (rule invoke_page_table_corres; simp)
           apply (rule corres_trivial, simp)
          apply (wp | clarsimp)+
      apply (rule corres_dummy_return_l)
      apply (rule corres_guard_imp)
        apply (rule corres_split)
           apply (rule invoke_page_directory_corres; simp)
          apply (rule corres_trivial[OF corres_free_return])
         apply (wp | clarsimp)+
     apply (rule corres_guard_imp)
       apply (rule invoke_page_corres)
       apply (wp | clarsimp simp:invocation_duplicates_valid_def)+
    apply (clarsimp split: asid_control_invocation.split)
    apply (rule corres_dummy_return_l)
    apply (rule corres_guard_imp)
      apply (rule corres_split)
         apply (rule invoke_asid_control_corres)
         apply (simp add: arch_invocation_relation_def translate_arch_invocation_def)
        apply (rule corres_trivial, simp)
       apply (wp | simp)+
   apply (clarsimp split: asid_pool_invocation.split)
   apply (rule corres_dummy_return_l)
   apply (rule corres_guard_imp)
     apply (rule corres_split)
        apply (rule invoke_asid_pool_corres)
        apply (simp add: arch_invocation_relation_def translate_arch_invocation_def)
       apply (rule corres_trivial[OF corres_free_return])
      apply (wp | clarsimp)+
  apply (rename_tac iv; case_tac iv)
  apply (clarsimp simp: perform_sgi_invocation_def transform_sgi_inv_def
                       invoke_sgi_signal_generate_def)
  apply (rule corres_add_noop_lhs)
  apply (rule corres_guard_imp)
    apply (rule corres_split)
       apply (rule dcorres_machine_op_noop)
       apply (wpsimp simp: sendSGI_def)
      apply (rule corres_inst[where P=\<top> and P'=\<top>])
      apply simp
     apply wpsimp+
  done

end

end
