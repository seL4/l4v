(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter \<open>ARM-specific definitions for abstract datatype for the abstract specification\<close>

theory ArchADT_AI
imports
  "Lib.Simulation"
  Invariants_AI
begin
context Arch begin arch_global_naming

subsection \<open>Constructing a virtual-memory view\<close>

text \<open>
  Function @{text get_pd_of_thread} takes three parameters:
  the kernel heap, the architecture-specific state, and
  a thread identifier.
  It returns the identifier of the corresponding page directory.
  Note that this function is total.
  If the traversal stops before a page directory can be found
  (e.g. because the VTable entry is not set or a reference has been invalid),
  the function returns the global kernel mapping.

  Looking up the page directory for a thread reference involves the following
  steps:

    At first, we check that the reference actually points to a TCB object in
  the kernel heap.
  If so, we check whether the vtable entry of the TCB contains a capability
  to a page directory with valid mapping data.
  Note that the mapping data might become stale.
  Hence, we have to follow the mapping data through the ASID table.
\<close>
definition
  get_pd_of_thread :: "kheap \<Rightarrow> arch_state \<Rightarrow> obj_ref \<Rightarrow> obj_ref"
where
  get_pd_of_thread_def:
  "get_pd_of_thread khp astate tcb_ref \<equiv>
   case khp tcb_ref of Some (TCB tcb) \<Rightarrow>
     (case tcb_vtable tcb of
        ArchObjectCap (PageDirectoryCap pd_ref (Some asid))
          \<Rightarrow> (case arm_asid_table astate (asid_high_bits_of asid) of
                None \<Rightarrow> arm_global_pd astate
              | Some p \<Rightarrow> (case khp p of
                            Some (ArchObj ako) \<Rightarrow>
                               if (VSRef (asid && mask asid_low_bits)
                                         (Some AASIDPool), pd_ref)
                                  \<in> vs_refs_arch ako
                                 then pd_ref
                               else arm_global_pd astate
                             | _ \<Rightarrow> arm_global_pd astate))
      | _ \<Rightarrow>  arm_global_pd astate)
   | _ \<Rightarrow>  arm_global_pd astate"


lemma VSRef_AASIDPool_in_vs_refs:
  "(VSRef (asid && mask asid_low_bits) (Some AASIDPool), r) \<in> vs_refs_arch ko =
   (\<exists>apool. ko = arch_kernel_obj.ASIDPool apool \<and>
            apool (ucast (asid && mask asid_low_bits)) = Some r)"
  apply simp
  apply (case_tac ko, simp_all add: image_def graph_of_def)
  apply (rename_tac arch_kernel_obj)
  apply (rule iffI)
   apply clarsimp
   apply (subst ucast_up_ucast_id, simp add: is_up, assumption)
  apply (intro exI conjI, assumption)
  apply (rule sym, rule ucast_ucast_len)
  apply (cut_tac and_mask_less'[of asid_low_bits asid])
   apply (simp_all add: asid_low_bits_def)
  done

context
notes vs_refs_arch_def[simp del]
begin

lemma get_pd_of_thread_def2:
  "get_pd_of_thread khp astate tcb_ref \<equiv>
        case khp tcb_ref of Some (TCB tcb) \<Rightarrow>
          (case tcb_vtable tcb of
             ArchObjectCap (PageDirectoryCap pd_ref (Some asid))
               \<Rightarrow> if (\<exists>p apool.
                        arm_asid_table astate (asid_high_bits_of asid) = Some p \<and>
                        khp p = Some (ArchObj (ASIDPool apool)) \<and>
                        apool (ucast (asid && mask asid_low_bits)) = Some pd_ref)
                    then pd_ref
                    else arm_global_pd astate
           | _ \<Rightarrow>  arm_global_pd astate)
        | _ \<Rightarrow>  arm_global_pd astate"
  apply (rule eq_reflection)
  apply (clarsimp simp: get_pd_of_thread_def
                 split: kernel_object.splits option.splits)
  apply (rename_tac tcb)
  apply (case_tac "tcb_vtable tcb",
         simp_all split: cap.splits arch_cap.splits kernel_object.splits
                         arch_kernel_obj.splits option.splits)
  apply (auto simp: VSRef_AASIDPool_in_vs_refs)
  done

lemma the_arch_cap_simp[simp]: "the_arch_cap (ArchObjectCap x) = x"
  by (simp add: the_arch_cap_def)

lemma get_pd_of_thread_vs_lookup:
  "get_pd_of_thread (kheap s) (arch_state s) tcb_ref =
   (case kheap s tcb_ref of
      Some (TCB tcb) \<Rightarrow>
        (case tcb_vtable tcb of
           ArchObjectCap (PageDirectoryCap pd_ref (Some asid)) \<Rightarrow>
             if (the (vs_cap_ref (tcb_vtable tcb)) \<rhd> pd_ref) s then pd_ref
             else arm_global_pd (arch_state s)
         | _ \<Rightarrow> arm_global_pd (arch_state s))
    | _ \<Rightarrow> arm_global_pd (arch_state s))"
  apply (clarsimp simp: get_pd_of_thread_def split: option.splits)
  apply (case_tac "the (kheap s tcb_ref)", simp_all, clarsimp)
  apply (rename_tac tcb)
  apply (case_tac "\<not> is_pd_cap (tcb_vtable tcb)")
   apply (clarsimp simp: is_pd_cap_def split: cap.split arch_cap.split)
  apply (clarsimp simp: is_pd_cap_def vs_cap_ref_def)
  apply (case_tac asid, simp_all, clarsimp)
  apply (intro conjI impI)

   apply (erule vs_lookupE)
   apply (clarsimp simp: vs_asid_refs_def split_def image_def graph_of_def)
   apply (erule rtranclE, simp)
   apply (clarsimp dest!: vs_lookup1D)
   apply (clarsimp simp: vs_refs_def vs_refs_arch_def graph_of_def
                  split: kernel_object.split_asm arch_kernel_obj.split_asm)
   apply (erule rtranclE)
    apply (clarsimp simp: up_ucast_inj_eq obj_at_def vs_refs_def vs_refs_arch_def graph_of_def
                          image_def
                   split: arch_kernel_obj.split_asm)
   apply (clarsimp dest!: vs_lookup1D)
   apply (clarsimp simp: vs_refs_def vs_refs_arch_def graph_of_def
                   split: kernel_object.split_asm arch_kernel_obj.split_asm)

  apply (erule swap)
  apply (clarsimp split: kernel_object.split_asm arch_kernel_obj.split_asm
                         option.split_asm if_split_asm)
  apply (rule vs_lookupI)
   apply (fastforce simp: vs_asid_refs_def image_def graph_of_def)
  apply (rule rtrancl_into_rtrancl)
   apply (rule rtrancl_refl)
  apply (rule vs_lookup1I, (simp add: obj_at_def vs_refs_def vs_refs_arch_def)+)
  done

end

(* NOTE: This statement would clearly be nicer for a partial function
         but later on, we really want the function to be total. *)
lemma get_pd_of_thread_eq:
  "pd_ref \<noteq> arm_global_pd (arch_state s) \<Longrightarrow>
   get_pd_of_thread (kheap s) (arch_state s) tcb_ref = pd_ref \<longleftrightarrow>
   (\<exists>tcb. kheap s tcb_ref = Some (TCB tcb) \<and>
          (\<exists>asid. tcb_vtable tcb =
                  cap.ArchObjectCap (PageDirectoryCap
                                       pd_ref (Some asid)) \<and>
                  (the (vs_cap_ref_arch (the_arch_cap (tcb_vtable tcb))) \<rhd> pd_ref) s))"
  by (auto simp: get_pd_of_thread_vs_lookup vs_cap_ref_def
          split: option.splits Structures_A.kernel_object.splits
                 cap.splits arch_cap.splits)


text \<open>Non-monad versions of @{term get_pte} and @{term get_pde}.
  The parameters are:
  \begin{description}
  \item[@{term ahp}] a heap of architecture-specific objects,
  \item[@{term pt_ref}] a page-table reference,
  \item[@{term pd_ref}] a page-directory reference, and
  \item[@{term vptr}] a virtual address.
  \end{description}
\<close>
definition
  "get_pt_entry ahp pt_ref vptr \<equiv>
   case ahp pt_ref of
     Some (PageTable pt) \<Rightarrow>
       Some (pt (ucast ((vptr >> 12) && mask 8)))
   | _ \<Rightarrow> None"
definition
  "get_pd_entry ahp pd_ref vptr \<equiv>
   case ahp pd_ref of
     Some (PageDirectory pd) \<Rightarrow> Some (pd (ucast (vptr >> 20)))
   | _ \<Rightarrow> None"

text \<open>The following function is used to extract the
  architecture-specific objects from the kernel heap\<close>
definition
  "get_arch_obj ==
   case_option None (%x. case x of ArchObj a \<Rightarrow> Some a | _ \<Rightarrow> None)"

lemma get_pd_entry_None_iff_get_pde_fail:
  "is_aligned pd_ref pd_bits \<Longrightarrow>
   get_pd_entry (\<lambda>obj. get_arch_obj (kheap s obj)) pd_ref vptr = None \<longleftrightarrow>
   get_pde (pd_ref + (vptr >> 20 << 2)) s = ({}, True)"
  apply (subgoal_tac "(vptr >> 20 << 2) && ~~ mask pd_bits = 0")
   apply (clarsimp simp: get_pd_entry_def get_arch_obj_def
                  split: option.splits Structures_A.kernel_object.splits
                         arch_kernel_obj.splits)
   apply (clarsimp simp: get_pde_def get_pd_def bind_def return_def assert_def mask_eqs
                         get_object_def simpler_gets_def fail_def split_def mask_out_sub_mask
                         gets_the_def assert_opt_def)
   apply (subgoal_tac "pd_ref + (vptr >> 20 << 2) -
                      (pd_ref + (vptr >> 20 << 2) && mask pd_bits) = pd_ref")
    apply (simp (no_asm_simp) add: fail_def return_def)
   apply clarsimp
   apply (simp add: mask_add_aligned pd_bits_def pageBits_def)
  apply (simp add: pd_bits_def pageBits_def)
  apply (simp add: and_not_mask)
  apply (simp add: shiftl_shiftr3 word_size shiftr_shiftr)
  apply (subgoal_tac "vptr >> 32 = 0", simp)
  apply (cut_tac shiftr_less_t2n'[of vptr 32 0], simp)
   apply (simp add: mask_eq_iff)
  apply (cut_tac lt2p_lem[of 32 vptr])
   apply (cut_tac word_bits_len_of, simp+)
  done

lemma get_pd_entry_Some_eq_get_pde:
  "is_aligned pd_ref pd_bits \<Longrightarrow>
   get_pd_entry (\<lambda>obj. get_arch_obj (kheap s obj)) pd_ref vptr = Some x \<longleftrightarrow>
   get_pde (pd_ref + (vptr >> 20 << 2)) s = ({(x,s)}, False)"
  apply (subgoal_tac "(vptr >> 20 << 2) && ~~ mask pd_bits = 0")
   apply (clarsimp simp: get_pd_entry_def get_arch_obj_def
                  split: option.splits Structures_A.kernel_object.splits
                         arch_kernel_obj.splits)
   apply (clarsimp simp: get_pde_def get_pd_def bind_def return_def assert_def
                         get_object_def simpler_gets_def fail_def split_def mask_out_sub_mask
                         mask_eqs gets_the_def assert_opt_def)
   apply (subgoal_tac "pd_ref + (vptr >> 20 << 2) -
                      (pd_ref + (vptr >> 20 << 2) && mask pd_bits) = pd_ref")
    apply (simp (no_asm_simp) add: fail_def return_def)
    apply (clarsimp simp: mask_add_aligned pd_bits_def pageBits_def)
    apply (cut_tac shiftl_shiftr_id[of 2 "vptr >> 20"])
      apply (simp add: word_bits_def)+
      apply (cut_tac shiftr_less_t2n'[of vptr 20 30])
        apply (simp add: word_bits_def)
        apply (simp add: mask_eq_iff)
        apply (cut_tac lt2p_lem[of 50 vptr])
         apply (cut_tac word_bits_len_of, simp+)
         apply (simp add: mask_add_aligned pd_bits_def pageBits_def)
         apply (simp add: pd_bits_def pageBits_def)
         apply (simp add: and_not_mask)
         apply (simp add: shiftl_shiftr3 word_size shiftr_shiftr)
         apply (subgoal_tac "vptr >> 32 = 0", simp)
          apply (cut_tac shiftr_less_t2n'[of vptr 32 0], simp)
            apply (simp add: mask_eq_iff)
            apply (cut_tac lt2p_lem[of 32 vptr])
             apply (cut_tac word_bits_len_of, simp+)
  done

lemma get_pt_entry_None_iff_get_pte_fail:
  "is_aligned pt_ref pt_bits \<Longrightarrow>
   get_pt_entry (\<lambda>obj. get_arch_obj (kheap s obj)) pt_ref vptr = None \<longleftrightarrow>
   get_pte (pt_ref + ((vptr >> 12) && 0xFF << 2)) s = ({}, True)"
  apply (clarsimp simp: get_pt_entry_def get_arch_obj_def
                 split: option.splits Structures_A.kernel_object.splits
                        arch_kernel_obj.splits)
  apply (clarsimp simp: get_pte_def get_pt_def bind_def return_def assert_def mask_eqs
                        get_object_def simpler_gets_def fail_def split_def mask_out_sub_mask
                        gets_the_def assert_opt_def)
  apply (subgoal_tac "pt_ref + ((vptr >> 12) && 0xFF << 2) -
                      (pt_ref + ((vptr >> 12) && 0xFF << 2) && mask pt_bits) =
                      pt_ref")
   apply (simp (no_asm_simp) add: fail_def return_def)
   apply clarsimp
  apply (simp add: mask_add_aligned pt_bits_def pageBits_def)
  apply (cut_tac and_mask_shiftl_comm[of 8 2 "vptr >> 12"])
   apply (simp_all add: word_size mask_def)
  done

lemma get_pt_entry_Some_eq_get_pte:
  "is_aligned pt_ref pt_bits \<Longrightarrow>
   get_pt_entry (\<lambda>obj. get_arch_obj (kheap s obj)) pt_ref vptr = Some x \<longleftrightarrow>
   get_pte (pt_ref + ((vptr >> 12) && mask 8 << 2)) s = ({(x,s)}, False)"
  apply (clarsimp simp: get_pt_entry_def get_arch_obj_def
                 split: option.splits Structures_A.kernel_object.splits
                        arch_kernel_obj.splits)
  apply (clarsimp simp: get_pte_def get_pt_def bind_def return_def
                        assert_def get_object_def simpler_gets_def fail_def split_def
                        mask_out_sub_mask mask_eqs gets_the_def assert_opt_def)
  apply (subgoal_tac "pt_ref + ((vptr >> 12) && mask 8 << 2) -
                      (pt_ref + ((vptr >> 12) && mask 8 << 2) && mask pt_bits) =
                      pt_ref")
   apply (simp (no_asm_simp) add: fail_def return_def)
   apply (clarsimp simp: mask_add_aligned pt_bits_def pageBits_def
                         word_size and_mask_shiftr_comm and_mask_shiftl_comm shiftr_shiftr)
   apply (cut_tac shiftl_shiftr_id[of 2 "vptr >> 12"])
     apply (simp add: word_bits_def)+
   apply (cut_tac shiftr_less_t2n'[of vptr 12 30])
     apply (simp add: word_bits_def)
    apply (simp add: mask_eq_iff)
    apply (cut_tac lt2p_lem[of 32 vptr])
     apply (cut_tac word_bits_len_of, simp+)
  apply (simp add: mask_add_aligned pt_bits_def pageBits_def word_size and_mask_shiftl_comm)
  done

definition
  "get_pt_info ahp pt_ref vptr \<equiv>
   case get_pt_entry ahp pt_ref vptr of
     Some (SmallPagePTE base attrs rights) \<Rightarrow> Some (base, 12, attrs, rights)
   | Some (LargePagePTE base attrs rights) \<Rightarrow> Some (base, 16, attrs, rights)
   | _ \<Rightarrow> None"

text \<open>
  @{text get_page_info} takes the architecture-specific part of the kernel heap,
  a reference to the page directory, and a virtual memory address.
  It returns a tuple containing
  (a) the physical address, where the associated page table starts,
  (b) the page table's size in bits, and
  (c) the page attributes (cachable, XNever, etc)
  (d) the access rights (a subset of @{term "{AllowRead, AllowWrite}"}).
\<close>
definition
  get_page_info :: "(obj_ref \<rightharpoonup> arch_kernel_obj) \<Rightarrow> obj_ref \<Rightarrow>
                    word32 \<rightharpoonup> (word32 \<times> nat \<times> vm_attributes \<times> vm_rights)"
where
  get_page_info_def:
  "get_page_info ahp pd_ref vptr \<equiv>
   case get_pd_entry ahp pd_ref vptr of
     Some (PageTablePDE p _ _) \<Rightarrow>
       get_pt_info ahp (ptrFromPAddr p) vptr
   | Some (SectionPDE base attrs _ rights) \<Rightarrow> Some (base, 20, attrs, rights)
   | Some (SuperSectionPDE base attrs rights) \<Rightarrow> Some (base,24, attrs, rights)
   | _ \<Rightarrow> None"

lemma pd_shifting':
 "is_aligned pd pd_bits \<Longrightarrow> (pd + (vptr >> 20 << 2) && ~~ mask pd_bits) = (pd::word32)"
  unfolding pd_bits_def pageBits_def
  by (rule pd_shifting_gen; simp add: word_size)

lemma lookup_pt_slot_fail:
  "is_aligned pd pd_bits \<Longrightarrow>
   lookup_pt_slot pd vptr s = ({},True) \<longleftrightarrow>
   (\<forall>pdo. kheap s pd \<noteq> Some (ArchObj (PageDirectory pdo)))"
  apply (frule pd_shifting'[of _ vptr])
  by (fastforce simp: lookup_pt_slot_def lookup_pd_slot_def liftE_def bindE_def
                      returnOk_def lift_def bind_def split_def throwError_def return_def
                      get_pde_def get_pd_def Union_eq get_object_def simpler_gets_def
                      assert_def fail_def mask_eqs gets_the_def assert_opt_def
               split: sum.splits if_split_asm Structures_A.kernel_object.splits
                      arch_kernel_obj.splits pde.splits option.splits)

(* FIXME: Lemma can be found in ArchAcc_R *)
lemma shiftr_shiftl_mask_pd_bits:
  "(((vptr :: word32) >> 20) << 2) && mask pd_bits = (vptr >> 20) << 2"
  apply (rule iffD2 [OF mask_eq_iff_w2p])
   apply (simp add: pd_bits_def pageBits_def word_size)
  apply (rule shiftl_less_t2n)
   apply (simp_all add: pd_bits_def word_bits_def pageBits_def word_size)
  apply (cut_tac shiftr_less_t2n'[of vptr 20 12])
    apply simp
   apply (simp add: mask_eq_iff)
   apply (cut_tac lt2p_lem[of 32 vptr], simp)
   apply (cut_tac word_bits_len_of, simp+)
  done

lemma lookup_pt_slot_no_fail:
  "is_aligned pd pd_bits \<Longrightarrow>
   kheap s pd = Some (ArchObj (PageDirectory pdo)) \<Longrightarrow>
   lookup_pt_slot pd vptr s =
   (case pdo (ucast (vptr >> 20)) of
      InvalidPDE \<Rightarrow>
        ({(Inl (ExceptionTypes_A.MissingCapability 20),s)},False)
    | PageTablePDE p _ _ \<Rightarrow>
        ({(Inr (ptrFromPAddr p + ((vptr >> 12) && 0xFF << 2)),s)},
         False)
    | SectionPDE _ _ _ _ \<Rightarrow>
        ({(Inl (ExceptionTypes_A.MissingCapability 20),s)},False)
    | SuperSectionPDE _ _ _ \<Rightarrow>
        ({(Inl (ExceptionTypes_A.MissingCapability 20),s)},False)  )"
  apply (frule pd_shifting'[of _ vptr])
  apply (cut_tac shiftr_shiftl_mask_pd_bits[of vptr])
  apply (subgoal_tac "vptr >> 20 << 2 >> 2 = vptr >> 20")
   defer
   apply (rule shiftl_shiftr_id)
    apply (simp_all add: word_bits_def)
   apply (cut_tac shiftr_less_t2n'[of vptr 20 30])
     apply (simp add: word_bits_def)
    apply (simp add: mask_eq_iff)
    apply (cut_tac lt2p_lem[of 32 vptr])
     apply (cut_tac word_bits_len_of, simp_all)
  by (clarsimp simp: lookup_pt_slot_def lookup_pd_slot_def liftE_def bindE_def
                     returnOk_def lift_def bind_def split_def throwError_def return_def
                     get_pde_def get_pd_def Union_eq get_object_def simpler_gets_def
                     assert_def fail_def mask_add_aligned gets_the_def assert_opt_def
              split: sum.splits if_split_asm kernel_object.splits arch_kernel_obj.splits
                     pde.splits)

lemma get_page_info_pte:
  "is_aligned pd_ref pd_bits \<Longrightarrow>
   lookup_pt_slot pd_ref vptr s = ({(Inr x,s)},False) \<Longrightarrow>
   is_aligned (x - ((vptr >> 12) && 0xFF << 2)) pt_bits \<Longrightarrow>
   get_pte x s = ({(pte,s)},False) \<Longrightarrow>
   get_page_info (\<lambda>obj. get_arch_obj (kheap s obj)) pd_ref vptr =
   (case pte of
     SmallPagePTE base attrs rights \<Rightarrow> Some (base, 12, attrs, rights)
   | LargePagePTE base attrs rights \<Rightarrow> Some (base, 16, attrs, rights)
   | _ \<Rightarrow> None)"
apply (clarsimp simp add: get_page_info_def get_pd_entry_def
                split: option.splits)
apply (intro conjI impI allI)
  apply (frule lookup_pt_slot_fail[of _ vptr s],
         clarsimp simp add: get_arch_obj_def)
 apply (frule lookup_pt_slot_fail[of _ vptr s],
        clarsimp simp add: get_arch_obj_def)
apply (frule lookup_pt_slot_fail[of _ vptr s],
       clarsimp simp add: get_arch_obj_def)
apply (frule (1) lookup_pt_slot_no_fail[where vptr=vptr])
apply (clarsimp split: pde.splits option.splits)
apply (clarsimp simp add: get_pt_info_def split: option.splits)
apply (intro conjI impI)
 apply (drule get_pt_entry_None_iff_get_pte_fail[where s=s and vptr=vptr])
 apply (simp add: pt_bits_def pageBits_def mask_def)
apply clarsimp
apply (drule_tac x=x2 in get_pt_entry_Some_eq_get_pte[where s=s and vptr=vptr])
apply (simp add: pt_bits_def pageBits_def mask_def)
done

lemma get_page_info_section:
  "is_aligned pd_ref pd_bits \<Longrightarrow>
   get_pde (lookup_pd_slot pd_ref vptr) s =
     ({(SectionPDE base attrs X rights, s)},False) \<Longrightarrow>
   get_page_info (\<lambda>obj. get_arch_obj (kheap s obj)) pd_ref vptr =
     Some (base, 20, attrs, rights)"
apply (simp add: lookup_pd_slot_def get_page_info_def split: option.splits)
apply (intro conjI impI allI)
 apply (drule get_pd_entry_None_iff_get_pde_fail[where s=s and vptr=vptr])
 apply (simp split: option.splits)
apply (drule_tac x=x2 in get_pd_entry_Some_eq_get_pde[where s=s and vptr=vptr])
apply clarsimp
done

lemma get_page_info_super_section:
  "is_aligned pd_ref pd_bits \<Longrightarrow>
   get_pde (lookup_pd_slot pd_ref vptr) s =
     ({(SuperSectionPDE base attrs rights,s)},False) \<Longrightarrow>
   get_page_info (\<lambda>obj. get_arch_obj (kheap s obj)) pd_ref vptr =
     Some (base, 24, attrs, rights)"
apply (simp add: lookup_pd_slot_def get_page_info_def split: option.splits)
apply (intro conjI impI allI)
 apply (drule get_pd_entry_None_iff_get_pde_fail[where s=s and vptr=vptr])
 apply (simp split: option.splits)
apply (drule_tac x=x2 in get_pd_entry_Some_eq_get_pde[where s=s and vptr=vptr])
apply clarsimp
done

text \<open>
  Both functions, @{text ptable_lift} and @{text vm_rights},
  take a kernel state and a virtual address.
  The former returns the physical address, the latter the associated rights.
\<close>
definition
  ptable_lift :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> word32 \<rightharpoonup> word32" where
  "ptable_lift tcb s \<equiv> \<lambda>addr.
   case_option None (\<lambda>(base, bits, rights). Some (base + (addr && mask bits)))
     (get_page_info (\<lambda>obj. get_arch_obj (kheap s obj))
        (get_pd_of_thread (kheap s) (arch_state s) tcb) addr)"
definition
  ptable_rights :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> word32 \<Rightarrow> vm_rights" where
 "ptable_rights tcb s \<equiv> \<lambda>addr.
  case_option {} (snd o snd o snd)
     (get_page_info (\<lambda>obj. get_arch_obj (kheap s obj))
        (get_pd_of_thread (kheap s) (arch_state s) tcb) addr)"

end
end
