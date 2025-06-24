(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Proofs about untyped invocations. *)

theory Untyped_R
imports Detype_R Invocations_R InterruptAcc_R
begin

unbundle l4v_word_context

context begin interpretation Arch . (*FIXME: arch-split*)

primrec
  untypinv_relation :: "Invocations_A.untyped_invocation \<Rightarrow>
                        Invocations_H.untyped_invocation \<Rightarrow> bool"
where
  "untypinv_relation
     (Invocations_A.Retype c reset ob n ao n2 cl d) x = (\<exists>ao'. x =
     (Invocations_H.Retype (cte_map c) reset ob n ao' n2
       (map cte_map cl) d)
           \<and> ao = APIType_map2 (Inr ao'))"

primrec
  valid_untyped_inv_wcap' :: "Invocations_H.untyped_invocation
    \<Rightarrow> capability option \<Rightarrow> kernel_state \<Rightarrow> bool"
where
 "valid_untyped_inv_wcap' (Invocations_H.Retype slot reset ptr_base ptr ty us slots d)
   = (\<lambda>co s. \<exists>sz idx. (cte_wp_at' (\<lambda>cte. cteCap cte = UntypedCap d ptr_base sz idx
              \<and> (co = None \<or> co = Some (cteCap cte))) slot s
          \<and> range_cover ptr sz (APIType_capBits ty us) (length slots)
          \<and> ((\<not> reset \<and> idx \<le> unat (ptr - ptr_base)) \<or> (reset \<and> ptr = ptr_base))
          \<and> (ptr && ~~ mask sz) = ptr_base)
          \<and> (reset \<longrightarrow> descendants_of' slot (ctes_of s) = {})
          \<and> distinct (slot # slots)
          \<and> (ty = APIObjectType ArchTypes_H.CapTableObject \<longrightarrow> us > 0)
          \<and> (ty = APIObjectType ArchTypes_H.Untyped \<longrightarrow> minUntypedSizeBits \<le> us \<and> us \<le> maxUntypedSizeBits)
          \<and> (\<forall>slot \<in> set slots. cte_wp_at' (\<lambda>c. cteCap c = NullCap) slot s)
          \<and> (\<forall>slot \<in> set slots. ex_cte_cap_to' slot s)
          \<and> sch_act_simple s \<and> 0 < length slots
          \<and> (d \<longrightarrow> ty = APIObjectType ArchTypes_H.Untyped \<or> isFrameType ty)
          \<and> APIType_capBits ty us \<le> maxUntypedSizeBits)"

abbreviation
  "valid_untyped_inv' ui \<equiv> valid_untyped_inv_wcap' ui None"

lemma valid_untyped_inv_wcap':
  "valid_untyped_inv' ui
    = (\<lambda>s. \<exists>sz idx. valid_untyped_inv_wcap' ui
        (Some (case ui of Invocations_H.Retype slot reset ptr_base ptr ty us slots d
            \<Rightarrow> UntypedCap d (ptr && ~~ mask sz) sz idx)) s)"
  by (cases ui, auto simp: fun_eq_iff cte_wp_at_ctes_of)

lemma whenE_rangeCheck_eq:
  "(rangeCheck (x :: 'a :: {linorder, integral}) y z) =
    (whenE (x < fromIntegral y \<or> fromIntegral z < x)
      (throwError (RangeError (fromIntegral y) (fromIntegral z))))"
  by (simp add: rangeCheck_def unlessE_whenE linorder_not_le[symmetric])

lemma APIType_map2_CapTable[simp]:
  "(APIType_map2 ty = Structures_A.CapTableObject)
    = (ty = Inr (APIObjectType ArchTypes_H.CapTableObject))"
  by (simp add: APIType_map2_def
         split: sum.split AARCH64_H.object_type.split
                apiobject_type.split
                kernel_object.split arch_kernel_object.splits)

lemma alignUp_H[simp]:
  "Untyped_H.alignUp = More_Word_Operations.alignUp"
  apply (rule ext)+
  apply (clarsimp simp:Untyped_H.alignUp_def More_Word_Operations.alignUp_def mask_def)
  done

(* FIXME: MOVE *)
lemma corres_check_no_children:
  "corres (\<lambda>x y. x = y) (cte_at slot)
     (pspace_aligned' and pspace_distinct' and valid_mdb' and
      cte_wp_at' (\<lambda>_. True) (cte_map slot))
     (const_on_failure x
        (doE z \<leftarrow> ensure_no_children slot;
             returnOk y
         odE))
     (constOnFailure x
        (doE z \<leftarrow> ensureNoChildren (cte_map slot);
             returnOk y
         odE))"
  apply (clarsimp simp:const_on_failure_def constOnFailure_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split_catch[where E = dc and E'=dc])
       apply (rule corres_guard_imp[OF corres_splitEE])
            apply (rule ensureNoChildren_corres)
            apply simp
           apply (rule corres_returnOkTT)
           apply simp
          apply wp+
        apply simp+
     apply (clarsimp simp:dc_def,wp)+
   apply simp
  apply simp
  done

lemma mapM_x_stateAssert:
  "mapM_x (\<lambda>x. stateAssert (f x) (ss x)) xs
    = stateAssert (\<lambda>s. \<forall>x \<in> set xs. f x s) []"
  apply (induct xs)
   apply (simp add: mapM_x_Nil)
  apply (simp add: mapM_x_Cons)
  apply (simp add: fun_eq_iff stateAssert_def bind_assoc exec_get assert_def)
  done

lemma mapM_locate_eq:
    "isCNodeCap cap
    \<Longrightarrow> mapM (\<lambda>x. locateSlotCap cap x) xs
        = (do stateAssert (\<lambda>s. case gsCNodes s (capUntypedPtr cap) of None \<Rightarrow> xs = [] | Some n
                \<Rightarrow> \<forall>x \<in> set xs. n = capCNodeBits cap \<and> x < 2 ^ n) [];
            return (map (\<lambda>x. (capCNodePtr cap) + 2 ^ cte_level_bits * x) xs) od)"
  apply (clarsimp simp: isCap_simps)
  apply (simp add: locateSlot_conv objBits_simps cte_level_bits_def
                   liftM_def[symmetric] mapM_liftM_const isCap_simps)
  apply (simp add: liftM_def mapM_discarded mapM_x_stateAssert)
  apply (intro bind_cong refl arg_cong2[where f=stateAssert] ext)
  apply (simp add: isCap_simps split: option.split)
  done

lemmas is_frame_type_defs = is_frame_type_def isFrameType_def arch_is_frame_type_def

lemma is_frame_type_isFrameType_eq[simp]:
  "(is_frame_type (APIType_map2 (Inr (toEnum (unat arg0))))) =
   (Types_H.isFrameType (toEnum (unat arg0)))"
  by (simp add: APIType_map2_def is_frame_type_defs split: apiobject_type.splits object_type.splits)+

(* FIXME: remove *)
lemmas APIType_capBits = objSize_eq_capBits

(* FIXME: move *)
lemma corres_whenE_throw_merge:
  "corres r P P' f (doE _ \<leftarrow> whenE (A \<or> B) (throwError e); h odE)
  \<Longrightarrow> corres r P P' f (doE _ \<leftarrow> whenE A (throwError e); _ \<leftarrow>  whenE B (throwError e); h odE)"
  by (auto simp: whenE_def split: if_splits)

lemma decodeUntypedInvocation_corres:
  assumes cap_rel: "list_all2 cap_relation cs cs'"
  shows "corres
        (ser \<oplus> untypinv_relation)
        (invs and cte_wp_at ((=) (cap.UntypedCap d w n idx)) slot and (\<lambda>s. \<forall>x \<in> set cs. s \<turnstile> x))
        (invs'
          and (\<lambda>s. \<forall>x \<in> set cs'. s \<turnstile>' x))
        (decode_untyped_invocation label args slot (cap.UntypedCap d w n idx) cs)
        (decodeUntypedInvocation label args (cte_map slot)
          (capability.UntypedCap d w n idx) cs')"
proof (cases "6 \<le> length args \<and> cs \<noteq> []
                \<and> gen_invocation_type label = UntypedRetype")
  case False
  show ?thesis using False cap_rel
    apply (clarsimp simp: decode_untyped_invocation_def
                          decodeUntypedInvocation_def
                          whenE_whenE_body unlessE_whenE
               split del: if_split cong: list.case_cong)
    apply (auto split: list.split)
    done
next
  case True
  have val_le_length_Cons: (* clagged from Tcb_R *)
    "\<And>n xs. n \<noteq> 0 \<Longrightarrow> (n \<le> length xs) = (\<exists>y ys. xs = y # ys \<and> (n - 1) \<le> length ys)"
    apply (case_tac xs, simp_all)
    apply (case_tac n, simp_all)
    done

  obtain arg0 arg1 arg2 arg3 arg4 arg5 argsmore cap cap' csmore csmore'
    where args: "args = arg0 # arg1 # arg2 # arg3 # arg4 # arg5 # argsmore"
      and   cs: "cs = cap # csmore"
      and  cs': "cs' = cap' # csmore'"
      and crel: "cap_relation cap cap'"
    using True cap_rel
    by (clarsimp simp: neq_Nil_conv list_all2_Cons1 val_le_length_Cons)

  have il: "gen_invocation_type label = UntypedRetype"
    using True by simp

  have word_unat_power2:
    "\<And>bits. \<lbrakk> bits < 64 \<or> bits < word_bits \<rbrakk> \<Longrightarrow> unat (2 ^ bits :: machine_word) = 2 ^ bits"
    by (simp add: word_bits_def)

  have P: "\<And>P. corres (ser \<oplus> dc) \<top> \<top>
                  (whenE P (throwError ExceptionTypes_A.syscall_error.TruncatedMessage))
                  (whenE P (throwError Fault_H.syscall_error.TruncatedMessage))"
    by (simp add: whenE_def returnOk_def)
  have Q: "\<And>v. corres (ser \<oplus> (\<lambda>a b. APIType_map2 (Inr (toEnum (unat v))) = a)) \<top> \<top>
                  (data_to_obj_type v)
                  (whenE (fromEnum (maxBound :: AARCH64_H.object_type) < unat v)
                       (throwError (Fault_H.syscall_error.InvalidArgument 0)))"
    apply (simp only: data_to_obj_type_def returnOk_bindE fun_app_def)
    apply (simp add: maxBound_def enum_apiobject_type
                     fromEnum_def whenE_def)
    apply (simp add: returnOk_def APIType_map2_def toEnum_def
                     enum_apiobject_type enum_object_type)
    apply (intro conjI impI)
     apply (subgoal_tac "unat v - 5 > 5")
      apply (simp add: arch_data_to_obj_type_def)
     apply simp
    apply (subgoal_tac "\<exists>n. unat v = n + 5")
     apply (clarsimp simp: arch_data_to_obj_type_def returnOk_def)
    apply (rule_tac x="unat v - 5" in exI)
    apply arith
    done
  have S: "\<And>x (y :: ('g :: len) word) (z :: 'g word) bits. \<lbrakk> bits < len_of TYPE('g); x < 2 ^ bits \<rbrakk> \<Longrightarrow> toEnum x = (of_nat x :: 'g word)"
    apply (rule toEnum_of_nat)
    apply (erule order_less_trans)
    apply simp
    done
  obtain xs where xs: "xs = [unat arg4..<unat arg4 + unat arg5]"
    by simp
  (* FIXME AARCH64: fix name *)
  have YUCK: "\<And>ref bits.
                  \<lbrakk> is_aligned ref bits;
                    Suc (unat arg4 + unat arg5 - Suc 0) \<le> 2 ^ bits;
                    bits < 64; 1 \<le> arg4 + arg5;
                    arg4 \<le> arg4 + arg5 \<rbrakk> \<Longrightarrow>
              (map (\<lambda>x. ref + 2 ^ cte_level_bits * x) [arg4 .e. arg4 + arg5 - 1])
              = map cte_map
               (map (Pair ref)
                 (map (nat_to_cref bits) xs))"
    apply (subgoal_tac "Suc (unat (arg4 + arg5 - 1)) = unat arg4 + unat arg5")
     apply (simp add: upto_enum_def xs del: upt.simps)
     apply (clarsimp simp: cte_map_def)
     apply (subst of_bl_nat_to_cref)
       apply simp
      apply (simp add: word_bits_def)
     apply (subst S)
       apply simp
      apply simp
     apply (simp add: cte_level_bits_def shiftl_t2n)
    apply unat_arith
    done
  have another:
    "\<And>bits a. \<lbrakk> (a::machine_word) \<le> 2 ^ bits; bits < word_bits\<rbrakk>
       \<Longrightarrow> 2 ^ bits - a = of_nat (2 ^ bits - unat a)"
    apply (subst of_nat_diff)
     apply (subst (asm) word_le_nat_alt)
     apply (simp add: word_unat_power2)
    apply simp
    done
   have ty_size:
   "\<And>x y. (obj_bits_api (APIType_map2 (Inr x)) y) = (Types_H.getObjectSize x y)"
      apply (clarsimp simp:obj_bits_api_def APIType_map2_def getObjectSize_def simp del: APIType_capBits)
      apply (case_tac x)
       apply (simp_all add:arch_kobj_size_def default_arch_object_def pageBits_def ptBits_def)
      apply (rename_tac apiobject_type)
      apply (case_tac apiobject_type)
       apply (simp_all add: apiGetObjectSize_def tcbBlockSizeBits_def epSizeBits_def
                            ntfnSizeBits_def slot_bits_def cteSizeBits_def bit_simps)
      done
    obtain if_res where if_res_def: "\<And>reset. if_res reset = (if reset then 0 else idx)"
      by auto
    have if_res_2n:
      "\<And>d res. (\<exists>s. s \<turnstile> cap.UntypedCap d w n idx) \<Longrightarrow> if_res res \<le> 2 ^ n"
      by (simp add: if_res_def valid_cap_def)

  note word_unat_power [symmetric, simp del]
  show ?thesis
    apply (rule corres_name_pre)
    apply clarsimp
    apply (subgoal_tac "cte_wp_at' (\<lambda>cte. cteCap cte = (capability.UntypedCap d w n idx)) (cte_map slot) s'")
    prefer 2
     apply (drule state_relation_pspace_relation)
      apply (case_tac slot)
      apply simp
     apply (drule(1) pspace_relation_cte_wp_at)
      apply fastforce+
    apply (clarsimp simp:cte_wp_at_caps_of_state)
    apply (frule caps_of_state_valid_cap[unfolded valid_cap_def])
     apply fastforce
    apply (clarsimp simp:cap_aligned_def)
(* ugh yuck. who likes a word proof? furthermore, some more restriction of
   the returnOk_bindE stuff needs to be done in order to give you a single
   target to do the word proof against or else it needs repeating. ugh.
   maybe could seperate out the equality Isar-style? *)
    apply (simp add: decodeUntypedInvocation_def decode_untyped_invocation_def
                     args cs cs' xs[symmetric] il whenE_rangeCheck_eq
                     cap_case_CNodeCap unlessE_whenE case_bool_If lookupTargetSlot_def
                     untypedBits_defs untyped_min_bits_def untyped_max_bits_def
                del: upt.simps
          split del: if_split
               cong: if_cong list.case_cong)
    apply (rule corres_guard_imp)
      apply (rule corres_splitEE[OF Q])
        apply (rule corres_whenE_throw_merge)
        apply (rule whenE_throwError_corres)
          apply (simp add: word_bits_def word_size)
         apply (clarsimp simp: word_size word_bits_def fromIntegral_def ty_size
                          toInteger_nat fromInteger_nat wordBits_def)
         apply (simp add: not_le)
        apply (rule whenE_throwError_corres, simp)
         apply (clarsimp simp: fromAPIType_def)
        apply (rule whenE_throwError_corres, simp)
         apply (clarsimp simp: fromAPIType_def)
        apply (rule_tac r' = "\<lambda>cap cap'. cap_relation cap cap'"
                in corres_splitEE[OF corres_if])
             apply simp
            apply (rule corres_returnOkTT)
            apply (rule crel)
           apply simp
           apply (rule corres_splitEE[OF lookupSlotForCNodeOp_corres])
               apply (rule crel)
              apply simp
             apply simp
             apply (rule getSlotCap_corres,simp)
            apply wp+
          apply (rule_tac corres_split_norE)
             apply (rule corres_if)
               apply simp
              apply (rule corres_returnOkTT,clarsimp)
             apply (rule corres_trivial)
             apply (clarsimp simp: fromAPIType_def lookup_failure_map_def)
            apply (rule_tac F="is_cnode_cap rva \<and> cap_aligned rva" in corres_gen_asm)
            apply (subgoal_tac "is_aligned (obj_ref_of rva) (bits_of rva) \<and> bits_of rva < 64")
             prefer 2
             apply (clarsimp simp: is_cap_simps bits_of_def cap_aligned_def word_bits_def
                                   is_aligned_weaken)
            apply (rule whenE_throwError_corres)
              apply (clarsimp simp:Kernel_Config.retypeFanOutLimit_def is_cap_simps bits_of_def)+
             apply (simp add: unat_arith_simps(2) unat_2p_sub_1 word_bits_def)
            apply (rule whenE_throwError_corres)
              apply (clarsimp simp:Kernel_Config.retypeFanOutLimit_def is_cap_simps bits_of_def)+
             apply (simp add: unat_eq_0 word_less_nat_alt)
            apply (rule whenE_throwError_corres)
              apply (clarsimp simp:Kernel_Config.retypeFanOutLimit_def is_cap_simps bits_of_def)+
             apply (clarsimp simp:toInteger_word unat_arith_simps(2) cap_aligned_def)
             apply (subst unat_sub)
              apply (simp add: linorder_not_less word_le_nat_alt)
             apply (fold neq0_conv)
             apply (simp add: unat_eq_0 cap_aligned_def)
            apply (clarsimp simp:fromAPIType_def)
            apply (clarsimp simp:liftE_bindE mapM_locate_eq)
            apply (subgoal_tac "unat (arg4 + arg5) = unat arg4 + unat arg5")
             prefer 2
             apply (clarsimp simp:not_less)
             apply (subst unat_word_ariths(1))
             apply (rule mod_less)
             apply (unfold word_bits_len_of)[1]
             apply (subgoal_tac "2 ^ bits_of rva < (2 :: nat) ^ word_bits")
              apply arith
             apply (rule power_strict_increasing, simp add: word_bits_conv)
             apply simp
            apply (rule_tac P'="valid_cap rva" in corres_stateAssert_implied)
             apply (frule_tac bits2 = "bits_of rva" in YUCK)
                 apply (simp)
                apply (simp add: word_bits_conv)
               apply (simp add: word_le_nat_alt)
              apply (simp add: word_le_nat_alt)
             apply (simp add:liftE_bindE[symmetric] free_index_of_def)
             apply (rule corres_split_norE)
                apply (clarsimp simp:is_cap_simps  simp del:ser_def)
                apply (simp add: mapME_x_map_simp  del: ser_def)
                apply (rule_tac P = "valid_cap (cap.CNodeCap r bits g) and invs" in corres_guard_imp [where P' = invs'])
                  apply (rule mapME_x_corres_inv [OF _ _ _ refl])
                    apply (simp del: ser_def)
                    apply (rule ensureEmptySlot_corres)
                    apply (clarsimp simp: is_cap_simps)
                   apply (simp, wp)
                  apply (simp, wp)
                  apply clarsimp
                 apply (clarsimp simp add: xs is_cap_simps bits_of_def valid_cap_def)
                 apply (erule cap_table_at_cte_at)
                 apply (simp add: nat_to_cref_def word_bits_conv)
                apply simp
               apply (subst liftE_bindE)+
               apply (rule corres_split_eqr[OF corres_check_no_children])
                 apply (simp only: free_index_of_def cap.simps if_res_def[symmetric])
                 apply (rule_tac F="if_res reset \<le> 2 ^ n" in corres_gen_asm)
                 apply (rule whenE_throwError_corres)
                   apply (clarsimp simp:shiftL_nat word_less_nat_alt shiftr_div_2n'
                              split del: if_split)+
                  apply (simp add: word_of_nat_le another)
                  apply (drule_tac x = "if_res reset" in unat_of_nat64[OF le_less_trans])
                   apply (simp add:ty_size shiftR_nat)+
                  apply (simp add:unat_of_nat64 le_less_trans[OF div_le_dividend]
                                  le_less_trans[OF diff_le_self])
                 apply (rule whenE_throwError_corres)
                   apply (clarsimp)
                  apply (clarsimp simp: fromAPIType_def)
                 apply (rule corres_returnOkTT)
                 apply (clarsimp simp:ty_size getFreeRef_def get_free_ref_def is_cap_simps)
                apply simp
                apply (strengthen if_res_2n, wp)
               apply simp
               apply wp
              apply (wp mapME_x_inv_wp
                        validE_R_validE[OF valid_validE_R[OF ensure_empty_inv]]
                        validE_R_validE[OF valid_validE_R[OF ensureEmpty_inv]])+
            apply (clarsimp simp: is_cap_simps valid_cap_simps
                                  cap_table_at_gsCNodes bits_of_def
                                  linorder_not_less)
            apply (erule order_le_less_trans)
            apply (rule word_leq_le_minus_one)
             apply (simp add: word_le_nat_alt)
            apply (simp add: unat_arith_simps)
           apply wpsimp+
          apply (rule hoare_strengthen_post[where Q'="\<lambda>r. invs and valid_cap r and cte_at slot"])
           apply wp+
          apply (clarsimp simp: is_cap_simps bits_of_def cap_aligned_def
                                valid_cap_def word_bits_def)
          apply (frule caps_of_state_valid_cap, clarsimp+)
          apply (strengthen refl exI[mk_strg I E] exI[where x=d])+
          apply simp
         apply wp+
         apply (rule hoare_strengthen_post[where Q'="\<lambda>r. invs' and cte_at' (cte_map slot)"])
          apply wp+
         apply (clarsimp simp:invs_pspace_aligned' invs_pspace_distinct')
        apply (wp whenE_throwError_wp | wp (once) hoare_drop_imps)+
     apply (clarsimp simp: invs_valid_objs' invs_pspace_aligned' invs_pspace_distinct'
                           cte_wp_at_caps_of_state cte_wp_at_ctes_of )
     apply (clarsimp simp: invs_valid_objs invs_psp_aligned)
     apply (frule caps_of_state_valid_cap, clarsimp+)
     apply (strengthen refl[where t=True] refl exI[mk_strg I E] exI[where x=d])+
     apply (clarsimp simp: is_cap_simps valid_cap_def bits_of_def cap_aligned_def
                           cte_level_bits_def word_bits_conv)
    apply (clarsimp simp: invs_valid_objs' invs_pspace_aligned' invs_pspace_distinct'
                          cte_wp_at_caps_of_state cte_wp_at_ctes_of )
    done
qed

lemma decodeUntyped_inv[wp]:
  "\<lbrace>P\<rbrace> decodeUntypedInvocation label args slot (UntypedCap d w n idx) cs \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: decodeUntypedInvocation_def whenE_def
                   split_def unlessE_def Let_def
              split del: if_split cong: if_cong list.case_cong)
  apply (rule hoare_pre)
   apply (wp mapME_x_inv_wp hoare_drop_imps constOnFailure_wp
             mapM_wp'
               | wpcw
               | simp add: lookupTargetSlot_def locateSlot_conv)+
  done

declare inj_Pair[simp]

declare upt_Suc[simp del]

lemma descendants_of_cte_at':
  "\<lbrakk>p \<in> descendants_of' x (ctes_of s); valid_mdb' s\<rbrakk> \<Longrightarrow> cte_wp_at' (\<lambda>_. True) p s"
  by (clarsimp simp: descendants_of'_def cte_wp_at_ctes_of dest!: subtree_target_Some)

lemma ctes_of_ko:
  "valid_cap' cap s \<Longrightarrow>
   isUntypedCap cap \<or>
   (\<forall>ptr\<in>capRange cap. \<exists>optr ko. ksPSpace s optr = Some ko \<and> ptr \<in> obj_range' optr ko)"
  apply (case_tac cap; simp add: isCap_simps capRange_def)
       \<comment> \<open>TCB case\<close>
       apply (clarsimp simp: valid_cap'_def obj_at'_def)
       apply (intro exI conjI, assumption)
       apply (clarsimp simp: objBits_def obj_range'_def mask_def add_diff_eq
                       dest!: projectKO_opt_tcbD simp: objBitsKO_def)
      \<comment> \<open>NTFN case\<close>
      apply (clarsimp simp: valid_cap'_def obj_at'_def)
      apply (intro exI conjI, assumption)
      apply (clarsimp simp: objBits_def mask_def add_diff_eq obj_range'_def objBitsKO_def)
     \<comment> \<open>EP case\<close>
     apply (clarsimp simp: valid_cap'_def obj_at'_def)
     apply (intro exI conjI, assumption)
     apply (clarsimp simp: objBits_def mask_def add_diff_eq obj_range'_def objBitsKO_def)
    \<comment> \<open>Zombie case\<close>
    apply (rename_tac word zombie_type nat)
    apply (case_tac zombie_type)
     apply (clarsimp simp: valid_cap'_def obj_at'_def)
     apply (intro exI conjI, assumption)
     apply (clarsimp simp: mask_def add_ac objBits_simps' obj_range'_def dest!: projectKO_opt_tcbD)
    apply (clarsimp simp: valid_cap'_def obj_at'_def capAligned_def objBits_simps')
    apply (frule_tac ptr=ptr and sz=cte_level_bits
             in nasty_range [where 'a=machine_word_len, folded word_bits_def])
       apply (simp add: cte_level_bits_def)+
    apply clarsimp
    apply (drule_tac x=idx in spec)
    apply (clarsimp simp: less_mask_eq)
    apply (fastforce simp: obj_range'_def objBits_simps' mask_def field_simps)
   \<comment> \<open>Arch cases\<close>
   apply (rename_tac arch_capability)
   apply (case_tac arch_capability)
        \<comment> \<open>ASID control\<close>
        apply clarsimp
       \<comment> \<open>ASIDPool\<close>
       apply (clarsimp simp: valid_cap'_def valid_arch_cap_ref'_def typ_at'_def ko_wp_at'_def)
       apply (intro exI conjI, assumption)
       apply (clarsimp simp: obj_range'_def archObjSize_def objBitsKO_def)
       apply (case_tac ko; simp)
       apply (rename_tac arch_kernel_object)
       apply (case_tac arch_kernel_object;
                simp add: archObjSize_def asid_low_bits_def bit_simps mask_def add_ac)
     \<comment> \<open>Frame case\<close>
      apply (rename_tac word vmrights vmpage_size option)
      apply (clarsimp simp: valid_cap'_def valid_arch_cap_ref'_def typ_at'_def
                            ko_wp_at'_def capAligned_def)
      apply (frule_tac ptr = ptr and sz = "pageBits" in
                       nasty_range[where 'a=machine_word_len, folded word_bits_def, rotated])
         apply simp
        apply (simp add: pbfs_atleast_pageBits)+
      apply (clarsimp simp: frame_at'_def)
      apply (drule_tac x = idx in spec, clarsimp simp: typ_at'_def ko_wp_at'_def)
      apply (intro exI conjI,assumption)
      apply (clarsimp simp: obj_range'_def shiftl_t2n mask_def add_diff_eq)
      apply (case_tac ko, simp_all split: if_splits,
            (simp add: objBitsKO_def archObjSize_def field_simps shiftl_t2n)+)[1]
     \<comment> \<open>PT case\<close>
     apply (rename_tac word pt_t option)
     apply (clarsimp simp: valid_cap'_def valid_arch_cap_ref'_def obj_at'_def
                           page_table_at'_def typ_at'_def ko_wp_at'_def)
     apply (cut_tac ptr=ptr and bz="ptBits pt_t" and word=word and sz=pte_bits in
                    nasty_range[where 'a=machine_word_len]; simp?)
      apply (simp add: pt_bits_def)
     apply clarsimp
     apply (drule_tac x="ucast idx" in spec)
     apply (clarsimp simp: pt_bits_def table_size_def le_mask_iff_lt_2n[THEN iffD1])
     apply (intro exI conjI,assumption)
     apply (clarsimp simp: obj_range'_def)
     apply (case_tac ko; simp)
     apply (rename_tac arch_kernel_object)
     apply (case_tac arch_kernel_object; simp)
     apply (simp add: objBitsKO_def archObjSize_def bit_simps mask_def ucast_ucast_len field_simps
                      shiftl_t2n)
    \<comment> \<open>VCPU case\<close>
    apply (clarsimp simp: valid_cap'_def typ_at'_def ko_wp_at'_def objBits_simps)
    apply (intro exI conjI, assumption)
    apply (clarsimp simp: obj_range'_def archObjSize_def objBitsKO_def)
    apply (case_tac ko, simp+)[1]
    apply (rename_tac arch_kernel_object)
    apply (case_tac arch_kernel_object;  simp add: archObjSize_def bit_simps mask_def add_ac)

   \<comment> \<open>SGISignalCap case\<close>
   apply (clarsimp simp: valid_cap'_def)

  \<comment> \<open>CNode case\<close>
  apply (clarsimp simp: valid_cap'_def obj_at'_def capAligned_def objBits_simps)
  apply (frule_tac ptr=ptr and sz=cte_level_bits
           in nasty_range [where 'a=machine_word_len, folded word_bits_def])
     apply (simp add: cte_level_bits_def objBits_defs)+
  apply clarsimp
  apply (drule_tac x=idx in spec)
  apply (clarsimp simp: less_mask_eq)
  apply (fastforce simp: obj_range'_def mask_def objBits_simps' field_simps)[1]
  done

lemma untypedCap_descendants_range':
  "\<lbrakk>valid_pspace' s; ctes_of s p = Some cte;
    isUntypedCap (cteCap cte); valid_mdb' s;
    q \<in> descendants_of' p (ctes_of s) \<rbrakk>
   \<Longrightarrow> cte_wp_at' (\<lambda>c. (capRange (cteCap c) \<inter>
                        usableUntypedRange (cteCap cte) = {})) q s"
  apply (clarsimp simp: valid_pspace'_def)
  apply (frule(1) descendants_of_cte_at')
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (clarsimp simp:valid_mdb'_def)
  apply (frule valid_mdb_no_loops)
  apply (case_tac "isUntypedCap (cteCap ctea)")
   apply (case_tac ctea)
   apply (rename_tac cap node)
   apply (case_tac cte)
   apply (rename_tac cap' node')
   apply clarsimp
   apply (frule(1) valid_capAligned[OF ctes_of_valid_cap'])
   apply (frule_tac c = cap in valid_capAligned[OF ctes_of_valid_cap'])
    apply (simp add:untypedCapRange)+
   apply (frule_tac c = cap' in aligned_untypedRange_non_empty)
    apply simp
   apply (frule_tac c = cap in aligned_untypedRange_non_empty)
    apply simp
   apply (clarsimp simp:valid_mdb'_def valid_mdb_ctes_def)
   apply (drule untyped_incD', simp+)
   apply clarify
   apply (erule subset_splitE)
      apply simp
      apply (thin_tac "P \<longrightarrow> Q" for P Q)+
      apply (elim conjE)
      apply (simp add:descendants_of'_def)
      apply (drule(1) subtree_trans)
      apply (simp add:no_loops_no_subtree)
     apply simp
    apply (clarsimp simp:descendants_of'_def | erule disjE)+
     apply (drule(1) subtree_trans)
     apply (simp add:no_loops_no_subtree)+
   apply (thin_tac "P \<longrightarrow> Q" for P Q)+
   apply (erule(1) disjoint_subset2[OF usableRange_subseteq])
   apply (simp add:Int_ac)
  apply (case_tac ctea)
  apply (rename_tac cap node)
  apply (case_tac cte)
  apply clarsimp
  apply (drule(1) ctes_of_valid_cap')+
  apply (frule_tac cap = cap in ctes_of_ko; assumption?)
  apply (elim disjE)
   apply clarsimp+
  apply (thin_tac "s \<turnstile>' cap")
  apply (clarsimp simp: valid_cap'_def isCap_simps valid_untyped'_def
                  simp del: usableUntypedRange.simps untypedRange.simps)
  apply (thin_tac "\<forall>x y z. P x y z" for P)
  apply (rule ccontr)
  apply (clarsimp dest!: int_not_emptyD
                  simp del: usableUntypedRange.simps untypedRange.simps)
  apply (drule(1) bspec)
  apply (clarsimp simp: ko_wp_at'_def simp del: usableUntypedRange.simps untypedRange.simps)
  apply (drule_tac x = optr in spec)
  apply (clarsimp simp: ko_wp_at'_def simp del: usableUntypedRange.simps untypedRange.simps)
  apply (frule(1) pspace_alignedD')
  apply (frule(1) pspace_distinctD')
  apply (erule(1) impE)
  apply (clarsimp simp del: usableUntypedRange.simps untypedRange.simps)
  apply blast
  done

lemma cte_wp_at_caps_descendants_range_inI':
  "\<lbrakk>invs' s; cte_wp_at' (\<lambda>c. cteCap c = UntypedCap d (ptr && ~~ mask sz) sz idx) cref s;
    idx \<le> unat (ptr && mask sz); sz < word_bits\<rbrakk>
   \<Longrightarrow> descendants_range_in' {ptr .. (ptr && ~~ mask sz) + mask sz}
         cref (ctes_of s)"
  apply (frule invs_mdb')
  apply (frule(1) le_mask_le_2p)
  apply (clarsimp simp: descendants_range_in'_def cte_wp_at_ctes_of)
  apply (drule untypedCap_descendants_range'[rotated])
      apply (simp add: isCap_simps)+
   apply (simp add: invs_valid_pspace')
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (erule disjoint_subset2[rotated])
  apply clarsimp
  apply (rule le_plus'[OF word_and_le2])
  apply simp
  apply (erule word_of_nat_le)
  done

lemma checkFreeIndex_wp:
  "\<lbrace>\<lambda>s. if descendants_of' slot (ctes_of s) = {} then Q y s else Q x s\<rbrace>
   constOnFailure x (doE z \<leftarrow> ensureNoChildren slot; returnOk y odE)
   \<lbrace>Q\<rbrace>"
  apply (clarsimp simp:constOnFailure_def const_def)
  apply (wp ensureNoChildren_wp)
  apply simp
  done

declare upt_Suc[simp]

lemma ensureNoChildren_sp:
  "\<lbrace>P\<rbrace> ensureNoChildren sl \<lbrace>\<lambda>rv s. P s \<and> descendants_of' sl (ctes_of s) = {}\<rbrace>,-"
  by (wp ensureNoChildren_wp, simp)

lemma dui_sp_helper':
  "\<lbrace>P\<rbrace> if Q then returnOk root_cap
       else doE slot \<leftarrow>
                  lookupTargetSlot root_cap cref dpth;
                  liftE (getSlotCap slot)
            odE \<lbrace>\<lambda>rv s. (rv = root_cap \<or> (\<exists>slot. cte_wp_at' ((=) rv o cteCap) slot s)) \<and> P s\<rbrace>, -"
  apply (cases Q, simp_all add: lookupTargetSlot_def)
   apply (wp, simp)
  apply (simp add: getSlotCap_def split_def)
  apply wp
    apply (rule hoare_strengthen_post [OF getCTE_sp[where P=P]])
    apply (clarsimp simp: cte_wp_at_ctes_of)
    apply (elim allE, drule(1) mp)
    apply simp
   apply wpsimp
  apply simp
  done

lemma map_ensure_empty':
  "\<lbrace>\<lambda>s. (\<forall>slot \<in> set slots. cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) slot s) \<longrightarrow> P s\<rbrace>
     mapME_x ensureEmptySlot slots
   \<lbrace>\<lambda>rv s. P s \<rbrace>,-"
  apply (induct slots arbitrary: P)
   apply (simp add: mapME_x_def sequenceE_x_def)
   apply wp
  apply (simp add: mapME_x_def sequenceE_x_def)
  apply (rule_tac Q="\<lambda>rv s. (\<forall>slot\<in>set slots. cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) slot s) \<longrightarrow> P s"
                  in validE_R_sp)
   apply (simp add: ensureEmptySlot_def unlessE_def)
   apply (wp getCTE_wp')
   apply (clarsimp elim!: cte_wp_at_weakenE')
  apply (erule meta_allE)
  apply (erule hoare_strengthen_postE_R)
  apply clarsimp
  done

lemma irq_nodes_global:
  "irq_node' s + (ucast (irq :: irq) << cteSizeBits) \<in> global_refs' s"
  by (simp add: global_refs'_def)

lemma valid_global_refsD2':
  "\<lbrakk>ctes_of s p = Some cte; valid_global_refs' s\<rbrakk> \<Longrightarrow> global_refs' s \<inter> capRange (cteCap cte) = {}"
  by (blast dest: valid_global_refsD')

lemma cte_cap_in_untyped_range:
  "\<lbrakk> ptr \<le> x; x \<le> ptr + mask bits; cte_wp_at' (\<lambda>cte. cteCap cte = UntypedCap d ptr bits idx) cref s;
     descendants_of' cref (ctes_of s) = {}; invs' s;
     ex_cte_cap_to' x s; valid_global_refs' s \<rbrakk> \<Longrightarrow> False"
  apply (clarsimp simp: ex_cte_cap_to'_def cte_wp_at_ctes_of)
  apply (case_tac ctea, simp)
  apply (rename_tac cap node)
  apply (frule ctes_of_valid_cap', clarsimp)
  apply (case_tac "\<exists>irq. cap = IRQHandlerCap irq")
   apply (drule (1) equals0D[where a=x, OF valid_global_refsD2'[where p=cref]])
   apply (clarsimp simp: irq_nodes_global add_mask_fold)
  apply (frule_tac p=crefa and p'=cref in caps_containedD', assumption)
     apply (clarsimp dest!: isCapDs)
    apply (rule_tac x=x in notemptyI)
    apply (simp add: subsetD[OF cte_refs_capRange] add_mask_fold)
   apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def valid_mdb'_def valid_mdb_ctes_def)
  apply (frule_tac p=cref and p'=crefa in untyped_mdbD', assumption)
      apply (simp_all add: isUntypedCap_def add_mask_fold)
    apply (frule valid_capAligned)
    apply (frule capAligned_capUntypedPtr)
     apply (case_tac cap; simp)
    apply blast
   apply (case_tac cap; simp)
  apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def valid_mdb'_def valid_mdb_ctes_def)
  done

lemma cap_case_CNodeCap_True_throw:
  "(case cap of CNodeCap a b c d \<Rightarrow> returnOk ()
         |  _ \<Rightarrow> throw $ e)
          = (whenE (\<not>isCNodeCap cap) (throwError e))"
  by (simp split: capability.split bool.split
             add: whenE_def isCNodeCap_def)

lemma empty_descendants_range_in':
  "\<lbrakk>descendants_of' slot m = {}\<rbrakk> \<Longrightarrow> descendants_range_in' S slot m "
  by (clarsimp simp:descendants_range_in'_def)

lemma liftE_validE_R:
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> liftE f \<lbrace>Q\<rbrace>,-"
  by wpsimp

lemma decodeUntyped_wf[wp]:
  "\<lbrace>invs' and cte_wp_at' (\<lambda>cte. cteCap cte = UntypedCap d w sz idx) slot
          and sch_act_simple
          and (\<lambda>s. \<forall>x \<in> set cs. s \<turnstile>' x)
          and (\<lambda>s. \<forall>x \<in> set cs. \<forall>r \<in> cte_refs' x (irq_node' s). ex_cte_cap_to' r s)\<rbrace>
     decodeUntypedInvocation label args slot
       (UntypedCap d w sz idx) cs
   \<lbrace>valid_untyped_inv'\<rbrace>,-"
  unfolding decodeUntypedInvocation_def
  apply (simp add: unlessE_def[symmetric] unlessE_whenE rangeCheck_def whenE_def[symmetric]
                   returnOk_liftE[symmetric] Let_def cap_case_CNodeCap_True_throw
              split del: if_split cong: if_cong list.case_cong)
  apply (rule list_case_throw_validE_R)
  apply (clarsimp split del: if_split split: list.splits)
  apply (intro conjI impI allI)
   apply (wp+)[6]
  apply (clarsimp split del: if_split)
  apply (rename_tac ty us nodeIndexW nodeDepthW nodeOffset nodeWindow rootCap cs' xs')
  apply (rule validE_R_sp[OF map_ensure_empty'] validE_R_sp[OF whenE_throwError_sp]
              validE_R_sp[OF dui_sp_helper'])+
  apply (case_tac "\<not> isCNodeCap nodeCap")
   apply (simp add: validE_R_def)
  apply (simp add: mapM_locate_eq bind_liftE_distrib bindE_assoc returnOk_liftE[symmetric])
  apply (rule validE_R_sp, rule liftE_validE_R, rule stateAssert_sp)
  apply (rule hoare_pre, wp whenE_throwError_wp checkFreeIndex_wp map_ensure_empty')
  apply (clarsimp simp:cte_wp_at_ctes_of not_less shiftL_nat)
  apply (case_tac cte)
  apply clarsimp
  apply (frule(1) valid_capAligned[OF ctes_of_valid_cap'[OF _ invs_valid_objs']])
  apply (clarsimp simp:capAligned_def)
  apply (subgoal_tac "idx \<le> 2^ sz")
   prefer 2
   apply (frule(1) ctes_of_valid_cap'[OF _ invs_valid_objs'])
   apply (clarsimp simp:valid_cap'_def valid_untyped_def)
  apply (subgoal_tac "(2 ^ sz - idx) < 2^ word_bits")
   prefer 2
   apply (rule le_less_trans[where y = "2^sz"])
    apply simp+
  apply (subgoal_tac "of_nat (2 ^ sz - idx) = (2::machine_word)^sz - of_nat idx")
   prefer 2
   apply (simp add:word_of_nat_minus)
  apply (subgoal_tac "valid_cap' nodeCap s")
   prefer 2
   apply (erule disjE)
    apply (fastforce dest: cte_wp_at_valid_objs_valid_cap')
   apply clarsimp
   apply (case_tac cte)
   apply clarsimp
   apply (drule(1) ctes_of_valid_cap'[OF _ invs_valid_objs'])+
   apply simp
  apply (clarsimp simp: toEnum_of_nat [OF less_Suc_unat_less_bound])
  apply (subgoal_tac "args ! 4 \<le> 2 ^ capCNodeBits nodeCap")
   prefer 2
   apply (clarsimp simp: isCap_simps)
   apply (subst (asm) le_m1_iff_lt[THEN iffD1])
    apply (clarsimp simp:valid_cap'_def isCap_simps p2_gt_0 capAligned_def word_bits_def)
   apply (rule less_imp_le)
   apply simp
  apply (subgoal_tac
    "distinct (map (\<lambda>y. capCNodePtr nodeCap + y * 2^cte_level_bits) [args ! 4 .e. args ! 4 + args ! 5 - 1])")
   prefer 2
   apply (simp add: distinct_map upto_enum_def del: upt_Suc)
   apply (rule comp_inj_on)
    apply (rule inj_onI)
    apply (clarsimp dest!: less_Suc_unat_less_bound)
    apply (erule word_unat.Abs_eqD)
     apply (simp add: unats_def)
    apply (simp add: unats_def)
   apply (rule inj_onI)
   apply (clarsimp simp: toEnum_of_nat[OF less_Suc_unat_less_bound] isCap_simps)
   apply (erule(2) inj_bits, simp add: cte_level_bits_def word_bits_def)
   apply (subst Suc_unat_diff_1)
    apply (rule word_le_plus_either,simp)
    apply (subst olen_add_eqv)
    apply (subst add.commute)
    apply (erule(1) plus_minus_no_overflow_ab)
   apply (drule(1) le_plus)
   apply (rule unat_le_helper)
   apply (erule order_trans)
   apply (subst unat_power_lower64[symmetric], simp add: word_bits_def cte_level_bits_def)
   apply (simp add: word_less_nat_alt[symmetric])
   apply (rule two_power_increasing)
    apply (clarsimp dest!: valid_capAligned
                     simp: capAligned_def objBits_def objBitsKO_def)
    apply (simp_all add: word_bits_def cte_level_bits_def objBits_defs)[2]
  apply (clarsimp simp: AARCH64_H.fromAPIType_def)
  apply (subgoal_tac "Suc (unat (args ! 4 + args ! 5 - 1)) = unat (args ! 4) + unat (args ! 5)")
   prefer 2
   apply simp
   apply (subst Suc_unat_diff_1)
    apply (rule word_le_plus_either,simp)
    apply (subst olen_add_eqv)
    apply (subst add.commute)
    apply (erule(1) plus_minus_no_overflow_ab)
   apply (rule unat_plus_simple[THEN iffD1])
   apply (subst olen_add_eqv)
   apply (subst add.commute)
   apply (erule(1) plus_minus_no_overflow_ab)
  apply clarsimp
  apply (subgoal_tac "(\<forall>x. (args ! 4) \<le> x \<and> x \<le> (args ! 4) + (args ! 5) - 1 \<longrightarrow>
                      ex_cte_cap_wp_to' (\<lambda>_. True) (capCNodePtr nodeCap + x * 2^cteSizeBits) s)")
   prefer 2
   apply clarsimp
   apply (erule disjE)
    apply (erule bspec)
    apply (clarsimp simp:isCap_simps image_def shiftl_t2n mult_ac)
    apply (rule_tac x = x in bexI,simp)
    apply (simp add: mask_def)
    apply (erule order_trans)
    apply (frule(1) le_plus)
    apply (rule word_l_diffs,simp+)
    apply (rule word_le_plus_either,simp)
    apply (subst olen_add_eqv)
    apply (subst add.commute)
    apply (erule(1) plus_minus_no_overflow_ab)
   apply (clarsimp simp:ex_cte_cap_wp_to'_def)
   apply (rule_tac x = nodeSlot in exI)
   apply (case_tac cte)
   apply (clarsimp simp: cte_wp_at_ctes_of isCap_simps image_def
                         shiftl_t2n)
   apply (rule_tac x = x in bexI,simp)
   apply (simp add: mask_def)
   apply (erule order_trans)
   apply (frule(1) le_plus)
   apply (rule word_l_diffs,simp+)
   apply (rule word_le_plus_either,simp)
   apply (subst olen_add_eqv)
   apply (subst add.commute)
   apply (erule(1) plus_minus_no_overflow_ab)
  apply (simp add: fromIntegral_def toInteger_nat fromInteger_nat)
  apply (rule conjI)
   apply (simp add: objBits_defs cte_level_bits_def)
   apply (clarsimp simp:of_nat_shiftR word_le_nat_alt)
   apply (frule_tac n = "unat (args ! 5)"
        and bits = "(APIType_capBits (toEnum (unat (args ! 0))) (unat (args ! 1)))"
       in range_cover_stuff[where rv = 0,rotated -1])
         apply (simp add:unat_1_0)
        apply simp
        apply (simp add:word_sub_le_iff word_of_nat_le)
       apply simp+
   apply (clarsimp simp:getFreeRef_def)
   apply (frule alignUp_idem[OF is_aligned_weaken,where a = w])
     apply (erule range_cover.sz)
    apply (simp add:range_cover_def)
   apply (simp add:empty_descendants_range_in' untypedBits_defs)
   apply (clarsimp simp: image_def isCap_simps nullPointer_def word_size field_simps)
   apply (intro conjI)
     apply (clarsimp simp: image_def isCap_simps nullPointer_def word_size field_simps)
     apply (drule_tac x=x in spec)+
     apply simp
    apply (clarsimp simp: APIType_capBits_def)
   apply clarsimp
  apply (clarsimp simp: image_def getFreeRef_def cte_level_bits_def objBits_simps' field_simps)
  apply (clarsimp simp: of_nat_shiftR word_le_nat_alt)
  apply (frule_tac n = "unat (args ! 5)"
               and bits = "(APIType_capBits (toEnum (unat (args ! 0))) (unat (args ! 1)))"
                in range_cover_stuff[where w=w and sz=sz and rv = idx,rotated -1]; simp?)
  apply (intro conjI; clarsimp simp add: image_def word_size)
   apply (clarsimp simp: image_def isCap_simps nullPointer_def word_size field_simps)
   apply (drule_tac x=x in spec)+
   apply simp
  apply (clarsimp simp: APIType_capBits_def)
  done

lemma corres_list_all2_mapM_':
  assumes w: "suffix xs oxs" "suffix ys oys"
  assumes y: "\<And>x xs y ys. \<lbrakk> F x y; suffix (x # xs) oxs; suffix (y # ys) oys \<rbrakk>
               \<Longrightarrow> corres dc (P (x # xs)) (P' (y # ys)) (f x) (g y)"
  assumes z: "\<And>x y xs. \<lbrakk> F x y; suffix (x # xs) oxs \<rbrakk> \<Longrightarrow> \<lbrace>P (x # xs)\<rbrace> f x \<lbrace>\<lambda>rv. P xs\<rbrace>"
             "\<And>x y ys. \<lbrakk> F x y; suffix (y # ys) oys \<rbrakk> \<Longrightarrow> \<lbrace>P' (y # ys)\<rbrace> g y \<lbrace>\<lambda>rv. P' ys\<rbrace>"
  assumes x: "list_all2 F xs ys"
  shows "corres dc (P xs) (P' ys) (mapM_x f xs) (mapM_x g ys)"
  apply (insert x w)
  apply (induct xs arbitrary: ys)
   apply (simp add: mapM_x_def sequence_x_def)
  apply (case_tac ys)
   apply simp
  apply (clarsimp simp add: mapM_x_def sequence_x_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF y]; assumption?)
      apply (clarsimp dest!: suffix_ConsD)
      apply (erule meta_allE, (drule(1) meta_mp)+)
      apply assumption
     apply (erule(1) z)+
   apply simp+
  done

lemmas suffix_refl = suffix_order.refl

lemmas corres_list_all2_mapM_
     = corres_list_all2_mapM_' [OF suffix_refl suffix_refl]

declare modify_map_id[simp]

lemma valid_mdbD3':
  "\<lbrakk> ctes_of s p = Some cte; valid_mdb' s \<rbrakk> \<Longrightarrow> p \<noteq> 0"
  by (clarsimp simp add: valid_mdb'_def valid_mdb_ctes_def no_0_def)

lemma capRange_sameRegionAs:
  "\<lbrakk> sameRegionAs x y; s \<turnstile>' y; capClass x = PhysicalClass \<or> capClass y = PhysicalClass \<rbrakk>
   \<Longrightarrow> capRange x \<inter> capRange y \<noteq> {}"
  apply (erule sameRegionAsE)
      apply (subgoal_tac "capClass x = capClass y \<and> capRange x = capRange y")
       apply simp
       apply (drule valid_capAligned)
       apply (drule(1) capAligned_capUntypedPtr)
       apply clarsimp
      apply (rule conjI)
       apply (rule master_eqI, rule capClass_Master, simp)
      apply (rule master_eqI, rule capRange_Master, simp)
     apply blast
    apply blast
   apply (clarsimp simp: isCap_simps)+
  done
end

locale mdb_insert_again =
  mdb_ptr_parent?: mdb_ptr m _ _ parent parent_cap parent_node +
  mdb_ptr_site?: mdb_ptr m _ _ site site_cap site_node
    for m parent parent_cap parent_node site site_cap site_node +

  fixes c'

  assumes site_cap: "site_cap = NullCap"
  assumes site_prev: "mdbPrev site_node = 0"
  assumes site_next: "mdbNext site_node = 0"

  assumes is_untyped: "isUntypedCap parent_cap"
  assumes same_region: "sameRegionAs parent_cap c'"

  assumes range: "descendants_range' c' parent m"
  assumes phys: "capClass c' = PhysicalClass"

  fixes s
  assumes valid_capI': "m p = Some (CTE cap node) \<Longrightarrow> s \<turnstile>' cap"

  assumes ut_rev: "ut_revocable' m"

  fixes n
  defines "n \<equiv>
           (modify_map
             (\<lambda>x. if x = site
                  then Some (CTE c' (MDB (mdbNext parent_node) parent True True))
                  else m x)
             parent (cteMDBNode_update (mdbNext_update (\<lambda>x. site))))"

  assumes neq: "parent \<noteq> site"

context mdb_insert_again
begin
interpretation Arch . (*FIXME: arch-split*)
lemmas parent = mdb_ptr_parent.m_p
lemmas site = mdb_ptr_site.m_p

lemma next_wont_bite:
  "\<lbrakk> mdbNext parent_node \<noteq> 0; m (mdbNext parent_node) = Some cte \<rbrakk>
  \<Longrightarrow> \<not> sameRegionAs c' (cteCap cte)"
  using range ut_rev
  apply (cases cte)
  apply clarsimp
  apply (cases "m \<turnstile> parent \<rightarrow> mdbNext parent_node")
   apply (drule (2) descendants_rangeD')
   apply (drule capRange_sameRegionAs)
     apply (erule valid_capI')
    apply (simp add: phys)
   apply blast
  apply (erule notE, rule direct_parent)
    apply (clarsimp simp: mdb_next_unfold parent)
   apply assumption
  apply (simp add: parentOf_def parent)
  apply (insert is_untyped same_region)
  apply (clarsimp simp: isMDBParentOf_CTE)
  apply (rule conjI)
   apply (erule (1) sameRegionAs_trans)
  apply (simp add: ut_revocable'_def)
  apply (insert parent)
  apply simp
  apply (clarsimp simp: isCap_simps)
  done

lemma no_0_helper: "no_0 m \<Longrightarrow> no_0 n"
  by (simp add: n_def, simp add: no_0_def)

lemma no_0_n [intro!]: "no_0 n" by (auto intro: no_0_helper)

lemmas n_0_simps [iff] = no_0_simps [OF no_0_n]

lemmas neqs [simp] = neq neq [symmetric]

definition
  "new_site \<equiv> CTE c' (MDB (mdbNext parent_node) parent True True)"

definition
  "new_parent \<equiv> CTE parent_cap (mdbNext_update (\<lambda>a. site) parent_node)"

lemma n: "n = m (site \<mapsto> new_site, parent \<mapsto> new_parent)"
  using parent site
  by (simp add: n_def modify_map_apply new_site_def new_parent_def
                fun_upd_def[symmetric])

lemma site_no_parent [iff]:
  "m \<turnstile> site \<rightarrow> x = False" using site site_next
  by (auto dest: subtree_next_0)

lemma site_no_child [iff]:
  "m \<turnstile> x \<rightarrow> site = False" using site site_prev
  by (auto dest: subtree_prev_0)

lemma parent_next: "m \<turnstile> parent \<leadsto> mdbNext parent_node"
  by (simp add: parent mdb_next_unfold)

lemma parent_next_rtrancl_conv [simp]:
  "m \<turnstile> mdbNext parent_node \<leadsto>\<^sup>* site = m \<turnstile> parent \<leadsto>\<^sup>+ site"
  apply (rule iffI)
   apply (insert parent_next)
   apply (fastforce dest: rtranclD)
  apply (drule tranclD)
  apply (clarsimp simp: mdb_next_unfold)
  done

lemma site_no_next [iff]:
  "m \<turnstile> x \<leadsto> site = False" using site site_prev dlist
  apply clarsimp
  apply (simp add: mdb_next_unfold)
  apply (elim exE conjE)
  apply (case_tac z)
  apply simp
  apply (rule dlistEn [where p=x], assumption)
   apply clarsimp
  apply clarsimp
  done

lemma site_no_next_trans [iff]:
  "m \<turnstile> x \<leadsto>\<^sup>+ site = False"
  by (clarsimp dest!: tranclD2)

lemma site_no_prev [iff]:
  "m \<turnstile> site \<leadsto> p = (p = 0)" using site site_next
  by (simp add: mdb_next_unfold)

lemma site_no_prev_trancl [iff]:
  "m \<turnstile> site \<leadsto>\<^sup>+ p = (p = 0)"
  apply (rule iffI)
   apply (drule tranclD)
   apply clarsimp
  apply simp
  apply (insert chain site)
  apply (simp add: mdb_chain_0_def)
  apply auto
  done

lemma chain_n:
  "mdb_chain_0 n"
proof -
  from chain
  have "m \<turnstile> mdbNext parent_node \<leadsto>\<^sup>* 0" using dlist parent
    apply (cases "mdbNext parent_node = 0")
     apply simp
    apply (erule dlistEn, simp)
    apply (auto simp: mdb_chain_0_def)
    done
  moreover
  have "\<not>m \<turnstile> mdbNext parent_node \<leadsto>\<^sup>* parent"
    using parent_next
    apply clarsimp
    apply (drule (1) rtrancl_into_trancl2)
    apply simp
    done
  moreover
  have "\<not> m \<turnstile> 0 \<leadsto>\<^sup>* site" using no_0 site
    by (auto elim!: next_rtrancl_tranclE dest!: no_0_lhs_trancl)
  moreover
  have "\<not> m \<turnstile> 0 \<leadsto>\<^sup>* parent" using no_0 parent
    by (auto elim!: next_rtrancl_tranclE dest!: no_0_lhs_trancl)
  moreover
  note chain
  ultimately show "mdb_chain_0 n" using no_0 parent site
    apply (simp add: n new_parent_def new_site_def)
    apply (auto intro!: mdb_chain_0_update no_0_update simp: next_update_lhs_rtrancl)
    done
qed

lemma no_loops_n: "no_loops n" using chain_n no_0_n
  by (rule mdb_chain_0_no_loops)

lemma n_direct_eq:
  "n \<turnstile> p \<leadsto> p' = (if p = parent then p' = site else
                 if p = site then m \<turnstile> parent \<leadsto> p'
                 else m \<turnstile> p \<leadsto> p')"
  using parent site site_prev
  by (auto simp: mdb_next_update n new_parent_def new_site_def
                 parent_next mdb_next_unfold)

lemma next_not_parent:
  "\<lbrakk> mdbNext parent_node \<noteq> 0; m (mdbNext parent_node) = Some cte \<rbrakk>
      \<Longrightarrow> \<not> isMDBParentOf new_site cte"
  apply (drule(1) next_wont_bite)
  apply (cases cte)
  apply (simp add: isMDBParentOf_def new_site_def)
  done

(* The newly inserted cap should never have children. *)
lemma site_no_parent_n:
  "n \<turnstile> site \<rightarrow> p = False" using parent valid_badges
  apply clarsimp
  apply (erule subtree.induct)
   prefer 2
   apply simp
  apply (clarsimp simp: parentOf_def mdb_next_unfold new_site_def n)
  apply (cases "mdbNext parent_node = site")
   apply (subgoal_tac "m \<turnstile> parent \<leadsto> site")
    apply simp
   apply (subst mdb_next_unfold)
   apply (simp add: parent)
  apply clarsimp
  apply (erule notE[rotated], erule(1) next_not_parent[unfolded new_site_def])
  done

end

locale mdb_insert_again_child = mdb_insert_again +
  assumes child:
  "isMDBParentOf
   (CTE parent_cap parent_node)
   (CTE c' (MDB (mdbNext parent_node) parent True True))"

context mdb_insert_again_child
begin

lemma new_child [simp]:
  "isMDBParentOf new_parent new_site"
  by (simp add: new_parent_def new_site_def) (rule child)

lemma n_site_child:
  "n \<turnstile> parent \<rightarrow> site"
  apply (rule subtree.direct_parent)
    apply (simp add: n_direct_eq)
   apply simp
  apply (clarsimp simp: parentOf_def parent site n)
  done

lemma parent_m_n:
  assumes "m \<turnstile> p \<rightarrow> p'"
  shows "if p' = parent then n \<turnstile> p \<rightarrow> site \<and> n \<turnstile> p \<rightarrow> p' else n \<turnstile> p \<rightarrow> p'" using assms
proof induct
  case (direct_parent c)
  thus ?case
    apply (cases "p = parent")
     apply simp
     apply (rule conjI, clarsimp)
     apply clarsimp
     apply (rule subtree.trans_parent [where c'=site])
        apply (rule n_site_child)
       apply (simp add: n_direct_eq)
      apply simp
     apply (clarsimp simp: parentOf_def n)
     apply (clarsimp simp: new_parent_def parent)
    apply simp
    apply (subgoal_tac "n \<turnstile> p \<rightarrow> c")
     prefer 2
     apply (rule subtree.direct_parent)
       apply (clarsimp simp add: n_direct_eq)
      apply simp
     apply (clarsimp simp: parentOf_def n)
     apply (fastforce simp: new_parent_def parent)
    apply clarsimp
    apply (erule subtree_trans)
    apply (rule n_site_child)
    done
next
  case (trans_parent c d)
  thus ?case
    apply -
    apply (cases "c = site", simp)
    apply (cases "d = site", simp)
    apply (cases "c = parent")
     apply clarsimp
     apply (erule subtree.trans_parent [where c'=site])
       apply (clarsimp simp add: n_direct_eq)
      apply simp
     apply (clarsimp simp: parentOf_def n)
     apply (rule conjI, clarsimp)
     apply (clarsimp simp: new_parent_def parent)
    apply clarsimp
    apply (subgoal_tac "n \<turnstile> p \<rightarrow> d")
     apply clarsimp
     apply (erule subtree_trans, rule n_site_child)
    apply (erule subtree.trans_parent)
      apply (simp add: n_direct_eq)
     apply simp
    apply (clarsimp simp: parentOf_def n)
    apply (fastforce simp: parent new_parent_def)
    done
qed

lemma n_to_site [simp]:
  "n \<turnstile> p \<leadsto> site = (p = parent)"
  by (simp add: n_direct_eq)

lemma parent_n_m:
  assumes "n \<turnstile> p \<rightarrow> p'"
  shows "if p' = site then p \<noteq> parent \<longrightarrow> m \<turnstile> p \<rightarrow> parent else m \<turnstile> p \<rightarrow> p'"
proof -
  from assms have [simp]: "p \<noteq> site" by (clarsimp simp: site_no_parent_n)
  from assms
  show ?thesis
  proof induct
    case (direct_parent c)
    thus ?case
      apply simp
      apply (rule conjI)
       apply clarsimp
      apply clarsimp
      apply (rule subtree.direct_parent)
        apply (simp add: n_direct_eq split: if_split_asm)
       apply simp
      apply (clarsimp simp: parentOf_def n parent new_parent_def split: if_split_asm)
      done
  next
    case (trans_parent c d)
    thus ?case
      apply clarsimp
      apply (rule conjI, clarsimp)
      apply (clarsimp split: if_split_asm)
      apply (simp add: n_direct_eq)
      apply (cases "p=parent")
       apply simp
       apply (rule subtree.direct_parent, assumption, assumption)
       apply (clarsimp simp: parentOf_def n parent new_parent_def split: if_split_asm)
      apply clarsimp
      apply (erule subtree.trans_parent, assumption, assumption)
      apply (clarsimp simp: parentOf_def n parent new_parent_def split: if_split_asm)
     apply (erule subtree.trans_parent)
       apply (simp add: n_direct_eq split: if_split_asm)
      apply assumption
     apply (clarsimp simp: parentOf_def n parent new_parent_def split: if_split_asm)
     done
 qed
qed

lemma descendants:
  "descendants_of' p n =
   (if parent \<in> descendants_of' p m \<or> p = parent
   then descendants_of' p m \<union> {site} else descendants_of' p m)"
  apply (rule set_eqI)
  apply (simp add: descendants_of'_def)
  apply (fastforce dest!: parent_n_m dest: parent_m_n simp: n_site_child split: if_split_asm)
  done

end

lemma blarg_descendants_of':
  "descendants_of' x (modify_map m p (if P then id else cteMDBNode_update (mdbPrev_update f)))
     = descendants_of' x m"
  by (simp add: descendants_of'_def)

lemma bluhr_descendants_of':
  "mdb_insert_again_child (ctes_of s') parent parent_cap pmdb site site_cap site_node cap s
   \<Longrightarrow>
   descendants_of' x
           (modify_map
             (modify_map
               (\<lambda>c. if c = site
                    then Some (CTE cap (MDB (mdbNext pmdb) parent True True))
                    else ctes_of s' c)
               (mdbNext pmdb)
               (if mdbNext pmdb = 0 then id
                else cteMDBNode_update (mdbPrev_update (\<lambda>x. site))))
             parent (cteMDBNode_update (mdbNext_update (\<lambda>x. site))))
     = (if parent \<in> descendants_of' x (ctes_of s') \<or> x = parent
        then descendants_of' x (ctes_of s') \<union> {site}
        else descendants_of' x (ctes_of s'))"
  apply (subst modify_map_com)
  apply (case_tac x, rename_tac node, case_tac node, clarsimp)
  apply (subst blarg_descendants_of')
  apply (erule mdb_insert_again_child.descendants)
  done

lemma mdb_relation_simp:
  "\<lbrakk> (s, s') \<in> state_relation; cte_at p s \<rbrakk>
    \<Longrightarrow> descendants_of' (cte_map p) (ctes_of s') = cte_map ` descendants_of p (cdt s)"
  by (cases p, clarsimp simp: state_relation_def cdt_relation_def)

lemma in_getCTE2:
  "((cte, s') \<in> fst (getCTE p s)) = (s' = s \<and> cte_wp_at' ((=) cte) p s)"
  apply (safe dest!: in_getCTE)
  apply (clarsimp simp: cte_wp_at'_def getCTE_def)
  done

declare wrap_ext_op_det_ext_ext_def[simp]

lemma do_ext_op_update_cdt_list_symb_exec_l':
  "corres_underlying {(s::det_state, s'). f (kheap s) s'} nf nf' dc P P' (create_cap_ext p z a) (return x)"
  apply (simp add: corres_underlying_def create_cap_ext_def
  update_cdt_list_def set_cdt_list_def bind_def put_def get_def gets_def return_def)
  done

crunch updateMDB, updateNewFreeIndex
  for it'[wp]: "\<lambda>s. P (ksIdleThread s)"
  and ups'[wp]: "\<lambda>s. P (gsUserPages s)"
  and cns'[wp]: "\<lambda>s. P (gsCNodes s)"
  and ksDomainTime[wp]: "\<lambda>s. P (ksDomainTime s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and ksWorkUnitsCompleted[wp]: "\<lambda>s. P (ksWorkUnitsCompleted s)"
  and ksMachineState[wp]: "\<lambda>s. P (ksMachineState s)"
  and ksArchState[wp]: "\<lambda>s. P (ksArchState s)"

crunch insertNewCap
  for ksInterrupt[wp]: "\<lambda>s. P (ksInterruptState s)"
  and norq[wp]: "\<lambda>s. P (ksReadyQueues s)"
  and ksIdleThread[wp]: "\<lambda>s. P (ksIdleThread s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"
  and pspace_canonical'[wp]: pspace_canonical'
  (wp: crunch_wps)

crunch insertNewCaps
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  (simp: crunch_simps zipWithM_x_mapM wp: crunch_wps)


crunch set_cdt
  for exst[wp]: "\<lambda>s. P (exst s)"

lemma set_original_symb_exec_l:
  "corres_underlying {(s, s'). f (kheap s) (exst s) s'} nf nf' dc P P' (set_original p b) (return x)"
  by (simp add: corres_underlying_def return_def set_original_def in_monad Bex_def)

lemma set_cdt_symb_exec_l:
  "corres_underlying {(s, s'). f (kheap s) (exst s) s'} nf nf' dc P P' (set_cdt g) (return x)"
  by (simp add: corres_underlying_def return_def set_cdt_def in_monad Bex_def)

crunch create_cap_ext
  for work_units_completed[wp]: "\<lambda>s. P (work_units_completed s)"
  (ignore_del: create_cap_ext)

context begin interpretation Arch . (*FIXME: arch-split*)

lemma updateNewFreeIndex_noop_psp_corres:
  "corres_underlying {(s, s'). pspace_relation (kheap s) (ksPSpace s')} False True
    dc \<top> (cte_at' slot)
    (return ()) (updateNewFreeIndex slot)"
  apply (simp add: updateNewFreeIndex_def)
  apply (rule corres_guard_imp)
    apply (rule corres_bind_return2)
    apply (rule corres_symb_exec_r_conj[where P'="cte_at' slot"])
       apply (rule corres_trivial, simp)
      apply (wp getCTE_wp' | wpc
        | simp add: updateTrackedFreeIndex_def getSlotCap_def)+
  done

crunch set_cap, set_cdt
  for domain_index[wp]: "\<lambda>s. P (domain_index s)"
  (wp: crunch_wps)

crunch updateMDB, updateNewFreeIndex, setCTE
  for rdyq_projs[wp]:
    "\<lambda>s. P (ksReadyQueues s) (tcbSchedNexts_of s) (tcbSchedPrevs_of s) (\<lambda>d p. inQ d p |< tcbs_of' s)"

lemma insertNewCap_corres:
notes if_cong[cong del] if_weak_cong[cong]
shows
  "\<lbrakk> cref' = cte_map (fst tup)
     \<and> cap_relation (default_cap tp (snd tup) sz d) cap \<rbrakk> \<Longrightarrow>
   corres dc
     (cte_wp_at ((=) cap.NullCap) (fst tup) and pspace_aligned
        and pspace_distinct and valid_objs and valid_mdb and valid_list
        and cte_wp_at ((\<noteq>) cap.NullCap) p)
     (cte_wp_at' (\<lambda>c. cteCap c = NullCap) cref' and
      cte_wp_at' (\<lambda>cte. isUntypedCap (cteCap cte) \<and> sameRegionAs (cteCap cte) cap) (cte_map p)
       and valid_mdb' and pspace_aligned' and pspace_distinct' and valid_objs'
       and (\<lambda>s. descendants_range' cap (cte_map p) (ctes_of s)))
     (create_cap tp sz p d tup)
     (insertNewCap (cte_map p) cref' cap)"
  apply (cases tup,
         clarsimp simp add: create_cap_def insertNewCap_def
                            liftM_def)
  apply (rule corres_symb_exec_r [OF _ getCTE_sp])+
      prefer 3
      apply (rule no_fail_pre, wp)
      apply (clarsimp elim!: cte_wp_at_weakenE')
     prefer 4
     apply (rule no_fail_pre, wp)
     apply (clarsimp elim!: cte_wp_at_weakenE')
    apply (rule corres_assert_assume)
     prefer 2
     apply (case_tac oldCTE)
     apply (clarsimp simp: cte_wp_at_ctes_of valid_mdb'_def valid_mdb_ctes_def
                           valid_nullcaps_def)
     apply (erule allE)+
     apply (erule (1) impE)
     apply (simp add: initMDBNode_def)
    apply clarsimp
    apply (rule_tac F="capClass cap = PhysicalClass" in corres_req)
     apply (clarsimp simp: cte_wp_at_ctes_of isCap_simps)
     apply (drule sameRegionAs_classes, simp)
    apply (rule corres_caps_decomposition)
                                              prefer 3
                                              apply wp+
                                                 apply (rule hoare_post_imp, simp)
                                                 apply (wp | assumption)+
                                             defer
                                             apply ((wp | simp)+)[1]
                                            apply (simp add: create_cap_ext_def set_cdt_list_def update_cdt_list_def bind_assoc)
                                            apply ((wp | simp)+)[1]
                                           apply (wp updateMDB_ctes_of_cases
                                                  | simp add: o_def split del: if_split)+
            apply (clarsimp simp: cdt_relation_def cte_wp_at_ctes_of
                     split del: if_split cong: if_cong simp del: id_apply)
            apply (subst if_not_P, erule(1) valid_mdbD3')
            apply (case_tac x, case_tac oldCTE)
            apply (subst bluhr_descendants_of')
             apply (rule mdb_insert_again_child.intro)
              apply (rule mdb_insert_again.intro)
                apply (rule mdb_ptr.intro)
                 apply (simp add: valid_mdb'_def vmdb_def)
                apply (rule mdb_ptr_axioms.intro)
                apply simp
               apply (rule mdb_ptr.intro)
                apply (simp add: valid_mdb'_def vmdb_def)
               apply (rule mdb_ptr_axioms.intro)
               apply fastforce
              apply (rule mdb_insert_again_axioms.intro)
                       apply (clarsimp simp: nullPointer_def)+
                apply (erule (1) ctes_of_valid_cap')
               apply (simp add: valid_mdb'_def valid_mdb_ctes_def)
              apply clarsimp
             apply (rule mdb_insert_again_child_axioms.intro)
             apply (clarsimp simp: isMDBParentOf_def)
             apply (clarsimp simp: isCap_simps isArchMDBParentOf_def)
             apply (clarsimp simp: valid_mdb'_def valid_mdb_ctes_def
                                   ut_revocable'_def)
            apply (fold fun_upd_def)
            apply (subst descendants_of_insert_child')
               apply (erule(1) mdb_Null_descendants)
              apply (clarsimp simp: cte_wp_at_def)
             apply (erule(1) mdb_Null_None)
            apply (subgoal_tac "cte_at (aa, bb) s")
             prefer 2
             apply (drule not_sym, clarsimp simp: cte_wp_at_caps_of_state split: if_split_asm)
            apply (subst descendants_of_eq' [OF _ cte_wp_at_cte_at], assumption+)
                 apply (clarsimp simp: state_relation_def)
                apply assumption+
            apply (subst cte_map_eq_subst [OF _ cte_wp_at_cte_at], assumption+)
            apply (simp add: mdb_relation_simp)
           defer
           apply (clarsimp split del: if_split)+
         apply (clarsimp simp add: revokable_relation_def cte_wp_at_ctes_of
                        split del: if_split)
         apply simp
         apply (rule conjI)
          apply clarsimp
          apply (elim modify_map_casesE)
             apply ((clarsimp split: if_split_asm cong: conj_cong
                              simp: cte_map_eq_subst cte_wp_at_cte_at
                                    revokable_relation_simp)+)[4]
         apply clarsimp
         apply (subgoal_tac "null_filter (caps_of_state s) (aa, bb) \<noteq> None")
          prefer 2
          apply (clarsimp simp: null_filter_def cte_wp_at_caps_of_state split: if_split_asm)
         apply (subgoal_tac "cte_at (aa,bb) s")
          prefer 2
          apply clarsimp
          apply (drule null_filter_caps_of_stateD)
          apply (erule cte_wp_cte_at)
         apply (elim modify_map_casesE)
            apply (clarsimp split: if_split_asm cong: conj_cong
                            simp: cte_map_eq_subst cte_wp_at_cte_at revokable_relation_simp)+
        apply (clarsimp simp: state_relation_def ghost_relation_of_heap pt_types_of_heap_eq o_def)+
     apply wp+
   apply (rule corres_guard_imp)
     apply (rule corres_underlying_symb_exec_l [OF gets_symb_exec_l])
      apply (rule corres_underlying_symb_exec_l [OF gets_symb_exec_l])
       apply (rule corres_underlying_symb_exec_l [OF set_cdt_symb_exec_l])
        apply (rule corres_underlying_symb_exec_l [OF do_ext_op_update_cdt_list_symb_exec_l'])
         apply (rule corres_underlying_symb_exec_l [OF set_original_symb_exec_l])
          apply (rule corres_cong[OF refl refl _ refl refl, THEN iffD1])
           apply (rule bind_return[THEN fun_cong])
          apply (rule corres_split)
             apply (rule setCTE_corres; simp)
            apply (subst bind_return[symmetric],
                   rule corres_split)
               apply (simp add: dc_def[symmetric])
               apply (rule updateMDB_symb_exec_r)
              apply (simp add: dc_def[symmetric])
              apply (rule corres_split_noop_rhs[OF updateMDB_symb_exec_r])
               apply (rule updateNewFreeIndex_noop_psp_corres)
              apply (wp getCTE_wp set_cdt_valid_objs set_cdt_cte_at
                        hoare_weak_lift_imp | simp add: o_def)+
    apply (clarsimp simp: cte_wp_at_cte_at)
   apply (clarsimp simp: cte_wp_at_ctes_of no_0_def valid_mdb'_def
                         valid_mdb_ctes_def)
   apply (rule conjI, clarsimp)
   apply clarsimp
   apply (erule (2) valid_dlistEn)
   apply simp
  apply(simp only: cdt_list_relation_def valid_mdb_def2)
  apply(subgoal_tac "finite_depth (cdt s)")
   prefer 2
   apply(simp add: finite_depth valid_mdb_def2[symmetric])
  apply(intro impI allI)
  apply(subgoal_tac "mdb_insert_abs (cdt s) p (a, b)")
   prefer 2
   apply(clarsimp simp: cte_wp_at_caps_of_state)
   apply(rule mdb_insert_abs.intro)
     apply(clarsimp)
    apply(erule (1) mdb_cte_at_Null_None)
   apply (erule (1) mdb_cte_at_Null_descendants)
  apply(subgoal_tac "no_0 (ctes_of s')")
   prefer 2
   apply(simp add: valid_mdb_ctes_def valid_mdb'_def)
  apply simp
  apply (elim conjE)
  apply (case_tac "cdt s (a,b)")
   prefer 2
   apply (simp add: mdb_insert_abs_def)
  apply simp
  apply(case_tac x)
  apply(simp add: cte_wp_at_ctes_of)
  apply(simp add: mdb_insert_abs.next_slot split del: if_split)
  apply(case_tac "c=p")
   apply(simp)
   apply(clarsimp simp: modify_map_def)
   apply(case_tac z)
   apply(fastforce split: if_split_asm)
  apply(case_tac "c = (a, b)")
   apply(simp)
   apply(case_tac "next_slot p (cdt_list s) (cdt s)")
    apply(simp)
   apply(simp)
   apply(clarsimp simp: modify_map_def const_def)
   apply(clarsimp split: if_split_asm)
    apply(drule_tac p="cte_map p" in valid_mdbD1')
      apply(simp)
     apply(simp add: valid_mdb'_def valid_mdb_ctes_def)
    apply(clarsimp simp: nullPointer_def no_0_def)
    apply(clarsimp simp: state_relation_def)
    apply(clarsimp simp: cte_wp_at_caps_of_state)
    apply(drule_tac slot=p in pspace_relation_ctes_ofI)
       apply(simp add: cte_wp_at_caps_of_state)
      apply(simp)
     apply(simp)
    apply(simp)
   apply(clarsimp simp: state_relation_def cdt_list_relation_def)
   apply(erule_tac x="fst p" in allE, erule_tac x="snd p" in allE)
   apply(fastforce)
  apply(simp)
  apply(case_tac "next_slot c (cdt_list s) (cdt s)")
   apply(simp)
  apply(simp)
  apply(subgoal_tac "cte_at c s")
   prefer 2
   apply(rule cte_at_next_slot)
      apply(simp_all add: valid_mdb_def2)[4]
  apply(clarsimp simp: modify_map_def const_def)
  apply(simp split: if_split_asm)
       apply(simp add: valid_mdb'_def)
       apply(drule_tac ptr="cte_map p" in no_self_loop_next)
        apply(simp)
       apply(simp)
      apply(drule_tac p="(aa, bb)" in cte_map_inj)
           apply(simp_all add: cte_wp_at_caps_of_state)[5]
       apply(clarsimp)
      apply(simp)
     apply(clarsimp)
     apply(drule cte_map_inj_eq; simp add: cte_wp_at_caps_of_state)
    apply(clarsimp)
    apply(case_tac z)
    apply(clarsimp simp: state_relation_def cdt_list_relation_def)
    apply(erule_tac x=aa in allE, erule_tac x=bb in allE)
    apply(fastforce)
   apply(clarsimp)
   apply(drule cte_map_inj_eq)
        apply(simp_all add: cte_wp_at_caps_of_state)[6]
  apply(clarsimp simp: state_relation_def cdt_list_relation_def)
  apply(erule_tac x=aa in allE, erule_tac x=bb in allE, fastforce)
  done

definition apitype_of :: "cap \<Rightarrow> apiobject_type option"
where
  "apitype_of c \<equiv> case c of
    Structures_A.UntypedCap d p b idx \<Rightarrow> Some ArchTypes_H.Untyped
  | Structures_A.EndpointCap r badge rights \<Rightarrow> Some EndpointObject
  | Structures_A.NotificationCap r badge rights \<Rightarrow> Some NotificationObject
  | Structures_A.CNodeCap r bits guard \<Rightarrow> Some ArchTypes_H.CapTableObject
  | Structures_A.ThreadCap r \<Rightarrow> Some TCBObject
  | _ \<Rightarrow> None"

lemma cte_wp_at_cteCaps_of:
  "cte_wp_at' (\<lambda>cte. P (cteCap cte)) p s
    = (\<exists>cap. cteCaps_of s p = Some cap \<and> P cap)"
  apply (subst tree_cte_cteCap_eq[unfolded o_def])
  apply (clarsimp split: option.splits)
  done

lemma caps_contained_modify_mdb_helper[simp]:
  "(\<exists>n. modify_map m p (cteMDBNode_update f) x = Some (CTE c n))
    = (\<exists>n. m x = Some (CTE c n))"
  apply (cases "m p", simp_all add: modify_map_def)
  apply (case_tac a, simp_all)
  done

lemma sameRegionAs_capRange_subset:
  "\<lbrakk> sameRegionAs c c'; capClass c = PhysicalClass \<rbrakk> \<Longrightarrow> capRange c' \<subseteq> capRange c"
  apply (erule sameRegionAsE)
      apply (rule equalityD1)
      apply (rule master_eqI, rule capRange_Master)
      apply simp
     apply assumption+
   apply (clarsimp simp: isCap_simps)+
  done


definition
  is_end_chunk :: "cte_heap \<Rightarrow> capability \<Rightarrow> machine_word \<Rightarrow> bool"
where
 "is_end_chunk ctes cap p \<equiv> \<exists>p'. ctes \<turnstile> p \<leadsto> p'
       \<and> (\<exists>cte. ctes p = Some cte \<and> sameRegionAs cap (cteCap cte))
       \<and> (\<forall>cte'. ctes p' = Some cte' \<longrightarrow> \<not> sameRegionAs cap (cteCap cte'))"

definition
  mdb_chunked2 :: "cte_heap \<Rightarrow> bool"
where
 "mdb_chunked2 ctes \<equiv> (\<forall>x p p' cte. ctes x = Some cte
         \<and> is_end_chunk ctes (cteCap cte) p \<and> is_end_chunk ctes (cteCap cte) p'
             \<longrightarrow> p = p')
      \<and> (\<forall>p p' cte cte'. ctes p = Some cte \<and> ctes p' = Some cte'
                 \<and> ctes \<turnstile> p \<leadsto> p' \<and> sameRegionAs (cteCap cte') (cteCap cte)
                      \<longrightarrow> sameRegionAs (cteCap cte) (cteCap cte'))"

lemma mdb_chunked2_revD:
  "\<lbrakk> ctes p = Some cte; ctes p' = Some cte'; ctes \<turnstile> p \<leadsto> p';
      mdb_chunked2 ctes; sameRegionAs (cteCap cte') (cteCap cte) \<rbrakk>
       \<Longrightarrow> sameRegionAs (cteCap cte) (cteCap cte')"
  by (fastforce simp add: mdb_chunked2_def)

lemma valid_dlist_step_back:
  "\<lbrakk> ctes \<turnstile> p \<leadsto> p''; ctes \<turnstile> p' \<leadsto> p''; valid_dlist ctes; p'' \<noteq> 0 \<rbrakk>
      \<Longrightarrow> p = p'"
  apply (simp add: mdb_next_unfold valid_dlist_def)
  apply (frule_tac x=p in spec)
  apply (drule_tac x=p' in spec)
  apply (clarsimp simp: Let_def)
  done

lemma chunk_sameRegionAs_step1:
  "\<lbrakk> ctes \<turnstile> p' \<leadsto>\<^sup>* p''; ctes p'' = Some cte;
      is_chunk ctes (cteCap cte) p p'';
      mdb_chunked2 ctes; valid_dlist ctes \<rbrakk> \<Longrightarrow>
     \<forall>cte'. ctes p' = Some cte'
     \<longrightarrow> ctes \<turnstile> p \<leadsto>\<^sup>+ p'
     \<longrightarrow> sameRegionAs (cteCap cte') (cteCap cte)"
  apply (erule converse_rtrancl_induct)
   apply (clarsimp simp: is_chunk_def)
   apply (drule_tac x=p'' in spec, clarsimp)
   apply (clarsimp simp: is_chunk_def)
  apply (frule_tac x=y in spec)
  apply (drule_tac x=z in spec)
  apply ((drule mp, erule(1) transitive_closure_trans)
              | clarsimp)+
  apply (rule sameRegionAs_trans[rotated], assumption)
  apply (drule(3) mdb_chunked2_revD)
   apply simp
   apply (erule(1) sameRegionAs_trans)
  apply simp
  done

end
locale mdb_insert_again_all = mdb_insert_again_child +
  assumes valid_c': "s \<turnstile>' c'"

  fixes n'
  defines "n' \<equiv> modify_map n (mdbNext parent_node) (cteMDBNode_update (mdbPrev_update (\<lambda>a. site)))"
begin
interpretation Arch . (*FIXME: arch-split*)
lemma no_0_n' [simp]: "no_0 n'"
  using no_0_n by (simp add: n'_def)

lemma dom_n' [simp]: "dom n' = dom n"
  apply (simp add: n'_def)
  apply (simp add: modify_map_if dom_def)
  apply (rule set_eqI)
  apply simp
  apply (rule iffI)
   apply auto[1]
  apply clarsimp
  apply (case_tac y)
  apply (case_tac "mdbNext parent_node = x")
   apply auto
  done

lemma mdb_chain_0_n' [simp]: "mdb_chain_0 n'"
  using chain_n
  apply (simp add: mdb_chain_0_def)
  apply (simp add: n'_def  trancl_prev_update)
  done

lemma parency_n':
  "n' \<turnstile> p \<rightarrow> p' = (if m \<turnstile> p \<rightarrow> parent \<or> p = parent
                 then m \<turnstile> p \<rightarrow> p' \<or> p' = site
                  else m \<turnstile> p \<rightarrow> p')"
  using descendants [of p]
  unfolding descendants_of'_def
  by (auto simp add: set_eq_iff n'_def)

lemma n'_direct_eq:
  "n' \<turnstile> p \<leadsto> p' = (if p = parent then p' = site else
                  if p = site then m \<turnstile> parent \<leadsto> p'
                  else m \<turnstile> p \<leadsto> p')"
  by (simp add: n'_def n_direct_eq)

lemma n'_tranclD:
  "n' \<turnstile> p \<leadsto>\<^sup>+ p' \<Longrightarrow>
  (if p = site then m \<turnstile> parent \<leadsto>\<^sup>+ p'
   else if m \<turnstile> p \<leadsto>\<^sup>+ parent \<or> p = parent  then m \<turnstile> p \<leadsto>\<^sup>+ p' \<or> p' = site
   else m \<turnstile> p \<leadsto>\<^sup>+ p')"
  apply (erule trancl_induct)
   apply (fastforce simp: n'_direct_eq split: if_split_asm)
  apply (fastforce simp: n'_direct_eq split: if_split_asm elim: trancl_trans)
  done

lemma site_in_dom: "site \<in> dom n"
  by (simp add: n)

lemma m_tranclD:
  assumes m: "m \<turnstile> p \<leadsto>\<^sup>+ p'"
  shows "p' \<noteq> site \<and> n' \<turnstile> p \<leadsto>\<^sup>+ p'"
proof -
  from m have "p = site \<longrightarrow> p' = 0" by clarsimp
  with mdb_chain_0_n' m
  show ?thesis
  apply -
  apply (erule trancl_induct)
   apply (rule context_conjI)
    apply clarsimp
   apply (cases "p = site")
    apply (simp add: mdb_chain_0_def site_in_dom)
   apply (cases "p = parent")
    apply simp
    apply (rule trancl_trans)
     apply (rule r_into_trancl)
     apply (simp add: n'_direct_eq)
    apply (rule r_into_trancl)
    apply (simp add: n'_direct_eq)
   apply (rule r_into_trancl)
   apply (simp add: n'_direct_eq)
  apply (rule context_conjI)
   apply clarsimp
  apply clarsimp
  apply (erule trancl_trans)
  apply (case_tac "y = parent")
   apply simp
   apply (rule trancl_trans)
    apply (rule r_into_trancl)
    apply (simp add: n'_direct_eq)
   apply (rule r_into_trancl)
   apply (simp add: n'_direct_eq)
  apply (rule r_into_trancl)
  apply (simp add: n'_direct_eq)
  done
qed

lemma n'_trancl_eq:
  "n' \<turnstile> p \<leadsto>\<^sup>+ p' =
  (if p = site then m \<turnstile> parent \<leadsto>\<^sup>+ p'
   else if m \<turnstile> p \<leadsto>\<^sup>+ parent \<or> p = parent  then m \<turnstile> p \<leadsto>\<^sup>+ p' \<or> p' = site
   else m \<turnstile> p \<leadsto>\<^sup>+ p')"
  apply simp
  apply (intro conjI impI iffI)
           apply (drule n'_tranclD)
           apply simp
          apply simp
         apply (drule n'_tranclD)
         apply simp
        apply (erule disjE)
         apply (drule m_tranclD)+
         apply simp
        apply (drule m_tranclD)
        apply simp
        apply (erule trancl_trans)
        apply (rule r_into_trancl)
        apply (simp add: n'_direct_eq)
       apply (drule n'_tranclD, simp)
      apply (erule disjE)
       apply (drule m_tranclD)
       apply simp
      apply simp
      apply (rule r_into_trancl)
      apply (simp add: n'_direct_eq)
     apply (drule n'_tranclD, simp)
    apply simp
    apply (cases "p' = site", simp)
    apply (drule m_tranclD)
    apply clarsimp
    apply (drule tranclD)
    apply (clarsimp simp: n'_direct_eq)
    apply (simp add: rtrancl_eq_or_trancl)
   apply (drule n'_tranclD, simp)
  apply clarsimp
  apply (drule m_tranclD, simp)
  done

lemma n'_rtrancl_eq:
  "n' \<turnstile> p \<leadsto>\<^sup>* p' =
   (if p = site then p' \<noteq> site \<and> m \<turnstile> parent \<leadsto>\<^sup>+ p' \<or> p' = site
    else if m \<turnstile> p \<leadsto>\<^sup>* parent then m \<turnstile> p \<leadsto>\<^sup>* p' \<or> p' = site
    else m \<turnstile> p \<leadsto>\<^sup>* p')"
  by (auto simp: rtrancl_eq_or_trancl n'_trancl_eq)

lemma mdbNext_parent_site [simp]:
  "mdbNext parent_node \<noteq> site"
proof
  assume "mdbNext parent_node = site"
  hence "m \<turnstile> parent \<leadsto> site"
    using parent
    by (unfold mdb_next_unfold) simp
  thus False by simp
qed

lemma mdbPrev_parent_site [simp]:
  "site \<noteq> mdbPrev parent_node"
proof
  assume "site = mdbPrev parent_node"
  with parent site
  have "m \<turnstile> site \<leadsto> parent"
    apply (unfold mdb_next_unfold)
    apply simp
    apply (erule dlistEp)
     apply clarsimp
    apply clarsimp
    done
  with p_0 show False by simp
qed

lemma parent_prev:
  "(m \<turnstile> parent \<leftarrow> p) = (p = mdbNext parent_node \<and> p \<noteq> 0)"
  apply (rule iffI)
   apply (frule dlist_prevD, rule parent)
   apply (simp add: mdb_next_unfold parent)
   apply (clarsimp simp: mdb_prev_def)
  apply clarsimp
  apply (rule dlist_nextD0)
   apply (rule parent_next)
  apply assumption
  done

lemma parent_next_prev:
  "(m \<turnstile> p \<leftarrow> mdbNext parent_node) = (p = parent \<and> mdbNext parent_node \<noteq> 0)"
  using parent
  apply -
  apply (rule iffI)
   apply (clarsimp simp add: mdb_prev_def)
   apply (rule conjI)
    apply (erule dlistEn)
     apply clarsimp
    apply simp
   apply clarsimp
  apply clarsimp
  apply (rule dlist_nextD0)
   apply (rule parent_next)
  apply assumption
  done


lemma n'_prev_eq:
  notes if_cong[cong del] if_weak_cong[cong]
  shows "n' \<turnstile> p \<leftarrow> p' = (if p' = site then p = parent
                         else if p = site then m \<turnstile> parent \<leftarrow> p'
                         else if p = parent then p' = site
                         else m \<turnstile> p \<leftarrow> p')"
  using parent site site_prev
  apply (simp add: n'_def n mdb_prev_def new_parent_def new_site_def split del: if_split)
  apply (clarsimp simp add: modify_map_if cong: if_cong split del: if_split)
  apply (cases "p' = site", simp)
  apply (simp cong: if_cong split del: if_split)
  apply (cases "p' = parent")
   apply clarsimp
   apply (rule conjI, clarsimp simp: mdb_prev_def)
   apply (clarsimp simp: mdb_prev_def)
  apply (simp cong: if_cong split del: if_split)
  apply (cases "p = site")
   apply (simp add: parent_prev)
   apply (cases "mdbNext parent_node = p'")
    apply simp
    apply (rule iffI)
     prefer 2
     apply clarsimp
     apply (erule dlistEn)
      apply simp
     apply clarsimp
     apply (case_tac cte')
     apply clarsimp
    apply clarsimp
   apply clarsimp
   apply (insert site_next)[1]
   apply (rule valid_dlistEp [OF dlist, where p=p'], assumption)
    apply clarsimp
   apply clarsimp
  apply (simp cong: if_cong split del: if_split)
  apply (cases "p = parent")
   apply clarsimp
   apply (insert site_next)
   apply (cases "mdbNext parent_node = p'", clarsimp)
   apply clarsimp
   apply (rule valid_dlistEp [OF dlist, where p=p'], assumption)
    apply clarsimp
   apply clarsimp
  apply simp
  apply (cases "mdbNext parent_node = p'")
   prefer 2
   apply (clarsimp simp: mdb_prev_def)
   apply (rule iffI, clarsimp)
   apply clarsimp
   apply (case_tac z)
   apply simp
  apply (rule iffI)
   apply (clarsimp simp: mdb_prev_def)
  apply (drule sym [where t=p'])
  apply (simp add: parent_next_prev)
  done

lemma dlist_n' [simp]:
  notes if_cong[cong del] if_weak_cong[cong]
  shows "valid_dlist n'"
  using no_0_n'
  by (clarsimp simp: valid_dlist_def2 n'_direct_eq
                     n'_prev_eq Invariants_H.valid_dlist_prevD [OF dlist])

lemma n'_cap:
  "n' p = Some (CTE c node) \<Longrightarrow>
  if p = site then c = c' \<and> m p = Some (CTE NullCap site_node)
  else \<exists>node'. m p = Some (CTE c node')"
  by (auto simp: n'_def n modify_map_if new_parent_def parent
                 new_site_def site site_cap split: if_split_asm)

lemma m_cap:
  "m p = Some (CTE c node) \<Longrightarrow>
  if p = site
  then \<exists>node'. n' site = Some (CTE c' node')
  else \<exists>node'. n' p = Some (CTE c node')"
  by (clarsimp simp: n n'_def new_parent_def new_site_def parent)

lemma n'_badged:
  "n' p = Some (CTE c node) \<Longrightarrow>
  if p = site then c = c' \<and> mdbFirstBadged node
  else \<exists>node'. m p = Some (CTE c node') \<and> mdbFirstBadged node = mdbFirstBadged node'"
  by (auto simp: n'_def n modify_map_if new_parent_def parent
                 new_site_def site site_cap split: if_split_asm)

lemma no_next_region:
  "\<lbrakk> m \<turnstile> parent \<leadsto> p'; m p' = Some (CTE cap' node) \<rbrakk> \<Longrightarrow> \<not>sameRegionAs c' cap'"
  apply (clarsimp simp: mdb_next_unfold parent)
  apply (frule next_wont_bite [rotated], clarsimp)
  apply simp
  done

lemma valid_badges_n' [simp]: "valid_badges n'"
  using valid_badges same_region parent
  apply (clarsimp simp: valid_badges_def valid_arch_badges_def)
  apply (simp add: n'_direct_eq)
  apply (drule n'_badged)+
  apply (clarsimp split: if_split_asm)
   apply (frule (1) no_next_region)
   apply (clarsimp simp: isCap_simps)
   apply (erule_tac x=parent in allE)
   apply simp
   apply (erule_tac x=p' in allE)
   apply (clarsimp simp: isCap_simps)
  apply (erule_tac x=p in allE)
  apply (erule_tac x=p' in allE)
  apply simp
  done

lemma c'_not_Null: "c' \<noteq> NullCap"
  using same_region by clarsimp

lemma valid_nullcaps_n' [simp]:
  "valid_nullcaps n'"
  using nullcaps is_untyped c'_not_Null
  apply (clarsimp simp: valid_nullcaps_def n'_def n modify_map_if new_site_def
                        new_parent_def isCap_simps)
  apply (erule allE)+
  apply (erule (1) impE)
  apply (simp add: nullMDBNode_def)
  apply (insert parent)
  apply (rule dlistEn, rule parent)
   apply clarsimp
  apply (clarsimp simp: nullPointer_def)
  done

lemma phys': "capClass parent_cap = PhysicalClass"
  using sameRegionAs_classes [OF same_region] phys
  by simp

lemma capRange_c': "capRange c' \<subseteq> capRange parent_cap"
  apply (rule sameRegionAs_capRange_subset)
   apply (rule same_region)
  apply (rule phys')
  done

lemma untypedRange_c':
  assumes ut: "isUntypedCap c'"
  shows "untypedRange c' \<subseteq> untypedRange parent_cap"
  using ut is_untyped capRange_c'
  by (auto simp: isCap_simps)

lemma sameRegion_parentI:
  "sameRegionAs c' cap \<Longrightarrow> sameRegionAs parent_cap cap"
  using same_region
  apply -
  apply (erule (1) sameRegionAs_trans)
  done

lemma no_loops_n': "no_loops n'"
  using mdb_chain_0_n' no_0_n'
  by (rule mdb_chain_0_no_loops)

lemmas no_loops_simps' [simp]=
  no_loops_trancl_simp [OF no_loops_n']
  no_loops_direct_simp [OF no_loops_n']

lemma rangeD:
  "\<lbrakk> m \<turnstile> parent \<rightarrow> p; m p = Some (CTE cap node) \<rbrakk> \<Longrightarrow>
  capRange cap \<inter> capRange c' = {}"
  using range by (rule descendants_rangeD')

lemma capAligned_c': "capAligned c'"
  using valid_c' by (rule valid_capAligned)

lemma capRange_ut:
  "capRange c' \<subseteq> untypedRange parent_cap"
  using capRange_c' is_untyped
  by (clarsimp simp: isCap_simps del: subsetI)

lemma untyped_mdb_n' [simp]: "untyped_mdb' n'"
  using untyped_mdb capRange_ut untyped_inc
  apply (clarsimp simp: untyped_mdb'_def descendants_of'_def)
  apply (drule n'_cap)+
  apply (simp add: parency_n')
  apply (simp split: if_split_asm)
    apply clarsimp
    apply (erule_tac x=parent in allE)
    apply (simp add: parent is_untyped)
    apply (erule_tac x=p' in allE)
    apply simp
    apply (frule untypedCapRange)
    apply (drule untypedRange_c')
    apply (erule impE, blast)
    apply (drule (1) rangeD)
    apply simp
   apply clarsimp
   apply (thin_tac "All P" for P)
   apply (simp add: untyped_inc'_def)
   apply (erule_tac x=parent in allE)
   apply (erule_tac x=p in allE)
   apply (simp add: parent is_untyped)
   apply (clarsimp simp: descendants_of'_def)
   apply (case_tac "untypedRange parent_cap = untypedRange c")
    apply simp
    apply (elim disjE conjE)
     apply (drule (1) rangeD)
     apply (drule untypedCapRange)
     apply simp
     apply blast
    apply simp
   apply (erule disjE)
    apply clarsimp
   apply (erule disjE)
    apply (simp add: psubsetI)
    apply (elim conjE)
    apply (drule (1) rangeD)
    apply (drule untypedCapRange)
    apply simp
    apply blast
   apply blast
  apply clarsimp
  done

lemma site':
  "n' site = Some new_site"
  by (simp add: n n'_def modify_map_if new_site_def)

lemma loopE: "m \<turnstile> x \<leadsto>\<^sup>+ x \<Longrightarrow> P"
  by simp

lemma m_loop_trancl_rtrancl:
  "m \<turnstile> y \<leadsto>\<^sup>* x \<Longrightarrow> \<not> m \<turnstile> x \<leadsto>\<^sup>+ y"
  apply clarsimp
  apply (drule(1) transitive_closure_trans)
  apply (erule loopE)
  done

lemma m_rtrancl_to_site:
  "m \<turnstile> p \<leadsto>\<^sup>* site = (p = site)"
  apply (rule iffI)
   apply (erule rtranclE)
    apply assumption
   apply simp
  apply simp
  done

lemma descendants_of'_D: "p' \<in> descendants_of' p ctes \<Longrightarrow> ctes \<turnstile> p \<rightarrow> p' "
  by (clarsimp simp:descendants_of'_def)

lemma untyped_inc_mdbD:
  "\<lbrakk> sameRegionAs cap cap'; isUntypedCap cap;
      ctes p = Some (CTE cap node); ctes p' = Some (CTE cap' node');
        untyped_inc' ctes; untyped_mdb' ctes; no_loops ctes \<rbrakk>
     \<Longrightarrow> ctes \<turnstile> p \<rightarrow> p' \<or> p = p' \<or>
          (isUntypedCap cap' \<and> untypedRange cap \<subseteq> untypedRange cap'
                  \<and> sameRegionAs cap' cap
                  \<and> ctes \<turnstile> p' \<rightarrow> p)"
  apply (subgoal_tac "untypedRange cap \<subseteq> untypedRange cap' \<longrightarrow> sameRegionAs cap' cap")
   apply (cases "isUntypedCap cap'")
    apply (drule(4) untyped_incD'[where p=p and p'=p'])
    apply (erule sameRegionAsE, simp_all add: untypedCapRange)[1]
       apply (cases "untypedRange cap = untypedRange cap'")
        apply simp
        apply (elim disjE conjE)
          apply (simp only: simp_thms descendants_of'_D)+
      apply (elim disjE conjE)
      apply (simp add: subset_iff_psubset_eq)
      apply (elim disjE)
       apply (simp add: descendants_of'_D)+
      apply (clarsimp simp: descendants_of'_def)
     apply (clarsimp simp: isCap_simps)
    apply (clarsimp simp: isCap_simps)
   apply clarsimp
   apply (erule sameRegionAsE)
       apply simp
      apply (drule(1) untyped_mdbD',simp)
         apply (simp add: untypedCapRange)
         apply blast
        apply simp
       apply assumption
      apply (simp add: descendants_of'_def)
     apply (clarsimp simp: isCap_simps)
    apply (clarsimp simp: isCap_simps)
   apply (clarsimp simp: isCap_simps)
  apply (clarsimp simp add: sameRegionAs_def3 del: disjCI)
  apply (rule disjI1)
  apply (erule disjE)
   apply (intro conjI)
     apply blast
    apply (simp add:untypedCapRange)
    apply (erule subset_trans[OF _ untypedRange_in_capRange])
   apply clarsimp
   apply (rule untypedRange_not_emptyD)
   apply (simp add:untypedCapRange)
   apply blast
  apply (clarsimp simp:isCap_simps)
  done

lemma parent_chunk:
  "is_chunk n' parent_cap parent site"
  by (clarsimp simp: is_chunk_def
                     n'_trancl_eq n'_rtrancl_eq site' new_site_def same_region
                     m_loop_trancl_rtrancl m_rtrancl_to_site)

lemma mdb_chunked_n' [simp]:
  notes if_cong[cong del] if_weak_cong[cong]
  shows "mdb_chunked n'"
  using chunked untyped_mdb untyped_inc
  apply (clarsimp simp: mdb_chunked_def)
  apply (drule n'_cap)+
  apply (simp add: n'_trancl_eq split del: if_split)
  apply (simp split: if_split_asm)
    apply clarsimp
    apply (frule sameRegion_parentI)
    apply (frule(1) untyped_inc_mdbD [OF _ is_untyped _ _ untyped_inc untyped_mdb no_loops, OF _ parent])
    apply (elim disjE)
      apply (frule sameRegionAs_capRange_Int)
         apply (simp add: phys)
        apply (rule valid_capAligned [OF valid_c'])
       apply (rule valid_capAligned)
       apply (erule valid_capI')
      apply (erule notE, erule(1) descendants_rangeD' [OF range, rotated])
     apply (clarsimp simp: parent parent_chunk)
    apply clarsimp
    apply (frule subtree_mdb_next)
    apply (simp add: m_loop_trancl_rtrancl [OF trancl_into_rtrancl, where x=parent])
    apply (case_tac "p' = parent")
     apply (clarsimp simp: parent)
    apply (drule_tac x=p' in spec)
    apply (drule_tac x=parent in spec)
    apply (frule sameRegionAs_trans [OF _ same_region])
    apply (clarsimp simp: parent is_chunk_def n'_trancl_eq n'_rtrancl_eq
                          m_rtrancl_to_site site' new_site_def)
    apply (prop_tac "mdb_chunked_arch_assms cap'", clarsimp simp: isCap_simps mdb_chunked_arch_assms_def)
    apply clarsimp
    apply (drule_tac x=p'' in spec)
    apply clarsimp
    apply (drule_tac p=p'' in m_cap, clarsimp)
   apply clarsimp
   apply (erule_tac x=p in allE)
   apply (erule_tac x=parent in allE)
   apply (insert parent is_untyped)[1]
   apply simp
   apply (case_tac "p = parent")
    apply (simp add: parent)
    apply (clarsimp simp add: is_chunk_def)
    apply (simp add: rtrancl_eq_or_trancl)
    apply (erule disjE)
     apply (clarsimp simp: site' new_site_def)
    apply clarsimp
    apply (drule tranclD)
    apply (clarsimp simp: n'_direct_eq)
    apply (drule (1) transitive_closure_trans)
    apply simp
   apply simp
   apply (case_tac "isUntypedCap cap")
    prefer 2
    apply (simp add: untyped_mdb'_def)
    apply (erule_tac x=parent in allE)
    apply simp
    apply (erule_tac x=p in allE)
    apply (simp add: descendants_of'_def)
    apply (drule mp[where P="S \<inter> T \<noteq> {}" for S T])
     apply (frule sameRegionAs_capRange_Int, simp add: phys)
       apply (rule valid_capAligned, erule valid_capI')
      apply (rule valid_capAligned, rule valid_c')
     apply (insert capRange_ut)[1]
     apply blast
    apply (drule (1) rangeD)
    apply (drule capRange_sameRegionAs, rule valid_c')
     apply (simp add: phys)
    apply simp
   apply (case_tac "untypedRange parent_cap \<subseteq> untypedRange cap")
    apply (erule impE)
     apply (clarsimp simp only: isCap_simps untypedRange.simps)
     apply (subst (asm) range_subset_eq)
      apply (drule valid_capI')+
      apply (drule valid_capAligned)+
      apply (clarsimp simp: capAligned_def)
      apply (erule is_aligned_no_overflow)
     apply (simp(no_asm) add: sameRegionAs_def3 isCap_simps)
     apply (drule valid_capI')+
     apply (drule valid_capAligned)+
     apply (clarsimp simp: capAligned_def is_aligned_no_overflow)
    apply clarsimp
    apply (erule disjE)
     apply simp
     apply (rule conjI)
      prefer 2
      apply clarsimp
      apply (drule (1) trancl_trans, erule loopE)
     apply (thin_tac "P \<longrightarrow> Q" for P Q)
     apply (clarsimp simp: is_chunk_def)
     apply (simp add: n'_trancl_eq n'_rtrancl_eq split: if_split_asm)
       apply (simp add: site' new_site_def)
      apply (erule_tac x=p'' in allE)
      apply clarsimp
      apply (drule_tac p=p'' in m_cap)
      apply clarsimp
     apply (simp add: rtrancl_eq_or_trancl)
    apply simp
    apply (rule conjI)
     apply clarsimp
     apply (drule (1) trancl_trans, erule loopE)
    apply clarsimp
    apply (clarsimp simp: is_chunk_def)
    apply (simp add: n'_trancl_eq n'_rtrancl_eq split: if_split_asm)
     apply (drule (1) transitive_closure_trans, erule loopE)
    apply (subgoal_tac "m \<turnstile> p \<rightarrow> parent")
     apply (drule subtree_mdb_next)
     apply (drule (1) trancl_trans, erule loopE)
    apply (thin_tac "All P" for P)
    apply (drule_tac p=parent and p'=p in untyped_incD'[rotated], assumption+)
    apply simp
    apply (subgoal_tac "\<not> m \<turnstile> parent \<rightarrow> p")
     prefer 2
     apply clarsimp
     apply (drule (1) rangeD)
     apply (drule capRange_sameRegionAs, rule valid_c')
      apply (simp add: phys)
     apply simp
    apply (clarsimp simp: descendants_of'_def subset_iff_psubset_eq)
    apply (erule disjE,simp,simp)
   apply (drule_tac p=parent and p'=p in untyped_incD'[rotated], assumption+)
   apply (simp add:subset_iff_psubset_eq descendants_of'_def)
    apply (elim disjE conjE| simp )+
      apply (drule(1) rangeD)
      apply (drule capRange_sameRegionAs[OF _ valid_c'])
       apply (simp add:phys)+
   apply (insert capRange_c' is_untyped)[1]
   apply (simp add: untypedCapRange [symmetric])
   apply (drule(1) disjoint_subset)
   apply (drule capRange_sameRegionAs[OF _ valid_c'])
    apply (simp add:phys)
   apply (simp add:Int_ac)
  apply clarsimp
  apply (erule_tac x=p in allE)
  apply (erule_tac x=p' in allE)
  apply clarsimp
  apply (erule disjE)
   apply simp
   apply (thin_tac "P \<longrightarrow> Q" for P Q)
   apply (subgoal_tac "is_chunk n' cap p p'")
    prefer 2
    apply (clarsimp simp: is_chunk_def)
    apply (simp add: n'_trancl_eq n'_rtrancl_eq split: if_split_asm)
        apply (erule disjE)
         apply (erule_tac x=parent in allE)
         apply clarsimp
         apply (erule impE, fastforce)
         apply (clarsimp simp: parent)
         apply (simp add: site' new_site_def)
         apply (erule sameRegionAs_trans, rule same_region)
        apply (clarsimp simp add: parent)
        apply (simp add: site' new_site_def)
        apply (rule same_region)
       apply (erule_tac x=p'' in allE)
       apply clarsimp
       apply (drule_tac p=p'' in m_cap)
       apply clarsimp
      apply (erule_tac x=p'' in allE)
      apply clarsimp
      apply (drule_tac p=p'' in m_cap)
      apply clarsimp
     apply (erule_tac x=p'' in allE)
     apply clarsimp
     apply (drule_tac p=p'' in m_cap)
     apply clarsimp
    apply (erule_tac x=p'' in allE)
    apply clarsimp
    apply (drule_tac p=p'' in m_cap)
    apply clarsimp
   apply simp
   apply (rule conjI)
    apply clarsimp
    apply (rule conjI)
     apply clarsimp
     apply (drule (1) trancl_trans, erule loopE)
    apply (rule conjI, clarsimp)
     apply (drule (1) trancl_trans, erule loopE)
    apply clarsimp
    apply (drule (1) trancl_trans, erule loopE)
   apply (rule conjI)
    apply clarsimp
    apply (drule (1) trancl_trans, erule loopE)
   apply clarsimp
   apply (rule conjI)
    apply clarsimp
    apply (drule (1) trancl_trans, erule loopE)
   apply (rule conjI, clarsimp)
   apply clarsimp
   apply (drule (1) trancl_trans, erule loopE)
  apply simp
  apply (thin_tac "P \<longrightarrow> Q" for P Q)
  apply (subgoal_tac "is_chunk n' cap' p' p")
   prefer 2
   apply (clarsimp simp: is_chunk_def)
   apply (simp add: n'_trancl_eq n'_rtrancl_eq split: if_split_asm)
       apply (erule disjE)
        apply (erule_tac x=parent in allE)
        apply clarsimp
        apply (erule impE, fastforce)
        apply (clarsimp simp: parent)
        apply (simp add: site' new_site_def)
        apply (erule sameRegionAs_trans, rule same_region)
       apply (clarsimp simp add: parent)
       apply (simp add: site' new_site_def)
       apply (rule same_region)
      apply (erule_tac x=p'' in allE)
      apply clarsimp
      apply (drule_tac p=p'' in m_cap)
      apply clarsimp
     apply (erule_tac x=p'' in allE)
     apply clarsimp
     apply (drule_tac p=p'' in m_cap)
     apply clarsimp
    apply (erule_tac x=p'' in allE)
    apply clarsimp
    apply (drule_tac p=p'' in m_cap)
    apply clarsimp
   apply (erule_tac x=p'' in allE)
   apply clarsimp
   apply (drule_tac p=p'' in m_cap)
   apply clarsimp
  apply simp
  apply (rule conjI)
   apply clarsimp
   apply (rule conjI)
    apply clarsimp
    apply (drule (1) trancl_trans, erule loopE)
   apply (rule conjI, clarsimp)
    apply (drule (1) trancl_trans, erule loopE)
   apply clarsimp
   apply (drule (1) trancl_trans, erule loopE)
  apply (rule conjI)
   apply clarsimp
   apply (drule (1) trancl_trans, erule loopE)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (drule (1) trancl_trans, erule loopE)
  apply (rule conjI, clarsimp)
  apply clarsimp
  apply (drule (1) trancl_trans, erule loopE)
  done

lemma caps_contained_n' [simp]: "caps_contained' n'"
  using caps_contained untyped_mdb untyped_inc
  apply (clarsimp simp: caps_contained'_def)
  apply (drule n'_cap)+
  apply (clarsimp split: if_split_asm)
     apply (drule capRange_untyped)
     apply simp
    apply (frule capRange_untyped)
    apply (frule untypedRange_c')
    apply (erule_tac x=parent in allE)
    apply (erule_tac x=p' in allE)
    apply (simp add: parent)
    apply (erule impE, blast)
    apply (simp add: untyped_mdb'_def)
    apply (erule_tac x=parent in allE)
    apply (erule_tac x=p' in allE)
    apply (simp add: parent is_untyped descendants_of'_def)
    apply (erule impE)
     apply (thin_tac "m site = t" for t)
     apply (drule valid_capI')
     apply (frule valid_capAligned)
     apply blast
    apply (drule (1) rangeD)
    apply (frule capRange_untyped)
    apply (drule untypedCapRange)
    apply simp
   apply (thin_tac "All P" for P)
   apply (insert capRange_c')[1]
   apply (simp add: untypedCapRange is_untyped)
   apply (subgoal_tac "untypedRange parent_cap \<inter> untypedRange c \<noteq> {}")
    prefer 2
    apply blast
   apply (frule untyped_incD'[OF _ capRange_untyped _ is_untyped])
    apply (case_tac c)
      apply simp_all
    apply (simp add:isCap_simps)
    apply (rule parent)
   apply clarsimp
   apply (case_tac "untypedRange c = untypedRange parent_cap")
    apply blast
   apply simp
   apply (elim disjE)
     apply (drule_tac A = "untypedRange c" in psubsetI)
      apply simp+
     apply (thin_tac "P\<longrightarrow>Q" for P Q)
     apply (elim conjE)
     apply (simp add:descendants_of'_def)
     apply (drule(1) rangeD)
     apply (frule capRange_untyped)
     apply (simp add:untypedCapRange Int_ac)
    apply blast
   apply (simp add:descendants_of'_def)
   apply blast
  apply blast
  done

lemma untyped_inc_n' [simp]: "untypedRange c' \<inter> usableUntypedRange parent_cap = {} \<Longrightarrow> untyped_inc' n'"
  using untyped_inc
  apply (clarsimp simp: untyped_inc'_def)
  apply (drule n'_cap)+
  apply (clarsimp simp: descendants_of'_def parency_n' split: if_split_asm)
    apply (frule untypedRange_c')
    apply (insert parent is_untyped)[1]
    apply (erule_tac x=parent in allE)
    apply (erule_tac x=p' in allE)
    apply clarsimp
    apply (case_tac "untypedRange parent_cap = untypedRange c'a")
     apply simp
     apply (intro conjI)
       apply (intro impI)
       apply (elim disjE conjE)
         apply (drule(1) subtree_trans,simp)
        apply (simp add:subset_not_psubset)
       apply simp
      apply (clarsimp simp:subset_not_psubset)
      apply (drule valid_capI')+
      apply (drule(2) disjoint_subset[OF usableRange_subseteq[OF valid_capAligned],rotated -1])
      apply simp
     apply (clarsimp)
     apply (rule int_not_empty_subsetD)
       apply (drule(1) rangeD)
       apply (simp add:untypedCapRange Int_ac)
      apply (erule aligned_untypedRange_non_empty[OF valid_capAligned[OF valid_c']])
     apply (erule(1) aligned_untypedRange_non_empty[OF valid_capAligned[OF valid_capI']])
    apply simp
    apply (erule subset_splitE)
       apply (simp|elim conjE)+
       apply (thin_tac "P \<longrightarrow> Q" for P Q)+
       apply blast
      apply (simp|elim conjE)+
      apply (thin_tac "P \<longrightarrow> Q" for P Q)+
      apply (intro conjI,intro impI,drule(1) subtree_trans,simp)
       apply clarsimp
      apply (intro impI)
      apply (drule(1) rangeD)
      apply (simp add:untypedCapRange Int_ac)
      apply (rule int_not_empty_subsetD)
        apply (simp add:Int_ac)
       apply (erule aligned_untypedRange_non_empty[OF valid_capAligned[OF valid_c']])
      apply (erule(1) aligned_untypedRange_non_empty[OF valid_capAligned[OF valid_capI']])
     apply simp
    apply (thin_tac "P \<longrightarrow> Q" for P Q)+
    apply (drule(1) disjoint_subset[rotated])
    apply simp
    apply (drule_tac B = "untypedRange c'a" in int_not_empty_subsetD)
      apply (erule aligned_untypedRange_non_empty[OF capAligned_c'])
     apply (erule(1) aligned_untypedRange_non_empty[OF valid_capAligned[OF valid_capI']])
    apply simp
   apply (frule untypedRange_c')
   apply (insert parent is_untyped)[1]
   apply (erule_tac x=p in allE)
   apply (erule_tac x=parent in allE)
   apply clarsimp
   apply (case_tac "untypedRange parent_cap = untypedRange c")
    apply simp
    apply (intro conjI)
      apply (intro impI)
      apply (elim disjE conjE)
        apply (clarsimp simp:subset_not_psubset )+
       apply (drule(1) subtree_trans,simp)
      apply simp
     apply (clarsimp simp:subset_not_psubset)
     apply (drule disjoint_subset[OF usableRange_subseteq[OF valid_capAligned[OF valid_capI']],rotated])
       apply simp
      apply assumption
     apply simp
    apply clarsimp
    apply (rule int_not_empty_subsetD)
      apply (drule(1) rangeD)
      apply (simp add:untypedCapRange Int_ac)
     apply (erule(1) aligned_untypedRange_non_empty[OF valid_capAligned[OF valid_capI']])
    apply (erule aligned_untypedRange_non_empty[OF capAligned_c'])
   apply simp
   apply (erule subset_splitE)
      apply (simp|elim conjE)+
      apply (thin_tac "P \<longrightarrow> Q" for P Q)+
      apply (intro conjI,intro impI,drule(1) subtree_trans,simp)
       apply clarsimp
      apply (intro impI)
      apply (drule(1) rangeD)
      apply (simp add:untypedCapRange Int_ac)
      apply (rule int_not_empty_subsetD)
        apply (simp add:Int_ac)
       apply (erule(1) aligned_untypedRange_non_empty[OF valid_capAligned[OF valid_capI']])
      apply (erule aligned_untypedRange_non_empty[OF valid_capAligned[OF valid_c']])
     apply simp
     apply (thin_tac "P\<longrightarrow>Q" for P Q)+
     apply blast
    apply (thin_tac "P\<longrightarrow>Q" for P Q)+
    apply simp
   apply (drule(1) disjoint_subset2[rotated])
   apply simp
   apply (drule_tac B = "untypedRange c'" in int_not_empty_subsetD)
     apply (erule(1) aligned_untypedRange_non_empty[OF valid_capAligned[OF valid_capI']])
    apply (erule aligned_untypedRange_non_empty[OF capAligned_c'])
   apply simp
  apply (erule_tac x=p in allE)
  apply (erule_tac x=p' in allE)
  apply simp
  apply blast
  done

lemma ut_rev_n' [simp]: "ut_revocable' n'"
  using ut_rev
  apply (clarsimp simp: ut_revocable'_def n'_def n_def)
  apply (clarsimp simp: modify_map_if split: if_split_asm)
  done

lemma class_links_m: "class_links m"
  using valid
  by (simp add: valid_mdb_ctes_def)

lemma parent_phys: "capClass parent_cap = PhysicalClass"
  using is_untyped
  by (clarsimp simp: isCap_simps)

lemma class_links [simp]: "class_links n'"
  using class_links_m
  apply (clarsimp simp add: class_links_def)
  apply (simp add: n'_direct_eq
            split: if_split_asm)
    apply (case_tac cte,
           clarsimp dest!: n'_cap simp: site' parent new_site_def phys parent_phys)
   apply (drule_tac x=parent in spec)
   apply (drule_tac x=p' in spec)
   apply (case_tac cte')
   apply (clarsimp simp: site' new_site_def parent parent_phys phys dest!: n'_cap
                  split: if_split_asm)
  apply (case_tac cte, case_tac cte')
  apply (clarsimp dest!: n'_cap split: if_split_asm)
  apply fastforce
  done

lemma irq_control_n' [simp]:
  "irq_control n'"
  using irq_control phys
  apply (clarsimp simp: irq_control_def)
  apply (clarsimp simp: n'_def n_def)
  apply (clarsimp simp: modify_map_if split: if_split_asm)
  done

lemma dist_z_m:
  "distinct_zombies m"
  using valid by auto

lemma dist_z [simp]:
  "distinct_zombies n'"
  using dist_z_m
  apply (simp add: n'_def distinct_zombies_nonCTE_modify_map)
  apply (simp add: n_def distinct_zombies_nonCTE_modify_map
                   fun_upd_def[symmetric])
  apply (erule distinct_zombies_seperateE, simp)
  apply (case_tac cte, clarsimp)
  apply (rename_tac cap node)
  apply (subgoal_tac "capRange cap \<inter> capRange c' \<noteq> {}")
   apply (frule untyped_mdbD' [OF _ _ _ _ _ untyped_mdb, OF parent])
      apply (simp add: is_untyped)
     apply (clarsimp simp add: untypedCapRange[OF is_untyped, symmetric])
     apply (drule disjoint_subset2 [OF capRange_c'])
     apply simp
    apply simp
   apply (simp add: descendants_of'_def)
   apply (drule(1) rangeD)
   apply simp
  apply (drule capAligned_capUntypedPtr [OF capAligned_c'])
  apply (frule valid_capAligned [OF valid_capI'])
  apply (drule(1) capAligned_capUntypedPtr)
  apply auto
  done

lemma reply_masters_rvk_fb_m:
  "reply_masters_rvk_fb m"
  using valid by auto

lemma reply_masters_rvk_fb_n[simp]:
  "reply_masters_rvk_fb n'"
  using reply_masters_rvk_fb_m
  apply (simp add: reply_masters_rvk_fb_def n'_def ball_ran_modify_map_eq
                   n_def fun_upd_def[symmetric])
  apply (rule ball_ran_fun_updI, assumption)
  apply clarsimp
  done

lemma valid_n':
  "untypedRange c' \<inter> usableUntypedRange parent_cap = {} \<Longrightarrow> valid_mdb_ctes n'"
  by auto

end

lemma caps_overlap_reserved'_D:
  "\<lbrakk>caps_overlap_reserved' S s; ctes_of s p = Some cte;isUntypedCap (cteCap cte)\<rbrakk> \<Longrightarrow> usableUntypedRange (cteCap cte) \<inter> S = {}"
  apply (simp add:caps_overlap_reserved'_def)
  apply (erule ballE)
   apply (erule(2) impE)
  apply fastforce
  done

context begin interpretation Arch . (*FIXME: arch-split*)
lemma insertNewCap_valid_mdb:
  "\<lbrace>valid_mdb' and valid_objs' and K (slot \<noteq> p) and
    caps_overlap_reserved' (untypedRange cap) and
    cte_wp_at' (\<lambda>cte. isUntypedCap (cteCap cte) \<and>
                      sameRegionAs (cteCap cte) cap) p and
    K (\<not>isZombie cap) and valid_cap' cap and
    (\<lambda>s. descendants_range' cap p (ctes_of s))\<rbrace>
  insertNewCap p slot cap
  \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  apply (clarsimp simp: insertNewCap_def valid_mdb'_def)
  apply (wp getCTE_ctes_of | simp add: o_def)+
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (rule conjI)
   apply (clarsimp simp: no_0_def valid_mdb_ctes_def)
  apply (case_tac cte)
  apply (rename_tac p_cap p_node)
  apply (clarsimp cong: if_cong)
  apply (case_tac ya)
  apply (rename_tac node)
  apply (clarsimp simp: nullPointer_def)
  apply (rule mdb_insert_again_all.valid_n')
   apply unfold_locales[1]
                apply (assumption|rule refl)+
        apply (frule sameRegionAs_classes, clarsimp simp: isCap_simps)
       apply (erule (1) ctes_of_valid_cap')
      apply (simp add: valid_mdb_ctes_def)
     apply simp
    apply (clarsimp simp: isMDBParentOf_CTE)
    apply (clarsimp simp: isCap_simps valid_mdb_ctes_def ut_revocable'_def)
   apply assumption
  apply (drule(1) caps_overlap_reserved'_D)
    apply simp
  apply (simp add:Int_ac)
  done

(* FIXME: move *)
lemma no_default_zombie:
  "cap_relation (default_cap tp p sz d) cap \<Longrightarrow> \<not>isZombie cap"
  by (cases tp, auto simp: isCap_simps)

lemmas updateNewFreeIndex_typ_ats[wp] = typ_at_lifts[OF updateNewFreeIndex_typ_at']

lemma updateNewFreeIndex_valid_objs[wp]:
  "\<lbrace>valid_objs'\<rbrace> updateNewFreeIndex slot \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (simp add: updateNewFreeIndex_def getSlotCap_def)
  apply (wp getCTE_wp' | wpc | simp add: updateTrackedFreeIndex_def)+
  done

lemma insertNewCap_valid_objs [wp]:
  "\<lbrace> valid_objs' and valid_cap' cap and pspace_aligned' and pspace_distinct'\<rbrace>
  insertNewCap parent slot cap
  \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (simp add: insertNewCap_def)
  apply (wp setCTE_valid_objs getCTE_wp')
  apply clarsimp
  done

lemma insertNewCap_valid_cap [wp]:
  "\<lbrace> valid_cap' c \<rbrace>
  insertNewCap parent slot cap
  \<lbrace>\<lambda>_. valid_cap' c\<rbrace>"
  apply (simp add: insertNewCap_def)
  apply (wp getCTE_wp')
  apply clarsimp
  done

lemmas descendants_of'_mdbPrev = descendants_of_prev_update

lemma insertNewCap_ranges:
  "\<lbrace>\<lambda>s. descendants_range' c p (ctes_of s) \<and>
   descendants_range' cap p (ctes_of s) \<and>
   capRange c \<inter> capRange cap = {} \<and>
   cte_wp_at' (\<lambda>cte. isUntypedCap (cteCap cte) \<and>
                     sameRegionAs (cteCap cte) cap) p s \<and>
   valid_mdb' s \<and> valid_objs' s\<rbrace>
  insertNewCap p slot cap
  \<lbrace>\<lambda>_ s. descendants_range' c p (ctes_of s)\<rbrace>"
  apply (simp add: insertNewCap_def)
  apply (wp getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (rule conjI)
   apply (clarsimp simp: valid_mdb'_def valid_mdb_ctes_def no_0_def)
  apply (case_tac ctea)
  apply (case_tac cteb)
  apply (clarsimp simp: nullPointer_def cong: if_cong)
  apply (simp (no_asm) add: descendants_range'_def descendants_of'_mdbPrev)
  apply (subst mdb_insert_again_child.descendants)
   apply unfold_locales[1]
               apply (simp add: valid_mdb'_def)
              apply (assumption|rule refl)+
       apply (frule sameRegionAs_classes, clarsimp simp: isCap_simps)
      apply (erule (1) ctes_of_valid_cap')
     apply (simp add: valid_mdb'_def valid_mdb_ctes_def)
    apply clarsimp
   apply (clarsimp simp: isMDBParentOf_def isArchMDBParentOf_def2)
   apply (clarsimp simp: isCap_simps valid_mdb'_def
                         valid_mdb_ctes_def ut_revocable'_def)
  apply clarsimp
  apply (rule context_conjI, blast)
  apply (clarsimp simp: descendants_range'_def)
  done

lemma insertNewCap_overlap_reserved'[wp]:
  "\<lbrace>\<lambda>s. caps_overlap_reserved' (capRange c) s\<and>
   capRange c \<inter> capRange cap = {} \<and> capAligned cap \<and>
   cte_wp_at' (\<lambda>cte. isUntypedCap (cteCap cte) \<and>
                     sameRegionAs (cteCap cte) cap) p s \<and>
   valid_mdb' s \<and> valid_objs' s\<rbrace>
  insertNewCap p slot cap
  \<lbrace>\<lambda>_ s. caps_overlap_reserved' (capRange c) s\<rbrace>"
  apply (simp add: insertNewCap_def caps_overlap_reserved'_def)
  apply (wp getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (rule conjI)
   apply (clarsimp simp: valid_mdb'_def valid_mdb_ctes_def no_0_def)
  apply (case_tac ctea)
  apply (case_tac cteb)
  apply (clarsimp simp: nullPointer_def ball_ran_modify_map_eq
                        caps_overlap_reserved'_def[symmetric])
  apply (clarsimp simp: ran_def split: if_splits)
  apply (case_tac "slot = a")
   apply clarsimp
   apply (rule disjoint_subset)
    apply (erule(1) usableRange_subseteq)
   apply (simp add:untypedCapRange Int_ac)+
  apply (subst Int_commute)
  apply (erule(2) caps_overlap_reserved'_D)
  done

crunch insertNewCap
  for ksArch[wp]: "\<lambda>s. P (ksArchState s)"
  (wp: crunch_wps)

lemma inv_untyped_corres_helper1:
  "list_all2 cap_relation (map (\<lambda>ref. default_cap tp ref sz d) orefs) cps
   \<Longrightarrow>
   corres dc
      (\<lambda>s. pspace_aligned s \<and> pspace_distinct s
          \<and> valid_objs s \<and> valid_mdb s \<and> valid_list s
          \<and> cte_wp_at is_untyped_cap p s
          \<and> (\<forall>tup \<in> set (zip crefs orefs).
              cte_wp_at (\<lambda>c. cap_range (default_cap tp (snd tup) sz d) \<subseteq> untyped_range c) p s)
          \<and> (\<forall>tup \<in> set (zip crefs orefs).
              descendants_range (default_cap tp (snd tup) sz d) p s)
          \<and> (\<forall>tup \<in> set (zip crefs orefs).
              caps_overlap_reserved (untyped_range (default_cap tp (snd tup) sz d)) s)
          \<and> (\<forall>tup \<in> set (zip crefs orefs). real_cte_at (fst tup) s)
          \<and> (\<forall>tup \<in> set (zip crefs orefs).
              cte_wp_at ((=) cap.NullCap) (fst tup) s)
          \<and> distinct (p # (map fst (zip crefs orefs)))
          \<and> distinct_sets (map (\<lambda>tup. cap_range (default_cap tp (snd tup) sz d)) (zip crefs orefs))
          \<and> (\<forall>tup \<in> set (zip crefs orefs).
              valid_cap (default_cap tp (snd tup) sz d) s))
      (\<lambda>s. (\<forall>tup \<in> set (zip (map cte_map crefs) cps). valid_cap' (snd tup) s)
         \<and> (\<forall>tup \<in> set (zip (map cte_map crefs) cps). cte_wp_at' (\<lambda>c. cteCap c = NullCap) (fst tup) s)
         \<and> cte_wp_at' (\<lambda>cte. isUntypedCap (cteCap cte) \<and>
                         (\<forall>tup \<in> set (zip (map cte_map crefs) cps).
                               sameRegionAs (cteCap cte) (snd tup)))
              (cte_map p) s
         \<and> distinct ((cte_map p) # (map fst (zip (map cte_map crefs) cps)))
         \<and> valid_mdb' s \<and> valid_objs' s \<and> pspace_aligned' s \<and> pspace_distinct' s
         \<and> (\<forall>tup \<in> set (zip (map cte_map crefs) cps). descendants_range' (snd tup) (cte_map p) (ctes_of s))
         \<and> (\<forall>tup \<in> set (zip (map cte_map crefs) cps).
              caps_overlap_reserved' (capRange (snd tup)) s)
         \<and> distinct_sets (map capRange (map snd (zip (map cte_map crefs) cps))))
      (sequence_x (map (create_cap tp sz p d) (zip crefs orefs)))
      (zipWithM_x (insertNewCap (cte_map p))
             ((map cte_map crefs)) cps)"
  apply (simp add: zipWithM_x_def zipWith_def split_def)
  apply (fold mapM_x_def)
  apply (rule corres_list_all2_mapM_)
     apply (rule corres_guard_imp)
       apply (erule insertNewCap_corres)
      apply (clarsimp simp: cte_wp_at_def is_cap_simps)
     apply (clarsimp simp: fun_upd_def cte_wp_at_ctes_of)
    apply clarsimp
    apply (rule hoare_pre, wp hoare_vcg_const_Ball_lift)
    apply clarsimp
    apply (rule conjI)
     apply (clarsimp simp: cte_wp_at_caps_of_state
                           cap_range_def[where c="default_cap a b c d" for a b c d])
     apply (drule(2) caps_overlap_reservedD[rotated])
     apply (simp add:Int_ac)
    apply (rule conjI)
     apply (clarsimp simp: valid_cap_def)
    apply (rule conjI)
     apply (clarsimp simp: cte_wp_at_caps_of_state)
    apply (rule conjI)
     apply (clarsimp simp:Int_ac)
     apply (erule disjoint_subset2[rotated])
     apply fastforce
    apply clarsimp
    apply (rule conjI)
     apply clarsimp
     apply (rule conjI)
      subgoal by fastforce
     apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps valid_cap_def)
    apply (fastforce simp: image_def)
   apply (rule hoare_pre)
    apply (wp
              hoare_vcg_const_Ball_lift
              insertNewCap_valid_mdb hoare_vcg_all_lift insertNewCap_ranges
               | subst cte_wp_at_cteCaps_of)+
   apply (subst(asm) cte_wp_at_cteCaps_of)+
   apply (clarsimp simp only:)
   apply simp
   apply (rule conjI)
    apply clarsimp
    apply (thin_tac "cte_map p \<notin> S" for S)
    apply (erule notE, erule rev_image_eqI)
    apply simp
   apply (rule conjI,clarsimp+)
   apply (rule conjI,erule caps_overlap_reserved'_subseteq)
   apply (rule untypedRange_in_capRange)
   apply (rule conjI,erule no_default_zombie)
   apply (rule conjI, clarsimp simp:Int_ac)
    apply fastforce
   apply (clarsimp simp:Int_ac valid_capAligned )
    apply fastforce
  apply (rule list_all2_zip_split)
   apply (simp add: list_all2_map2 list_all2_refl)
  apply (simp add: list_all2_map1)
  done

lemma createNewCaps_valid_pspace_extras:
  "\<lbrace>(\<lambda>s.    n \<noteq> 0 \<and> ptr \<noteq> 0 \<and> range_cover ptr sz (APIType_capBits ty us) n
          \<and> sz \<le> maxUntypedSizeBits \<and> canonical_address (ptr && ~~ mask sz)
          \<and> pspace_no_overlap' ptr sz s
          \<and> valid_pspace' s \<and> caps_no_overlap'' ptr sz s
          \<and> caps_overlap_reserved' {ptr .. ptr + of_nat n * 2 ^ APIType_capBits ty us - 1} s
          \<and> ksCurDomain s \<le> maxDomain
   )\<rbrace>
     createNewCaps ty ptr n us d
   \<lbrace>\<lambda>rv. pspace_aligned'\<rbrace>"
  "\<lbrace>(\<lambda>s.    n \<noteq> 0 \<and> ptr \<noteq> 0 \<and> range_cover ptr sz (APIType_capBits ty us) n
          \<and> sz \<le> maxUntypedSizeBits \<and> canonical_address (ptr && ~~ mask sz)
          \<and> pspace_no_overlap' ptr sz s
          \<and> valid_pspace' s \<and> caps_no_overlap'' ptr sz s
          \<and> caps_overlap_reserved' {ptr .. ptr + of_nat n * 2 ^ APIType_capBits ty us - 1} s
          \<and> ksCurDomain s \<le> maxDomain
   )\<rbrace>
     createNewCaps ty ptr n us d
   \<lbrace>\<lambda>rv. pspace_canonical'\<rbrace>"
  "\<lbrace>(\<lambda>s.    n \<noteq> 0 \<and> ptr \<noteq> 0 \<and> range_cover ptr sz (APIType_capBits ty us) n
          \<and> sz \<le> maxUntypedSizeBits \<and> canonical_address (ptr && ~~ mask sz)
          \<and> pspace_no_overlap' ptr sz s
          \<and> valid_pspace' s \<and> caps_no_overlap'' ptr sz s
          \<and> caps_overlap_reserved' {ptr .. ptr + of_nat n * 2 ^ APIType_capBits ty us - 1} s
          \<and> ksCurDomain s \<le> maxDomain
   )\<rbrace>
     createNewCaps ty ptr n us d
   \<lbrace>\<lambda>rv. pspace_distinct'\<rbrace>"
  "\<lbrace>(\<lambda>s.    n \<noteq> 0 \<and> ptr \<noteq> 0 \<and> range_cover ptr sz (APIType_capBits ty us) n
          \<and> sz \<le> maxUntypedSizeBits \<and> canonical_address (ptr && ~~ mask sz)
          \<and> pspace_no_overlap' ptr sz s
          \<and> valid_pspace' s \<and> caps_no_overlap'' ptr sz s
          \<and> caps_overlap_reserved' {ptr .. ptr + of_nat n * 2 ^ APIType_capBits ty us - 1} s
          \<and> ksCurDomain s \<le> maxDomain
   )\<rbrace>
     createNewCaps ty ptr n us d
   \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  "\<lbrace>(\<lambda>s.    n \<noteq> 0 \<and> ptr \<noteq> 0 \<and> range_cover ptr sz (APIType_capBits ty us) n
          \<and> sz \<le> maxUntypedSizeBits \<and> canonical_address (ptr && ~~ mask sz)
          \<and> pspace_no_overlap' ptr sz s
          \<and> valid_pspace' s \<and> caps_no_overlap'' ptr sz s
          \<and> caps_overlap_reserved' {ptr .. ptr + of_nat n * 2 ^ APIType_capBits ty us - 1} s
          \<and> ksCurDomain s \<le> maxDomain
   )\<rbrace>
     createNewCaps ty ptr n us d
   \<lbrace>\<lambda>rv. valid_objs'\<rbrace>"
      apply (rule hoare_grab_asm)+
      apply (rule hoare_pre,rule hoare_strengthen_post[OF createNewCaps_valid_pspace])
           apply (simp add:valid_pspace'_def)+
     apply (rule hoare_grab_asm)+
     apply (rule hoare_pre,rule hoare_strengthen_post[OF createNewCaps_valid_pspace])
          apply (simp add:valid_pspace'_def)+
    apply (rule hoare_grab_asm)+
    apply (rule hoare_pre,rule hoare_strengthen_post[OF createNewCaps_valid_pspace])
         apply (simp add:valid_pspace'_def)+
   apply (rule hoare_grab_asm)+
   apply (rule hoare_pre,rule hoare_strengthen_post[OF createNewCaps_valid_pspace])
        apply (simp add:valid_pspace'_def)+
  apply (rule hoare_grab_asm)+
  apply (rule hoare_pre,rule hoare_strengthen_post[OF createNewCaps_valid_pspace])
       apply (simp add:valid_pspace'_def)+
  done

declare map_fst_zip_prefix[simp]

declare map_snd_zip_prefix[simp]

declare word_unat_power [symmetric, simp del]

lemma createNewCaps_range_helper:
  "\<lbrace>\<lambda>s. range_cover ptr sz (APIType_capBits tp us) n \<and> 0 < n\<rbrace>
     createNewCaps tp ptr n us d
   \<lbrace>\<lambda>rv s. \<exists>capfn.
        rv = map capfn (map (\<lambda>p. ptr_add ptr (p * 2 ^ (APIType_capBits tp us)))
                               [0 ..< n])
          \<and> (\<forall>p. capClass (capfn p) = PhysicalClass
                 \<and> capUntypedPtr (capfn p) = p
                 \<and> capBits (capfn p) = (APIType_capBits tp us))\<rbrace>"
  apply (simp add: createNewCaps_def toAPIType_def Arch_createNewCaps_def
               split del: if_split cong: option.case_cong)
  apply (rule hoare_grab_asm)+
  apply (frule range_cover.range_cover_n_less)
  apply (frule range_cover.unat_of_nat_n)
  apply (cases tp, simp_all split del: if_split)
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type, simp_all split del: if_split)
            \<comment>\<open>Untyped\<close>
            apply (rule hoare_pre, wp)
            apply (frule range_cover_not_zero[rotated -1],simp)
            apply (clarsimp simp: APIType_capBits_def objBits_simps ptr_add_def o_def)
            apply (subst upto_enum_red')
             apply unat_arith
            apply (clarsimp simp: o_def fromIntegral_def toInteger_nat fromInteger_nat)
            apply fastforce
           \<comment>\<open>TCB\<close>
           apply (rule hoare_pre, wp createObjects_ret2)
            apply (wpsimp simp: curDomain_def)
           apply (clarsimp simp: APIType_capBits_def word_bits_def objBits_simps ptr_add_def o_def)
           apply (fastforce simp: objBitsKO_def objBits_def)
          \<comment>\<open>other APIObjectType\<close>
          apply ((rule hoare_pre, wp createObjects_ret2,
                  clarsimp simp: APIType_capBits_def word_bits_def objBits_simps ptr_add_def o_def,
                  fastforce simp: objBitsKO_def objBits_def)+)[3]
       \<comment>\<open>Arch objects\<close>
       by (wp createObjects_ret2
           | clarsimp simp: APIType_capBits_def objBits_if_dev word_bits_def
                 split del: if_split
           | simp add: objBits_simps
           | (rule exI, (fastforce simp: bit_simps)))+

lemma createNewCaps_range_helper2:
  "\<lbrace>\<lambda>s. range_cover ptr sz (APIType_capBits tp us) n \<and> 0 < n\<rbrace>
     createNewCaps tp ptr n us d
   \<lbrace>\<lambda>rv s. \<forall>cp \<in> set rv. capRange cp \<noteq> {} \<and> capRange cp \<subseteq> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1}\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (rule hoare_strengthen_post)
   apply (rule createNewCaps_range_helper)
  apply (clarsimp simp: capRange_def ptr_add_def word_unat_power[symmetric]
                  simp del: atLeastatMost_subset_iff
                  dest!: less_two_pow_divD)
  apply (rule conjI)
   apply (rule is_aligned_no_overflow)
   apply (rule is_aligned_add_multI [OF _ _ refl])
    apply (fastforce simp:range_cover_def)
   apply simp
  apply (rule range_subsetI)
   apply (rule machine_word_plus_mono_right_split[OF range_cover.range_cover_compare])
     apply (assumption)+
   apply (simp add:range_cover_def word_bits_def)
  apply (frule range_cover_cell_subset)
   apply (erule of_nat_mono_maybe[rotated])
   apply (drule (1) range_cover.range_cover_n_less )
  apply (clarsimp)
  apply (erule impE)
   apply (simp add:range_cover_def)
   apply (rule is_aligned_no_overflow)
   apply (rule is_aligned_add_multI[OF _ le_refl refl])
   apply (fastforce simp:range_cover_def)
  apply simp
  done

lemma createNewCaps_children:
  "\<lbrace>\<lambda>s. cap = UntypedCap d (ptr && ~~ mask sz) sz idx
     \<and> range_cover ptr sz (APIType_capBits tp us) n \<and> 0 < n\<rbrace>
     createNewCaps tp ptr n us d
   \<lbrace>\<lambda>rv s. \<forall>y \<in> set rv. (sameRegionAs cap y)\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (rule hoare_chain [OF createNewCaps_range_helper2])
   apply fastforce
  apply clarsimp
  apply (drule(1) bspec)
  apply (clarsimp simp: sameRegionAs_def3 isCap_simps)
  apply (drule(1) subsetD)
  apply clarsimp
  apply (erule order_trans[rotated])
  apply (rule word_and_le2)
  done

fun isDeviceCap :: "capability \<Rightarrow> bool"
where
  "isDeviceCap (UntypedCap d _ _ _) = d"
| "isDeviceCap (ArchObjectCap (FrameCap _ _ _ d _)) = d"
| "isDeviceCap _ = False"

lemmas makeObjectKO_simp = makeObjectKO_def[split_simps AARCH64_H.object_type.split
  Structures_H.kernel_object.split ArchTypes_H.apiobject_type.split
  sum.split arch_kernel_object.split]

lemma createNewCaps_descendants_range':
  "\<lbrace>\<lambda>s. descendants_range' p q (ctes_of s) \<and>
        range_cover ptr sz (APIType_capBits ty us) n \<and> n \<noteq> 0 \<and>
        pspace_aligned' s \<and> pspace_distinct' s \<and> pspace_no_overlap' ptr sz s\<rbrace>
   createNewCaps ty ptr n us d
   \<lbrace> \<lambda>rv s. descendants_range' p q (ctes_of s)\<rbrace>"
  apply (clarsimp simp:descendants_range'_def2 descendants_range_in'_def2)
  apply (wp createNewCaps_null_filter')
  apply fastforce
  done

lemma caps_overlap_reserved'_def2:
  "caps_overlap_reserved' S =
   (\<lambda>s. (\<forall>cte \<in> ran (null_filter' (ctes_of s)).
        isUntypedCap (cteCap cte) \<longrightarrow>
        usableUntypedRange (cteCap cte) \<inter> S = {}))"
  apply (rule ext)
  apply (clarsimp simp:caps_overlap_reserved'_def)
  apply (intro iffI ballI impI)
    apply (elim ballE impE)
      apply simp
     apply simp
    apply (simp add:ran_def null_filter'_def split:if_split_asm option.splits)
  apply (elim ballE impE)
    apply simp
   apply simp
  apply (clarsimp simp: ran_def null_filter'_def is_cap_simps
                  simp del: split_paired_All split_paired_Ex split: if_splits)
  apply (drule_tac x = a in spec)
  apply simp
  done

lemma createNewCaps_caps_overlap_reserved':
  "\<lbrace>\<lambda>s. caps_overlap_reserved' S s \<and> pspace_aligned' s \<and> pspace_distinct' s \<and>
        pspace_no_overlap' ptr sz s \<and> 0 < n \<and>
        range_cover ptr sz (APIType_capBits ty us) n\<rbrace>
   createNewCaps ty ptr n us d
   \<lbrace>\<lambda>rv s. caps_overlap_reserved' S s\<rbrace>"
  apply (clarsimp simp: caps_overlap_reserved'_def2)
  apply (wp createNewCaps_null_filter')
  apply fastforce
  done

lemma createNewCaps_caps_overlap_reserved_ret':
  "\<lbrace>\<lambda>s. caps_overlap_reserved'
          {ptr..ptr + of_nat n * 2 ^ APIType_capBits ty us - 1} s \<and>
        pspace_aligned' s \<and> pspace_distinct' s \<and> pspace_no_overlap' ptr sz s \<and>
        0 < n \<and> range_cover ptr sz (APIType_capBits ty us) n\<rbrace>
   createNewCaps ty ptr n us d
   \<lbrace>\<lambda>rv s. \<forall>y\<in>set rv. caps_overlap_reserved' (capRange y) s\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp:valid_def)
  apply (frule use_valid[OF _ createNewCaps_range_helper])
   apply fastforce
  apply clarsimp
  apply (erule use_valid[OF _ createNewCaps_caps_overlap_reserved'])
  apply (intro conjI,simp_all)
  apply (erule caps_overlap_reserved'_subseteq)
  apply (drule(1) range_cover_subset)
   apply simp
  apply (clarsimp simp: ptr_add_def capRange_def
                  simp del: atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
                            Int_atLeastAtMost atLeastatMost_empty_iff)
  done

lemma createNewCaps_descendants_range_ret':
 "\<lbrace>\<lambda>s.  (range_cover ptr sz (APIType_capBits ty us) n \<and> 0 < n)
        \<and> pspace_aligned' s \<and> pspace_distinct' s
        \<and> pspace_no_overlap' ptr sz s
        \<and> descendants_range_in' {ptr..ptr + of_nat n * 2^(APIType_capBits ty us) - 1} cref (ctes_of s)\<rbrace>
   createNewCaps ty ptr n us d
  \<lbrace> \<lambda>rv s. \<forall>y\<in>set rv. descendants_range' y cref (ctes_of s)\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp: valid_def)
  apply (frule use_valid[OF _ createNewCaps_range_helper])
   apply simp
  apply (erule use_valid[OF _ createNewCaps_descendants_range'])
  apply (intro conjI,simp_all)
  apply (clarsimp simp:descendants_range'_def descendants_range_in'_def)
  apply (drule(1) bspec)+
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (erule disjoint_subset2[rotated])
  apply (drule(1) range_cover_subset)
   apply simp
  apply (simp add:capRange_def ptr_add_def)
  done

lemma createNewCaps_parent_helper:
  "\<lbrace>\<lambda>s. cte_wp_at' (\<lambda>cte. cteCap cte = UntypedCap d (ptr && ~~ mask sz) sz idx) p s
      \<and> pspace_aligned' s \<and> pspace_distinct' s
      \<and> pspace_no_overlap' ptr sz s
      \<and> (ty = APIObjectType ArchTypes_H.CapTableObject \<longrightarrow> 0 < us)
      \<and> range_cover ptr sz (APIType_capBits ty us) n \<and> 0 < n \<rbrace>
    createNewCaps ty ptr n us d
   \<lbrace>\<lambda>rv. cte_wp_at' (\<lambda>cte. isUntypedCap (cteCap cte) \<and>
                       (\<forall>tup\<in>set (zip (xs rv) rv).
                                sameRegionAs (cteCap cte) (snd tup)))
    p\<rbrace>"
  apply (rule hoare_post_imp[where Q'="\<lambda>rv s. \<exists>cte. cte_wp_at' ((=) cte) p s
                                           \<and> isUntypedCap (cteCap cte)
                                           \<and> (\<forall>tup\<in>set (zip (xs rv) rv).
                                sameRegionAs (cteCap cte) (snd tup))"])
   apply (clarsimp elim!: cte_wp_at_weakenE')
  apply (rule hoare_pre)
  apply (wp hoare_vcg_ex_lift createNewCaps_cte_wp_at'
            set_tuple_pick createNewCaps_children)
  apply (auto simp:cte_wp_at'_def isCap_simps)
  done

lemma createNewCaps_valid_cap':
  "\<lbrace>\<lambda>s. pspace_no_overlap' ptr sz s \<and>
        valid_pspace' s \<and> n \<noteq> 0 \<and>
        range_cover ptr sz (APIType_capBits ty us) n \<and>
        (ty = APIObjectType ArchTypes_H.CapTableObject \<longrightarrow> 0 < us) \<and>
        (ty = APIObjectType apiobject_type.Untyped \<longrightarrow> minUntypedSizeBits \<le> us \<and> us \<le> maxUntypedSizeBits) \<and>
        ptr \<noteq> 0 \<and> sz \<le> maxUntypedSizeBits \<and> canonical_address (ptr && ~~ mask sz)\<rbrace>
    createNewCaps ty ptr n us d
  \<lbrace>\<lambda>r s. \<forall>cap\<in>set r. s \<turnstile>' cap\<rbrace>"
  apply (rule hoare_assume_pre)
  apply clarsimp
  apply (erule createNewCaps_valid_cap; simp)
  done

lemma createNewCaps_ranges:
  "\<lbrace>\<lambda>s. range_cover ptr sz (APIType_capBits ty us) n \<and> 0<n \<rbrace>
  createNewCaps ty ptr n us d
  \<lbrace>\<lambda>rv s. distinct_sets (map capRange rv)\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (rule hoare_chain)
    apply (rule createNewCaps_range_helper)
   apply fastforce
  apply (clarsimp simp: distinct_sets_prop distinct_prop_map)
  apply (rule distinct_prop_distinct)
   apply simp
  apply (clarsimp simp: capRange_def simp del: Int_atLeastAtMost
                  dest!: less_two_pow_divD)
  apply (rule aligned_neq_into_no_overlap[simplified field_simps])
     apply (rule notI)
     apply (erule(3) ptr_add_distinct_helper)
      apply (simp add:range_cover_def word_bits_def)
     apply (erule range_cover.range_cover_n_le(1)[where 'a=machine_word_len])
    apply (clarsimp simp: ptr_add_def word_unat_power[symmetric])
    apply (rule is_aligned_add_multI[OF _ le_refl refl])
     apply (simp add:range_cover_def)+
   apply (clarsimp simp: ptr_add_def word_unat_power[symmetric])
   apply (rule is_aligned_add_multI[OF _ le_refl refl])
  apply (simp add:range_cover_def)+
  done

lemma createNewCaps_ranges':
  "\<lbrace>\<lambda>s. range_cover ptr sz (APIType_capBits ty us) n \<and> 0 < n\<rbrace>
  createNewCaps ty ptr n us d
  \<lbrace>\<lambda>rv s. distinct_sets (map capRange (map snd (zip xs rv)))\<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule createNewCaps_ranges)
  apply (simp add: distinct_sets_prop del: map_map)
  apply (erule distinct_prop_prefixE)
  apply (rule Sublist.map_mono_prefix)
  apply (rule map_snd_zip_prefix [unfolded less_eq_list_def])
  done

declare split_paired_Ex[simp del]
lemmas corres_split_retype_createNewCaps
   = corres_split[OF corres_retype_region_createNewCaps,
                   simplified bind_assoc, simplified ]
declare split_paired_Ex[simp add]

lemma retype_region_caps_overlap_reserved:
  "\<lbrace>valid_pspace and valid_mdb and
    pspace_no_overlap_range_cover ptr sz and caps_no_overlap ptr sz and
    caps_overlap_reserved
      {ptr..ptr + of_nat n * 2^obj_bits_api (APIType_map2 (Inr ao')) us - 1} and
    (\<lambda>s. \<exists>slot. cte_wp_at (\<lambda>c. up_aligned_area ptr sz \<subseteq> cap_range c \<and> cap_is_device c = dev) slot s) and
    K (APIType_map2 (Inr ao') = Structures_A.apiobject_type.CapTableObject \<longrightarrow> 0 < us) and
    K (range_cover ptr sz (obj_bits_api (APIType_map2 (Inr ao')) us) n) and
    K (S \<subseteq> {ptr..ptr + of_nat n *
                  2 ^ obj_bits_api (APIType_map2 (Inr ao')) us - 1})\<rbrace>
   retype_region ptr n us (APIType_map2 (Inr ao')) dev
   \<lbrace>\<lambda>rv s. caps_overlap_reserved S s\<rbrace>"
  apply (rule hoare_gen_asm)+
  apply (simp (no_asm) add:caps_overlap_reserved_def2)
  apply (rule hoare_pre)
  apply (wp retype_region_caps_of)
   apply simp+
  apply (simp add:caps_overlap_reserved_def2)
  apply (intro conjI,simp+)
  apply clarsimp
  apply (drule bspec)
   apply simp+
  apply (erule(1) disjoint_subset2)
  done

lemma retype_region_caps_overlap_reserved_ret:
  "\<lbrace>valid_pspace and valid_mdb and caps_no_overlap ptr sz and
    pspace_no_overlap_range_cover ptr sz and
    caps_overlap_reserved
      {ptr..ptr + of_nat n * 2^obj_bits_api (APIType_map2 (Inr ao')) us - 1} and
    (\<lambda>s. \<exists>slot. cte_wp_at (\<lambda>c. up_aligned_area ptr sz \<subseteq> cap_range c \<and> cap_is_device c = dev) slot s) and
    K (APIType_map2 (Inr ao') = Structures_A.apiobject_type.CapTableObject \<longrightarrow> 0 < us) and
    K (range_cover ptr sz (obj_bits_api (APIType_map2 (Inr ao')) us) n)\<rbrace>
   retype_region ptr n us (APIType_map2 (Inr ao')) dev
   \<lbrace>\<lambda>rv s. \<forall>y\<in>set rv. caps_overlap_reserved (untyped_range (default_cap
                            (APIType_map2 (Inr ao')) y us d)) s\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp:valid_def)
  apply (frule retype_region_ret[unfolded valid_def,simplified,THEN spec,THEN bspec])
  apply clarsimp
  apply (erule use_valid[OF _ retype_region_caps_overlap_reserved])
  apply clarsimp
  apply (intro conjI,simp_all)
   apply fastforce
  apply (case_tac ao')
        apply (simp_all add:APIType_map2_def)
  apply (rename_tac apiobject_type)
  apply (case_tac apiobject_type)
      apply (simp_all add:obj_bits_api_def ptr_add_def)
  apply (drule(1) range_cover_subset)
   apply (clarsimp)+
  done

lemma updateFreeIndex_pspace_no_overlap':
  "\<lbrace>\<lambda>s. pspace_no_overlap' ptr sz s \<and>
        valid_pspace' s \<and> cte_wp_at' (isUntypedCap o cteCap) src s\<rbrace>
   updateFreeIndex src index
   \<lbrace>\<lambda>r s. pspace_no_overlap' ptr sz s\<rbrace>"
  apply (simp add: updateFreeIndex_def getSlotCap_def updateTrackedFreeIndex_def)
  apply (rule hoare_pre)
   apply (wp getCTE_wp' | wp (once) pspace_no_overlap'_lift
     | simp)+
  apply (clarsimp simp:valid_pspace'_def pspace_no_overlap'_def)
  done

lemma updateFreeIndex_updateCap_caps_overlap_reserved:
  "\<lbrace>\<lambda>s. valid_mdb' s \<and> valid_objs' s \<and> S \<subseteq> untypedRange cap \<and>
        usableUntypedRange (capFreeIndex_update (\<lambda>_. index) cap) \<inter> S = {} \<and>
        isUntypedCap cap \<and> descendants_range_in' S src (ctes_of s) \<and>
        cte_wp_at' (\<lambda>c. cteCap c = cap) src s\<rbrace>
   updateCap src (capFreeIndex_update (\<lambda>_. index) cap)
   \<lbrace>\<lambda>r s. caps_overlap_reserved' S s\<rbrace>"
  apply (clarsimp simp:caps_overlap_reserved'_def)
  apply (wp updateCap_ctes_of_wp)
  apply (clarsimp simp:modify_map_def cte_wp_at_ctes_of)
  apply (erule ranE)
  apply (clarsimp split:if_split_asm simp:valid_mdb'_def valid_mdb_ctes_def)
  apply (case_tac cte)
  apply (case_tac ctea)
  apply simp
  apply (drule untyped_incD')
      apply (simp+)[4]
  apply clarify
  apply (erule subset_splitE)
     apply (simp del:usable_untyped_range.simps)
     apply (thin_tac "P \<longrightarrow> Q" for P Q)+
     apply (elim conjE)
     apply blast
    apply (simp)
    apply (thin_tac "P\<longrightarrow>Q" for P Q)+
    apply (elim conjE)
    apply (drule(2) descendants_range_inD')
    apply simp
    apply (rule disjoint_subset[OF usableRange_subseteq])
      apply (rule valid_capAligned)
      apply (erule(1) ctes_of_valid_cap')
     apply (simp add:untypedCapRange)+
   apply (elim disjE)
    apply clarsimp
    apply (drule(2) descendants_range_inD')
    apply simp
    apply (rule disjoint_subset[OF usableRange_subseteq])
      apply (rule valid_capAligned)
      apply (erule(1) ctes_of_valid_cap')
     apply (simp add:untypedCapRange)+
  apply (thin_tac "P\<longrightarrow>Q" for P Q)+
  apply (rule disjoint_subset[OF usableRange_subseteq])
    apply (rule valid_capAligned)
    apply (erule(1) ctes_of_valid_cap')
   apply simp+
  apply blast
  done

lemma updateFreeIndex_caps_overlap_reserved:
  "\<lbrace>\<lambda>s. valid_pspace' s \<and> descendants_range_in' S src (ctes_of s)
        \<and> cte_wp_at' ((\<lambda>cap. S \<subseteq> untypedRange cap \<and>
            usableUntypedRange (capFreeIndex_update (\<lambda>_. index) cap) \<inter> S = {} \<and>
            isUntypedCap cap) o cteCap) src s\<rbrace>
   updateFreeIndex src index
   \<lbrace>\<lambda>r s. caps_overlap_reserved' S s\<rbrace>"
  apply (simp add: updateFreeIndex_def updateTrackedFreeIndex_def getSlotCap_def)
  apply (wp updateFreeIndex_updateCap_caps_overlap_reserved getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of valid_pspace'_def)
  apply (clarsimp simp: valid_mdb'_def split: option.split)
  done

lemma updateFreeIndex_updateCap_caps_no_overlap'':
  "\<lbrace>\<lambda>s. isUntypedCap cap \<and> caps_no_overlap'' ptr sz s \<and>
        cte_wp_at' (\<lambda>c. cteCap c = cap) src s\<rbrace>
   updateCap src (capFreeIndex_update (\<lambda>_. index) cap)
   \<lbrace>\<lambda>r s. caps_no_overlap'' ptr sz s\<rbrace>"
  apply (clarsimp simp:caps_no_overlap''_def)
  apply (wp updateCap_ctes_of_wp)
  apply (clarsimp simp: modify_map_def ran_def cte_wp_at_ctes_of
              simp del: atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
                        Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex)
  apply (case_tac "a = src")
   apply (clarsimp simp del: atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
     Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex)
   apply (erule subsetD[rotated])
   apply (elim allE impE)
     apply fastforce
    apply (clarsimp simp:isCap_simps)
   apply (erule subset_trans)
   apply (clarsimp simp:isCap_simps)
  apply (clarsimp simp del: atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
     Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex)
   apply (erule subsetD[rotated])
  apply (elim allE impE)
   prefer 2
    apply assumption
  apply fastforce+
  done

lemma updateFreeIndex_caps_no_overlap'':
  "\<lbrace>\<lambda>s. caps_no_overlap'' ptr sz s \<and>
        cte_wp_at' (isUntypedCap o cteCap) src s\<rbrace>
   updateFreeIndex src index
   \<lbrace>\<lambda>r s. caps_no_overlap'' ptr sz s\<rbrace>"
  apply (simp add: updateFreeIndex_def updateTrackedFreeIndex_def getSlotCap_def)
  apply (wp updateFreeIndex_updateCap_caps_no_overlap'' getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (clarsimp simp: caps_no_overlap''_def split: option.split)
  done

lemma updateFreeIndex_descendants_of':
  "\<lbrace>\<lambda>s. cte_wp_at' (\<lambda>c. \<exists>idx'. cteCap c = capFreeIndex_update (K idx') cap) ptr s \<and> isUntypedCap cap \<and>
        P ((swp descendants_of') (null_filter' (ctes_of s)))\<rbrace>
   updateCap ptr (capFreeIndex_update (\<lambda>_. index) cap)
   \<lbrace>\<lambda>r s. P ((swp descendants_of') (null_filter' (ctes_of s)))\<rbrace>"
  apply (wp updateCap_ctes_of_wp)
  apply clarsimp
  apply (erule subst[rotated,where P = P])
  apply (rule ext)
  apply (clarsimp simp:null_filter_descendants_of'[OF null_filter_simp'])
  apply (rule mdb_inv_preserve.descendants_of)
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (frule_tac m="ctes_of s" and index=index in mdb_inv_preserve_updateCap)
   apply (clarsimp simp: isCap_simps)
  apply (clarsimp simp: isCap_simps)
  done

lemma updateFreeIndex_updateCap_descendants_range_in':
  "\<lbrace>\<lambda>s. cte_wp_at' (\<lambda>c. cteCap c = cap) slot s \<and> isUntypedCap cap \<and>
        descendants_range_in' S slot (ctes_of s)\<rbrace>
   updateCap slot (capFreeIndex_update (\<lambda>_. index) cap)
   \<lbrace>\<lambda>r s. descendants_range_in' S slot (ctes_of s)\<rbrace>"
  apply (rule hoare_pre)
   apply (wp descendants_range_in_lift'
     [where Q'="\<lambda>s. cte_wp_at' (\<lambda>c. cteCap c = cap) slot s \<and> isUntypedCap cap" and
       Q = "\<lambda>s. cte_wp_at' (\<lambda>c. cteCap c = cap) slot s \<and> isUntypedCap cap "] )
    apply (wp updateFreeIndex_descendants_of')
    apply (clarsimp simp: cte_wp_at_ctes_of swp_def isCap_simps)
   apply (simp add:updateCap_def)
   apply (wp setCTE_weak_cte_wp_at getCTE_wp)
   apply (fastforce simp:cte_wp_at_ctes_of isCap_simps)
  apply (clarsimp)
  done

lemma updateFreeIndex_descendants_range_in':
  "\<lbrace>\<lambda>s. cte_wp_at' (isUntypedCap o cteCap) slot s
      \<and> descendants_range_in' S slot (ctes_of s)\<rbrace>
     updateFreeIndex slot index
   \<lbrace>\<lambda>r s. descendants_range_in' S slot (ctes_of s)\<rbrace>"
  apply (simp add: updateFreeIndex_def updateTrackedFreeIndex_def getSlotCap_def)
  apply (wp updateFreeIndex_updateCap_descendants_range_in' getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma caps_no_overlap''_def2:
  "caps_no_overlap'' ptr sz =
   (\<lambda>s. \<forall>cte\<in>ran (null_filter' (ctes_of s)).
            untypedRange (cteCap cte) \<inter>
            {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1} \<noteq> {} \<longrightarrow>
            {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1} \<subseteq>
            untypedRange (cteCap cte))"
  apply (intro ext iffI)
    apply (clarsimp simp:caps_no_overlap''_def null_filter'_def ran_def)
    apply (drule_tac x = cte in spec)
    apply fastforce
  apply (clarsimp simp:caps_no_overlap''_def null_filter'_def)
  apply (case_tac "cte = CTE capability.NullCap nullMDBNode")
   apply clarsimp
  apply (drule_tac x = cte in  bspec)
   apply (clarsimp simp:ran_def)
   apply (rule_tac x= a in exI)
   apply clarsimp
  apply clarsimp
  apply (erule subsetD)
  apply simp
  done

lemma deleteObjects_caps_no_overlap'':
  "\<lbrace>\<lambda>s. invs' s \<and> ct_active' s \<and> sch_act_simple s \<and>
        cte_wp_at' (\<lambda>c. cteCap c = capability.UntypedCap d ptr sz idx) slot s \<and>
        caps_no_overlap'' ptr sz s \<and>
        descendants_range' (capability.UntypedCap d ptr sz idx) slot (ctes_of s)\<rbrace>
   deleteObjects ptr sz
   \<lbrace>\<lambda>rv s. caps_no_overlap'' ptr sz s\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp split:if_splits)
  apply (clarsimp simp:caps_no_overlap''_def2 deleteObjects_def2 capAligned_def valid_cap'_def
    dest!:ctes_of_valid_cap')
  apply (wp deleteObjects_null_filter[where idx = idx and p = slot])
  apply (clarsimp simp:cte_wp_at_ctes_of invs_def)
  apply (case_tac cte)
  apply clarsimp
  apply (frule ctes_of_valid_cap')
   apply (simp add:invs_valid_objs')
  apply (simp add:valid_cap'_def capAligned_def)
  done

lemma descendants_range_in_subseteq':
  "\<lbrakk>descendants_range_in' A p ms ;B\<subseteq> A\<rbrakk> \<Longrightarrow> descendants_range_in' B p ms"
  by (auto simp:descendants_range_in'_def cte_wp_at_ctes_of dest!:bspec)

lemma updateFreeIndex_mdb_simple':
  "\<lbrace>\<lambda>s. descendants_of' src (ctes_of s) = {} \<and>
        pspace_no_overlap' (capPtr cap) (capBlockSize cap) s \<and>
        valid_pspace' s \<and> cte_wp_at' (\<lambda>c. \<exists>idx'. cteCap c = capFreeIndex_update (\<lambda>_. idx') cap) src s \<and>
        isUntypedCap cap\<rbrace>
   updateCap src (capFreeIndex_update (\<lambda>_. idx) cap)
   \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  apply (clarsimp simp:valid_mdb'_def updateCap_def valid_pspace'_def)
  apply (wp getCTE_wp)
  apply (clarsimp simp:cte_wp_at_ctes_of isCap_simps simp del:fun_upd_apply)

  apply (frule mdb_inv_preserve_updateCap[where index=idx and m="ctes_of s" and slot=src for s])
   apply (simp add: isCap_simps)
  apply (simp add: modify_map_def)
  apply (clarsimp simp add: mdb_inv_preserve.preserve_stuff mdb_inv_preserve.by_products valid_mdb_ctes_def)

  proof -
  fix s cte ptr sz idx' d
  assume descendants: "descendants_of' src (ctes_of s) = {}"
  and    cte_wp_at' :"ctes_of s src = Some cte" "cteCap cte = capability.UntypedCap d ptr sz idx'"
  and      unt_inc' :"untyped_inc' (ctes_of s)"
  and   valid_objs' :"valid_objs' s"
  and invp: "mdb_inv_preserve (ctes_of s) ((ctes_of s)(src \<mapsto> cteCap_update (\<lambda>_. UntypedCap d ptr sz idx) cte))"
    (is "mdb_inv_preserve (ctes_of s) ?ctes")

  show "untyped_inc' ?ctes"
  using cte_wp_at'
  apply (clarsimp simp:untyped_inc'_def mdb_inv_preserve.descendants_of[OF invp, symmetric]
                       descendants
             split del: if_split)
  apply (case_tac "ctes_of s p")
   apply (simp split: if_split_asm)
  apply (case_tac "ctes_of s p'")
   apply (simp split: if_split_asm)
  apply (case_tac "the (ctes_of s p)", case_tac "the (ctes_of s p')")
  apply clarsimp
  apply (cut_tac p=p and p'=p' in untyped_incD'[OF _ _ _ _ unt_inc'])
      apply assumption
     apply (clarsimp simp: isCap_simps split: if_split_asm)
    apply assumption
   apply (clarsimp simp: isCap_simps split: if_split_asm)
  apply (clarsimp simp: descendants split: if_split_asm)
  done
qed

lemma pspace_no_overlap_valid_untyped':
  "\<lbrakk>  pspace_no_overlap' ptr bits s; is_aligned ptr bits; bits < word_bits;
      pspace_aligned' s \<rbrakk>
  \<Longrightarrow> valid_untyped' d ptr bits idx s"
  apply (clarsimp simp: valid_untyped'_def ko_wp_at'_def split del: if_split)
  apply (frule(1) pspace_no_overlapD')
  apply (simp add: obj_range'_def[symmetric] Int_commute add_mask_fold)
  apply (erule disjE)
   apply (drule base_member_set[simplified field_simps add_mask_fold])
    apply (simp add: word_bits_def)
   apply blast
  apply (simp split: if_split_asm)
  apply (erule notE, erule disjoint_subset2[rotated])
  apply (clarsimp simp: is_aligned_no_wrap'[OF _ word_of_nat_less])
  done

lemma updateFreeIndex_valid_pspace_no_overlap':
  "\<lbrace>\<lambda>s. valid_pspace' s \<and>
        (\<exists>ptr sz. pspace_no_overlap' ptr sz s \<and> idx \<le> 2 ^ sz \<and>
        cte_wp_at' ((\<lambda>c. isUntypedCap c \<and> capPtr c = ptr \<and> capBlockSize c = sz) o cteCap) src s)
        \<and> is_aligned (of_nat idx :: machine_word) minUntypedSizeBits \<and>
        descendants_of' src (ctes_of s) = {}\<rbrace>
     updateFreeIndex src idx
   \<lbrace>\<lambda>r s. valid_pspace' s\<rbrace>"
  apply (clarsimp simp:valid_pspace'_def updateFreeIndex_def updateTrackedFreeIndex_def)
  apply (rule hoare_pre)
   apply (rule hoare_vcg_conj_lift)
    apply (clarsimp simp:updateCap_def getSlotCap_def)
    apply (wp getCTE_wp | simp)+
     apply (wp updateFreeIndex_mdb_simple' getCTE_wp' | simp add: getSlotCap_def)+
  apply (clarsimp simp:cte_wp_at_ctes_of valid_pspace'_def)
  apply (case_tac cte,simp add:isCap_simps)
  apply (frule(1) ctes_of_valid_cap')
  apply (clarsimp simp: valid_cap_simps' capAligned_def pspace_no_overlap_valid_untyped')
  done

crunch updateFreeIndex
  for vms'[wp]: "valid_machine_state'"

(* FIXME: move *)
lemma setCTE_tcbDomain_inv[wp]:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbState tcb)) t\<rbrace> setCTE ptr v \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbState tcb)) t\<rbrace>"
  apply (simp add: setCTE_def)
  apply (rule setObject_cte_obj_at_tcb', simp_all)
  done

(* FIXME: move *)
crunch cteInsert
  for tcbState_inv[wp]: "obj_at' (\<lambda>tcb. P (tcbState tcb)) t"
  (wp: crunch_simps hoare_drop_imps)

lemma updateFreeIndex_clear_invs':
  "\<lbrace>\<lambda>s. invs' s \<and>
        (\<exists>ptr sz. pspace_no_overlap' ptr sz s \<and> idx \<le> 2 ^ sz \<and>
        cte_wp_at' ((\<lambda>c. isUntypedCap c \<and> capPtr c = ptr \<and> capBlockSize c = sz) o cteCap) src s)
        \<and> is_aligned (of_nat idx :: machine_word) minUntypedSizeBits
        \<and> descendants_of' src (ctes_of s) = {}\<rbrace>
   updateFreeIndex src idx
   \<lbrace>\<lambda>r s. invs' s\<rbrace>"
  apply (clarsimp simp:invs'_def valid_state'_def)
  apply (wp updateFreeIndex_valid_pspace_no_overlap')
   apply (simp add: updateFreeIndex_def updateTrackedFreeIndex_def)
   apply (wp updateFreeIndex_valid_pspace_no_overlap' sch_act_wf_lift valid_queues_lift
             updateCap_iflive' tcb_in_cur_domain'_lift
            | simp add: pred_tcb_at'_def)+
     apply (rule hoare_vcg_conj_lift)
      apply (simp add: ifunsafe'_def3 cteInsert_def setUntypedCapAsFull_def
              split del: if_split)
      apply wp+
     apply (rule hoare_vcg_conj_lift)
      apply (simp add: updateCap_def)
      apply (wp valid_irq_node_lift setCTE_typ_at')+
     apply (rule hoare_vcg_conj_lift)
      apply (simp add:updateCap_def)
      apply (wp setCTE_irq_handlers' getCTE_wp)
     apply (simp add:updateCap_def)
     apply (wp irqs_masked_lift cur_tcb_lift ct_idle_or_in_cur_domain'_lift
               hoare_vcg_disj_lift untyped_ranges_zero_lift getCTE_wp valid_bitmaps_lift
              | wp (once) hoare_use_eq[where f="gsUntypedZeroRanges"]
              | simp add: getSlotCap_def
              | simp add: cte_wp_at_ctes_of)+
  apply (clarsimp simp: cte_wp_at_ctes_of fun_upd_def[symmetric])
  apply (clarsimp simp: isCap_simps)
  apply (frule(1) valid_global_refsD_with_objSize)
  apply clarsimp
  apply (intro conjI allI impI)
   apply (clarsimp simp: modify_map_def cteCaps_of_def ifunsafe'_def3 split:if_splits)
    apply (drule_tac x=src in spec)
    apply (clarsimp simp:isCap_simps)
    apply (rule_tac x = cref' in exI)
    apply clarsimp
   apply (drule_tac x = cref in spec)
   apply clarsimp
   apply (rule_tac x = cref' in exI)
   apply clarsimp
  apply (clarsimp simp: valid_pspace'_def)
  apply (erule untyped_ranges_zero_fun_upd, simp_all)
  apply (clarsimp simp: untypedZeroRange_def cteCaps_of_def isCap_simps)
  done

lemma cte_wp_at_pspace_no_overlapI':
  "\<lbrakk>invs' s; cte_wp_at' (\<lambda>c. cteCap c = capability.UntypedCap
                                          d (ptr && ~~ mask sz) sz idx) cref s;
    idx \<le> unat (ptr && mask sz); sz < word_bits\<rbrakk>
   \<Longrightarrow> pspace_no_overlap' ptr sz s"
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (case_tac cte,clarsimp)
  apply (frule ctes_of_valid_cap')
    apply (simp add:invs_valid_objs')
  apply (clarsimp simp:valid_cap'_def invs'_def valid_state'_def valid_pspace'_def
    valid_untyped'_def simp del:usableUntypedRange.simps)
  apply (unfold pspace_no_overlap'_def)
  apply (intro allI impI)
  apply (unfold ko_wp_at'_def)
  apply (clarsimp simp del: atLeastAtMost_iff
          atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff  usableUntypedRange.simps)
  apply (drule spec)+
  apply (frule(1) pspace_distinctD')
  apply (frule(1) pspace_alignedD')
  apply (erule(1) impE)+
  apply (clarsimp simp: obj_range'_def simp del: atLeastAtMost_iff
          atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff  usableUntypedRange.simps)
  apply (erule disjoint_subset2[rotated])
  apply (frule(1) le_mask_le_2p)
  apply (clarsimp simp:p_assoc_help)
  apply (rule le_plus'[OF word_and_le2])
  apply simp
  apply (erule word_of_nat_le)
  done

lemma descendants_range_caps_no_overlapI':
  "\<lbrakk>invs' s; cte_wp_at' (\<lambda>c. cteCap c = capability.UntypedCap
                                          d (ptr && ~~ mask sz) sz idx) cref s;
    descendants_range_in' {ptr .. (ptr && ~~ mask sz) + mask sz} cref (ctes_of s)\<rbrakk>
   \<Longrightarrow> caps_no_overlap'' ptr sz s"
  apply (frule invs_mdb')
  apply (clarsimp simp:valid_mdb'_def valid_mdb_ctes_def cte_wp_at_ctes_of
                  simp del:usableUntypedRange.simps untypedRange.simps)
  apply (unfold caps_no_overlap''_def add_mask_fold)
  apply (intro ballI impI)
  apply (erule ranE)
  apply (subgoal_tac "isUntypedCap (cteCap ctea)")
   prefer 2
   apply (rule untypedRange_not_emptyD)
   apply blast
  apply (case_tac ctea,case_tac cte)
  apply simp
  apply (drule untyped_incD')
      apply ((simp add:isCap_simps del:usableUntypedRange.simps untypedRange.simps)+)[4]
  apply (elim conjE subset_splitE)
     apply (erule subset_trans[OF _ psubset_imp_subset,rotated])
     apply (clarsimp simp:word_and_le2 add_mask_fold)
    apply simp
    apply (elim conjE)
    apply (thin_tac "P\<longrightarrow>Q" for P Q)+
    apply (drule(2) descendants_range_inD')
    apply (simp add:untypedCapRange)+
   apply (erule subset_trans[OF _  equalityD1,rotated])
   apply (clarsimp simp:word_and_le2 add_mask_fold)
  apply (thin_tac "P\<longrightarrow>Q" for P Q)+
  apply (drule disjoint_subset[rotated, where A' = "{ptr..(ptr && ~~ mask sz) + mask sz}"])
   apply (clarsimp simp:word_and_le2 Int_ac add_mask_fold)+
  done

lemma cte_wp_at_caps_no_overlapI':
  "\<lbrakk>invs' s; cte_wp_at' (\<lambda>c. (cteCap c) = UntypedCap d (ptr && ~~ mask sz) sz idx) cref s;
    idx \<le> unat (ptr && mask sz); sz < word_bits\<rbrakk>
   \<Longrightarrow> caps_no_overlap'' ptr sz s"
  apply (frule invs_mdb')
  apply (frule(1) le_mask_le_2p)
  apply (clarsimp simp:valid_mdb'_def valid_mdb_ctes_def cte_wp_at_ctes_of)
  apply (case_tac cte)
  apply simp
  apply (frule(1) ctes_of_valid_cap'[OF _ invs_valid_objs'])
  apply (unfold caps_no_overlap''_def)
  apply (intro ballI impI)
  apply (erule ranE)
  apply (subgoal_tac "isUntypedCap (cteCap ctea)")
   prefer 2
   apply (rule untypedRange_not_emptyD)
   apply blast
  apply (case_tac ctea)
  apply simp
  apply (drule untyped_incD')
      apply (simp add:isCap_simps)+
  apply (elim conjE)
  apply (erule subset_splitE)
     apply (erule subset_trans[OF _ psubset_imp_subset,rotated])
     apply (clarsimp simp: word_and_le2)
    apply simp
    apply (thin_tac "P\<longrightarrow>Q" for P Q)+
    apply (elim conjE)
    apply (drule disjoint_subset2[rotated, where B' = "{ptr..(ptr && ~~ mask sz) + mask sz}"])
     apply clarsimp
     apply (rule le_plus'[OF word_and_le2])
     apply simp
     apply (erule word_of_nat_le)
    apply (simp add: add_mask_fold)
   apply (erule subset_trans[OF _  equalityD1,rotated])
   apply (clarsimp simp:word_and_le2)
  apply (thin_tac "P\<longrightarrow>Q" for P Q)+
  apply (drule disjoint_subset[rotated, where A' = "{ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}"])
   apply (clarsimp simp:word_and_le2 Int_ac)+
  done


lemma descendants_range_ex_cte':
  "\<lbrakk>descendants_range_in' S p (ctes_of s'); ex_cte_cap_wp_to' P q s'; S \<subseteq> capRange (cteCap cte);
    invs' s'; ctes_of s' p = Some cte; isUntypedCap (cteCap cte)\<rbrakk> \<Longrightarrow> q \<notin> S"
  apply (frule invs_valid_objs')
  apply (frule invs_mdb')
  apply (clarsimp simp:invs'_def valid_state'_def)
  apply (clarsimp simp: ex_cte_cap_to'_def cte_wp_at_ctes_of)
  apply (frule_tac cte = "cte" in  valid_global_refsD')
   apply simp
  apply (case_tac "\<exists>irq. cteCap ctea = IRQHandlerCap irq")
   apply clarsimp
   apply (erule(1) in_empty_interE[OF _ _ subsetD,rotated -1])
    apply (clarsimp simp:global_refs'_def)
    apply (erule_tac A = "range P" for P in subsetD)
    apply (simp add:range_eqI field_simps)
   apply (case_tac ctea)
   apply clarsimp
  apply (case_tac ctea)
  apply (drule_tac cte = "cte" and cte' = ctea in untyped_mdbD')
       apply assumption
      apply (clarsimp simp:isCap_simps)
     apply (drule_tac B = "untypedRange (cteCap cte)" in subsetD[rotated])
      apply (clarsimp simp:untypedCapRange)
     apply clarsimp
     apply (drule_tac x = " (irq_node' s')" in cte_refs_capRange[rotated])
      apply (erule(1) ctes_of_valid_cap')
     apply blast
    apply (clarsimp simp:isCap_simps)
   apply (simp add:valid_mdb'_def valid_mdb_ctes_def)
  apply (drule(2) descendants_range_inD')
  apply clarsimp
  apply (drule_tac x = " (irq_node' s')" in cte_refs_capRange[rotated])
   apply (erule(1) ctes_of_valid_cap')
  apply blast
  done

lemma updateCap_isUntypedCap_corres:
  "\<lbrakk>is_untyped_cap cap; isUntypedCap cap'; cap_relation cap cap'\<rbrakk>
   \<Longrightarrow> corres dc
         (cte_wp_at (\<lambda>c. is_untyped_cap c \<and> obj_ref_of c = obj_ref_of cap \<and>
          cap_bits c = cap_bits cap \<and> cap_is_device c = cap_is_device cap) src and valid_objs and
          pspace_aligned and pspace_distinct)
         (cte_at' (cte_map src) and pspace_distinct' and pspace_aligned')
         (set_cap cap src) (updateCap (cte_map src) cap')"
  apply (rule corres_name_pre)
  apply (simp add: updateCap_def)
  apply (frule state_relation_pspace_relation)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (frule pspace_relation_cte_wp_atI)
    apply (fastforce simp: cte_wp_at_ctes_of)
   apply simp
  apply clarify
  apply (frule cte_map_inj_eq)
       apply (fastforce simp: cte_wp_at_ctes_of cte_wp_at_caps_of_state)+
  apply (clarsimp simp: is_cap_simps isCap_simps)
  apply (rule corres_guard_imp)
    apply (rule corres_symb_exec_r)
       apply (rule_tac F = "cteCap_update (\<lambda>_. capability.UntypedCap dev r bits f) ctea
                            = cteCap_update (\<lambda>cap. capFreeIndex_update (\<lambda>_. f) (cteCap cte)) cte"
                       in corres_gen_asm2)
       apply (rule_tac F = " (cap.UntypedCap dev r bits f) = free_index_update (\<lambda>_. f) c"
                       in corres_gen_asm)
       apply simp
       apply (rule setCTE_UntypedCap_corres)
         apply ((clarsimp simp: cte_wp_at_caps_of_state cte_wp_at_ctes_of)+)[3]
      apply (subst identity_eq)
      apply (wp getCTE_sp getCTE_get no_fail_getCTE)+
    apply (clarsimp simp: cte_wp_at_ctes_of cte_wp_at_caps_of_state)+
  done

end

lemma updateFreeIndex_corres:
  "\<lbrakk>is_untyped_cap cap; free_index_of cap = idx \<rbrakk>
   \<Longrightarrow> corres dc
         (cte_wp_at (\<lambda>c. is_untyped_cap c \<and> obj_ref_of c = obj_ref_of cap \<and>
          cap_bits c = cap_bits cap \<and> cap_is_device c = cap_is_device cap) src and valid_objs
           and pspace_aligned and pspace_distinct)
         (cte_at' (cte_map src)
           and pspace_distinct' and pspace_aligned')
         (set_cap cap src) (updateFreeIndex (cte_map src) idx)"
  supply AARCH64.ghost_relation_wrapper_def[simp] (* FIXME arch-split *)
  apply (rule corres_name_pre)
  apply (simp add: updateFreeIndex_def updateTrackedFreeIndex_def)
  apply (rule corres_guard_imp)
    apply (rule corres_symb_exec_r_conj[where P'="cte_at' (cte_map src)"])+
          apply (rule_tac F="isUntypedCap capa
                             \<and> cap_relation cap (capFreeIndex_update (\<lambda>_. idx) capa)"
                          in corres_gen_asm2)
          apply (rule updateCap_isUntypedCap_corres, simp+)
           apply (clarsimp simp: gen_isCap_simps)
          apply simp
         apply (wp getSlotCap_wp)+
        apply (clarsimp simp: state_relation_def cte_wp_at_ctes_of)
       apply (rule no_fail_pre, wp no_fail_getSlotCap)
       apply (clarsimp simp: cte_wp_at_ctes_of)
      apply (wp getSlotCap_wp)+
     apply (clarsimp simp: state_relation_def cte_wp_at_ctes_of)
    apply (rule no_fail_pre, wp no_fail_getSlotCap)
    apply simp
   apply clarsimp
  apply (clarsimp simp: cte_wp_at_ctes_of cte_wp_at_caps_of_state)
  apply (frule state_relation_pspace_relation)
  apply (frule(1) pspace_relation_ctes_ofI[OF _ caps_of_state_cteD], simp+)
  apply (clarsimp simp: gen_isCap_simps is_cap_simps
                        cte_wp_at_caps_of_state free_index_of_def)
  done


locale invokeUntyped_proofs =
 fixes s cref reset ptr_base ptr tp us slots sz idx dev
    assumes vui: "valid_untyped_inv_wcap'
      (Invocations_H.Retype cref reset ptr_base ptr tp us slots dev)
          (Some (UntypedCap dev (ptr && ~~ mask sz) sz idx)) s"
  and misc: "ct_active' s" "invs' s"

begin

lemma cte_wp_at': "cte_wp_at' (\<lambda>cte. cteCap cte = capability.UntypedCap
      dev (ptr && ~~ mask sz) sz idx) cref s"
  and cover: "range_cover ptr sz (APIType_capBits tp us) (length (slots::machine_word list))"
  and misc2: "distinct slots"
     "slots \<noteq> []"
      "\<forall>slot\<in>set slots. cte_wp_at' (\<lambda>c. cteCap c = capability.NullCap) slot s"
      "\<forall>x\<in>set slots. ex_cte_cap_wp_to' (\<lambda>_. True) x s"
  using vui
  by (auto simp: cte_wp_at_ctes_of)

interpretation Arch . (*FIXME: arch-split*)

lemma idx_cases:
  "((\<not> reset \<and> idx \<le> unat (ptr - (ptr && ~~ mask sz))) \<or> reset \<and> ptr = ptr && ~~ mask sz)"
  using vui
  by (clarsimp simp: cte_wp_at_ctes_of)

lemma desc_range:
  "reset \<longrightarrow> descendants_range_in' (mask_range ptr sz) (cref) (ctes_of s)"
  using vui by (clarsimp simp: empty_descendants_range_in')

abbreviation(input)
  "retype_range == {ptr..ptr + of_nat (length slots) * 2 ^ APIType_capBits tp us - 1}"

abbreviation(input)
  "usable_range ==  {ptr..(ptr && ~~ mask sz) + mask sz}"

lemma not_0_ptr[simp]: "ptr\<noteq> 0"
  using misc cte_wp_at'
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (case_tac cte)
  apply clarsimp
  apply (drule(1) ctes_of_valid_cap'[OF _ invs_valid_objs'])
  apply (simp add: valid_cap'_def)
  done

lemmas range_cover_subset'' = range_cover_subset'[simplified add_mask_fold]

lemma subset_stuff[simp]:
  "retype_range \<subseteq> usable_range"
  apply (rule range_cover_subset''[OF cover])
  apply (simp add:misc2)
  done

lemma descendants_range[simp]:
  "descendants_range_in' usable_range cref (ctes_of s)"
  "descendants_range_in' retype_range cref (ctes_of s)"
proof -
  have "descendants_range_in' usable_range cref (ctes_of s)"
    using misc idx_cases cte_wp_at' cover
    apply -
    apply (erule disjE)
     apply (erule cte_wp_at_caps_descendants_range_inI'
                  [OF _ _ _ range_cover.sz(1)[where 'a=machine_word_len, folded word_bits_def]])
       apply simp+
    using desc_range
    apply simp
    done
  thus "descendants_range_in' usable_range cref (ctes_of s)"
    by simp
  thus "descendants_range_in' retype_range cref (ctes_of s)"
    by (rule descendants_range_in_subseteq'[OF _ subset_stuff])
qed

lemma vc'[simp] : "s \<turnstile>' capability.UntypedCap dev (ptr && ~~ mask sz) sz idx"
  using misc cte_wp_at'
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (case_tac cte)
  apply clarsimp
  apply (erule ctes_of_valid_cap')
  apply (simp add: invs_valid_objs')
  done

lemma ptr_cn[simp]:
  "canonical_address (ptr && ~~ mask sz)"
  using vc' unfolding valid_cap'_def by simp

lemma sz_limit[simp]:
  "sz \<le> maxUntypedSizeBits"
  using vc' unfolding valid_cap'_def by clarsimp

lemma ps_no_overlap'[simp]: "\<not> reset \<Longrightarrow> pspace_no_overlap' ptr sz s"
  using misc cte_wp_at' cover idx_cases
  apply clarsimp
  apply (erule cte_wp_at_pspace_no_overlapI'
    [OF  _ _ _ range_cover.sz(1)[where 'a=machine_word_len, folded word_bits_def]])
    apply (simp add: cte_wp_at_ctes_of)
   apply simp+
  done

lemma caps_no_overlap'[simp]: "caps_no_overlap'' ptr sz s"
  using cte_wp_at' misc cover desc_range idx_cases
  apply -
  apply (erule disjE)
   apply (erule cte_wp_at_caps_no_overlapI'
     [OF  _ _ _ range_cover.sz(1)[where 'a=machine_word_len, folded word_bits_def]])
    apply simp+
  apply (erule descendants_range_caps_no_overlapI')
   apply simp+
  done

lemma idx_compare'[simp]:
  "unat ((ptr && mask sz) + (of_nat (length slots)<< (APIType_capBits tp us))) \<le> 2 ^ sz"
  apply (rule le_trans[OF unat_plus_gt])
  apply (simp add: range_cover.unat_of_nat_n_shift[OF cover] range_cover_unat)
  apply (insert range_cover.range_cover_compare_bound[OF cover])
  apply simp
  done

lemma ex_cte_no_overlap':
  "\<And>P p. ex_cte_cap_wp_to' P p s \<Longrightarrow> p \<notin> usable_range"
  using cte_wp_at' misc
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (drule_tac cte = cte in descendants_range_ex_cte'[OF descendants_range(1)])
      apply (clarsimp simp: word_and_le2 isCap_simps add_mask_fold)+
  done

lemma cref_inv: "cref \<notin> usable_range"
  apply (insert misc cte_wp_at')
  apply (drule if_unsafe_then_capD')
    apply (simp add: invs'_def valid_state'_def)
   apply simp
  apply (erule ex_cte_no_overlap')
  done

lemma slots_invD:
  "\<And>x. x \<in> set slots \<Longrightarrow> x \<noteq> cref \<and> x \<notin> usable_range \<and> ex_cte_cap_wp_to' (\<lambda>_. True) x s"
  using misc cte_wp_at' vui
  apply clarsimp
  apply (drule(1) bspec)+
  apply (drule ex_cte_no_overlap')
  apply simp
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma usableRange_disjoint:
  "usableUntypedRange (capability.UntypedCap d (ptr && ~~ mask sz) sz
       (unat ((ptr && mask sz) + of_nat (length slots) * 2 ^ APIType_capBits tp us))) \<inter>
       {ptr..ptr + of_nat (length slots) * 2 ^ APIType_capBits tp us - 1} = {}"
proof -
  have idx_compare''[simp]:
    "unat ((ptr && mask sz) + (of_nat (length slots) * (2::machine_word) ^ APIType_capBits tp us)) < 2 ^ sz
     \<Longrightarrow> ptr + of_nat (length slots) * 2 ^ APIType_capBits tp us - 1
         < ptr + of_nat (length slots) * 2 ^ APIType_capBits tp us"
    apply (rule word_leq_le_minus_one,simp)
    apply (rule neq_0_no_wrap)
     apply (rule machine_word_plus_mono_right_split)
      apply (simp add: shiftl_t2n range_cover_unat[OF cover] field_simps)
     apply (simp add: range_cover.sz(1)[where 'a=machine_word_len, folded word_bits_def, OF cover])+
    done
  show ?thesis
    apply (clarsimp simp: mask_out_sub_mask)
    apply (drule idx_compare'')
    apply simp
    done
qed

lemma szw: "sz < word_bits"
  using cte_wp_at_valid_objs_valid_cap'[OF cte_wp_at'] misc
  by (clarsimp simp: valid_cap_simps' capAligned_def invs_valid_objs')

lemma idx_le_new_offs:
  "\<not> reset
   \<longrightarrow> idx \<le> unat ((ptr && mask sz) + (of_nat (length slots) * 2 ^ (APIType_capBits tp us)))"
  using misc idx_cases range_cover.range_cover_base_le[OF cover]
  apply (clarsimp simp only: simp_thms)
  apply (erule order_trans)
  apply (simp add: word_le_nat_alt[symmetric]
                   shiftl_t2n mult.commute)
  done

end

context begin interpretation Arch . (*FIXME: arch-split*)

crunch deleteObjects
  for ksIdleThread[wp]: "\<lambda>s. P (ksIdleThread s)"
  (simp: crunch_simps wp: hoare_drop_imps unless_wp)
crunch deleteObjects
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  (simp: crunch_simps wp: hoare_drop_imps unless_wp)
crunch deleteObjects
  for irq_node[wp]: "\<lambda>s. P (irq_node' s)"
  (simp: crunch_simps wp: hoare_drop_imps unless_wp)

lemma deleteObjects_ksCurThread[wp]:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> deleteObjects ptr sz \<lbrace>\<lambda>_ s. P (ksCurThread s)\<rbrace>"
  apply (simp add: deleteObjects_def3)
  apply (wp | simp add: doMachineOp_def split_def)+
  done

lemma deleteObjects_ct_active':
  "\<lbrace>invs' and sch_act_simple and ct_active'
      and cte_wp_at' (\<lambda>c. cteCap c = UntypedCap d ptr sz idx) cref
      and (\<lambda>s. descendants_range' (UntypedCap d ptr sz idx) cref (ctes_of s))
      and K (sz < word_bits \<and> is_aligned ptr sz)\<rbrace>
     deleteObjects ptr sz
   \<lbrace>\<lambda>_. ct_active'\<rbrace>"
  apply (simp add: ct_in_state'_def)
  apply (rule hoare_pre)
   apply wps
   apply (wp deleteObjects_st_tcb_at')
  apply (auto simp: ct_in_state'_def elim: pred_tcb'_weakenE)
  done

defs cNodeOverlap_def:
  "cNodeOverlap \<equiv> \<lambda>cns inRange. \<exists>p n. cns p = Some n \<and> (\<not> is_aligned p (cte_level_bits + n)
      \<or> cte_level_bits + n \<ge> word_bits
      \<or> ({p .. p + 2 ^ (cte_level_bits + n) - 1} \<inter> {p. inRange p} \<noteq> {}))"

defs archOverlap_def:
  "archOverlap \<equiv> \<lambda>s inRange.
    \<exists>p pt_t. gsPTTypes (ksArchState s) p = Some pt_t \<and>
             (\<not>is_aligned p (pt_bits pt_t) \<or>
              ({p .. p + 2 ^ pt_bits pt_t - 1} \<inter> {p. inRange p} \<noteq> {}))"

lemma cNodeNoOverlap:
  notes Int_atLeastAtMost[simp del]
  shows
  "corres dc (\<lambda>s. \<exists>cref. cte_wp_at (\<lambda>cap. is_untyped_cap cap
                  \<and> Collect R \<subseteq> usable_untyped_range cap) cref s
              \<and> valid_objs s \<and> pspace_aligned s)
             \<top>
             (return x) (stateAssert (\<lambda>s. \<not> cNodeOverlap (gsCNodes s) R) [])"
  apply (simp add: stateAssert_def assert_def)
  apply (rule corres_symb_exec_r[OF _ get_sp])
    apply (rule corres_req[rotated], subst if_P, assumption)
     apply simp
    apply (clarsimp simp: cNodeOverlap_def cte_wp_at_caps_of_state)
    apply (frule(1) caps_of_state_valid_cap)
    apply (frule usable_range_subseteq[rotated], simp add: valid_cap_def)
    apply (clarsimp simp: valid_cap_def valid_untyped_def cap_table_at_gsCNodes_eq
                          obj_at_def is_cap_table is_cap_simps)
    apply (frule(1) pspace_alignedD)
    apply simp
    apply (elim allE, drule(1) mp, simp add: obj_range_def valid_obj_def cap_aligned_def)
    apply (erule is_aligned_get_word_bits[where 'a=machine_word_len, folded word_bits_def])
     apply (clarsimp simp: is_aligned_no_overflow simp del: )
     apply blast
    apply (simp add: is_aligned_no_overflow power_overflow word_bits_def
                     Int_atLeastAtMost)
   apply wp+
  done

lemma archNoOverlap:
  notes Int_atLeastAtMost[simp del]
  shows
  "corres dc (\<lambda>s. \<exists>cref. cte_wp_at (\<lambda>cap. is_untyped_cap cap
                                          \<and> Collect R \<subseteq> usable_untyped_range cap) cref s
                         \<and> valid_objs s \<and> pspace_aligned s)
             \<top>
             (return x) (stateAssert (\<lambda>s. \<not> archOverlap s R) [])"
  apply (simp add: stateAssert_def assert_def)
  apply (rule corres_symb_exec_r[OF _ get_sp])
    apply (rule corres_req[rotated], subst if_P, assumption)
     apply simp
    apply (clarsimp simp: archOverlap_def cte_wp_at_caps_of_state)
    apply (frule state_rel_ghost)
    apply (drule (1) ghost_PTTypes)
    apply (frule(1) caps_of_state_valid_cap)
    apply (frule usable_range_subseteq[rotated], simp add: valid_cap_def)
    apply (clarsimp simp: valid_cap_def valid_untyped_def
                          obj_at_def is_cap_table is_cap_simps)
    apply (frule(1) pspace_alignedD)
    apply (simp add: pt_bits_def)
    apply (elim allE, drule(1) mp, simp add: obj_range_def valid_obj_def cap_aligned_def)
    apply (erule is_aligned_get_word_bits[where 'a=machine_word_len, folded word_bits_def])
     apply (clarsimp simp: is_aligned_no_overflow simp del: )
     apply blast
    apply (simp add: is_aligned_no_overflow power_overflow word_bits_def
                     Int_atLeastAtMost)
   apply wp+
  done

lemma reset_ineq_eq_idx_0:
  "\<lbrakk> idx \<le> 2 ^ sz; b \<le> sz; (ptr :: obj_ref) \<noteq> 0; is_aligned ptr sz; sz < word_bits \<rbrakk>
   \<Longrightarrow> (ptr + of_nat idx - 1 < ptr) = (idx = 0)"
  apply (cases "idx = 0")
   apply (simp add: gt0_iff_gem1[symmetric] word_neq_0_conv)
  apply simp
  apply (subgoal_tac "ptr \<le> ptr + of_nat idx - 1", simp_all)[1]
  apply (subst field_simps[symmetric], erule is_aligned_no_wrap')
  apply (subst word_less_nat_alt)
  apply simp
  apply (subst unat_of_nat_minus_1)
    apply (erule order_le_less_trans, rule power_strict_increasing)
     apply (simp add: word_bits_def)
    apply simp
   apply (rule notI, simp)
  apply (erule order_less_le_trans[rotated])
  apply simp
  done

lemma reset_addrs_same:
  "\<lbrakk> idx \<le> 2 ^ sz; resetChunkBits \<le> sz; ptr \<noteq> 0; is_aligned ptr sz; sz < word_bits \<rbrakk>
   \<Longrightarrow> [ptr , ptr + 2 ^ resetChunkBits .e. getFreeRef ptr idx - 1] =
       map (\<lambda>i. getFreeRef ptr (i * 2 ^ resetChunkBits))
           [i\<leftarrow>[0..<2 ^ (sz - resetChunkBits)]. i * 2 ^ resetChunkBits < idx]"
  apply (simp add: upto_enum_step_def getFreeRef_def reset_ineq_eq_idx_0)
  apply (clarsimp simp: upto_enum_word o_def unat_div simp del: upt.simps)
  apply (subst unat_of_nat_minus_1)
    apply (rule_tac y="2 ^ sz" in order_le_less_trans, simp)
    apply (rule power_strict_increasing, simp_all add: word_bits_def)[1]
   apply simp
  apply (rule_tac f="map f" for f in arg_cong)
  apply (rule filter_upt_eq[symmetric])
     apply clarsimp
     apply (erule order_le_less_trans[rotated])
     apply simp
    apply (rule notI)
    apply (drule order_less_le_trans[where x="a * b" for a b],
           rule_tac m="2 ^ resetChunkBits" and n=idx in alignUp_ge_nat)
     apply simp+
    apply (simp add: field_simps)
    apply (simp only: mult_Suc_right[symmetric])
    apply (subst(asm) div_add_self1[where 'a=nat, simplified, symmetric])
     apply simp
    apply (simp only: field_simps)
    apply simp
   apply clarsimp
   apply (rule order_le_less_trans, rule div_mult_le, simp)
  apply (simp add: Suc_le_eq td_gal_lt[symmetric] power_add[symmetric])
  done

lemmas descendants_of_null_filter' = null_filter_descendants_of'[OF null_filter_simp']

lemmas deleteObjects_descendants
    = deleteObjects_null_filter[where P="\<lambda>c. Q (descendants_of' p c)" for p Q,
                   simplified descendants_of_null_filter']

lemma updateFreeIndex_descendants_of2:
  " \<lbrace>\<lambda>s. cte_wp_at' (isUntypedCap o cteCap) ptr s \<and>
         P (\<lambda>y. descendants_of' y (ctes_of s))\<rbrace>
    updateFreeIndex ptr index
  \<lbrace>\<lambda>r s. P (\<lambda>y. descendants_of' y (ctes_of s))\<rbrace>"
  apply (simp add: updateFreeIndex_def updateTrackedFreeIndex_def getSlotCap_def)
  apply (wp updateFreeIndex_descendants_of'[simplified swp_def descendants_of_null_filter']
           getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of isCap_simps)
  done

crunch updateFreeIndex
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"

lemma updateFreeIndex_cte_wp_at:
  "\<lbrace>\<lambda>s. cte_wp_at' (\<lambda>c. P (cteCap_update (if p = slot
      then capFreeIndex_update (\<lambda>_. idx) else id) c)) p s\<rbrace>
    updateFreeIndex slot idx
  \<lbrace>\<lambda>rv. cte_wp_at' P p\<rbrace>"
  apply (simp add: updateFreeIndex_def updateTrackedFreeIndex_def getSlotCap_def split del: if_split)
  apply (rule hoare_pre, wp updateCap_cte_wp_at' getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (case_tac "the (ctes_of s p)")
  apply (auto split: if_split_asm)
  done

lemma ex_tupI:
  "P (fst x) (snd x) \<Longrightarrow> \<exists>a b. P a b"
  by blast

context begin interpretation Arch . (*FIXME: arch-split*)

lemma resetUntypedCap_corres:
  "untypinv_relation ui ui'
    \<Longrightarrow> corres (dc \<oplus> dc)
    (einvs and schact_is_rct and ct_active
     and valid_untyped_inv_wcap ui (Some (cap.UntypedCap dev ptr sz idx))
     and (\<lambda>_. \<exists>ptr_base ptr' ty us slots dev'.
               ui = Invocations_A.Retype slot True ptr_base ptr' ty us slots dev))
    (invs' and valid_untyped_inv_wcap' ui' (Some (UntypedCap dev ptr sz idx)) and ct_active')
    (reset_untyped_cap slot) (resetUntypedCap (cte_map slot))"
  apply (rule corres_gen_asm, clarsimp)
  apply (simp add: reset_untyped_cap_def resetUntypedCap_def liftE_bindE cong: if_cong)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF getSlotCap_corres])
       apply simp
      apply (rule_tac F="cap = cap.UntypedCap dev ptr sz idx \<and> (\<exists>s. s \<turnstile> cap)" in corres_gen_asm)
      apply (clarsimp simp: bits_of_def free_index_of_def unlessE_def
                      split del: if_split cong: if_cong)
      apply (rule corres_if[OF refl])
       apply (rule corres_returnOk[where P=\<top> and P'=\<top>], simp)
      apply (rule corres_split[OF deleteObjects_corres])
          apply (clarsimp simp add: valid_cap_def cap_aligned_def)
         apply (clarsimp simp add: valid_cap_def cap_aligned_def untyped_min_bits_def)
        apply (rule corres_if)
          apply simp
         apply (simp add: bits_of_def shiftL_nat)
         apply (rule corres_split_nor)
            apply (simp add: unless_def)
            apply (rule corres_when, simp)
            apply (rule corres_machine_op)
            apply (rule corres_Id, simp, simp, wp)
           apply (rule updateFreeIndex_corres, simp)
           apply (simp add: free_index_of_def)
          apply (wp | simp only: unless_def)+
        apply (rule_tac F="sz < word_bits \<and> idx \<le> 2 ^ sz
                            \<and> ptr \<noteq> 0 \<and> is_aligned ptr sz
                            \<and> resetChunkBits \<le> sz" in corres_gen_asm)
        apply (simp add: bits_of_def free_index_of_def mapME_x_map_simp liftE_bindE
                         reset_addrs_same[where ptr=ptr and idx=idx and sz=sz]
                         o_def rev_map
                    del: capFreeIndex_update.simps)
        apply (rule_tac P="\<lambda>x. valid_objs and pspace_aligned and pspace_distinct
                       and pspace_no_overlap {ptr .. ptr + 2 ^ sz - 1}
                       and cte_wp_at (\<lambda>a. is_untyped_cap a \<and> obj_ref_of a = ptr \<and> cap_bits a = sz
                           \<and> cap_is_device a = dev) slot"
                   and P'="\<lambda>_. valid_pspace' and (\<lambda>s. descendants_of' (cte_map slot) (ctes_of s) = {})
                       and pspace_no_overlap' ptr sz
                       and cte_wp_at' (\<lambda>cte. \<exists>idx. cteCap cte = UntypedCap dev ptr sz idx) (cte_map slot)"
              in mapME_x_corres_same_xs)
           apply (rule corres_guard_imp)
             apply (rule corres_split_nor)
                apply (rule corres_machine_op)
                apply (rule corres_Id)
                  apply (simp add: shiftL_nat getFreeRef_def shiftl_t2n mult.commute)
                 apply simp
                apply wp
               apply (rule corres_split_nor[OF updateFreeIndex_corres])
                   apply simp
                  apply (simp add: getFreeRef_def getFreeIndex_def free_index_of_def)
                  apply clarify
                  apply (subst unat_mult_simple)
                   apply (subst unat_of_nat_eq)
                    apply (rule order_less_trans[rotated],
                           rule_tac n=sz in power_strict_increasing; simp add: word_bits_def)
                    apply (erule order_less_le_trans; simp)
                   apply (subst unat_p2)
                    apply (simp add: Kernel_Config.resetChunkBits_def)
                   apply (rule order_less_trans[rotated],
                         rule_tac n=sz in power_strict_increasing; simp add: word_bits_def)
                  apply (subst unat_of_nat_eq)
                   apply (rule order_less_trans[rotated],
                          rule_tac n=sz in power_strict_increasing; simp add: word_bits_def)
                   apply (erule order_less_le_trans; simp)
                  apply simp
                 apply (rule preemptionPoint_corres)
                apply wp+
            apply (clarsimp simp: cte_wp_at_caps_of_state)
           apply (clarsimp simp: getFreeRef_def valid_pspace'_def cte_wp_at_ctes_of
                                 valid_cap_def cap_aligned_def)
           apply (erule aligned_add_aligned)
            apply (rule is_aligned_weaken)
             apply (rule is_aligned_mult_triv2)
            apply (simp add: Kernel_Config.resetChunkBits_def)
           apply (simp add: untyped_min_bits_def)
          apply (rule hoare_pre)
           apply simp
           apply (strengthen imp_consequent)
           apply (wp preemption_point_inv set_cap_cte_wp_at update_untyped_cap_valid_objs
                     set_cap_no_overlap | simp)+
          apply (clarsimp simp: exI cte_wp_at_caps_of_state)
          apply (drule caps_of_state_valid_cap, simp+)
          apply (clarsimp simp: is_cap_simps valid_cap_simps
                                cap_aligned_def
                                valid_untyped_pspace_no_overlap)
         apply (rule hoare_pre)
          apply (simp del: capFreeIndex_update.simps)
          apply (strengthen imp_consequent)
          apply (wp updateFreeIndex_valid_pspace_no_overlap'
                    updateFreeIndex_descendants_of2
                    doMachineOp_psp_no_overlap
                    updateFreeIndex_cte_wp_at
                    pspace_no_overlap'_lift
                    preemptionPoint_inv
                    hoare_vcg_ex_lift
                    | simp)+
         apply (clarsimp simp add: cte_wp_at_ctes_of exI isCap_simps valid_pspace'_def)
         apply (clarsimp simp: getFreeIndex_def getFreeRef_def)
         apply (subst is_aligned_weaken[OF is_aligned_mult_triv2])
          apply (simp add: Kernel_Config.resetChunkBits_def minUntypedSizeBits_def)
         apply (subst unat_mult_simple)
          apply (subst unat_of_nat_eq)
           apply (rule order_less_trans[rotated],
                  rule_tac n=sz in power_strict_increasing; simp add: word_bits_def)
           apply (erule order_less_le_trans; simp)
          apply (subst unat_p2)
           apply (simp add: Kernel_Config.resetChunkBits_def)
          apply (rule order_less_trans[rotated],
                 rule_tac n=sz in power_strict_increasing; simp add: word_bits_def)
         apply (subst unat_of_nat_eq)
          apply (rule order_less_trans[rotated],
                 rule_tac n=sz in power_strict_increasing; simp add: word_bits_def)
          apply (erule order_less_le_trans; simp)
         apply simp
        apply simp
       apply (simp add: if_apply_def2)
       apply (strengthen invs_valid_objs invs_psp_aligned invs_distinct)
       apply (wp hoare_vcg_const_imp_lift)
      apply (simp add: if_apply_def2)
      apply (strengthen invs_pspace_aligned' invs_pspace_distinct'
                        invs_valid_pspace')
      apply (wp hoare_vcg_const_imp_lift deleteObjects_cte_wp_at'[where p="cte_map slot"]
                deleteObjects_invs'[where p="cte_map slot"]
                deleteObjects_descendants[where p="cte_map slot"]
           | simp)+
     apply (wp get_cap_wp getCTE_wp' | simp add: getSlotCap_def)+
   apply (clarsimp simp: cte_wp_at_caps_of_state descendants_range_def2)
   apply (cases slot)
   apply (strengthen empty_descendants_range_in
                     ex_tupI[where x=slot])+
   apply (frule(1) caps_of_state_valid)
   apply (clarsimp simp: valid_cap_simps cap_aligned_def)
   apply (frule(1) caps_of_state_valid)
   apply (frule if_unsafe_then_capD[OF caps_of_state_cteD], clarsimp+)
   apply (drule(1) ex_cte_cap_protects[OF _ caps_of_state_cteD
                                          empty_descendants_range_in _ order_refl]; clarsimp)
   apply (intro conjI impI; auto)[1]
  apply (clarsimp simp: cte_wp_at_ctes_of descendants_range'_def2
                        empty_descendants_range_in')
  apply (frule cte_wp_at_valid_objs_valid_cap'[OF ctes_of_cte_wpD], clarsimp+)
  apply (clarsimp simp: valid_cap_simps' capAligned_def is_aligned_weaken untypedBits_defs)
  apply (frule if_unsafe_then_capD'[OF ctes_of_cte_wpD], clarsimp+)
  apply (frule(1) descendants_range_ex_cte'[OF empty_descendants_range_in' _ order_refl],
        (simp add: isCap_simps add_mask_fold)+)
  apply (auto simp: descendants_range_in'_def valid_untyped'_def)
  done

end

lemma deleteObjects_ex_cte_cap_wp_to':
  "\<lbrace>invs' and ex_cte_cap_wp_to' P slot and (\<lambda>s. descendants_of' p (ctes_of s) = {})
      and cte_wp_at' (\<lambda>cte. \<exists>idx d. cteCap cte = UntypedCap d ptr sz idx) p\<rbrace>
    deleteObjects ptr sz
  \<lbrace>\<lambda>rv. ex_cte_cap_wp_to' P slot\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (rule hoare_pre)
   apply (simp add: ex_cte_cap_wp_to'_def)
   apply wps
   apply (wp hoare_vcg_ex_lift)
   apply (rule_tac idx=idx in deleteObjects_cte_wp_at')
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (frule ctes_of_valid[OF ctes_of_cte_wpD], clarsimp+)
  apply (clarsimp simp: ex_cte_cap_wp_to'_def
                        cte_wp_at_ctes_of)
  apply (rule_tac x=cref in exI, simp)
  apply (frule_tac p=cref in if_unsafe_then_capD'[OF ctes_of_cte_wpD], clarsimp+)
  apply (frule descendants_range_ex_cte'[rotated, OF _ order_refl, where p=p],
         (simp add: isCap_simps empty_descendants_range_in')+)
  apply (auto simp: add_mask_fold)
  done

lemma updateCap_cte_cap_wp_to':
  "\<lbrace>\<lambda>s. cte_wp_at' (\<lambda>cte. p' \<in> cte_refs' (cteCap cte) (irq_node' s) \<and> P (cteCap cte)
                           \<longrightarrow> p' \<in> cte_refs' cap (irq_node' s) \<and> P cap) p s
        \<and> ex_cte_cap_wp_to' P p' s\<rbrace>
     updateCap p cap
   \<lbrace>\<lambda>rv. ex_cte_cap_wp_to' P p'\<rbrace>"
  apply (simp add: ex_cte_cap_wp_to'_def cte_wp_at_ctes_of updateCap_def)
  apply (rule hoare_pre, (wp getCTE_wp | wps)+)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (rule_tac x=cref in exI)
  apply auto
  done

crunch doMachineOp
  for ct_in_state'[wp]: "ct_in_state' P"
  (simp: crunch_simps ct_in_state'_def)

crunch doMachineOp
  for st_tcb_at'[wp]: "st_tcb_at' P p"
  (simp: crunch_simps ct_in_state'_def)

lemma ex_cte_cap_wp_to_irq_state_independent_H[simp]:
  "irq_state_independent_H (ex_cte_cap_wp_to' P slot)"
  by (simp add: ex_cte_cap_wp_to'_def)

context begin interpretation Arch . (*FIXME: arch-split*)

lemma updateFreeIndex_ctes_of:
  "\<lbrace>\<lambda>s.  P (modify_map (ctes_of s) ptr (cteCap_update (capFreeIndex_update (\<lambda>_. idx))))\<rbrace>
    updateFreeIndex ptr idx
  \<lbrace>\<lambda>r s.  P (ctes_of s)\<rbrace>"
  apply (simp add: updateFreeIndex_def updateTrackedFreeIndex_def getSlotCap_def)
  apply (wp updateCap_ctes_of_wp getCTE_wp' | simp)+
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (erule rsubst[where P=P])
  apply (case_tac cte)
  apply (clarsimp simp: modify_map_def fun_eq_iff)
  done

lemma updateFreeIndex_cte_cap_wp_to'[wp]:
  "\<lbrace>\<lambda>s. cte_wp_at' (isUntypedCap o cteCap) p s
        \<and> ex_cte_cap_wp_to' P p' s\<rbrace>
     updateFreeIndex p idx
   \<lbrace>\<lambda>rv. ex_cte_cap_wp_to' P p'\<rbrace>"
  apply (simp add: updateFreeIndex_def updateTrackedFreeIndex_def getSlotCap_def)
  apply (wp updateCap_cte_cap_wp_to' getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (clarsimp simp: isCap_simps ex_cte_cap_wp_to'_def split: option.split)
  done

lemma setCTE_ct_in_state:
  "\<lbrace>ct_in_state' P\<rbrace> setCTE p cte \<lbrace>\<lambda>rv. ct_in_state' P\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (rule hoare_pre, wp ct_in_state'_decomp setCTE_pred_tcb_at')
  apply (auto simp: ct_in_state'_def)
  done

crunch updateFreeIndex
  for ct_in_state[wp]: "ct_in_state' P"
crunch updateFreeIndex
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"

lemma resetUntypedCap_invs_etc:
  "\<lbrace>invs' and valid_untyped_inv_wcap' ui
      (Some (UntypedCap dev ptr sz idx))
         and ct_active'
         and K (\<exists>ptr_base ptr' ty us slots. ui = Retype slot True ptr_base ptr' ty us slots dev)\<rbrace>
    resetUntypedCap slot
  \<lbrace>\<lambda>_. invs' and valid_untyped_inv_wcap' ui (Some (UntypedCap dev ptr sz 0))
      and ct_active'
      and pspace_no_overlap' ptr sz\<rbrace>, \<lbrace>\<lambda>_. invs'\<rbrace>"
  (is "\<lbrace>invs' and valid_untyped_inv_wcap' ?ui (Some ?cap) and ct_active' and ?asm\<rbrace>
    ?f \<lbrace>\<lambda>_. invs' and ?vu2 and ct_active' and ?psp\<rbrace>, \<lbrace>\<lambda>_. invs'\<rbrace>")
  apply (simp add: resetUntypedCap_def getSlotCap_def
                   liftE_bind_return_bindE_returnOk bindE_assoc)
  apply (rule bindE_wp_fwd)
   apply simp
   apply (rule getCTE_sp)
  apply (rule hoare_name_pre_stateE)
  apply (clarsimp split del: if_split)
  apply (subgoal_tac "capAligned ?cap")
   prefer 2
   apply (frule cte_wp_at_valid_objs_valid_cap', clarsimp+)
   apply (clarsimp simp: cte_wp_at_ctes_of capAligned_def valid_cap_simps')
  apply (cases "idx = 0")
   apply (clarsimp simp: cte_wp_at_ctes_of unlessE_def split del: if_split)
   apply wp
   apply (clarsimp simp: valid_cap_simps' capAligned_def)
   apply (rule cte_wp_at_pspace_no_overlapI'[where cref=slot],
       (simp_all add: cte_wp_at_ctes_of)+)[1]
  apply (clarsimp simp: unlessE_def cte_wp_at_ctes_of
             split del: if_split)
  apply (rule_tac Q'="\<lambda>_. invs' and valid_untyped_inv_wcap' ?ui (Some ?cap) and ct_active' and ?psp"
               in bindE_wp_fwd)
   apply clarsimp
   apply (rule hoare_pre)
    apply (simp add: sch_act_simple_def)
    apply (wps )
    apply (wp deleteObject_no_overlap[where idx=idx]
              deleteObjects_invs'[where idx=idx and p=slot]
              hoare_vcg_ex_lift hoare_vcg_const_Ball_lift
              deleteObjects_cte_wp_at'[where idx=idx]
              deleteObjects_descendants[where p=slot]
              deleteObjects_nosch
              deleteObjects_ct_active'[where idx=idx and cref=slot]
              deleteObjects_ex_cte_cap_wp_to'[where p=slot])
   apply (clarsimp simp: cte_wp_at_ctes_of descendants_range'_def2
                         empty_descendants_range_in'
                         capAligned_def sch_act_simple_def)
   apply (strengthen refl)
   apply (frule ctes_of_valid[OF ctes_of_cte_wpD], clarsimp+)
   apply (frule if_unsafe_then_capD'[OF ctes_of_cte_wpD], clarsimp+)
   apply (erule rev_mp[where P="Ball S f" for S f]
                rev_mp[where P="ex_cte_cap_wp_to' P p s" for P p s])+
   apply (strengthen descendants_range_ex_cte'[rotated, OF _ order_refl, mk_strg D _ E])
   apply (clarsimp simp: isCap_simps empty_descendants_range_in' add_mask_fold)
   apply auto[1]
  apply (cases "dev \<or> sz < resetChunkBits")
   apply (simp add: pred_conj_def unless_def)
   apply (rule hoare_pre)
    apply (strengthen exI[where x=sz])
    apply (wp updateFreeIndex_clear_invs'
              hoare_vcg_ex_lift
              hoare_vcg_const_Ball_lift
              updateFreeIndex_descendants_of2
              sch_act_simple_lift
              pspace_no_overlap'_lift
              doMachineOp_psp_no_overlap
              updateFreeIndex_ctes_of
              updateFreeIndex_cte_wp_at
            | simp | wps | wp (once) ex_cte_cap_to'_pres)+
   apply (clarsimp simp: cte_wp_at_ctes_of isCap_simps
                         modify_map_def)
   apply auto[1]
  apply simp
  apply (rule hoare_pre, rule hoare_strengthen_postE,
    rule_tac P="\<lambda>i. invs' and ?psp and ct_active' and valid_untyped_inv_wcap' ?ui
        (Some (UntypedCap dev ptr sz (if i = 0 then idx
            else (length [ptr , ptr + 2 ^ resetChunkBits .e. getFreeRef ptr idx - 1] - i) * 2 ^ resetChunkBits)))"
      and E="\<lambda>_. invs'"
      in mapME_x_validE_nth)
     apply (rule hoare_pre)
      apply simp
      apply (wp preemptionPoint_invs
                updateFreeIndex_clear_invs'
                hoare_vcg_ex_lift
                updateFreeIndex_descendants_of2
                updateFreeIndex_ctes_of
                updateFreeIndex_cte_wp_at
                doMachineOp_psp_no_overlap
                hoare_vcg_ex_lift hoare_vcg_const_Ball_lift
                pspace_no_overlap'_lift[OF preemptionPoint_inv]
                pspace_no_overlap'_lift
                updateFreeIndex_ct_in_state[unfolded ct_in_state'_def]
              | strengthen invs_pspace_aligned' invs_pspace_distinct'
              | simp add: ct_in_state'_def
                          sch_act_simple_def
              | rule hoare_vcg_conj_liftE_R
              | wp (once) preemptionPoint_inv
              | wps
              | wp (once) ex_cte_cap_to'_pres)+
     apply (clarsimp simp: cte_wp_at_ctes_of isCap_simps
                           conj_comms)
     apply (subgoal_tac "getFreeIndex ptr
            (rev [ptr , ptr + 2 ^ resetChunkBits .e. getFreeRef ptr idx - 1] ! i)
          = (length [ptr , ptr + 2 ^ resetChunkBits .e. getFreeRef ptr idx - 1] - Suc i) *
               2 ^ resetChunkBits")
      apply clarsimp
      apply (frule ctes_of_valid[OF ctes_of_cte_wpD], clarsimp+)
      apply (subgoal_tac "resetChunkBits < word_bits \<and> sz < word_bits")
       apply (strengthen is_aligned_weaken[OF is_aligned_mult_triv2])
       apply (subst nat_less_power_trans2[THEN order_less_imp_le])
         apply (clarsimp simp add: upto_enum_step_def getFreeRef_def)
         apply (rule less_imp_diff_less)
         apply (simp add: unat_div td_gal_lt[symmetric] power_add[symmetric])
         apply (cases "idx = 0")
          apply (simp add: gt0_iff_gem1[symmetric, folded word_neq_0_conv])
          apply (simp add: valid_cap_simps')
         apply (subst unat_minus_one)
          apply (clarsimp simp: valid_cap_simps')
          apply (drule of_nat64_0)
           apply (erule order_le_less_trans, simp)
          apply simp
         apply (clarsimp simp: unat_of_nat valid_cap_simps')
         apply (erule order_less_le_trans[rotated], simp)
        apply simp
       apply (auto simp: Kernel_Config.resetChunkBits_def minUntypedSizeBits_def)[1]
      apply (simp add: valid_cap_simps' Kernel_Config.resetChunkBits_def capAligned_def)
     apply (simp add: nth_rev)
     apply (simp add: upto_enum_step_def upto_enum_word getFreeIndex_def
                      getFreeRef_def
                 del: upt.simps)
     apply (intro conjI impI, simp_all)[1]
     apply (subgoal_tac "resetChunkBits < word_bits")
      apply (rule word_unat.Abs_eqD[OF _ word_unat.Rep])
       apply (simp add: word_of_nat_plus Abs_fnat_hom_mult[symmetric])
      apply (simp only: unats_def word_bits_def[symmetric])
      apply (clarsimp simp: unat_div nat_mult_power_less_eq)
      apply (rule less_imp_diff_less)
      apply (simp add: td_gal_lt[symmetric] power_add[symmetric])
      apply (simp only: unat_lt2p word_bits_def)
     apply (simp add: Kernel_Config.resetChunkBits_def word_bits_def)
    apply (clarsimp simp: cte_wp_at_ctes_of getFreeRef_def
                          upto_enum_step_def upto_enum_word)
    apply (frule cte_wp_at_valid_objs_valid_cap'[OF ctes_of_cte_wpD], clarsimp+)
    apply (clarsimp simp: valid_cap_simps' capAligned_def)
    apply (simp add: reset_ineq_eq_idx_0)
   apply simp
  apply clarsimp
  done

end

lemma whenE_reset_resetUntypedCap_invs_etc:
  "\<lbrace>invs' and valid_untyped_inv_wcap' ui
      (Some (UntypedCap dev ptr sz idx))
         and ct_active'
         and K (\<exists>ptr_base ty us slots. ui = Retype slot reset ptr_base ptr' ty us slots dev)\<rbrace>
    whenE reset (resetUntypedCap slot)
  \<lbrace>\<lambda>_. invs' and valid_untyped_inv_wcap' ui (Some (UntypedCap dev ptr sz (if reset then 0 else idx)))
      and ct_active'
      and pspace_no_overlap' (if reset then ptr else ptr') sz\<rbrace>, \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (rule hoare_pre)
   apply (wp whenE_wp resetUntypedCap_invs_etc[where idx=idx,
           simplified pred_conj_def conj_assoc]
       | simp)+
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (frule cte_wp_at_valid_objs_valid_cap'[OF ctes_of_cte_wpD], clarsimp+)
  apply (clarsimp simp: valid_cap_simps' capAligned_def)
  apply (drule_tac cref=slot in cte_wp_at_pspace_no_overlapI',
    simp add: cte_wp_at_ctes_of, simp+)
  done

crunch updateFreeIndex
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"

end

lemma (in range_cover) funky_aligned:
  "is_aligned ((ptr && foo) + v * 2 ^ sbit) sbit"
  apply (rule aligned_add_aligned)
    apply (rule is_aligned_andI1)
    apply (rule aligned)
   apply (rule is_aligned_mult_triv2)
  apply simp
  done

defs canonicalAddressAssert_def:
  "canonicalAddressAssert \<equiv> AARCH64.canonical_address"

context begin interpretation Arch . (*FIXME: arch-split*)

lemma inv_untyped_corres':
  "\<lbrakk> untypinv_relation ui ui' \<rbrakk> \<Longrightarrow>
   corres (dc \<oplus> (=))
     (einvs and valid_untyped_inv ui and ct_active and schact_is_rct)
     (invs' and valid_untyped_inv' ui' and ct_active')
     (invoke_untyped ui) (invokeUntyped ui')"
  apply (cases ui)
  apply (rule corres_name_pre)
  apply (clarsimp simp only: valid_untyped_inv_wcap
           valid_untyped_inv_wcap'
           Invocations_A.untyped_invocation.simps
           Invocations_H.untyped_invocation.simps
           untypinv_relation.simps)
  apply (rename_tac cref oref reset ptr ptr' dc us slots dev s s' ao' sz sz' idx idx')
  proof -
    fix cref reset ptr ptr_base us slots dev ao' sz sz' idx idx' s s'

  let ?ui = "Invocations_A.Retype cref reset ptr_base ptr (APIType_map2 (Inr ao')) us slots dev"
  let ?ui' = "Invocations_H.untyped_invocation.Retype
                (cte_map cref) reset ptr_base ptr ao' us (map cte_map slots) dev"

    assume invs: "invs (s :: det_state)" "ct_active s" "valid_list s" "valid_sched s"
                 "schact_is_rct s"
    and   invs': "invs' s'" "ct_active' s'"
    and      sr: "(s, s') \<in> state_relation"
    and     vui: "valid_untyped_inv_wcap ?ui (Some (cap.UntypedCap dev (ptr && ~~ mask sz) sz idx)) s"
                 (is "valid_untyped_inv_wcap _ (Some ?cap) s")
    and    vui': "valid_untyped_inv_wcap' ?ui' (Some (UntypedCap dev (ptr && ~~ mask sz') sz' idx')) s'"
    assume ui: "ui = ?ui" and ui': "ui' = ?ui'"

    have cte_at: "cte_wp_at ((=) ?cap) cref s" (is "?cte_cond s")
       using vui by (simp add:cte_wp_at_caps_of_state)

    have ptr_sz_simp[simp]: "ptr_base = ptr && ~~ mask sz
        \<and> sz' = sz \<and> idx' = idx \<and> 2 \<le> sz"
       using cte_at vui vui' sr invs
       apply (clarsimp simp: cte_wp_at_ctes_of)
       apply (drule pspace_relation_cte_wp_atI'[OF state_relation_pspace_relation])
         apply (simp add:cte_wp_at_ctes_of)
        apply (simp add:invs_valid_objs)
       apply (clarsimp simp:is_cap_simps isCap_simps)
       apply (frule cte_map_inj_eq)
        apply ((erule cte_wp_at_weakenE | simp
          | clarsimp simp: cte_wp_at_caps_of_state)+)[5]
       apply (clarsimp simp:cte_wp_at_caps_of_state cte_wp_at_ctes_of)
       apply (drule caps_of_state_valid_cap,fastforce)
       apply (clarsimp simp:valid_cap_def untyped_min_bits_def)
       done

    have obj_bits_low_bound[simp]:
      "minUntypedSizeBits \<le> obj_bits_api (APIType_map2 (Inr ao')) us"
      using vui
      apply clarsimp
      apply (cases ao')
      apply (simp_all add: obj_bits_api_def slot_bits_def arch_kobj_size_def default_arch_object_def
                           APIType_map2_def bit_simps untyped_min_bits_def minUntypedSizeBits_def
                    split: apiobject_type.splits)
      done

    have cover: "range_cover ptr sz
        (obj_bits_api (APIType_map2 (Inr ao')) us) (length slots)"
     and vslot: "slots\<noteq> []"
      using vui
      by (auto simp: cte_wp_at_caps_of_state)

    have misc'[simp]:
      "distinct (map cte_map slots)"
      using vui'
      by (auto simp: cte_wp_at_ctes_of)

    have intvl_eq[simp]:
    "ptr && ~~ mask sz = ptr \<Longrightarrow> {ptr + of_nat k |k. k < 2 ^ sz} = {ptr..ptr + 2 ^ sz - 1}"
      using cover
      apply (subgoal_tac "is_aligned (ptr &&~~ mask sz) sz")
       apply (rule intvl_range_conv)
        apply (simp)
       apply (drule range_cover.sz)
       apply simp
      apply (rule is_aligned_neg_mask,simp)
      done

    have delete_objects_rewrite:
      "ptr && ~~ mask sz = ptr \<Longrightarrow> delete_objects ptr sz =
      do y \<leftarrow> modify (clear_um {ptr + of_nat k |k. k < 2 ^ sz});
              modify (detype {ptr && ~~ mask sz..ptr + 2 ^ sz - 1})
      od"
      using cover
      apply (clarsimp simp:delete_objects_def freeMemory_def word_size_def)
      apply (subgoal_tac "is_aligned (ptr &&~~ mask sz) sz")
       apply (subst mapM_storeWord_clear_um[simplified word_size_def word_size_bits_def];
              clarsimp simp: range_cover_def word_bits_def)
       apply (drule_tac z=sz in order_trans[OF obj_bits_low_bound];
              simp add: minUntypedSizeBits_def)
      apply (rule is_aligned_neg_mask)
      apply simp
      done

    have of_nat_length: "(of_nat (length slots)::machine_word) - (1::machine_word) < (of_nat (length slots)::machine_word)"
       using vslot
       using range_cover.range_cover_le_n_less(1)[OF cover,where p = "length slots"]
       apply -
       apply (case_tac slots)
       apply clarsimp+
       apply (subst add.commute)
       apply (subst word_le_make_less[symmetric])
       apply (rule less_imp_neq)
       apply (simp add:word_bits_def minus_one_norm)
       apply (rule word_of_nat_less)
       apply auto
       done

    have not_0_ptr[simp]: "ptr\<noteq> 0"
       using cte_at invs
      apply (clarsimp simp:cte_wp_at_caps_of_state)
      apply (drule(1) caps_of_state_valid)+
      apply (simp add:valid_cap_def)
      done

    have size_eq[simp]: "APIType_capBits ao' us = obj_bits_api (APIType_map2 (Inr ao')) us"
      apply (case_tac ao')
        apply (rename_tac apiobject_type)
        apply (case_tac apiobject_type)
        apply (clarsimp simp: APIType_capBits_def objBits_simps' arch_kobj_size_def default_arch_object_def
                              obj_bits_api_def APIType_map2_def slot_bits_def pageBitsForSize_def bit_simps)+
      done

    have non_reset_idx_le[simp]: "\<not> reset \<Longrightarrow> idx < 2^sz"
       using vui
       apply (clarsimp simp: cte_wp_at_caps_of_state )
       apply (erule le_less_trans)
       apply (rule unat_less_helper)
       apply simp
       apply (rule and_mask_less')
       using cover
       apply (clarsimp simp:range_cover_def)
       done

    note blah[simp del] = untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex usableUntypedRange.simps

    have vc'[simp] : "s' \<turnstile>' capability.UntypedCap dev (ptr && ~~ mask sz) sz idx"
      using vui' invs'
      apply (clarsimp simp:cte_wp_at_ctes_of)
      apply (case_tac cte)
      apply clarsimp
      apply (erule ctes_of_valid_cap')
      apply (simp add:invs_valid_objs')
      done

    have nidx[simp]: "ptr + (of_nat (length slots) * 2^obj_bits_api (APIType_map2 (Inr ao')) us) - (ptr && ~~ mask sz)
      = (ptr && mask sz) + (of_nat (length slots) * 2^obj_bits_api (APIType_map2 (Inr ao')) us)"
       apply (subst word_plus_and_or_coroll2[symmetric,where w = "mask sz" and t = ptr])
       apply simp
       done

    have idx_compare'[simp]:"unat ((ptr && mask sz) + (of_nat (length slots)<< obj_bits_api (APIType_map2 (Inr ao')) us)) \<le> 2 ^ sz"
      apply (rule le_trans[OF unat_plus_gt])
      apply (simp add:range_cover.unat_of_nat_n_shift[OF cover] range_cover_unat)
      apply (insert range_cover.range_cover_compare_bound[OF cover])
      apply simp
      done

    have idx_compare''[simp]:
       "unat ((ptr && mask sz) + (of_nat (length slots) * (2::machine_word) ^ obj_bits_api (APIType_map2 (Inr ao')) us)) < 2 ^ sz
        \<Longrightarrow> ptr + of_nat (length slots) * 2 ^ obj_bits_api (APIType_map2 (Inr ao')) us - 1
        < ptr + of_nat (length slots) * 2 ^ obj_bits_api (APIType_map2 (Inr ao')) us"
      apply (rule word_leq_le_minus_one,simp)
      apply (rule neq_0_no_wrap)
      apply (rule machine_word_plus_mono_right_split)
      apply (simp add:shiftl_t2n range_cover_unat[OF cover] field_simps)
      apply (simp add:range_cover.sz[where 'a=machine_word_len, folded word_bits_def, OF cover])+
      done

    note neg_mask_add_mask = word_plus_and_or_coroll2[symmetric,where w = "mask sz" and t = ptr,symmetric]

    have idx_compare'''[simp]:
      "\<lbrakk>unat (of_nat (length slots) * (2::machine_word) ^ obj_bits_api (APIType_map2 (Inr ao')) us) < 2 ^ sz;
       ptr && ~~ mask sz = ptr\<rbrakk>
      \<Longrightarrow> ptr + of_nat (length slots) * 2 ^ obj_bits_api (APIType_map2 (Inr ao')) us - 1
      < ptr + of_nat (length slots) * 2 ^ obj_bits_api (APIType_map2 (Inr ao')) us "
      apply (rule word_leq_le_minus_one,simp)
      apply (simp add:is_aligned_neg_mask_eq'[symmetric])
      apply (rule neq_0_no_wrap)
      apply (rule machine_word_plus_mono_right_split[where sz = sz])
       apply (simp add:is_aligned_mask)+
      apply (simp add:range_cover.sz[where 'a=machine_word_len, folded word_bits_def, OF cover])+
      done

    have maxDomain:"ksCurDomain s' \<le> maxDomain"
      using invs'
      by (simp add:invs'_def valid_state'_def)

    have sz_mask_less:
      "unat (ptr && mask sz) < 2 ^ sz"
      using range_cover.sz[OF cover]
      by (simp add: unat_less_helper and_mask_less_size word_size)

    have ptr_cn[simp]: "canonical_address (ptr && ~~ mask sz)"
      using vc' unfolding valid_cap'_def by simp

    have overlap_ranges1:
      "{x. ptr \<le> x \<and> x \<le> ptr + 2 ^ obj_bits_api (APIType_map2 (Inr ao')) us
            * of_nat (length slots) - 1} \<subseteq> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1}"
      apply (rule order_trans[rotated])
       apply (rule range_cover_subset'[OF cover], simp add: vslot)
      apply (clarsimp simp: atLeastAtMost_iff field_simps)
      done

    have overlap_ranges2:
      "idx \<le> unat (ptr && mask sz)
        \<Longrightarrow> {x. ptr \<le> x \<and> x \<le> ptr + 2 ^ obj_bits_api (APIType_map2 (Inr ao')) us
            * of_nat (length slots) - 1} \<subseteq> {(ptr && ~~ mask sz) + of_nat idx..(ptr && ~~ mask sz) + 2 ^ sz - 1}"
      apply (rule order_trans[OF overlap_ranges1])
      apply (clarsimp simp add: atLeastatMost_subset_iff)
      apply (rule order_trans, rule word_plus_mono_right)
        apply (erule word_of_nat_le)
       apply (simp add: add.commute word_plus_and_or_coroll2 word_and_le2)
      apply (simp add: add.commute word_plus_and_or_coroll2)
      done

   have overlap_ranges:
     "{x. ptr \<le> x \<and> x \<le> ptr + 2 ^ obj_bits_api (APIType_map2 (Inr ao')) us * of_nat (length slots) - 1}
         \<subseteq> usable_untyped_range (cap.UntypedCap dev (ptr && ~~ mask sz) sz (if reset then 0 else idx))"
     apply (cases reset, simp_all add: usable_untyped_range.simps)
      apply (rule order_trans, rule overlap_ranges1)
      apply (simp add: blah word_and_le2)
     apply (rule overlap_ranges2)
     apply (cut_tac vui)
     apply (clarsimp simp: cte_wp_at_caps_of_state)
     done

    have sz_limit[simp]: "sz \<le> maxUntypedSizeBits"
      using vc' unfolding valid_cap'_def by clarsimp

    from ptr_cn sz_limit
    have canonical_ptr[simp]: "canonical_address ptr"
      unfolding canonical_address_range maxUntypedSizeBits_def canonical_bit_def
      by word_bitwise (simp add: word_size)

    note set_cap_free_index_invs_spec = set_free_index_invs[where cap = "cap.UntypedCap
        dev (ptr && ~~ mask sz) sz (if reset then 0 else idx)"
      ,unfolded free_index_update_def free_index_of_def,simplified]

    note msimp[simp add] = neg_mask_add_mask
    note if_split[split del]
    show " corres (dc \<oplus> (=)) ((=) s) ((=) s')
           (invoke_untyped ?ui)
           (invokeUntyped ?ui')"
      apply (clarsimp simp:invokeUntyped_def invoke_untyped_def getSlotCap_def bind_assoc)
      apply (insert cover)
      apply (rule corres_guard_imp)
        apply (rule corres_split_norE)
           apply (rule corres_whenE, simp)
            apply (rule resetUntypedCap_corres[where ui=ui and ui'=ui'])
            apply (simp add: ui ui')
           apply simp
          apply simp
          apply (rule corres_symb_exec_l_Ex)
          apply (rule_tac F = "cap = cap.UntypedCap dev (ptr && ~~ mask sz)
                sz (if reset then 0 else idx)" in corres_gen_asm)
          apply (rule corres_add_noop_lhs)
          apply (rule corres_split_nor[OF cNodeNoOverlap _ return_wp stateAssert_wp])
          apply (rule corres_add_noop_lhs)
          apply (rule corres_split_nor[OF archNoOverlap _ return_wp stateAssert_wp])
          apply (clarsimp simp: canonicalAddressAssert_def)
          apply (rule corres_split[OF updateFreeIndex_corres])
              apply (simp add:isCap_simps)+
             apply (clarsimp simp:getFreeIndex_def bits_of_def shiftL_nat shiftl_t2n
                                  free_index_of_def)
            apply (insert range_cover.range_cover_n_less[OF cover] vslot)
            apply (rule createNewObjects_corres_helper)
                    apply simp+
             apply (simp add: insertNewCaps_def)
             apply (rule corres_split_retype_createNewCaps[where sz = sz,OF corres_rel_imp])
                apply (rule inv_untyped_corres_helper1)
                apply simp
               apply simp
              apply ((wp retype_region_invs_extras[where sz = sz]
                   retype_region_plain_invs [where sz = sz]
                   retype_region_descendants_range_ret[where sz = sz]
                   retype_region_caps_overlap_reserved_ret[where sz = sz]
                   retype_region_cte_at_other[where sz = sz]
                   retype_region_distinct_sets[where sz = sz]
                   retype_region_ranges[where p=cref and sz = sz]
                   retype_ret_valid_caps [where sz = sz]
                   retype_region_arch_objs [where sza = "\<lambda>_. sz"]
                   hoare_vcg_const_Ball_lift
                   set_tuple_pick distinct_tuple_helper
                   retype_region_obj_at_other3[where sz = sz]
                 | assumption)+)[1]
             apply (wp set_tuple_pick createNewCaps_cte_wp_at'[where sz= sz]
                 hoare_vcg_ex_lift distinct_tuple_helper
                 createNewCaps_parent_helper [where p="cte_map cref" and sz = sz]
                 createNewCaps_valid_pspace_extras [where ptr=ptr and sz = sz]
                 createNewCaps_ranges'[where sz = sz]
                 hoare_vcg_const_Ball_lift createNewCaps_valid_cap'[where sz = sz]
                 createNewCaps_descendants_range_ret'[where sz = sz]
                 createNewCaps_caps_overlap_reserved_ret'[where sz = sz])
            apply clarsimp
            apply (erule cte_wp_at_weakenE')
            apply (case_tac c, simp)
            apply hypsubst
            apply (case_tac c,clarsimp simp:isCap_simps)
           apply (clarsimp simp: getFreeIndex_def is_cap_simps bits_of_def shiftL_nat)
           apply (clarsimp simp:conj_comms)
           apply (strengthen invs_mdb invs_valid_objs
              invs_valid_pspace invs_arch_state invs_psp_aligned
              caps_region_kernel_window_imp[where p=cref]
              invs_cap_refs_in_kernel_window)+
           apply (clarsimp simp:conj_comms bits_of_def)
           apply (wp set_cap_free_index_invs_spec set_cap_caps_no_overlap set_cap_no_overlap)
           apply (rule hoare_vcg_conj_lift)
            apply (rule hoare_strengthen_post[OF set_cap_sets])
            apply (clarsimp simp:cte_wp_at_caps_of_state)
           apply (wp set_cap_no_overlap hoare_vcg_ball_lift
                     set_cap_free_index_invs_spec
                     set_cap_descendants_range_in
                     set_untyped_cap_caps_overlap_reserved[where
                        idx="if reset then 0 else idx"]
                     set_cap_cte_wp_at
                     | strengthen exI[where x=cref])+
          apply (clarsimp simp:conj_comms ball_conj_distrib simp del:capFreeIndex_update.simps)
          apply (strengthen invs_pspace_aligned' invs_pspace_distinct'
               invs_valid_pspace' invs_arch_state'
               imp_consequent[where Q = "(\<exists>x. x \<in> cte_map ` set slots)"]
             | clarsimp simp: conj_comms simp del: capFreeIndex_update.simps)+
          apply ((wp updateFreeIndex_forward_invs' updateFreeIndex_caps_overlap_reserved
             updateFreeIndex_caps_no_overlap'' updateFreeIndex_pspace_no_overlap'
             hoare_vcg_const_Ball_lift updateFreeIndex_cte_wp_at
             updateFreeIndex_descendants_range_in')+)[1]
         apply clarsimp
         apply (clarsimp simp:conj_comms)
         apply (strengthen invs_mdb invs_valid_objs
                invs_valid_pspace invs_arch_state invs_psp_aligned
                invs_distinct)
         apply (clarsimp simp:conj_comms ball_conj_distrib ex_in_conv)
         apply ((rule validE_R_validE)?,
          rule_tac Q'="\<lambda>_ s. valid_list s \<and> invs s \<and> ct_active s
          \<and> valid_untyped_inv_wcap ui
            (Some (cap.UntypedCap dev (ptr && ~~ mask sz) sz (if reset then 0 else idx))) s
          \<and> (reset \<longrightarrow> pspace_no_overlap {ptr && ~~ mask sz..(ptr && ~~ mask sz) + 2 ^ sz - 1} s)
          " in hoare_strengthen_postE_R)
          apply (simp add: whenE_def, wp)
           apply (rule validE_validE_R, rule hoare_strengthen_postE, rule reset_untyped_cap_invs_etc, auto)[1]
          apply wp
         apply (clarsimp simp: ui cte_wp_at_caps_of_state
                               bits_of_def untyped_range.simps)
         apply (frule(1) valid_global_refsD2[OF _ invs_valid_global_refs])
         apply (cut_tac cref="cref" and reset=reset
           in invoke_untyped_proofs.intro,
           simp_all add: cte_wp_at_caps_of_state)[1]
          apply (rule conjI, (assumption | rule refl))+
          apply (simp split: if_split)

         apply (simp add: invoke_untyped_proofs.simps)
         apply (strengthen if_split[where P="\<lambda>v. v \<le> unat x" for x, THEN iffD2]
                           exI[where x=cref])
         apply (simp add: arg_cong[OF mask_out_sub_mask, where f="\<lambda>y. x - y" for x]
                          field_simps invoke_untyped_proofs.idx_le_new_offs
                          if_split[where P="\<lambda>v. v \<le> unat x" for x])
         apply (frule range_cover.sz(1), fold word_bits_def)
         apply (frule cte_wp_at_pspace_no_overlapI,
           simp add: cte_wp_at_caps_of_state, simp split: if_split,
           simp add: invoke_untyped_proofs.szw)
         apply (simp add: field_simps conj_comms ex_in_conv
                          cte_wp_at_caps_of_state
                          in_get_cap_cte_wp_at
                          atLeastatMost_subset_iff[where b=x and d=x for x]
                          word_and_le2)
         apply (intro conjI impI)

            (* offs *)
            apply (drule(1) invoke_untyped_proofs.idx_le_new_offs)
            apply simp

           (* usable untyped range *)
           apply (simp add: shiftL_nat shiftl_t2n overlap_ranges)

          apply (rule order_trans, erule invoke_untyped_proofs.subset_stuff)
          apply (simp add: blah word_and_le2)

         apply (drule invoke_untyped_proofs.usable_range_disjoint)
         apply (clarsimp simp: field_simps mask_out_sub_mask shiftl_t2n)

        apply ((rule validE_validE_R)?, rule hoare_strengthen_postE,
               rule whenE_reset_resetUntypedCap_invs_etc[where ptr="ptr && ~~ mask sz"
                   and ptr'=ptr and sz=sz and idx=idx and ui=ui' and dev=dev])

         prefer 2
         apply simp
        apply clarsimp
        apply (simp only: ui')
        apply (frule(2) invokeUntyped_proofs.intro)
        apply (clarsimp simp: cte_wp_at_ctes_of
                              invokeUntyped_proofs.caps_no_overlap'
                              invokeUntyped_proofs.ps_no_overlap'
                              invokeUntyped_proofs.descendants_range
                              if_split[where P="\<lambda>v. v \<le> getFreeIndex x y" for x y]
                              empty_descendants_range_in'
                              invs_pspace_aligned' invs_pspace_distinct'
                              invs_ksCurDomain_maxDomain'
                        cong: if_cong)
        apply (strengthen refl)
        apply (frule invokeUntyped_proofs.idx_le_new_offs)
        apply (frule invokeUntyped_proofs.szw)
        apply (frule invokeUntyped_proofs.descendants_range(2), simp)
        apply (clarsimp simp: getFreeIndex_def conj_comms shiftL_nat
                              is_aligned_weaken[OF range_cover.funky_aligned]
                              invs_valid_pspace' isCap_simps
                              arg_cong[OF mask_out_sub_mask, where f="\<lambda>y. x - y" for x]
                              field_simps)

        apply (intro conjI)
            (* pspace_no_overlap' *)
            apply (cases reset, simp_all)[1]
           apply (rule order_trans[rotated],
                  erule invokeUntyped_proofs.idx_compare')
          apply (simp add: shiftl_t2n mult.commute)
         apply (drule invokeUntyped_proofs.subset_stuff, simp,
             erule order_trans, simp add: blah word_and_le2 add_mask_fold)
        apply (auto simp: add_mask_fold split: if_split)[1]
       apply (drule invokeUntyped_proofs.usableRange_disjoint, simp)
      apply (clarsimp simp only: pred_conj_def invs ui)
      apply (strengthen vui)
      apply (cut_tac vui invs invs')
      apply (clarsimp simp: cte_wp_at_caps_of_state schact_is_rct_def)
     apply (cut_tac vui' invs')
     apply (clarsimp simp: ui cte_wp_at_ctes_of if_apply_def2 ui')
     done
qed

lemmas inv_untyped_corres = inv_untyped_corres'

crunch insertNewCap, doMachineOp
  for pred_tcb_at'[wp]: "pred_tcb_at' proj P t"
  (wp: crunch_wps)

lemma sts_valid_untyped_inv':
  "\<lbrace>valid_untyped_inv' ui\<rbrace> setThreadState st t \<lbrace>\<lambda>rv. valid_untyped_inv' ui\<rbrace>"
  apply (cases ui, simp add: ex_cte_cap_to'_def)
  apply (rule hoare_pre)
   apply (rule hoare_use_eq_irq_node' [OF setThreadState_ksInterruptState])
   apply (wp hoare_vcg_const_Ball_lift hoare_vcg_ex_lift | simp)+
  done

crunch invokeUntyped
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  (simp: crunch_simps zipWithM_x_mapM
     wp: crunch_wps unless_wp mapME_x_inv_wp preemptionPoint_inv)

crunch insertNewCap
  for no_0_obj'[wp]: no_0_obj'
  (wp: crunch_wps)

lemma insertNewCap_valid_pspace':
  "\<lbrace>\<lambda>s. valid_pspace' s \<and> s \<turnstile>' cap
          \<and> slot \<noteq> parent \<and> caps_overlap_reserved' (untypedRange cap) s
          \<and> cte_wp_at' (\<lambda>cte. isUntypedCap (cteCap cte) \<and>
                              sameRegionAs (cteCap cte) cap) parent s
          \<and> \<not> isZombie cap \<and> descendants_range' cap parent (ctes_of s)\<rbrace>
     insertNewCap parent slot cap
   \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  apply (simp add: valid_pspace'_def)
  apply (wp insertNewCap_valid_mdb)
     apply simp_all
  done

crunch insertNewCap
  for tcb'[wp]: "tcb_at' t"
  and inQ[wp]: "obj_at' (inQ d p) t"
  and norqL1[wp]: "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  and norqL2[wp]: "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
  and state_refs_of'[wp]: "\<lambda>s. P (state_refs_of' s)"
  and state_hyp_refs_of'[wp]: "\<lambda>s. P (state_hyp_refs_of' s)"
  and idle'[wp]: "valid_idle'"
  and global_refs': "\<lambda>s. P (global_refs' s)"
  and gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"
  and irq_states' [wp]: valid_irq_states'
  and irqs_masked' [wp]: irqs_masked'
  and valid_machine_state'[wp]: valid_machine_state'
  and pspace_domain_valid[wp]: pspace_domain_valid
  and ct_not_inQ[wp]: "ct_not_inQ"
  and tcbState_inv[wp]: "obj_at' (\<lambda>tcb. P (tcbState tcb)) t"
  and tcbDomain_inv[wp]: "obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t"
  and tcbPriority_inv[wp]: "obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t"
  and sched_queues_projs[wp]: "\<lambda>s. P (tcbSchedNexts_of s) (tcbSchedPrevs_of s)"
  and tcbQueueds_of[wp]: "\<lambda>s. P (tcbQueued |< tcbs_of' s)"
  and valid_sched_pointers[wp]: valid_sched_pointers
  (wp: crunch_wps)

crunch updateNewFreeIndex
  for if_unsafe_then_cap'[wp]: "if_unsafe_then_cap'"

lemma insertNewCap_ifunsafe'[wp]:
  "\<lbrace>if_unsafe_then_cap' and ex_cte_cap_to' slot\<rbrace>
     insertNewCap parent slot cap
   \<lbrace>\<lambda>rv s. if_unsafe_then_cap' s\<rbrace>"
  apply (simp add: insertNewCap_def)
  apply (rule hoare_pre)
    apply (wp getCTE_wp' | clarsimp simp: ifunsafe'_def3)+
  apply (clarsimp simp: ex_cte_cap_to'_def cte_wp_at_ctes_of cteCaps_of_def)
  apply (drule_tac x=cref in spec)
  apply (rule conjI)
   apply clarsimp
   apply (rule_tac x=crefa in exI, fastforce)
  apply clarsimp
  apply (rule_tac x=cref' in exI, fastforce)
  done

crunch updateNewFreeIndex
  for if_live_then_nonz_cap'[wp]: "if_live_then_nonz_cap'"

lemma insertNewCap_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> insertNewCap parent slot cap \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: insertNewCap_def)
  apply (wp setCTE_iflive' getCTE_wp')
  apply (clarsimp elim!: cte_wp_at_weakenE')
  done

lemma insertNewCap_cte_wp_at'':
  "\<lbrace>cte_wp_at' (\<lambda>cte. P (cteCap cte)) p and K (\<not> P NullCap)\<rbrace>
     insertNewCap parent slot cap
   \<lbrace>\<lambda>rv s. cte_wp_at' (P \<circ> cteCap) p s\<rbrace>"
  apply (simp add: insertNewCap_def tree_cte_cteCap_eq)
  apply (wp getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of cteCaps_of_def)
  done

lemmas insertNewCap_cte_wp_at' = insertNewCap_cte_wp_at''[unfolded o_def]

lemma insertNewCap_cap_to'[wp]:
  "\<lbrace>ex_cte_cap_to' p\<rbrace> insertNewCap parent slot cap \<lbrace>\<lambda>rv. ex_cte_cap_to' p\<rbrace>"
  apply (simp add: ex_cte_cap_to'_def)
  apply (rule hoare_pre)
   apply (rule hoare_use_eq_irq_node'[OF insertNewCap_ksInterrupt])
   apply (wp hoare_vcg_ex_lift insertNewCap_cte_wp_at')
  apply clarsimp
  done

lemma insertNewCap_nullcap:
  "\<lbrace>P and cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) slot\<rbrace> insertNewCap parent slot cap \<lbrace>Q\<rbrace>
    \<Longrightarrow> \<lbrace>P\<rbrace> insertNewCap parent slot cap \<lbrace>Q\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (subgoal_tac "cte_wp_at' (\<lambda>cte. cteCap cte = NullCap) slot s")
   apply fastforce
  apply (clarsimp simp: insertNewCap_def in_monad cte_wp_at_ctes_of liftM_def
                 dest!: use_valid [OF _ getCTE_sp[where P="(=) s" for s], OF _ refl])
  done

lemma insertNewCap_valid_global_refs':
  "\<lbrace>valid_global_refs' and
        cte_wp_at' (\<lambda>cte. capRange cap \<subseteq> capRange (cteCap cte)
            \<and> capBits cap \<le> capBits (cteCap cte)) parent\<rbrace>
     insertNewCap parent slot cap
   \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  apply (simp add: valid_global_refs'_def valid_refs'_cteCaps valid_cap_sizes_cteCaps)
  apply (rule hoare_pre)
   apply (rule hoare_use_eq [where f=global_refs', OF insertNewCap_global_refs'])
   apply (rule hoare_use_eq [where f=gsMaxObjectSize])
    apply wp+
  apply (clarsimp simp: cte_wp_at_ctes_of cteCaps_of_def ball_ran_eq)
  apply (frule power_increasing[where a=2], simp)
  apply (blast intro: order_trans)
  done

lemma insertNewCap_valid_irq_handlers:
  "\<lbrace>valid_irq_handlers' and (\<lambda>s. \<forall>irq. cap = IRQHandlerCap irq \<longrightarrow> irq_issued' irq s)\<rbrace>
     insertNewCap parent slot cap
   \<lbrace>\<lambda>rv. valid_irq_handlers'\<rbrace>"
  apply (simp add: insertNewCap_def valid_irq_handlers'_def irq_issued'_def)
  apply (wp | wp (once) hoare_use_eq[where f=ksInterruptState, OF updateNewFreeIndex_ksInterrupt])+
     apply (simp add: cteCaps_of_def)
     apply (wp | wp (once) hoare_use_eq[where f=ksInterruptState, OF setCTE_ksInterruptState]
               getCTE_wp)+
  apply (clarsimp simp: cteCaps_of_def cte_wp_at_ctes_of ran_def)
  apply auto
  done

lemma insertNewCap_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace>ct_idle_or_in_cur_domain' and ct_active'\<rbrace> insertNewCap parent slot cap \<lbrace>\<lambda>_. ct_idle_or_in_cur_domain'\<rbrace>"
apply (wp ct_idle_or_in_cur_domain'_lift_futz[where Q=\<top>])
apply (rule_tac Q'="\<lambda>_. obj_at' (\<lambda>tcb. tcbState tcb \<noteq> Structures_H.thread_state.Inactive) t and obj_at' (\<lambda>tcb. d = tcbDomain tcb) t"
             in hoare_strengthen_post)
apply (wp | clarsimp elim: obj_at'_weakenE)+
apply (auto simp: obj_at'_def)
done

crunch insertNewCap
  for ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  (wp: crunch_simps hoare_drop_imps)

lemma capRange_subset_capBits:
  "capAligned cap \<Longrightarrow> capAligned cap'
    \<Longrightarrow> capRange cap \<subseteq> capRange cap'
    \<Longrightarrow> capRange cap \<noteq> {}
    \<Longrightarrow> capBits cap \<le> capBits cap'"
  supply
    is_aligned_neg_mask_eq[simp del]
    is_aligned_neg_mask_weaken[simp del]
  apply (simp add: capRange_def capAligned_def is_aligned_no_overflow
            split: if_split_asm del: atLeastatMost_subset_iff)
  apply (frule_tac c="capUntypedPtr cap" in subsetD)
   apply (simp only: mask_in_range[symmetric])
   apply (simp add: is_aligned_neg_mask_eq)
  apply (drule_tac c="(capUntypedPtr cap && ~~ mask (capBits cap))
        || (~~ capUntypedPtr cap' && mask (capBits cap))" in subsetD)
   apply (simp_all only: mask_in_range[symmetric])
   apply (simp add: word_ao_dist is_aligned_neg_mask_eq)
  apply (simp add: word_ao_dist)
  apply (cases "capBits cap = 0")
   apply simp
  apply (drule_tac f="\<lambda>x. x !! (capBits cap - 1)"
        and x="a || b" for a b in arg_cong)
  apply (simp add: word_ops_nth_size word_bits_def word_size)
  apply auto
  done

lemma insertNewCap_urz[wp]:
  "\<lbrace>untyped_ranges_zero' and valid_objs' and valid_mdb'\<rbrace>
      insertNewCap parent slot cap \<lbrace>\<lambda>rv. untyped_ranges_zero'\<rbrace>"
  apply (simp add: insertNewCap_def updateNewFreeIndex_def)
  apply (wp getCTE_cteCap_wp
    | simp add: updateTrackedFreeIndex_def getSlotCap_def case_eq_if_isUntypedCap
               split: option.split split del: if_split
    | wps | wp (once) getCTE_wp')+
  apply (clarsimp simp: cte_wp_at_ctes_of fun_upd_def[symmetric])
  apply (strengthen untyped_ranges_zero_fun_upd[mk_strg I E])
  apply (intro conjI impI; clarsimp simp: isCap_simps)
    apply (auto simp add: cteCaps_of_def untypedZeroRange_def isCap_simps)
  done

crunch insertNewCap
  for valid_arch'[wp]: valid_arch_state'
  (wp: crunch_wps)

lemma insertNewCap_invs':
  "\<lbrace>invs' and ct_active'
          and valid_cap' cap
          and cte_wp_at' (\<lambda>cte. isUntypedCap (cteCap cte) \<and>
                              sameRegionAs (cteCap cte) cap) parent
          and K (\<not> isZombie cap) and (\<lambda>s. descendants_range' cap parent (ctes_of s))
          and caps_overlap_reserved' (untypedRange cap)
          and ex_cte_cap_to' slot
          and (\<lambda>s. ksIdleThread s \<notin> capRange cap)
          and (\<lambda>s. \<forall>irq. cap = IRQHandlerCap irq \<longrightarrow> irq_issued' irq s)\<rbrace>
     insertNewCap parent slot cap
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (rule insertNewCap_nullcap)
  apply (simp add: invs'_def valid_state'_def)
  apply (rule hoare_pre)
   apply (wp insertNewCap_valid_pspace' sch_act_wf_lift
             cur_tcb_lift tcb_in_cur_domain'_lift valid_bitmaps_lift
             insertNewCap_valid_global_refs' sym_heap_sched_pointers_lift
             valid_irq_node_lift insertNewCap_valid_irq_handlers)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (frule ctes_of_valid[rotated, where p=parent, OF valid_pspace_valid_objs'])
   apply (fastforce simp: cte_wp_at_ctes_of)
  apply (auto simp: isCap_simps sameRegionAs_def3
            intro!: capRange_subset_capBits
              elim: valid_capAligned)
  done

lemma insertNewCap_irq_issued'[wp]:
  "\<lbrace>\<lambda>s. P (irq_issued' irq s)\<rbrace> insertNewCap parent slot cap \<lbrace>\<lambda>rv s. P (irq_issued' irq s)\<rbrace>"
  by (simp add: irq_issued'_def, wp)

lemma insertNewCap_ct_in_state'[wp]:
  "\<lbrace>ct_in_state' p\<rbrace>insertNewCap parent slot cap \<lbrace>\<lambda>rv. ct_in_state' p\<rbrace>"
  unfolding ct_in_state'_def
  apply (rule hoare_pre)
   apply wps
   apply wp
  apply simp
  done

lemma zipWithM_x_insertNewCap_invs'':
  "\<lbrace>\<lambda>s. invs' s \<and> ct_active' s \<and> (\<forall>tup \<in> set ls. s \<turnstile>' snd tup)
        \<and> cte_wp_at' (\<lambda>cte. isUntypedCap (cteCap cte) \<and>
                            (\<forall>tup \<in> set ls. sameRegionAs (cteCap cte) (snd tup))) parent s
        \<and> (\<forall>tup \<in> set ls. \<not> isZombie (snd tup))
        \<and> (\<forall>tup \<in> set ls. ex_cte_cap_to' (fst tup) s)
        \<and> (\<forall>tup \<in> set ls. descendants_range' (snd tup) parent (ctes_of s))
        \<and> (\<forall>tup \<in> set ls. ksIdleThread s \<notin> capRange (snd tup))
        \<and> (\<forall>tup \<in> set ls. caps_overlap_reserved' (capRange (snd tup)) s)
        \<and> distinct_sets (map capRange (map snd ls))
        \<and> (\<forall>irq. IRQHandlerCap irq \<in> set (map snd ls) \<longrightarrow> irq_issued' irq s)
        \<and> distinct (map fst ls)\<rbrace>
    mapM (\<lambda>(x, y). insertNewCap parent x y) ls
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (induct ls)
   apply (simp add: mapM_def sequence_def)
   apply (wp, simp)
  apply (simp add: mapM_Cons)
  including no_pre apply wp
  apply (thin_tac "valid P f Q" for P f Q)
  apply clarsimp
  apply (rule hoare_pre)
   apply (wp insertNewCap_invs'
             hoare_vcg_const_Ball_lift
             insertNewCap_cte_wp_at' insertNewCap_ranges
             hoare_vcg_all_lift insertNewCap_pred_tcb_at')+
  apply (clarsimp simp: cte_wp_at_ctes_of invs_mdb' invs_valid_objs' dest!:valid_capAligned)
  apply (drule caps_overlap_reserved'_subseteq[OF _ untypedRange_in_capRange])
  apply (auto simp:comp_def)
  done

lemma createNewCaps_not_isZombie[wp]:
  "\<lbrace>\<top>\<rbrace> createNewCaps ty ptr bits sz d \<lbrace>\<lambda>rv s. (\<forall>cap \<in> set rv. \<not> isZombie cap)\<rbrace>"
  apply (simp add: createNewCaps_def toAPIType_def
              cong: option.case_cong if_cong apiobject_type.case_cong)
  apply (wpsimp wp: undefined_valid simp: isCap_simps)
  done

lemma createNewCaps_cap_to':
  "\<lbrace>\<lambda>s. ex_cte_cap_to' p s \<and> 0 < n
      \<and> range_cover ptr sz (APIType_capBits ty us) n
      \<and> pspace_aligned' s \<and> pspace_distinct' s
      \<and> pspace_no_overlap' ptr sz s\<rbrace>
     createNewCaps ty ptr n us d
   \<lbrace>\<lambda>rv. ex_cte_cap_to' p\<rbrace>"
  apply (simp add: ex_cte_cap_to'_def)
  apply (wp hoare_vcg_ex_lift
            hoare_use_eq_irq_node' [OF createNewCaps_ksInterrupt
                                       createNewCaps_cte_wp_at'])
  apply fastforce
  done

lemma createNewCaps_idlethread_ranges[wp]:
  "\<lbrace>\<lambda>s. 0 < n \<and> range_cover ptr sz (APIType_capBits tp us) n
           \<and> ksIdleThread s \<notin> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1}\<rbrace>
     createNewCaps tp ptr n us d
   \<lbrace>\<lambda>rv s. \<forall>cap\<in>set rv. ksIdleThread s \<notin> capRange cap\<rbrace>"
  apply (rule hoare_as_subst [OF createNewCaps_it])
  apply (rule hoare_assume_pre)
  apply (rule hoare_chain, rule createNewCaps_range_helper2)
   apply fastforce
  apply blast
  done

lemma createNewCaps_IRQHandler[wp]:
  "\<lbrace>\<top>\<rbrace>
     createNewCaps tp ptr sz us d
   \<lbrace>\<lambda>rv s. IRQHandlerCap irq \<in> set rv \<longrightarrow> P rv s\<rbrace>"
  apply (simp add: createNewCaps_def split del: if_split)
  apply (rule hoare_pre)
   apply (wp | wpc | simp add: image_def | rule hoare_pre_cont)+
  done

lemma createNewCaps_ct_active':
  "\<lbrace>ct_active' and pspace_aligned' and pspace_distinct' and pspace_no_overlap' ptr sz and K (range_cover ptr sz (APIType_capBits ty us) n \<and> 0 < n)\<rbrace>
    createNewCaps ty ptr n us d
   \<lbrace>\<lambda>_. ct_active'\<rbrace>"
   apply (simp add: ct_in_state'_def)
   apply (rule hoare_pre)
   apply wps
   apply (wp createNewCaps_pred_tcb_at'[where sz=sz])
   apply simp
   done

crunch deleteObjects
  for gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"
  (simp: unless_def wp: crunch_wps)

crunch updateFreeIndex
  for gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"

crunch updateFreeIndex
  for ksIdleThread[wp]: "\<lambda>s. P (ksIdleThread s)"

lemma invokeUntyped_invs'':
 assumes insertNew_Q[wp]: "\<And>p cref cap.
    \<lbrace>Q\<rbrace> insertNewCap p cref cap \<lbrace>\<lambda>_. Q\<rbrace>"
 assumes createNew_Q: "\<And>tp ptr n us sz dev. \<lbrace>\<lambda>s. Q s
     \<and> range_cover ptr sz (APIType_capBits tp us) n
     \<and> (tp = APIObjectType ArchTypes_H.apiobject_type.CapTableObject \<longrightarrow> 0 < us)
     \<and> 0 < n \<and> valid_pspace' s \<and> pspace_no_overlap' ptr sz s\<rbrace>
    createNewCaps tp ptr n us dev \<lbrace>\<lambda>_. Q\<rbrace>"
 assumes set_free_Q[wp]: "\<And>slot idx. \<lbrace>invs' and Q\<rbrace> updateFreeIndex slot idx \<lbrace>\<lambda>_.Q\<rbrace>"
 assumes reset_Q: "\<lbrace>Q'\<rbrace> resetUntypedCap (case ui of Invocations_H.Retype src_slot _ _ _ _ _ _ _ \<Rightarrow> src_slot) \<lbrace>\<lambda>_. Q\<rbrace>"
 shows "\<lbrace>invs' and valid_untyped_inv' ui
          and (\<lambda>s. (case ui of Invocations_H.Retype _ reset _ _ _ _ _ _ \<Rightarrow> reset) \<longrightarrow> Q' s)
          and Q and ct_active'\<rbrace>
     invokeUntyped ui
   \<lbrace>\<lambda>rv. invs' and Q\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp only: pred_conj_def valid_untyped_inv_wcap')
  proof -
    fix s sz idx
    assume vui1: "valid_untyped_inv_wcap' ui
        (Some (case ui of
                Invocations_H.untyped_invocation.Retype slot reset ptr_base ptr ty us slots d \<Rightarrow>
                  capability.UntypedCap d (ptr && ~~ mask sz) sz idx)) s"
    assume misc: "invs' s" "Q s" "ct_active' s"
        "(case ui of
         Invocations_H.untyped_invocation.Retype x reset _ _ _ _ _ _ \<Rightarrow> reset) \<longrightarrow>
        Q' s"

    obtain cref reset ptr tp us slots dev
      where pf: "invokeUntyped_proofs s cref reset (ptr && ~~ mask sz) ptr tp us slots sz idx dev"
      and ui: "ui = Invocations_H.Retype cref reset (ptr && ~~ mask sz) ptr tp us slots dev"
      using vui1 misc
      apply (cases ui, simp only: Invocations_H.untyped_invocation.simps)
      apply (frule(2) invokeUntyped_proofs.intro)
      apply clarsimp
      apply (unfold cte_wp_at_ctes_of)
      apply (drule meta_mp; clarsimp)
      done

    note vui = vui1[simplified ui Invocations_H.untyped_invocation.simps]

    have cover: "range_cover ptr sz (APIType_capBits tp us) (length slots)"
      and slots: "cref \<notin> set slots" "distinct slots" "slots \<noteq> []"
      and tps: "tp = APIObjectType ArchTypes_H.apiobject_type.CapTableObject \<longrightarrow> 0 < us"
            "tp = APIObjectType ArchTypes_H.apiobject_type.Untyped \<longrightarrow> minUntypedSizeBits \<le> us \<and> us \<le> maxUntypedSizeBits"
      using vui
      by (clarsimp simp: ui cte_wp_at_ctes_of)+

    note not_0_ptr[simp] = invokeUntyped_proofs.not_0_ptr [OF pf]
    note subset_stuff[simp] = invokeUntyped_proofs.subset_stuff[OF pf]

    have non_detype_idx_le[simp]: "~ reset \<Longrightarrow> idx < 2^sz"
       using vui ui
       apply (clarsimp simp: cte_wp_at_ctes_of)
       apply (erule le_less_trans)
       apply (rule unat_less_helper)
       apply simp
       apply (rule le_less_trans)
       apply (rule word_and_le1)
       apply (simp add:mask_def)
       apply (rule word_leq_le_minus_one)
        apply simp
       apply (clarsimp simp:range_cover_def)
       done

    note blah[simp del] = untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff
                          atLeastatMost_subset_iff atLeastLessThan_iff Int_atLeastAtMost
                          atLeastatMost_empty_iff split_paired_Ex usableUntypedRange.simps
    note descendants_range[simp] = invokeUntyped_proofs.descendants_range[OF pf]
    note vc'[simp] = invokeUntyped_proofs.vc'[OF pf]
    note ps_no_overlap'[simp] = invokeUntyped_proofs.ps_no_overlap'[OF pf]
    note caps_no_overlap'[simp] = invokeUntyped_proofs.caps_no_overlap'[OF pf]
    note ex_cte_no_overlap' = invokeUntyped_proofs.ex_cte_no_overlap'[OF pf]
    note cref_inv = invokeUntyped_proofs.cref_inv[OF pf]
    note slots_invD = invokeUntyped_proofs.slots_invD[OF pf]
    note nidx[simp] = add_minus_neg_mask[where ptr = ptr]
    note idx_compare' = invokeUntyped_proofs.idx_compare'[OF pf]
    note ptr_cn[simp] = invokeUntyped_proofs.ptr_cn[OF pf]
    note sz_limit[simp] = invokeUntyped_proofs.sz_limit[OF pf]

    have valid_global_refs': "valid_global_refs' s"
      using misc by auto

    have mapM_insertNewCap_Q:
      "\<And>caps. \<lbrace>Q\<rbrace> mapM (\<lambda>(x, y). insertNewCap cref x y) (zip slots caps) \<lbrace>\<lambda>rv. Q\<rbrace>"
      by (wp mapM_wp' | clarsimp)+

    note reset_Q' = reset_Q[simplified ui, simplified]

    note neg_mask_add_mask = word_plus_and_or_coroll2[symmetric,where w = "mask sz" and t = ptr,symmetric]
    note msimp[simp add] =  misc neg_mask_add_mask
    show "\<lbrace>(=) s\<rbrace> invokeUntyped ui \<lbrace>\<lambda>rv s. invs' s \<and> Q s\<rbrace>"
    including no_pre
    apply (clarsimp simp:invokeUntyped_def getSlotCap_def ui)
    apply (rule validE_valid)
    apply (rule hoare_pre)
     apply (rule_tac Q'="\<lambda>_ s. invs' s \<and> Q s \<and> ct_active' s
                               \<and> valid_untyped_inv_wcap' ui
                                   (Some (UntypedCap dev (ptr && ~~ mask sz) sz (if reset then 0 else idx))) s
                               \<and> (reset \<longrightarrow> pspace_no_overlap' (ptr && ~~ mask sz) sz s)"
                  in bindE_wp_fwd)
      apply (simp only: whenE_def)
      apply wp
       apply (rule hoare_strengthen_postE, rule combine_validE,
           rule resetUntypedCap_invs_etc, rule valid_validE, rule reset_Q')
        apply (clarsimp simp only: if_True)
        apply auto[1]
       apply simp
      apply wp[1]
     prefer 2
     apply (cut_tac vui1 misc)
     apply (clarsimp simp: ui cte_wp_at_ctes_of simp del: misc)
     apply auto[1]
    apply (rule hoare_pre)
     apply (wp createNewObjects_wp_helper[where sz = sz])
            apply (simp add: slots)+
           apply (rule cover)
          apply (simp add: slots)+
        apply (clarsimp simp:insertNewCaps_def)
        apply (wp zipWithM_x_insertNewCap_invs''
                set_tuple_pick distinct_tuple_helper
                hoare_vcg_const_Ball_lift
                createNewCaps_invs'[where sz = sz]
                createNewCaps_valid_cap[where sz = sz,OF cover]
                createNewCaps_parent_helper[where sz = sz]
                createNewCaps_cap_to'[where sz = sz]
                createNewCaps_descendants_range_ret'[where sz = sz]
                createNewCaps_caps_overlap_reserved_ret'[where sz = sz]
                createNewCaps_ranges[where sz = sz]
                createNewCaps_ranges'[where sz = sz]
                createNewCaps_IRQHandler
                createNewCaps_ct_active'[where sz=sz]
                mapM_insertNewCap_Q
          | simp add: zipWithM_x_mapM slots tps)+
        apply (wp hoare_vcg_all_lift)
         apply (wp hoare_strengthen_post[OF createNewCaps_IRQHandler])
         apply (intro impI)
         apply (erule impE)
          apply (erule(1) snd_set_zip_in_set)
        apply (simp add: conj_comms, wp createNew_Q[where sz=sz])
        apply (wp hoare_strengthen_post[OF createNewCaps_range_helper[where sz = sz]])
        apply (clarsimp simp: slots)
       apply (clarsimp simp:conj_comms ball_conj_distrib pred_conj_def
                   simp del:capFreeIndex_update.simps)
       apply (strengthen invs_pspace_aligned' invs_pspace_distinct'
                invs_valid_pspace' invs_arch_state'
                imp_consequent[where Q = "(\<exists>x. x \<in> set slots)"]
              | clarsimp simp: conj_comms simp del: capFreeIndex_update.simps)+
       apply (wp updateFreeIndex_forward_invs' updateFreeIndex_caps_overlap_reserved
           updateFreeIndex_caps_no_overlap'' updateFreeIndex_pspace_no_overlap'
           hoare_vcg_const_Ball_lift
           updateFreeIndex_cte_wp_at
           updateCap_cte_cap_wp_to')
       apply (wp updateFreeIndex_caps_overlap_reserved
                 updateFreeIndex_descendants_range_in' getCTE_wp | simp)+
    apply (clarsimp simp only: ui)
    apply (frule(2) invokeUntyped_proofs.intro)
    apply (frule invokeUntyped_proofs.idx_le_new_offs)
    apply (frule invokeUntyped_proofs.szw)
    apply (frule invokeUntyped_proofs.descendants_range(2), simp)
    apply (frule invokeUntyped_proofs.idx_compare')
    apply (clarsimp simp: cte_wp_at_ctes_of isCap_simps getFreeIndex_def
                          shiftL_nat shiftl_t2n mult.commute
                          if_split[where P="\<lambda>x. x \<le> unat v" for v]
                          invs_valid_pspace' invs_ksCurDomain_maxDomain'
                          invokeUntyped_proofs.caps_no_overlap'
                          invokeUntyped_proofs.usableRange_disjoint
               split del: if_split)
    apply (strengthen refl)
    apply simp
    apply (intro conjI; assumption?)
          apply (erule is_aligned_weaken[OF range_cover.funky_aligned])
          apply (simp add: APIType_capBits_def objBits_simps' bit_simps untypedBits_defs
                    split: object_type.split apiobject_type.split)[1]
         apply (cases reset)
          apply (clarsimp simp: bit_simps)
         apply (clarsimp simp: invokeUntyped_proofs.ps_no_overlap')
        apply (drule invs_valid_global')
        apply (clarsimp simp: valid_global_refs'_def cte_at_valid_cap_sizes_0)
       apply (auto)[1]
      apply (frule valid_global_refsD', clarsimp)
      apply (clarsimp simp: Int_commute)
      apply (erule disjoint_subset2[rotated])
      apply (simp add: blah word_and_le2)
     apply (rule order_trans, erule invokeUntyped_proofs.subset_stuff)
     apply (simp add: blah word_and_le2 add_mask_fold)
    apply (frule valid_global_refsD2', clarsimp)
    apply (clarsimp simp: global_refs'_def)
    apply (erule notE, erule subsetD[rotated], simp add: blah word_and_le2)
    done
qed

lemma invokeUntyped_invs'[wp]:
  "\<lbrace>invs' and valid_untyped_inv' ui and ct_active'\<rbrace>
     invokeUntyped ui
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (wp invokeUntyped_invs''[where Q=\<top>, simplified hoare_TrueI, simplified])
  apply auto
  done

crunch updateFreeIndex
  for pred_tcb_at'[wp]: "pred_tcb_at' pr P p"

lemma resetUntypedCap_st_tcb_at':
  "\<lbrace>invs' and st_tcb_at' (P and ((\<noteq>) Inactive) and ((\<noteq>) IdleThreadState)) t
      and cte_wp_at' (\<lambda>cp. isUntypedCap (cteCap cp)) slot
      and ct_active' and sch_act_simple and (\<lambda>s. descendants_of' slot (ctes_of s) = {})\<rbrace>
    resetUntypedCap slot
  \<lbrace>\<lambda>_. st_tcb_at' P t\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp: cte_wp_at_ctes_of isCap_simps)
  apply (simp add: resetUntypedCap_def)
  apply (rule hoare_pre)
   apply (wp mapME_x_inv_wp preemptionPoint_inv
             deleteObjects_st_tcb_at'[where p=slot] getSlotCap_wp
           | simp add: unless_def
           | wp (once) hoare_drop_imps)+
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (strengthen refl)
  apply (rule exI, strengthen refl)
  apply (frule cte_wp_at_valid_objs_valid_cap'[OF ctes_of_cte_wpD], clarsimp+)
  apply (clarsimp simp: valid_cap_simps' capAligned_def empty_descendants_range_in'
                        descendants_range'_def2
                 elim!: pred_tcb'_weakenE)
  done

lemma inv_untyp_st_tcb_at'[wp]:
  "\<lbrace>invs' and st_tcb_at' (P and ((\<noteq>) Inactive) and ((\<noteq>) IdleThreadState)) tptr
         and valid_untyped_inv' ui and ct_active'\<rbrace>
     invokeUntyped ui
   \<lbrace>\<lambda>rv. st_tcb_at' P tptr\<rbrace>"
  apply (rule hoare_pre)
   apply (rule hoare_strengthen_post)
    apply (rule invokeUntyped_invs''[where Q="st_tcb_at' P tptr"];
           wp createNewCaps_pred_tcb_at')
      apply (auto simp: valid_pspace'_def)[1]
     apply (wp resetUntypedCap_st_tcb_at' | simp)+
  apply (cases ui, clarsimp simp: cte_wp_at_ctes_of isCap_simps)
  apply (clarsimp elim!: pred_tcb'_weakenE)
  done

lemma inv_untyp_tcb'[wp]:
  "\<lbrace>invs' and st_tcb_at' active' tptr
         and valid_untyped_inv' ui and ct_active'\<rbrace>
     invokeUntyped ui
   \<lbrace>\<lambda>rv. tcb_at' tptr\<rbrace>"
  apply (rule hoare_chain [OF inv_untyp_st_tcb_at'[where tptr=tptr and P="\<top>"]])
   apply (clarsimp elim!: pred_tcb'_weakenE)
   apply fastforce
  apply (clarsimp simp: pred_tcb_at'_def)
  done

crunch invokeUntyped
  for ksInterruptState_eq[wp]: "\<lambda>s. P (ksInterruptState s)"
  (wp: crunch_wps mapME_x_inv_wp preemptionPoint_inv
   simp: crunch_simps unless_def)

crunch deleteObjects, updateFreeIndex
  for valid_irq_states'[wp]: "valid_irq_states'"
  (wp: doMachineOp_irq_states' crunch_wps
   simp: freeMemory_def no_irq_storeWord unless_def)

lemma resetUntypedCap_IRQInactive:
  "\<lbrace>valid_irq_states'\<rbrace>
    resetUntypedCap slot
  \<lbrace>\<lambda>_ _. True\<rbrace>, \<lbrace>\<lambda>rv s. intStateIRQTable (ksInterruptState s) rv \<noteq> irqstate.IRQInactive\<rbrace>"
  (is "\<lbrace>?P\<rbrace> resetUntypedCap slot \<lbrace>?Q\<rbrace>,\<lbrace>?E\<rbrace>")
  apply (simp add: resetUntypedCap_def)
  apply (rule hoare_pre)
   apply (wp mapME_x_inv_wp[where P=valid_irq_states' and E="?E", THEN hoare_strengthen_postE]
             doMachineOp_irq_states' preemptionPoint_inv hoare_drop_imps
     | simp add: no_irq_clearMemory if_apply_def2)+
  done

lemma inv_untyped_IRQInactive:
  "\<lbrace>valid_irq_states'\<rbrace>
   invokeUntyped ui
   -, \<lbrace>\<lambda>rv s. intStateIRQTable (ksInterruptState s) rv \<noteq> irqstate.IRQInactive\<rbrace>"
  unfolding invokeUntyped_def
  by (wpsimp wp: whenE_wp resetUntypedCap_IRQInactive)

end
end
