(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Arch generic lemmas that should be moved into theory files before CRefine *)

theory Move_C
imports Refine.Refine
begin

lemma dumb_bool_for_all: "(\<forall>x. x) = False"
  by auto

lemma (in semigroup) foldl_first:
  "f x (foldl f y zs) = foldl f (f x y) zs"
  by (induction zs arbitrary: x y) (auto simp: assoc)

lemma (in monoid) foldl_first':
  "f x (foldl f z zs) = foldl f x zs"
  using foldl_first by simp

(* FIXME: move to Lib *)
lemma hd_in_zip_set:
   "slots \<noteq> [] \<Longrightarrow> (hd slots, 0) \<in> set (zip slots [0.e.of_nat (length slots - Suc 0)::machine_word])"
   by (cases slots; simp add: upto_enum_word upto_0_to_n2 del: upt_Suc)

(* FIXME: move to Lib *)
lemma last_in_zip_set:
  "\<lbrakk> slots \<noteq> []; length js = length slots \<rbrakk> \<Longrightarrow> (last slots, last js) \<in> set (zip slots js)"
   apply (simp add: in_set_zip last_conv_nth)
   apply (rule_tac x="length slots - 1" in exI)
   apply clarsimp
   apply (subst last_conv_nth)
    apply (cases js; simp)
   apply simp
   done

(* FIXME: move to Lib *)
lemma list_length_less:
  "(args = [] \<or> length args \<le> Suc 0) = (length args < 2)"
  by (case_tac args, simp_all)

(* FIXME: move to Lib *)
lemma at_least_2_args:
  "\<not>  length args < 2 \<Longrightarrow> \<exists>a b c. args = a#b#c"
  apply (case_tac args)
   apply simp
  apply (case_tac list)
   apply simp
  apply (case_tac lista)
   apply simp
  apply simp
  done

(* FIXME: move to Lib *)
lemma rel_option_alt_def:
  "rel_option f a b = (
      (a = None \<and>  b = None)
      \<or> (\<exists>x y. a = Some x \<and>  b = Some y \<and> f x y))"
  apply (case_tac a, case_tac b, simp, simp, case_tac b, auto)
  done

lemmas and_neq_0_is_nth = arg_cong [where f=Not, OF and_eq_0_is_nth, simplified]

lemma nat_le_induct [consumes 1, case_names base step]:
  assumes le: "i \<le> (k::nat)" and
        base: "P(k)" and
        step: "\<And>i. \<lbrakk>i \<le> k; P i; 0 < i\<rbrakk> \<Longrightarrow> P(i - 1)"
  shows "P i"
proof -
  obtain j where jk: "j \<le> k" and j_eq: "i = k - j"
    using le
    apply (drule_tac x="k - i" in meta_spec)
    apply simp
    done

  have "j \<le> k \<Longrightarrow> P (k - j)"
    apply (induct j)
     apply (simp add: base)
    apply simp
    apply (drule step[rotated], simp+)
    done

  thus "P i" using jk j_eq
    by simp
qed

lemma assumes A: "is_inv f g" shows the_inv_map_eq: "the_inv_map f = g"
 by (simp add: is_inv_unique[OF A A[THEN is_inv_inj, THEN is_inv_the_inv_map]])

lemma ran_map_comp_subset: "ran (map_comp f g) <= (ran f)"
  by (fastforce simp: map_comp_def ran_def split: option.splits)

lemma eq_option_to_0_rev:
  "Some 0 ~: A \<Longrightarrow> \<forall>x. \<forall>y\<in>A.
   ((=) \<circ> option_to_0) y x \<longrightarrow> (if x = 0 then None else Some x) = y"
  by (clarsimp simp: option_to_0_def split: option.splits)

lemma inj_image_inv:
  assumes inj_f: "inj f"
  shows "f ` A = B \<Longrightarrow> inv f ` B = A"
  by (drule sym) (simp add: image_inv_f_f[OF inj_f])

lemma Collect_mono2: "Collect P \<subseteq> Collect Q \<longleftrightarrow> (\<forall>x. P x \<longrightarrow> Q x)" by auto

lemma injection_handler_liftM:
  "injection_handler f
    = liftM (\<lambda>v. case v of Inl ex \<Rightarrow> Inl (f ex) | Inr rv \<Rightarrow> Inr rv)"
  apply (intro ext, simp add: injection_handler_def liftM_def
                              handleE'_def)
  apply (rule bind_apply_cong, rule refl)
  apply (simp add: throwError_def split: sum.split)
  done

(* FIXME MOVE to where option_to_0 is defined *)
lemma option_to_0_simps [simp]:
  "option_to_0 None =  0"
  "option_to_0 (Some x) = x"
  by (auto simp: option_to_0_def split: option.split)

lemma of_bool_from_bool: "of_bool = from_bool"
  by (rule ext, simp add: from_bool_def split: bool.split)

(* FIXME: move to Lib *)
lemma length_Suc_0_conv:
  "length x = Suc 0 = (\<exists>y. x = [y])"
  by (induct x; clarsimp)

lemma imp_ignore: "B \<Longrightarrow> A \<longrightarrow> B" by blast

lemmas cteSizeBits_eq = cteSizeBits_cte_level_bits

lemma cteSizeBits_le_cte_level_bits[simp]:
  "cteSizeBits \<le> cte_level_bits"
  by (simp add: cteSizeBits_eq)

lemma unat_ucast_prio_mask_simp[simp]:
  "unat (ucast (p::priority) && mask m :: machine_word) = unat (p && mask m)"
  by (simp add: ucast_and_mask)

lemma unat_ucast_prio_shiftr_simp[simp]:
  "unat (ucast (p::priority) >> n :: machine_word) = unat (p >> n)"
  by simp

lemma wb_gt_2:
  "2 < word_bits" by (simp add: word_bits_conv)

declare from_bool_to_bool_and_1[simp]

(* NOTE: unused. *)
lemma inj_on_option_map:
 "inj_on (map_option f o m) (dom m) \<Longrightarrow> inj_on m (dom m)"
  by (simp add: inj_on_imageI2)

lemma of_bool_inject[simp]: "of_bool a = of_bool b \<longleftrightarrow> a=b"
  by (cases a) (cases b, simp_all)+

lemma shiftr_and_eq_shiftl:
  fixes w x y :: "'a::len word"
  assumes r: "(w >> n) && x = y"
  shows "w && (x << n) = (y << n)"
  using assms
  proof -
    { fix i
      assume i: "i < LENGTH('a)"
      hence "test_bit (w && (x << n)) i \<longleftrightarrow> test_bit (y << n) i"
        using word_eqD[where x="i-n", OF r]
        by (cases "n \<le> i") (auto simp: nth_shiftl nth_shiftr)
    }
    thus ?thesis using word_eq_iff by blast
  qed

(* FIXME: move to Word_Lib *)
lemma sign_extend_0[simp]:
  "sign_extend a 0 = 0"
  by (simp add: sign_extend_def)

lemma mask_shiftr_times_simp:
  "\<lbrakk>x > n;is_aligned p n\<rbrakk> \<Longrightarrow> (p && mask x >> n) * (2^n) = (p && mask x)"
  apply (subst mult.commute)
  apply (simp add: shiftl_t2n[symmetric])
  by (simp add: is_aligned_andI1 is_aligned_shiftr_shiftl)

lemma name_seq_bound_helper:
  "(\<not> CP n \<and> (\<forall>n' < n. CP n'))
    \<Longrightarrow> (if \<exists>n. \<not> CP n
            then simpl_sequence c' (map f [0 ..< (LEAST n. \<not> CP n)])
            else c) = (simpl_sequence c' (map f [0 ..< n]))"
  apply (simp add: exI[where x=n])
  apply (subst Least_equality[where x=n], simp_all)
  apply (rule ccontr, simp add: linorder_not_le)
  done

(* FIXME: what's being proven here? it's a pure word lemma - should it go in Word_Lib? *)
lemma reset_name_seq_bound_helper:
  fixes sz
  fixes v :: "('a :: len) word"
  defines "CP \<equiv> (\<lambda>n. ~ (v && ~~ mask sz) + of_nat n * (-1 << sz) =
                          ((-1 :: 'a word) << sz))"
      and "n \<equiv> Suc (unat (shiftR v sz))"
  assumes vsz: "v + 1 < 2 ^ (len_of TYPE('a) - 1)" "2 ^ sz \<noteq> (0 :: 'a word)"
    and vless: "v < v'"
  shows "(\<not> CP n \<and> (\<forall>n' < n. CP n'))"
  apply (clarsimp simp: shiftl_t2n field_simps less_Suc_eq_le CP_def n_def)
  apply (simp add: shiftr_shiftl1[where b=sz and c=sz, simplified, symmetric]
                   shiftl_t2n)
  apply (clarsimp simp: word_sle_msb_le shiftl_t2n[symmetric])
  apply (case_tac n', simp_all)
   apply (cut_tac vsz(1) order_less_le_trans[OF vless max_word_max])
   apply (clarsimp simp: shiftr_shiftl1 dest!: word_add_no_overflow)
   apply (drule_tac f="\<lambda>x. x - 2 ^ sz" in arg_cong, simp)
   apply (metis less_irrefl order_le_less_trans order_less_trans
                word_and_le2[where a=v and y="~~ mask sz"]
                word_two_power_neg_ineq[OF vsz(2)])
  apply (clarsimp simp add: field_simps)
  apply (drule_tac f="\<lambda>x. shiftr x sz" in arg_cong)
  apply simp
  apply (simp add: shiftr_div_2n')
  apply (simp only: linorder_not_less[symmetric], erule notE)
  apply (rule order_le_less_trans[OF div_le_mono])
   apply (rule_tac b="v * 2 ^ sz" for v in word_unat_less_le,
     simp, rule order_refl)
  apply simp
  done

(* FIXME move to lib/Eisbach_Methods *)
(* FIXME consider printing error on solve goal apply *)
context
begin

private definition "bool_protect (b::bool) \<equiv> b"

lemma bool_protectD:
  "bool_protect P \<Longrightarrow> P"
  unfolding bool_protect_def by simp

lemma bool_protectI:
  "P \<Longrightarrow> bool_protect P"
  unfolding bool_protect_def by simp

(*
  When you want to apply a rule/tactic to transform a potentially complex goal into another
  one manually, but want to indicate that any fresh emerging goals are solved by a more
  brutal method.
  E.g. apply (solves_emerging \<open>frule x=... in my_rule\<close>\<open>fastforce simp: ... intro!: ... \<close>  *)
method solves_emerging methods m1 m2 = (rule bool_protectD, (m1 ; (rule bool_protectI | (m2; fail))))

end

lemma shiftr_le_mask:
  fixes w :: "'a::len word"
  shows "w >> n \<le> mask (LENGTH('a) - n)"
  by (metis and_mask_eq_iff_shiftr_0 le_mask_iff shiftr_mask_eq word_size)

lemma word_minus_1_shiftr:
  notes word_unat.Rep_inject[simp del]
  fixes w :: "'a::len word"
  assumes low_bits_zero: "w && mask n = 0"
  assumes neq_zero: "w \<noteq> 0"
  shows "(w - 1) >> n = (w >> n) - 1"
  using neq_zero low_bits_zero
  apply (subgoal_tac "n < LENGTH('a)")
   prefer 2
   apply (metis not_less ucast_id ucast_mask_drop)
  apply (rule_tac t="w - 1" and s="(w && ~~ mask n) - 1" in subst,
         fastforce simp: low_bits_zero mask_eq_x_eq_0)
  apply (clarsimp simp: mask_eq_0_eq_x neg_mask_is_div lt1_neq0[symmetric])
  apply (subst shiftr_div_2n_w)+
  apply (rule word_uint.Rep_eqD)
  apply (simp only: uint_word_ariths uint_div uint_power_lower)
  apply (subst mod_pos_pos_trivial, fastforce, fastforce)+
  apply (subst mod_pos_pos_trivial)
    apply (simp add: word_less_def word_le_def)
   apply (subst uint_1[symmetric])
   apply (fastforce intro: uint_sub_lt2p)
  apply (subst int_div_sub_1, fastforce)
  apply (clarsimp simp: and_mask_dvd low_bits_zero)
  apply (subst mod_pos_pos_trivial)
    apply (simp add: word_le_def)
    apply (metis (mono_tags) More_Word.word_div_mult assms(2) div_of_0_id p2_gt_0 uint_2p_alt uint_div
                             unsigned_eq_0_iff word_less_div word_less_iff_unsigned)
   apply (metis shiftr_div_2n uint_1 uint_sub_lt2p)
  apply fastforce
  done

(* FIXME: move to Word *)
lemma ucast_shiftr:
  "UCAST('a::len \<rightarrow> 'b::len) w >> n = UCAST('a \<rightarrow> 'b) ((w && mask LENGTH('b)) >> n)"
  by (word_eqI_solve dest: bit_imp_le_length)

(* FIXME: move to Word *)
lemma mask_eq_ucast_shiftr:
  assumes mask: "w && mask LENGTH('b) = w"
  shows "UCAST('a::len \<rightarrow> 'b::len) w >> n = UCAST('a \<rightarrow> 'b) (w >> n)"
  by (rule ucast_shiftr[where 'a='a and 'b='b, of w n, simplified mask])

(* FIXME: move to Word *)
lemma mask_eq_ucast_shiftl:
  assumes "w && mask (LENGTH('a) - n) = w"
  shows "UCAST('a::len \<rightarrow> 'b::len) w << n = UCAST('a \<rightarrow> 'b) (w << n)"
  apply (rule subst[where P="\<lambda>c. ucast c << n = ucast (c << n)", OF assms])
  by word_eqI_solve

(* FIXME: replace by mask_mono *)
lemma mask_le_mono:
  "m \<le> n \<Longrightarrow> mask m \<le> (mask n::'a::len word)"
  by (rule mask_mono)

(* FIXME: move to Word *)
lemma word_and_mask_eq_le_mono:
  "w && mask m = w \<Longrightarrow> m \<le> n \<Longrightarrow> w && mask n = w"
  apply (simp add: and_mask_eq_iff_le_mask)
  by (erule order.trans, erule mask_le_mono)

lemma word_not_exists_nth:
  "(w::'a::len word) = 0 \<Longrightarrow> \<forall>i<LENGTH('a). \<not> w !! i"
  by (clarsimp simp: nth_0)

lemma word_highbits_bounded_highbits_eq:
  "\<lbrakk>x \<le> (y :: 'a::len word); y < (x >> n) + 1 << n\<rbrakk> \<Longrightarrow> x >> n  = y >> n"
  apply (cases "n < LENGTH('a)")
   prefer 2
   apply (simp add: shiftr_eq_0)
  apply (drule_tac n=n in le_shiftr)
  apply (subst (asm) word_shiftl_add_distrib)
  apply (drule_tac word_less_sub_1)
  apply (simp only: add_diff_eq[symmetric] mask_def[symmetric] and_not_mask[symmetric])
  apply (drule_tac u=y and n=n in le_shiftr)
  apply (subgoal_tac "(x && ~~ mask n) + mask n >> n \<le> x >> n")
   apply fastforce
  apply (subst aligned_shift')
     apply (fastforce simp: mask_lt_2pn)
    apply (fastforce simp: is_aligned_neg_mask)
   apply fastforce
  apply (fastforce simp: mask_shift)
  done

lemma word_eq_cast_unsigned:
  "(x = y) = (UCAST ('a signed \<rightarrow> ('a :: len)) x = ucast y)"
  by (simp add: word_eq_iff nth_ucast)

(* tcbIPCBufferSlot is last slot in TCB *)
(* FIXME arch-split: Arch is needed for wordSizeCase, proof is same on all arches *)
lemma (in Arch) cteSizeBits_2ptcbBlockSizeBits[simplified tcbIPCBufferSlot_def]:
  "n \<le> tcbIPCBufferSlot \<Longrightarrow> n << cteSizeBits < 2 ^ tcbBlockSizeBits"
  unfolding tcbIPCBufferSlot_def tcbBlockSizeBits_def cteSizeBits_def
  apply (simp only: wordSizeCase_simp)
  apply (rule shiftl_less_t2n; simp)
  apply unat_arith
  done

requalify_facts Arch.cteSizeBits_2ptcbBlockSizeBits

lemmas zero_less_2p_tcbBlockSizeBits = cteSizeBits_2ptcbBlockSizeBits[where n=0, simplified]

lemma ran_tcb_cte_cases:
  "ran tcb_cte_cases =
   {(Structures_H.tcbCTable, tcbCTable_update),
    (Structures_H.tcbVTable, tcbVTable_update),
    (Structures_H.tcbReply, tcbReply_update),
    (Structures_H.tcbCaller, tcbCaller_update),
    (tcbIPCBufferFrame, tcbIPCBufferFrame_update)}"
  unfolding tcb_cte_cases_def
  by (auto split: if_split_asm simp: tcb_cte_cases_neqs)

lemma user_data_at_ko:
  "typ_at' UserDataT p s \<Longrightarrow> ko_at' UserData p s"
  apply (clarsimp simp: typ_at'_def obj_at'_def ko_wp_at'_def projectKOs)
  apply (case_tac ko, auto)
  done

lemma map_to_ko_atI:
  "\<lbrakk>(projectKO_opt \<circ>\<^sub>m ksPSpace s) x = Some v;
    pspace_aligned' s; pspace_distinct' s\<rbrakk>
   \<Longrightarrow> ko_at' v x s"
  apply (clarsimp simp: map_comp_Some_iff)
  apply (erule (2) aligned_distinct_obj_atI')
  apply (simp add: project_inject)
  done

lemma map_to_ko_atI':
  "\<lbrakk>(projectKO_opt \<circ>\<^sub>m (ksPSpace s)) x = Some v; invs' s\<rbrakk> \<Longrightarrow> ko_at' v x s"
  apply (clarsimp simp: map_comp_Some_iff)
  apply (erule aligned_distinct_obj_atI')
    apply clarsimp
   apply clarsimp
  apply (simp add: project_inject)
  done

lemma map_to_ko_at_updI':
  "\<And>x x' y y' y''.
   \<lbrakk> (projectKO_opt \<circ>\<^sub>m (ksPSpace s)) x = Some y;
     valid_pspace' s; ko_at' y' x' s;
     objBitsKO (injectKO y') = objBitsKO y''; x \<noteq> x' \<rbrakk> \<Longrightarrow>
   ko_at' y x (s\<lparr>ksPSpace := (ksPSpace s)(x' \<mapsto> y'')\<rparr>)"
  by (fastforce simp: obj_at'_def projectKOs objBitsKO_def ps_clear_upd
               dest: map_to_ko_atI)

lemma ps_clear_upd_None:
  "ksPSpace s y = None \<Longrightarrow>
    ps_clear x n (ksPSpace_update (\<lambda>a. (ksPSpace s)(y := None)) s') = ps_clear x n s"
  by (rule iffI | clarsimp elim!: ps_clear_domE | fastforce)+

(* FIXME move the thread_submonad stuff to SubMonad_R and use it for asUser *)
definition
  "thread_fetch \<equiv> \<lambda>ext t s. case (ksPSpace s t) of
      Some (KOTCB tcb) \<Rightarrow> ext tcb
    | None \<Rightarrow> undefined"

definition
  "thread_fetch_option \<equiv> \<lambda>ext t s. case (ksPSpace s t) of
      Some (KOTCB tcb) \<Rightarrow> ext tcb
    | None \<Rightarrow> None"

definition
  "thread_replace \<equiv> \<lambda>upd t nv s.
      let obj = case (ksPSpace s t) of
                   Some (KOTCB tcb) \<Rightarrow> Some (KOTCB (upd (\<lambda>_. nv) tcb))
                 | obj \<Rightarrow> obj
      in s \<lparr> ksPSpace := (ksPSpace s) (t := obj) \<rparr>"

lemma thread_submonad_args:
  "\<lbrakk> \<And>f v. ext (upd f v) = f (ext v);
     \<And>f1 f2 v. upd f1 (upd f2 v) = upd (f1 \<circ> f2) v;
     \<And>f v. upd (\<lambda>_. ext v) v = v \<rbrakk> \<Longrightarrow>
   submonad_args (thread_fetch ext t) (thread_replace upd t) (tcb_at' t)"
  apply unfold_locales
     apply (clarsimp simp: thread_fetch_def thread_replace_def
                           Let_def obj_at'_def projectKOs
                    split: kernel_object.split option.split)
    apply (clarsimp simp: thread_replace_def Let_def
                   split: kernel_object.split option.split)
   apply (clarsimp simp: thread_fetch_def thread_replace_def Let_def
                         fun_upd_idem
                  split: kernel_object.splits option.splits)
  apply (clarsimp simp: obj_at'_def thread_replace_def Let_def projectKOs
                 split: kernel_object.splits option.splits)
  apply (rename_tac tcb)
  apply (case_tac tcb, simp add: objBitsKO_def ps_clear_def)
  done

lemma tcbFault_submonad_args:
  "submonad_args (thread_fetch tcbFault t) (thread_replace tcbFault_update t)
                 (tcb_at' t)"
  apply (rule thread_submonad_args)
    apply (case_tac v, simp)+
  done

lemma threadGet_stateAssert_gets:
  "threadGet ext t = do stateAssert (tcb_at' t) []; gets (thread_fetch ext t) od"
  apply (rule is_stateAssert_gets [OF _ _ empty_fail_threadGet no_fail_threadGet])
  apply (wp threadGet_wp | clarsimp simp: obj_at'_def thread_fetch_def projectKOs)+
  done

lemma threadGet_tcbFault_submonad_fn:
  "threadGet tcbFault t =
   submonad_fn (thread_fetch tcbFault t) (thread_replace tcbFault_update t)
               (tcb_at' t) get"
  apply (rule ext)
  apply (clarsimp simp: submonad_fn_def bind_assoc split_def)
  apply (subst threadGet_stateAssert_gets, simp)
  apply (rule bind_apply_cong [OF refl])
  apply (clarsimp simp: in_monad bind_def gets_def get_def return_def
                        submonad_args.args(3) [OF tcbFault_submonad_args]
                        select_f_def modify_def put_def)
  done

lemma is_stateAssert_modify:
  "\<lbrakk> \<forall>s. \<lbrace>(=) s\<rbrace> f \<lbrace>\<lambda>_. (=) (replace s)\<rbrace>; \<forall>s. \<lbrace>(=) s\<rbrace> f \<lbrace>\<lambda>_ _. guard s\<rbrace>;
     empty_fail f; no_fail guard f \<rbrakk>
   \<Longrightarrow> f = do stateAssert guard []; modify replace od"
  apply (rule ext)
  apply (rename_tac s)
  apply (clarsimp simp: bind_def empty_fail_def valid_def no_fail_def
                        stateAssert_def assert_def simpler_modify_def get_def
                        return_def fail_def image_def split_def)
  apply (case_tac "f s")
  apply (intro conjI impI)
   apply (drule_tac x=s in spec)+
   apply (subgoal_tac "\<forall>x\<in>fst (f s). fst x = () \<and> snd x = replace s")
    apply fastforce
   apply clarsimp
  apply (drule_tac x=s in spec)+
  apply fastforce
  done

lemma threadSet_stateAssert_modify:
  "threadSet f t = do stateAssert (tcb_at' t) []; modify (thread_replace (\<lambda>_. f) t ()) od"
  apply (rule is_stateAssert_modify [OF _ _ empty_fail_threadSet no_fail_threadSet])
  apply (wp threadSet_wp | clarsimp simp: obj_at'_def thread_replace_def projectKOs)+
  done

lemmas asUser_return = submonad.return [OF submonad_asUser]

lemmas asUser_bind_distrib =
  submonad_bind [OF submonad_asUser submonad_asUser submonad_asUser]

lemma asUser_obj_at_notQ:
  "\<lbrace>obj_at' (Not \<circ> tcbQueued) t\<rbrace>
   asUser t (setRegister r v)
   \<lbrace>\<lambda>rv. obj_at' (Not \<circ> tcbQueued) t\<rbrace>"
  apply (simp add: asUser_def)
  apply (rule bind_wp)+
    apply (simp add: split_def)
    apply (rule threadSet_obj_at'_really_strongest)
   apply (wp threadGet_wp |rule gets_inv|wpc|clarsimp)+
  apply (clarsimp simp: obj_at'_def)
  done

lemma empty_fail_asUser[iff]:
  "empty_fail m \<Longrightarrow> empty_fail (asUser t m)"
  apply (simp add: asUser_def split_def)
  apply (intro empty_fail_bind, simp_all)
  apply (simp add: select_f_def empty_fail_def)
  done

lemma asUser_mapM_x:
  "(\<And>x. empty_fail (f x)) \<Longrightarrow>
    asUser t (mapM_x f xs) = do stateAssert (tcb_at' t) []; mapM_x (\<lambda>x. asUser t (f x)) xs od"
  supply empty_fail_cond[simp]
  apply (simp add: mapM_x_mapM asUser_bind_distrib)
  apply (subst submonad_mapM [OF submonad_asUser submonad_asUser])
   apply simp
  apply (simp add: asUser_return bind_assoc o_def)
  apply (rule ext)
  apply (rule bind_apply_cong [OF refl])+
  apply (clarsimp simp: in_monad dest!: fst_stateAssertD)
  apply (drule use_valid, rule mapM_wp', rule asUser_typ_ats, assumption)
  apply (simp add: stateAssert_def get_def Nondet_Monad.bind_def)
  done

lemma asUser_threadGet_tcbFault_comm:
  "empty_fail im \<Longrightarrow>
   do y \<leftarrow> asUser t im;
      x \<leftarrow> threadGet tcbFault t';
      n x y
   od =
   do x \<leftarrow> threadGet tcbFault t';
      asUser t im >>= n x
   od"
  apply (rule submonad_comm2 [OF tcbFault_submonad_args
                                 threadGet_tcbFault_submonad_fn
                                 submonad_asUser, symmetric])
      apply (clarsimp simp: thread_replace_def asUser_replace_def Let_def
                     split: option.split)
      apply (clarsimp simp: fun_upd_idem fun_upd_twist
                     split: kernel_object.split)
      apply (rename_tac tcb)
      apply (case_tac tcb, simp)
     apply (clarsimp simp: asUser_replace_def Let_def obj_at'_real_def
                           ko_wp_at'_def ps_clear_upd_None ps_clear_upd
                           objBitsKO_def projectKOs
                    split: option.split kernel_object.split)
    apply (clarsimp simp: thread_replace_def Let_def obj_at'_real_def
                          ko_wp_at'_def ps_clear_upd_None
                          ps_clear_upd objBitsKO_def projectKOs
                   split: option.split kernel_object.split)
   apply (simp add: get_def empty_fail_def)
  apply assumption
  done

lemma asUser_getRegister_threadGet_comm:
  "do
     ra \<leftarrow> asUser a (getRegister r);
     rb \<leftarrow> threadGet fb b;
     c ra rb
   od = do
     rb \<leftarrow> threadGet fb b;
     ra \<leftarrow> asUser a (getRegister r);
     c ra rb
   od"
  by (rule bind_inv_inv_comm, auto; wp)

lemma threadGet_tcbFault_doMachineOp_comm:
  "\<lbrakk> empty_fail m' \<rbrakk> \<Longrightarrow>
   do x \<leftarrow> threadGet tcbFault t; y \<leftarrow> doMachineOp m'; n x y od =
   do y \<leftarrow> doMachineOp m'; x \<leftarrow> threadGet tcbFault t; n x y od"
  apply (rule submonad_comm2 [OF tcbFault_submonad_args
                                 threadGet_tcbFault_submonad_fn
                                 submonad_doMachineOp])
      apply (simp add: thread_replace_def Let_def)
     apply simp
    apply (rule refl)
   apply (simp add: get_def empty_fail_def)
  apply assumption
  done

lemma getObject_tcb_det:
  "(r::tcb,s') \<in> fst (getObject p s) \<Longrightarrow> fst (getObject p s) = {(r,s)} \<and> s' = s"
  apply (clarsimp simp add: getObject_def bind_def get_def gets_def
                            return_def loadObject_default_def split_def)
  apply (clarsimp split: kernel_object.split_asm if_split_asm option.split_asm
                   simp: in_monad typeError_def alignError_def magnitudeCheck_def
                         objBits_def objBitsKO_def projectKOs
                         lookupAround2_def Let_def o_def)
   apply (simp_all add: bind_def return_def assert_opt_def split_def projectKOs
                        alignCheck_def is_aligned_mask[symmetric]
                        unless_def when_def magnitudeCheck_def)
  done

lemma threadGet_again:
  "\<And>rv s s' n. (rv, s') \<in> fst (threadGet ext t s) \<Longrightarrow>
   (threadGet ext t >>= n) s' = n rv s'"
  apply (clarsimp simp add: threadGet_def liftM_def in_monad)
  apply (frule use_valid [OF _ getObject_obj_at'])
     apply (simp add: gen_objBits_simps tcbBlockSizeBits_def)+ (* FIXME arch-split: tcbBlockSizeBits *)
  apply (frule getObject_tcb_det)
  apply (clarsimp simp: bind_def split_def)
  apply (insert no_fail_getObject_tcb)
  apply (clarsimp simp: no_fail_def obj_at'_def is_tcb)
  done

lemma setMRs_Nil:
  "setMRs thread buffer [] = stateAssert (tcb_at' thread) [] >>= (\<lambda>_. return 0)"
  unfolding setMRs_def
  by (simp add: zipWithM_x_def sequence_x_def zipWith_def
                asUser_return)

lemma device_data_at_ko:
  "typ_at' UserDataDeviceT p s \<Longrightarrow> ko_at' UserDataDevice p s"
  apply (clarsimp simp: typ_at'_def obj_at'_def ko_wp_at'_def
    projectKO_user_data_device projectKO_eq projectKO_eq2)
  apply (case_tac ko, auto)
  done

lemma empty_fail_rethrowFailure:
  "empty_fail f \<Longrightarrow> empty_fail (rethrowFailure fn f)"
  apply (simp add: rethrowFailure_def handleE'_def)
  apply (erule empty_fail_bind)
  apply (simp split: sum.split)
  done

lemma empty_fail_resolveAddressBits:
  "empty_fail (resolveAddressBits cap cptr bits)"
proof -
  note empty_fail_cond[simp]
  show ?thesis
  apply (rule empty_fail_use_cutMon)
  apply (induct rule: resolveAddressBits.induct)
  apply (subst resolveAddressBits.simps)
  apply (unfold Let_def cnode_cap_case_if fun_app_def
                K_bind_def haskell_assertE_def split_def)
  apply (intro empty_fail_cutMon_intros)
  apply (clarsimp simp: empty_fail_drop_cutMon locateSlot_conv returnOk_liftE[symmetric]
                        isCap_simps)+
  done
qed

lemma mapM_only_length:
  "do ys \<leftarrow> mapM f xs;
      g (length ys)
   od =
   do _ \<leftarrow> mapM_x f xs;
      g (length xs)
   od"
  by (subst bind_return_subst [OF mapM_length])
     (rule mapM_discarded)

lemma tcb_aligned':
  "tcb_at' t s \<Longrightarrow> is_aligned t tcbBlockSizeBits"
  by (drule obj_at_aligned'; simp add: gen_objBits_simps)

(* identical proof on all arches *)
lemma (in Arch) cte_at_0'[dest!]:
  "\<lbrakk> cte_at' 0 s; no_0_obj' s \<rbrakk> \<Longrightarrow> False"
  apply (clarsimp simp: cte_wp_at_obj_cases')
  by (auto simp: tcb_cte_cases_def is_aligned_def objBits_simps' dest!:tcb_aligned' split: if_split_asm)

requalify_facts Arch.cte_at_0'
lemmas [dest!] = cte_at_0'

lemma getMessageInfo_le3:
  "\<lbrace>\<top>\<rbrace> getMessageInfo sender \<lbrace>\<lambda>rv s. unat (msgExtraCaps rv) \<le> 3\<rbrace>"
  including no_pre
  apply (simp add: getMessageInfo_def)
  apply wp
  apply (rule_tac Q'="\<lambda>_. \<top>" in hoare_strengthen_post)
   apply wp
  apply (rename_tac rv s)
  apply (simp add: messageInfoFromWord_def Let_def msgExtraCapBits_def)
  apply (cut_tac y="rv >> Types_H.msgLengthBits" in word_and_le1 [where a=3])
  apply (simp add: word_le_nat_alt)
  done

lemma getMessageInfo_msgLength:
  "\<lbrace>\<top>\<rbrace> getMessageInfo sender \<lbrace>\<lambda>rv. K (unat (msgLength rv) \<le> msgMaxLength)\<rbrace>"
  including no_pre
  apply (simp add: getMessageInfo_def)
  apply wp
  apply (rule_tac Q'="\<lambda>_. \<top>" in hoare_strengthen_post)
   apply wp
  apply (simp add: messageInfoFromWord_def Let_def not_less msgMaxLength_def msgLengthBits_def
            split: if_split)
  apply (cut_tac y="r" in word_and_le1 [where a="0x7F"])
  apply (simp add: word_le_nat_alt)
  done

lemma cancelAllIPC_sch_act_wf:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
  cancelAllIPC ep
  \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: cancelAllIPC_def)
  apply (rule hoare_TrueI|wp getEndpoint_wp|wpc|simp)+
  apply fastforce?
  done

lemma cancelAllSignals_sch_act_wf:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
  cancelAllSignals ep
  \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: cancelAllSignals_def)
  apply (rule hoare_TrueI|wp getNotification_wp|wpc|simp)+
  apply fastforce?
  done

lemma cteDeleteOne_sch_act_wf:
  "\<lbrace>\<lambda>s. sch_act_wf (ksSchedulerAction s) s\<rbrace>
  cteDeleteOne slot
  \<lbrace>\<lambda>rv s. sch_act_wf (ksSchedulerAction s) s\<rbrace>"
  apply (simp add: cteDeleteOne_def unless_when split_def)
  apply (simp add: finaliseCapTrue_standin_def Let_def)
  apply (rule hoare_pre)
  apply (wp isFinalCapability_inv cancelAllSignals_sch_act_wf
            cancelAllIPC_sch_act_wf getCTE_wp' hoare_weak_lift_imp
         | wpc
         | simp add: Let_def split: if_split)+
  done

lemma vp_invs_strg': "invs' s \<longrightarrow> valid_pspace' s" by auto

lemma setCTE_tcbFault:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace>
  setCTE slot cte
  \<lbrace>\<lambda>rv. obj_at' (\<lambda>tcb. P (tcbFault tcb)) t\<rbrace>"
  apply (simp add: setCTE_def)
  apply (rule setObject_cte_obj_at_tcb', simp_all)
  done

lemmas threadSet_obj_at' = threadSet_obj_at'_strongish

lemmas setEndpoint_tcb = KHeap_R.setEndpoint_obj_at'_tcb

lemma setNotification_tcb:
  "\<lbrace>obj_at' (\<lambda>tcb::tcb. P tcb) t\<rbrace>
  setNotification ntfn e
  \<lbrace>\<lambda>_. obj_at' P t\<rbrace>"
  apply (simp add: setNotification_def)
  apply (rule obj_at_setObject2)
  apply (clarsimp simp: updateObject_default_def in_monad)
  done

lemma state_refs_of'_upd:
  "\<lbrakk> valid_pspace' s; ko_wp_at' (\<lambda>ko. objBitsKO ko = objBitsKO ko') ptr s \<rbrakk> \<Longrightarrow>
   state_refs_of' (s\<lparr>ksPSpace := (ksPSpace s)(ptr \<mapsto> ko')\<rparr>) =
   (state_refs_of' s)(ptr := refs_of' ko')"
  apply (rule ext)
  apply (clarsimp simp: ps_clear_upd valid_pspace'_def pspace_aligned'_def
                        obj_at'_def ko_wp_at'_def state_refs_of'_def
                 split: option.split if_split)
  done

lemma ex_st_tcb_at'_simp[simp]:
  "(\<exists>ts. st_tcb_at' ((=) ts) dest s) = tcb_at' dest s"
  by (auto simp add: pred_tcb_at'_def obj_at'_def)

lemma threadGet_wp'':
  "\<lbrace>\<lambda>s. \<forall>v. obj_at' (\<lambda>tcb. f tcb = v) thread s \<longrightarrow> P v s\<rbrace> threadGet f thread \<lbrace>P\<rbrace>"
  apply (rule hoare_pre)
  apply (rule threadGet_wp)
  apply (clarsimp simp: obj_at'_def)
  done

lemma filter_empty_unfiltered_contr:
  "\<lbrakk> [x\<leftarrow>xs . x \<noteq> y] = [] ; x' \<in> set xs ; x' \<noteq> y \<rbrakk> \<Longrightarrow> False"
  by (induct xs, auto split: if_split_asm)

lemma filter_noteq_op:
  "[x \<leftarrow> xs . x \<noteq> y] = filter ((\<noteq>) y) xs"
  by (induct xs) auto

lemma all_filter_propI:
  "\<forall>x\<in>set lst. P x \<Longrightarrow> \<forall>x\<in>set (filter Q lst). P x"
  by (induct lst, auto)

lemma returnOK_catch[simp]:
  "(returnOk rv <catch> m) = return rv"
  unfolding catch_def returnOk_def
  by clarsimp

lemma ignoreFailure_liftM:
  "ignoreFailure = liftM (\<lambda>v. ())"
  apply (rule ext)+
  apply (simp add: ignoreFailure_def liftM_def
                   catch_def)
  apply (rule bind_apply_cong[OF refl])
  apply (simp split: sum.split)
  done

lemma dom_eq:
  "dom um = dom um' \<longleftrightarrow> (\<forall>a. um a = None \<longleftrightarrow> um' a = None)"
  apply (simp add: dom_def del: not_None_eq)
  apply (rule iffI)
   apply (rule allI)
   apply (simp add: set_eq_iff)
   apply (drule_tac x=a in spec)
   apply auto
  done

lemma dom_user_mem':
  "dom (user_mem' s) = {p. typ_at' UserDataT (p && ~~ mask pageBits) s}"
  by (clarsimp simp:user_mem'_def dom_def pointerInUserData_def split:if_splits)

lemma dom_device_mem':
  "dom (device_mem' s) = {p. typ_at' UserDataDeviceT (p && ~~ mask pageBits) s}"
  by (clarsimp simp: device_mem'_def dom_def pointerInDeviceData_def split: if_splits)

lemma valid_idle'_tcb_at'_ksIdleThread:
  "valid_idle' s \<Longrightarrow> tcb_at' (ksIdleThread s) s"
  by (clarsimp simp: valid_idle'_def pred_tcb_at'_def obj_at'_def)

lemma invs_no_cicd'_valid_idle':
  "invs_no_cicd' s \<Longrightarrow> valid_idle' s"
  by (simp add: invs_no_cicd'_def)

lemma empty_fail_getIdleThread [simp,intro!]:
  "empty_fail getIdleThread"
  by (simp add: getIdleThread_def)

lemma setTCB_cur:
  "\<lbrace>cur_tcb'\<rbrace> setObject t (v::tcb) \<lbrace>\<lambda>_. cur_tcb'\<rbrace>"
  including classic_wp_pre
  apply (wp cur_tcb_lift)
  apply (simp add: setObject_def split_def updateObject_default_def)
  apply wp
  apply simp
  done

lemma empty_fail_slotCapLongRunningDelete:
  "empty_fail (slotCapLongRunningDelete slot)"
  by (auto simp: slotCapLongRunningDelete_def Let_def
                 case_Null_If isFinalCapability_def
          split: if_split)

lemmas mapM_x_append = mapM_x_append2

(* FIXME move to Invariants_H *)
lemma invs_cicd_arch_state' [elim!]:
  "all_invs_but_ct_idle_or_in_cur_domain' s \<Longrightarrow> valid_arch_state' s"
  by (simp add: all_invs_but_ct_idle_or_in_cur_domain'_def valid_state'_def)

(* FIXME move to Invariants_H *)
lemma invs_cicd_no_0_obj'[elim!]:
  "all_invs_but_ct_idle_or_in_cur_domain' s \<Longrightarrow> no_0_obj' s"
  by (simp add: all_invs_but_ct_idle_or_in_cur_domain'_def valid_state'_def valid_pspace'_def)

lemma getSlotCap_wp':
  "\<lbrace>\<lambda>s. \<forall>cap. cte_wp_at' (\<lambda>c. cteCap c = cap) p s \<longrightarrow> Q cap s\<rbrace> getSlotCap p \<lbrace>Q\<rbrace>"
  apply (simp add: getSlotCap_def)
  apply (wp getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma invs_cicd_valid_objs' [elim!]:
  "all_invs_but_ct_idle_or_in_cur_domain' s \<Longrightarrow> valid_objs' s"
  by (simp add: all_invs_but_ct_idle_or_in_cur_domain'_def valid_pspace'_def)

lemma st_tcb_at'_opeq_simp:
  "st_tcb_at' ((=) Structures_H.thread_state.Running) (ksCurThread s) s
    = st_tcb_at' (\<lambda>st. st = Structures_H.thread_state.Running) (ksCurThread s) s"
  by (fastforce simp add: st_tcb_at'_def obj_at'_def)

lemma invs'_pspace_domain_valid:
  "invs' s \<Longrightarrow> pspace_domain_valid s"
  by (simp add: invs'_def valid_state'_def)

lemma and_eq_0_is_nth:
  fixes x :: "('a :: len) word"
  shows "y = 1 << n \<Longrightarrow> ((x && y) = 0) = (\<not> (x !! n))"
  by (metis (poly_guards_query) and_eq_0_is_nth)

lemma magnitudeCheck_assert2:
  "\<lbrakk> is_aligned x n; (1 :: machine_word) < 2 ^ n; ksPSpace s x = Some v \<rbrakk> \<Longrightarrow>
   magnitudeCheck x (snd (lookupAround2 x (ksPSpace (s :: kernel_state)))) n
     = assert (ps_clear x n s)"
  using in_magnitude_check[where x=x and n=n and s=s and s'=s and v="()"]
  by (simp add: magnitudeCheck_assert in_monad)

lemma setObject_tcb_ep_obj_at'[wp]:
  "\<lbrace>obj_at' (P :: endpoint \<Rightarrow> bool) ptr\<rbrace> setObject ptr' (tcb :: tcb) \<lbrace>\<lambda>rv. obj_at' P ptr\<rbrace>"
  apply (rule obj_at_setObject2, simp_all)
  apply (clarsimp simp: updateObject_default_def in_monad)
  done

crunch setThreadState
  for ep_obj_at'[wp]: "obj_at' (P :: endpoint \<Rightarrow> bool) ptr"
  (simp: unless_def)

(* FIXME: move to AInvs *)
context
  fixes ptr sz us n p
  assumes cover: "range_cover ptr sz us n"
  assumes p: "p < n"
begin

lemma range_cover_mask_offset_bound:
  "(ptr && mask sz) + (of_nat p << us) < 2 ^ sz"
proof -
  note sz = range_cover.sz[OF cover]
  note al = range_cover.aligned[OF cover]
  have 1: "unat (ptr && mask sz >> us) + p < 2 ^ (sz - us)"
    using sz(3) p by simp
  have 2: "(ptr && mask sz >> us) + of_nat p < 2 ^ (sz - us)"
    using of_nat_power[OF 1 less_imp_diff_less, OF sz(1)]
          of_nat_add word_unat.Rep_inverse
    by simp
  have 3: "ptr && mask sz >> us << us = ptr && mask sz"
    by (rule is_aligned_shiftr_shiftl[OF is_aligned_after_mask[OF al sz(2)]])
  have 4: "((ptr && mask sz >> us) + of_nat p) << us < 2 ^ sz"
    by (rule shiftl_less_t2n[OF 2 sz(1)])
  show ?thesis
    by (rule 4[simplified 3 word_shiftl_add_distrib])
qed

lemma range_cover_neg_mask_offset:
  "ptr + (of_nat p << us) && ~~ mask sz = ptr && ~~ mask sz"
  apply (subst AND_NOT_mask_plus_AND_mask_eq[of ptr sz, symmetric], subst add.assoc)
  apply (rule is_aligned_add_helper[THEN conjunct2])
   apply (rule Aligned.is_aligned_neg_mask[OF order_refl])
  apply (rule range_cover_mask_offset_bound)
  done

end

lemma ko_at_projectKO_opt:
  "ko_at' ko p s \<Longrightarrow> (projectKO_opt \<circ>\<^sub>m ksPSpace s) p = Some ko"
  by (clarsimp elim!: obj_atE' simp: projectKOs)

lemma capFaultOnFailure_if_case_sum:
  " (capFaultOnFailure epCPtr b (if c then f else g) >>=
      sum.case_sum (handleFault thread) return) =
    (if c then ((capFaultOnFailure epCPtr b  f)
                 >>= sum.case_sum (handleFault thread) return)
          else ((capFaultOnFailure epCPtr b  g)
                 >>= sum.case_sum (handleFault thread) return))"
  by (case_tac c, clarsimp, clarsimp)

lemma dmo_machine_valid_lift:
  "(\<And>s f m. P s = P (ksMachineState_update f s)) \<Longrightarrow> \<lbrace>P\<rbrace> doMachineOp f' \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (wpsimp simp: split_def doMachineOp_def machine_op_lift_def machine_rest_lift_def in_monad)
  done

lemma tcb_runnable_imp_simple:
  "obj_at' (\<lambda>s. runnable' (tcbState s)) t s \<Longrightarrow> obj_at' (\<lambda>s. simple' (tcbState s)) t s"
  apply (clarsimp simp: obj_at'_def)
  apply (case_tac "tcbState obj" ; clarsimp)
  done

lemma injection_handler_returnOk:
  "injection_handler injector (returnOk v) = returnOk v"
  by (simp add: returnOk_liftE injection_liftE)

lemma injection_handler_If:
  "injection_handler injector (If P a b)
     = If P (injection_handler injector a)
            (injection_handler injector b)"
  by (simp split: if_split)

lemma injection_handler_throwError:
  "injection_handler f (throwError v) = throwError (f v)"
  by (simp add: injection_handler_def handleE'_def
                throwError_bind)

lemma injection_handler_whenE:
  "injection_handler injf (whenE P f)
    = whenE P (injection_handler injf f)"
  by (simp add: whenE_def injection_handler_returnOk split: if_split)

lemmas injection_handler_bindE = injection_bindE [OF refl refl]
lemmas injection_handler_wp = injection_wp [OF refl]

lemma if_n_updateCapData_valid_strg:
  "s \<turnstile>' cap \<longrightarrow> s \<turnstile>' (if P then cap else updateCapData prs v cap)"
  by (simp add: valid_updateCapDataI split: if_split)

lemma tcb_in_cur_domain'_def':
  "tcb_in_cur_domain' t = (\<lambda>s. obj_at' (\<lambda>tcb. tcbDomain tcb = ksCurDomain s) t s)"
  unfolding tcb_in_cur_domain'_def
  by (auto simp: obj_at'_def)

lemma updateCapData_Untyped:
  "isUntypedCap a
         \<Longrightarrow> updateCapData b c a = a"
 by (clarsimp simp: isCap_simps updateCapData_def)

lemma ctes_of_valid_strengthen:
  "(invs' s \<and> ctes_of s p = Some cte) \<longrightarrow> valid_cap' (cteCap cte) s"
  apply (case_tac cte)
  apply clarsimp
  apply (erule ctes_of_valid_cap')
  apply fastforce
  done

lemma finaliseCap_Reply:
  "\<lbrace>Q (NullCap,NullCap) and K (isReplyCap cap)\<rbrace> finaliseCapTrue_standin cap is_final \<lbrace>Q\<rbrace>"
  apply (rule Nondet_VCG.hoare_gen_asm)
  apply (wpsimp simp: finaliseCapTrue_standin_def isCap_simps)
  done

lemma cteDeleteOne_Reply:
  "\<lbrace>st_tcb_at' P t and cte_wp_at' (isReplyCap o cteCap) slot\<rbrace> cteDeleteOne slot \<lbrace>\<lambda>_. st_tcb_at' P t\<rbrace>"
  apply (simp add: cteDeleteOne_def unless_def split_def)
  apply (wp finaliseCap_Reply isFinalCapability_inv getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma cancelSignal_st_tcb':
  "\<lbrace>\<lambda>s. t\<noteq>t' \<and> st_tcb_at' P t' s\<rbrace> cancelSignal t ntfn \<lbrace>\<lambda>_. st_tcb_at' P t'\<rbrace>"
  apply (simp add: cancelSignal_def Let_def)
  apply (rule hoare_pre)
   apply (wp sts_pred_tcb_neq' getNotification_wp | wpc)+
  apply clarsimp
  done

lemma cancelIPC_st_tcb_at':
  "\<lbrace>\<lambda>s. t\<noteq>t' \<and> st_tcb_at' P t' s\<rbrace> cancelIPC t \<lbrace>\<lambda>_. st_tcb_at' P t'\<rbrace>"
  apply (simp add: cancelIPC_def Let_def getThreadReplySlot_def locateSlot_conv)
  apply (wp sts_pred_tcb_neq' getEndpoint_wp cteDeleteOne_Reply getCTE_wp' | wpc)+
          apply (rule hoare_strengthen_post[where Q'="\<lambda>_. st_tcb_at' P t'"])
           apply (wp threadSet_st_tcb_at2)
           apply simp
          apply (clarsimp simp: cte_wp_at_ctes_of capHasProperty_def)
         apply (wp cancelSignal_st_tcb' sts_pred_tcb_neq' getEndpoint_wp gts_wp' | wpc)+
  apply clarsimp
  done

lemma suspend_st_tcb_at':
  "\<lbrace>\<lambda>s. (t\<noteq>t' \<longrightarrow> st_tcb_at' P t' s) \<and> (t=t' \<longrightarrow> P Inactive)\<rbrace>
  suspend t
  \<lbrace>\<lambda>_. st_tcb_at' P t'\<rbrace>"
  apply (simp add: suspend_def unless_def)
  unfolding updateRestartPC_def
  apply (cases "t=t'")
   apply (simp | wp cancelIPC_st_tcb_at' sts_st_tcb')+
  done

lemma typ_at'_no_0_objD:
  "typ_at' P p s \<Longrightarrow> no_0_obj' s \<Longrightarrow> p \<noteq> 0"
  by (cases "p = 0" ; clarsimp)

lemma ko_at'_not_NULL:
  "\<lbrakk> ko_at' ko p s ; no_0_obj' s\<rbrakk>
   \<Longrightarrow> p \<noteq> 0"
  by (fastforce simp:  word_gt_0 typ_at'_no_0_objD)

crunch setQueue
  for ksReadyQueuesL1Bitmap[wp]: "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"

lemma sts_running_ksReadyQueuesL1Bitmap[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s)\<rbrace>
   setThreadState Structures_H.thread_state.Running t
   \<lbrace>\<lambda>_ s. P (ksReadyQueuesL1Bitmap s)\<rbrace>"
  unfolding setThreadState_def
  apply wp
       apply (rule hoare_pre_cont)
      apply (wpsimp simp: if_apply_def2
                    wp: hoare_drop_imps hoare_vcg_disj_lift threadSet_tcbState_st_tcb_at')+
  done

lemma sts_running_ksReadyQueuesL2Bitmap[wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL2Bitmap s)\<rbrace>
   setThreadState Structures_H.thread_state.Running t
   \<lbrace>\<lambda>_ s. P (ksReadyQueuesL2Bitmap s)\<rbrace>"
  unfolding setThreadState_def
  apply wp
       apply (rule hoare_pre_cont)
      apply (wpsimp simp: if_apply_def2
                    wp: hoare_drop_imps hoare_vcg_disj_lift threadSet_tcbState_st_tcb_at')+
  done

lemma asUser_obj_at_not_queued[wp]:
  "\<lbrace>obj_at' (\<lambda>tcb. \<not> tcbQueued tcb) p\<rbrace> asUser t m \<lbrace>\<lambda>rv. obj_at' (\<lambda>tcb. \<not> tcbQueued tcb) p\<rbrace>"
  apply (simp add: asUser_def split_def)
  apply (wp hoare_drop_imps | simp)+
  done

lemma ko_at'_obj_at'_field:
  "ko_at' ko (t s) s \<Longrightarrow> obj_at' (\<lambda>ko'. f ko' = f ko) (t s) s"
  by (erule obj_at'_weakenE, simp)

lemma cond_throw_whenE:
   "(if P then f else throwError e) = (whenE (\<not> P) (throwError e) >>=E (\<lambda>_. f))"
   by (auto split: if_splits
             simp: throwError_def bindE_def
                   whenE_def bind_def returnOk_def return_def)

lemma ksPSpace_update_eq_ExD:
  "s = t\<lparr> ksPSpace := ksPSpace s\<rparr>
     \<Longrightarrow> \<exists>ps. s = t \<lparr> ksPSpace := ps \<rparr>"
  by (erule exI)

(* FIXME BV: generalise *)
lemma word_clz_1[simp]:
  "word_clz (1::32 word) = 31"
  "word_clz (1::64 word) = 63"
  by (clarsimp simp: word_clz_def to_bl_def)+

(* FIXME BV: generalise *)
lemma word_ctz_0[simp]:
  "word_ctz (0::32 word) = 32"
  "word_ctz (0::64 word) = 64"
  by (clarsimp simp: word_ctz_def to_bl_def)+

(* FIXME move to Word_Lib *)
lemma unat_trans_ucast_helper:
  "\<lbrakk> unat x < n ; n \<le> Suc 0 \<rbrakk> \<Longrightarrow> ucast x = 0"
  by (simp add: le_Suc_eq unsigned_eq_0_iff)

lemma numPriorities_machine_word_safe:
  "unat (of_nat numPriorities :: machine_word) = numPriorities"
  by (simp add: numPriorities_def)

(* needed consequence of word_less_1 when word_less_1 isn't safe, e.g. when
   using no_less_1_simps; otherwise you'll be able to prove that 0 < 300, but
   not that 0 < 1 *)
lemma word_zero_less_one[simp]:
  "0 < (1::'a::len word)"
  by simp

bundle no_less_1_simps
begin
  declare word_less_1[simp del]
  declare less_Suc0[iff del]
end

lemma koTypeOf_injectKO:
  fixes v :: "'a :: pspace_storable" shows
  "koTypeOf (injectKO v) = koType TYPE('a)"
  apply (cut_tac v1=v in iffD2 [OF project_inject, OF refl])
  apply (simp add: project_koType[symmetric])
  done

lemma ctes_of_cte_at:
  "ctes_of s p = Some x \<Longrightarrow> cte_at' p s"
  by (simp add: cte_wp_at_ctes_of)

lemmas tcbSlots =
  tcbCTableSlot_def tcbVTableSlot_def
  tcbReplySlot_def tcbCallerSlot_def tcbIPCBufferSlot_def

lemma updateObject_cte_tcb:
  assumes tc: "tcb_cte_cases (ptr - ptr') = Some (accF, updF)"
  shows   "updateObject ctea (KOTCB tcb) ptr ptr' next =
   (do alignCheck ptr' (objBits tcb);
        magnitudeCheck ptr' next (objBits tcb);
        return (KOTCB (updF (\<lambda>_. ctea) tcb))
    od)"
  using tc unfolding tcb_cte_cases_def
  by (clarsimp simp: updateObject_cte Let_def tcb_cte_cases_neqs gen_objBits_simps tcbSlots
               split: if_split_asm
               cong: if_cong)

lemma self_elim:
  "\<And>P Q. \<lbrakk> P \<Longrightarrow> Q; P \<rbrakk> \<Longrightarrow> Q"
  by blast

lemma tcb_cte_cases_in_range1:
  assumes tc:"tcb_cte_cases (y - x) = Some v"
  and     al: "is_aligned x tcbBlockSizeBits"
  shows   "x \<le> y"
proof -
  from tc obtain q where yq: "y = x + q" and qv: "q < 2 ^ tcbBlockSizeBits"
    unfolding tcb_cte_cases_def
    by (clarsimp simp: diff_eq_eq tcbSlot_defs
                 simp del: shiftl_1
                 elim!: self_elim
                 intro!: cteSizeBits_2ptcbBlockSizeBits zero_less_2p_tcbBlockSizeBits
                 split: if_split_asm)

  have "x \<le> x + 2 ^ tcbBlockSizeBits - 1" using al
    by (rule is_aligned_no_overflow)

  hence "x \<le> x + q" using qv
    by unat_arith

  thus ?thesis using yq by simp
qed

lemma tcbBlockSizeBits_word_less_sub_le:
  fixes x :: machine_word
  shows "(x \<le> 2 ^ tcbBlockSizeBits - 1) = (x < 2 ^ tcbBlockSizeBits)"
  unfolding tcbBlockSizeBits_def
  by (subst word_less_sub_le; simp)

lemma tcb_cte_cases_in_range2:
  assumes tc: "tcb_cte_cases (y - x) = Some v"
  and     al: "is_aligned x tcbBlockSizeBits"
  shows   "y \<le> x + 2 ^ tcbBlockSizeBits - 1"
proof -
  from tc obtain q where yq: "y = x + q" and qv: "q \<le> 2 ^ tcbBlockSizeBits - 1"
    unfolding tcb_cte_cases_def
    by (clarsimp simp: diff_eq_eq tcbSlot_defs tcbBlockSizeBits_word_less_sub_le
                 simp del: shiftl_1
                 elim!: self_elim
                 intro!: cteSizeBits_2ptcbBlockSizeBits zero_less_2p_tcbBlockSizeBits
                 split: if_split_asm)

  have "x + q \<le> x + (2 ^ tcbBlockSizeBits - 1)" using qv
    apply (rule word_plus_mono_right)
    apply (rule is_aligned_no_overflow' [OF al])
    done

  thus ?thesis using yq by (simp add: field_simps)
qed

lemma valid_cap_cte_at':
  "\<lbrakk>isCNodeCap cap; valid_cap' cap s'\<rbrakk>
   \<Longrightarrow> cte_at' (capCNodePtr cap + 2^cteSizeBits * (addr && mask (capCNodeBits cap))) s'"
  apply (clarsimp simp: isCap_simps valid_cap'_def)
  apply (rule real_cte_at')
  apply (erule spec)
  done

lemma cd_wp[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s) s\<rbrace> curDomain \<lbrace>P\<rbrace>"
  by (unfold curDomain_def, wp)

lemma empty_fail_getEndpoint:
  "empty_fail (getEndpoint ep)"
  unfolding getEndpoint_def
  by (auto intro: empty_fail_getObject)

lemma ko_at_valid_ep':
  "\<lbrakk>ko_at' ep p s; valid_objs' s\<rbrakk> \<Longrightarrow> valid_ep' ep s"
  apply (erule obj_atE')
  apply (erule (1) valid_objsE')
   apply (simp add: projectKOs valid_obj'_def)
   done

lemma cap_case_EndpointCap_NotificationCap:
  "(case cap of EndpointCap v0 v1 v2 v3 v4 v5 \<Rightarrow> f v0 v1 v2 v3 v4 v5
              | NotificationCap v0 v1 v2 v3  \<Rightarrow> g v0 v1 v2 v3
              | _ \<Rightarrow> h)
   = (if isEndpointCap cap
      then f (capEPPtr cap) (capEPBadge cap) (capEPCanSend cap) (capEPCanReceive cap)
             (capEPCanGrant cap) (capEPCanGrantReply cap)
      else if isNotificationCap cap
           then g (capNtfnPtr cap)  (capNtfnBadge cap) (capNtfnCanSend cap) (capNtfnCanReceive cap)
           else h)"
  by (simp add: isCap_simps
         split: capability.split split del: if_split)

lemma asUser_obj_at':
  "\<lbrace> K(t\<noteq>t') and obj_at' P t' \<rbrace> asUser t f \<lbrace> \<lambda>_.  obj_at' (P::Structures_H.tcb \<Rightarrow> bool) t' \<rbrace>"
  including no_pre
  apply (simp add: asUser_def)
  apply wpsimp
  apply (case_tac "t=t'"; clarsimp)
  apply (rule hoare_drop_imps)
  apply wp
  done

(* FIXME: partial copy from SR_Lemmas since only map_to_ctes is defined.
          All of the update_*_map_tos in SR_lemmas can be moved up. *)
lemma update_ep_map_to_ctes:
  fixes P :: "endpoint \<Rightarrow> bool"
  assumes at: "obj_at' P p s"
  shows     "map_to_ctes ((ksPSpace s)(p \<mapsto> KOEndpoint ko)) = map_to_ctes (ksPSpace s)"
  using at
  by (auto elim!: obj_atE' intro!: map_to_ctes_upd_other map_comp_eqI
    simp: projectKOs projectKO_opts_defs split: kernel_object.splits if_split_asm)

(* FIXME AARCH64 move *)
lemma multiple_add_less_nat:
  "\<lbrakk> a < (c :: nat); x dvd a; x dvd c; b < x \<rbrakk>
   \<Longrightarrow> a + b < c"
  apply (subgoal_tac "b < c - a")
   apply simp
  apply (erule order_less_le_trans)
  apply (rule dvd_imp_le)
   apply simp
  apply simp
  done

end
