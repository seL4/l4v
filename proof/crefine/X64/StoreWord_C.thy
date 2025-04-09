(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory StoreWord_C
imports VSpace_C
begin

context kernel_m
begin

lemma in_doMachineOp:
  "(a, s) \<in> fst (doMachineOp f s') = (\<exists>b. (a, b) \<in> fst (f (ksMachineState s')) \<and> s = s'\<lparr>ksMachineState := b\<rparr>)"
  unfolding doMachineOp_def
  by (simp add: in_monad select_f_def)

lemma dom_heap_to_user_data:
  "dom (heap_to_user_data hp uhp) = dom (map_to_user_data hp)"
  unfolding heap_to_user_data_def by (simp add: Let_def dom_def)

lemma dom_heap_to_device_data:
  "dom (heap_to_device_data hp uhp) = dom (map_to_user_data_device hp)"
  unfolding heap_to_device_data_def by (simp add: Let_def dom_def)

lemma projectKO_opt_retyp_same:
  assumes pko: "projectKO_opt ko = Some v"
  shows "projectKO_opt \<circ>\<^sub>m
    (\<lambda>x. if x \<in> set (new_cap_addrs sz ptr ko) then Some ko else ksPSpace \<sigma> x)
  =
  (\<lambda>x. if x \<in> set (new_cap_addrs sz ptr ko) then Some v else (projectKO_opt \<circ>\<^sub>m (ksPSpace \<sigma>)) x)"
  (is "?LHS = ?RHS")
proof (rule ext)
  fix x

  show "?LHS x = ?RHS x"
  proof (cases "x \<in> set (new_cap_addrs sz ptr ko)")
    case True
    thus ?thesis using pko by simp
  next
    case False
    thus ?thesis by (simp add: map_comp_def)
  qed
qed


lemma byte_to_word_heap_upd_outside_range:
  "p \<notin> {(base + ucast off * 8)..+8} \<Longrightarrow>
   byte_to_word_heap (m (p := v')) base off = byte_to_word_heap m base off"
  apply (simp add: byte_to_word_heap_def Let_def)
  apply (erule contrapos_np)
  by (clarsimp intro!: intvl_inter_le [where k=0 and ka=7, simplified, OF refl]
                       intvl_inter_le [where k=0 and ka=6, simplified, OF refl]
                       intvl_inter_le [where k=0 and ka=5, simplified, OF refl]
                       intvl_inter_le [where k=0 and ka=4, simplified, OF refl]
                       intvl_inter_le [where k=0 and ka=3, simplified, OF refl]
                       intvl_inter_le [where k=0 and ka=2, simplified, OF refl]
                       intvl_inter_le [where k=0 and ka=1, simplified, OF refl]
                       intvl_inter_le [where k=0 and ka=0, simplified, OF refl]
                split: if_split_asm) (* long, many if_asm splits *)

lemma intvl_range_conv:
  "\<lbrakk> is_aligned (ptr :: 'a :: len word) bits; bits < len_of TYPE('a) \<rbrakk> \<Longrightarrow>
   {ptr ..+ 2 ^ bits} = {ptr .. ptr + 2 ^ bits - 1}"
  by (rule upto_intvl_eq)

lemma byte_to_word_heap_upd_neq:
  assumes   alb: "is_aligned base 3"
  and       alp: "is_aligned p 3"
  and       neq: "base + ucast off * 8 \<noteq> p"
  and word_byte: "n < 8"
  shows "byte_to_word_heap (m (p + n := v')) base off = byte_to_word_heap m base off"
proof -
  from alb have alw: "is_aligned (base + ucast off * 8) 3"
    by (fastforce elim: aligned_add_aligned
                intro: is_aligned_mult_triv2 [where n=3, simplified]
                 simp: word_bits_def)

  from alp have p_intvl: "p + n \<in> {p .. p + 7}"
    apply (clarsimp simp: word_byte)
    apply (rule conjI)
     apply (fastforce elim: is_aligned_no_wrap' simp: word_byte)
    apply (subst word_plus_mono_right)
      apply (clarsimp simp: word_byte word_le_make_less)
     apply (simp add: word_bits_def is_aligned_no_overflow'[OF alp, simplified])
    apply simp
    done

  hence not_in_range: "p + n \<notin> {(base + ucast off * 8)..+8}"
    apply (subst intvl_range_conv [OF alw, simplified])
     apply (simp add: word_bits_def)
    apply (cut_tac aligned_neq_into_no_overlap [OF neq alw alp])
     apply (auto simp: field_simps range_inter)[1]
    done

  thus ?thesis
    (* when this is "by ..", it waits for byte_to_word_heap_upd_outside_range to complete *)
    apply (rule byte_to_word_heap_upd_outside_range)
    done
qed

lemma update_ti_t_acc_foo:
  "\<And>acc f v. \<lbrakk> \<And>a ys v. \<lbrakk> a \<in> set adjs; length ys = size_td_pair a \<rbrakk>
                \<Longrightarrow> acc (update_ti_pair a ys v) = update_ti_pair (f a) ys (acc v);
              \<And>a. size_td_pair (f a) = size_td_pair a \<rbrakk> \<Longrightarrow>
       \<forall>xs. acc (update_ti_list_t adjs xs v) = update_ti_list_t (map f adjs) xs (acc v)"
  apply (simp add: update_ti_list_t_def size_td_list_map2 split: if_split)
  apply (induct adjs)
   apply simp
  apply clarsimp
  done

lemma nat_less_8_cases:
  "i < (8::nat) ==> i = 0 | i = 1 | i = 2 | i = 3 | i = 4 | i = 5 | i = 6 | i = 7"
  by auto

lemma user_data_relation_upd:
  assumes al: "is_aligned ptr 3"
  shows "cuser_user_data_relation
            (byte_to_word_heap
              (underlying_memory (ksMachineState \<sigma>)) (ptr && ~~ mask pageBits))
            (the (cslift s (Ptr (ptr && ~~ mask pageBits)))) \<Longrightarrow>
     cuser_user_data_relation
            (byte_to_word_heap
              ((underlying_memory (ksMachineState \<sigma>))
               (ptr := word_rsplit w ! 7, ptr + 1 := word_rsplit w ! 6,
                ptr + 2 := word_rsplit w ! 5, ptr + 3 := word_rsplit w ! 4,
                ptr + 4 := word_rsplit w ! 3, ptr + 5 := word_rsplit w ! 2,
                ptr + 6 := word_rsplit w ! Suc 0, ptr + 7 := word_rsplit w ! 0))
              (ptr && ~~ mask pageBits))
            (user_data_C.words_C_update
              (\<lambda>ws. Arrays.update ws (unat (ucast ((ptr && mask pageBits) >> 3):: 9 word)) w)
              (the (cslift s (Ptr (ptr && ~~ mask pageBits)))))"
  unfolding cuser_user_data_relation_def
  apply -
  apply (erule allEI)
  apply (case_tac "off = ucast ((ptr && mask pageBits) >> 3)")
   apply (clarsimp simp: mask_pageBits_inner_beauty [OF al] byte_to_word_heap_def)
   apply (subst index_update)
    apply (simp, unat_arith, simp)
   apply (subgoal_tac "map ((!) (word_rsplit w)) [0,1,2,3,4,5,6,7]
                      = (word_rsplit w :: word8 list)")
    apply (clarsimp simp: word_rcat_rsplit)
   apply (cut_tac w=w and m=8 and 'a=8
               in length_word_rsplit_even_size [OF refl])
    apply (simp add: word_size)
   apply (rule nth_equalityI[symmetric])
    apply simp
   apply (subgoal_tac "[0,1,2,3,4,5,6,7] = [0..<8]")
    apply clarsimp
   apply (rule nth_equalityI[symmetric])
    apply simp
   apply (auto dest: nat_less_8_cases)[1]
  apply (frule more_pageBits_inner_beauty)
  apply (simp add: byte_to_word_heap_upd_neq aligned_already_mask al
                   byte_to_word_heap_upd_neq [where n=0, simplified])
  apply (subst index_update2)
   apply (cut_tac x=off in unat_lt2p, simp)
   apply simp
  apply simp
  done

(* This lemma is true for trivial reason.
   But it might become non-trivial if we change our way of modeling device memory *)
lemma user_data_device_relation_upd:
  assumes al: "is_aligned ptr 3"
  shows "cuser_user_data_device_relation
            (byte_to_word_heap
              (underlying_memory (ksMachineState \<sigma>)) (ptr && ~~ mask pageBits))
            (the (cslift s (Ptr (ptr && ~~ mask pageBits)))) \<Longrightarrow>
     cuser_user_data_device_relation
            (byte_to_word_heap
              ((underlying_memory (ksMachineState \<sigma>))
               (ptr := word_rsplit w ! 7, ptr + 1 := word_rsplit w ! 6,
                ptr + 2 := word_rsplit w ! 5, ptr + 3 := word_rsplit w ! 4,
                ptr + 4 := word_rsplit w ! 3, ptr + 5 := word_rsplit w ! 2,
                ptr + 6 := word_rsplit w ! Suc 0, ptr + 7 := word_rsplit w ! 0))
              (ptr && ~~ mask pageBits))
            (user_data_device_C.words_C_update
              (\<lambda>ws. Arrays.update ws (unat (ucast ((ptr && mask pageBits) >> 3):: 9 word)) w)
              (the (cslift s (Ptr (ptr && ~~ mask pageBits)))))"
  by (simp add:cuser_user_data_device_relation_def )

lemma deviceDataSeperate:
  "\<lbrakk>\<not> pointerInDeviceData ptr \<sigma>; pspace_distinct' \<sigma>; pspace_aligned' \<sigma>; ksPSpace \<sigma> x = Some KOUserDataDevice\<rbrakk>
  \<Longrightarrow> ptr \<noteq> x"
  apply (rule ccontr,clarsimp)
  apply (frule(1) pspace_alignedD')
  apply (clarsimp simp: pointerInDeviceData_def objBits_simps typ_at'_def ko_wp_at'_def)
  apply (frule(1) pspace_distinctD')
  apply (clarsimp simp: objBits_simps)
  done

lemma userDataSeperate:
  "\<lbrakk>\<not> pointerInUserData ptr \<sigma>; pspace_distinct' \<sigma>; pspace_aligned' \<sigma>; ksPSpace \<sigma> x = Some KOUserData\<rbrakk>
  \<Longrightarrow> ptr \<noteq> x"
  apply (rule ccontr,clarsimp)
  apply (frule(1) pspace_alignedD')
  apply (clarsimp simp: pointerInUserData_def objBits_simps typ_at'_def ko_wp_at'_def)
  apply (frule(1) pspace_distinctD')
  apply (clarsimp simp: objBits_simps)
  done

lemma pointerInUserData_whole_word[simp]:
  "\<lbrakk>is_aligned ptr 3;  n < 8\<rbrakk> \<Longrightarrow> pointerInUserData (ptr + n) \<sigma> = pointerInUserData ptr \<sigma>"
  apply (simp add:pointerInUserData_def pageBits_def)
  apply (subst and_not_mask_twice[symmetric,where m = 12 and n =3,simplified])
  apply (simp add: neg_mask_add_aligned[where n=3,simplified])
  done

lemma pointerInDeviceData_whole_word[simp]:
  "\<lbrakk>is_aligned ptr 3;  n < 8\<rbrakk> \<Longrightarrow> pointerInDeviceData (ptr + n) \<sigma> = pointerInDeviceData ptr \<sigma>"
  apply (simp add:pointerInDeviceData_def pageBits_def)
  apply (subst and_not_mask_twice[symmetric,where m = 12 and n =3,simplified])
  apply (simp add: neg_mask_add_aligned[where n=3,simplified])
  done

lemma du_ptr_disjoint:
 "pointerInDeviceData ptr \<sigma> \<Longrightarrow> \<not> pointerInUserData ptr \<sigma>"
 "pointerInUserData ptr \<sigma> \<Longrightarrow> \<not> pointerInDeviceData ptr \<sigma>"
 by (auto simp: pointerInDeviceData_def pointerInUserData_def typ_at'_def ko_wp_at'_def)

lemma heap_to_device_data_seperate:
  "\<lbrakk> \<not> pointerInDeviceData ptr \<sigma>; pspace_distinct' \<sigma>; pspace_aligned' \<sigma>\<rbrakk>
      \<Longrightarrow> heap_to_device_data (ksPSpace \<sigma>) (fun_upd ms ptr a) x
      = heap_to_device_data (ksPSpace \<sigma>) ms x"
  apply (simp add : heap_to_device_data_def)
  apply (case_tac "map_to_user_data_device (ksPSpace \<sigma>) x")
   apply simp
  apply simp
  apply (clarsimp simp add: projectKO_opt_user_data_device map_comp_def
                     split: option.split_asm kernel_object.splits)
  apply (frule deviceDataSeperate)
   apply simp+
  apply (frule(1) pspace_alignedD')
  apply (simp add: objBits_simps)
  apply (rule ext)
  apply (subst AND_NOT_mask_plus_AND_mask_eq[symmetric,where n =3])
  apply (subst byte_to_word_heap_upd_neq[where n = "ptr && mask 3",simplified])
      apply (erule is_aligned_weaken,simp add:pageBits_def)
     apply simp+
   apply (clarsimp simp: pointerInDeviceData_def pageBits_def)
   apply (subst(asm) and_not_mask_twice[symmetric,where m = 12 and n =3,simplified])
   apply (drule sym[where t=" ptr && ~~ mask 3"])
   apply simp
   apply (subst(asm) neg_mask_add_aligned,assumption)
    apply (rule word_less_power_trans2[where k = 3,simplified])
      apply (simp add: pageBits_def)
      apply (rule less_le_trans[OF ucast_less],simp+)
    apply (clarsimp simp: typ_at'_def ko_wp_at'_def pageBits_def objBits_simps
                   dest!: pspace_distinctD')
    apply (rule word_and_less')
    apply (simp add:mask_def)
   apply simp
  done

lemma heap_to_user_data_seperate:
  "\<lbrakk> \<not> pointerInUserData ptr \<sigma>; pspace_distinct' \<sigma>; pspace_aligned' \<sigma>\<rbrakk>
      \<Longrightarrow> heap_to_user_data (ksPSpace \<sigma>) (fun_upd ms ptr a) x
      = heap_to_user_data (ksPSpace \<sigma>) ms x"
  apply (simp add : heap_to_user_data_def)
  apply (case_tac "map_to_user_data (ksPSpace \<sigma>) x")
   apply simp
  apply simp
  apply (clarsimp simp add: projectKO_opt_user_data map_comp_def
                     split: option.split_asm kernel_object.splits)
  apply (frule userDataSeperate)
   apply simp+
  apply (frule(1) pspace_alignedD')
  apply (simp add:objBits_simps)
  apply (rule ext)
  apply (subst AND_NOT_mask_plus_AND_mask_eq[symmetric,where n =3])
  apply (subst byte_to_word_heap_upd_neq[where n = "ptr && mask 3",simplified])
      apply (erule is_aligned_weaken, simp add: pageBits_def)
     apply simp+
   apply (clarsimp simp: pointerInUserData_def pageBits_def)
   apply (subst(asm) and_not_mask_twice[symmetric,where m = 12 and n =3,simplified])
   apply (drule sym[where t=" ptr && ~~ mask 3"])
   apply simp
   apply (subst(asm) neg_mask_add_aligned,assumption)
    apply (rule word_less_power_trans2[where k = 3,simplified])
      apply (simp add: pageBits_def)
      apply (rule less_le_trans[OF ucast_less],simp+)
    apply (clarsimp simp: typ_at'_def ko_wp_at'_def pageBits_def objBits_simps
                   dest!: pspace_distinctD')
    apply (rule word_and_less')
    apply (simp add:mask_def)
   apply simp
  done

lemma storeWordUser_rf_sr_upd':
  shows "\<forall>\<sigma> s.
   (\<sigma>, s) \<in> rf_sr \<and> pspace_aligned' \<sigma> \<and> pspace_distinct' \<sigma>
                   \<and> pointerInUserData ptr \<sigma> \<and> is_aligned ptr 3 \<longrightarrow>
   (\<sigma>\<lparr>ksMachineState := underlying_memory_update (\<lambda>m.
           m(ptr := word_rsplit (w::machine_word) ! 7, ptr + 1 := word_rsplit w ! 6,
             ptr + 2 := word_rsplit w ! 5, ptr + 3 := word_rsplit w ! 4,
             ptr + 4 := word_rsplit (w::machine_word) ! 3, ptr + 5 := word_rsplit w ! 2,
             ptr + 6 := word_rsplit w ! 1, ptr + 7 := word_rsplit w ! 0))
                   (ksMachineState \<sigma>)\<rparr>,
    s\<lparr>globals := globals s\<lparr>t_hrs_' := hrs_mem_update (heap_update (Ptr ptr) w) (t_hrs_' (globals s))\<rparr>\<rparr>) \<in> rf_sr"
  (is "\<forall>\<sigma> s. ?P \<sigma> s \<longrightarrow>
    (\<sigma>\<lparr>ksMachineState := ?ms \<sigma>\<rparr>,
     s\<lparr>globals := globals s\<lparr>t_hrs_' := ?ks' s\<rparr>\<rparr>) \<in> rf_sr")
proof (intro allI impI)
  fix \<sigma> s
  let ?thesis = "(\<sigma>\<lparr>ksMachineState := ?ms \<sigma>\<rparr>, s\<lparr>globals := globals s\<lparr>t_hrs_' := ?ks' s\<rparr>\<rparr>) \<in> rf_sr"
  let ?ms = "?ms \<sigma>"
  let ?ks' = "?ks' s"
  let ?ptr = "Ptr ptr :: machine_word ptr"
  let ?hp = "t_hrs_' (globals s)"

  assume "?P \<sigma> s"
  hence rf: "(\<sigma>, s) \<in> rf_sr" and al: "is_aligned ptr 3"
    and pal: "pspace_aligned' \<sigma>" and pdst: "pspace_distinct' \<sigma>"
    and piud: "pointerInUserData ptr \<sigma>"
    by simp_all

  define offset where "offset \<equiv> ucast ((ptr && mask pageBits) >> 3) :: 9 word"
  define base where "base \<equiv> Ptr (ptr && ~~ mask  pageBits) :: user_data_C ptr"

  from piud
  obtain old_w where
    old_w: "heap_to_user_data (ksPSpace \<sigma>) (underlying_memory (ksMachineState \<sigma>)) (ptr_val base) = Some old_w"
    apply (clarsimp simp: heap_to_user_data_def pointerInUserData_def Let_def)
    apply (drule user_data_at_ko)
    apply (drule ko_at_projectKO_opt)
    apply (simp add: base_def)
    done

  from rf
  obtain page :: user_data_C
    where page: "cslift s base = Some page"
    apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def cpspace_relation_def)
    apply (erule cmap_relationE1, rule old_w)
    apply simp
    done

  from page
  have page_def: "page = the (cslift s base)" by simp

  have size_td_list_map[rule_format, OF order_refl]:
    "\<And>f xs v S. set xs \<subseteq> S \<longrightarrow> (\<forall>x. x \<in> S \<longrightarrow> size_td_pair (f x) = v)
        \<longrightarrow> size_td_list (map f xs) = v * length xs"
    apply (induct_tac xs)
     apply simp_all
    done

  have user_data_upd:
    "\<And>A f v. heap_update base (user_data_C.words_C_update f v) =
            heap_update (ptr_coerce base) (f (user_data_C.words_C v))"
    apply (rule ext)
    apply (simp add: heap_update_def to_bytes_def)
    apply (simp add: user_data_C_typ_tag user_data_C_tag_def)
    apply (simp add: final_pad_def Let_def)
    apply (simp add: align_td_array' cong: if_cong)
    apply (simp add: ti_typ_pad_combine_def Let_def ti_typ_combine_def adjust_ti_def empty_typ_info_def size_td_array cong: if_cong)
    apply (simp add: padup_def)
    apply (simp add: typ_info_array')
    apply (simp add: size_of_def size_td_list_map)
    done

  have ud_split: "\<And>x z. user_data_C.words_C_update (\<lambda>_. x) z = user_data_C x"
    by (case_tac z, simp)

  have map_td_list_map:
    "\<And>f xs. map_td_list f xs = map (map_td_pair f) xs"
    by (induct_tac xs, simp_all)

  have update_ti_t_Cons_foo:
  "\<And>Cons upd adjs f v v'. \<lbrakk> v = Cons v'; \<And>a ys v. length ys = size_td_pair a
            \<Longrightarrow> update_ti_pair (map_td_pair f a) ys (Cons v) = Cons (update_ti_pair a ys v) \<rbrakk>
      \<Longrightarrow> \<forall>xs. update_ti_list_t (map_td_list f adjs) xs v
     = Cons (update_ti_list_t adjs xs v')"
    apply (simp add: update_ti_list_t_def split: if_split)
    apply (induct_tac adjs)
     apply simp
    apply clarsimp
    done

  note if_cong[cong]
  have hval:
    "\<And>hp. h_val hp base = user_data_C (h_val hp (ptr_coerce base))"
    apply (simp add: h_val_def base_def from_bytes_def)
    apply (simp add: user_data_C_typ_tag user_data_C_tag_def)
    apply (simp add: final_pad_def Let_def)
    apply (simp add: align_td_array' cong: if_cong)
    apply (simp add: ti_typ_pad_combine_def Let_def ti_typ_combine_def adjust_ti_def empty_typ_info_def size_td_array)
    apply (simp add: padup_def size_of_def typ_info_array' size_td_list_map)
    apply (simp add: map_td_list_map)
    apply (rule injD[where f=user_data_C.words_C])
     apply (rule injI)
     apply (case_tac x, case_tac y, simp)
    apply (simp add: map_td_list_map del: map_map)
    apply (rule trans, rule_tac acc=user_data_C.words_C
                          and f="map_td_pair (K (K (update_desc user_data_C (\<lambda>a b. user_data_C.words_C a))))"
                          in update_ti_t_acc_foo[rule_format])
      apply (clarsimp simp: map_td_list_map typ_info_word
                            adjust_ti_def update_desc_def)
     apply simp
    apply simp
    apply (simp add: update_ti_list_array'[where g="\<lambda>n. typ_info_t TYPE(machine_word)", OF refl]
                     typ_info_word adjust_ti_def update_desc_def)
    apply (rule Arrays.cart_eq[THEN iffD2], clarsimp)
    apply (subst index_fold_update | clarsimp)+
    apply (subst if_P, arith)+
    apply simp
    done

  from and_mask_less_size [of pageBits ptr]
  have ptr_mask_less: "ptr && mask pageBits >> 3 < 2^9"
    apply -
    apply (rule shiftr_less_t2n)
    apply (simp add: pageBits_def word_size)
    done
  hence uoffset:
    "unat offset = unat (ptr && mask pageBits >> 3)"
    apply (simp add: offset_def)
    apply (simp add: unat_ucast)
    apply (simp add: word_less_nat_alt)
    done

  have heap_upd:
    "heap_update ?ptr w =
    (\<lambda>hp. heap_update base (user_data_C.words_C_update (\<lambda>ws. Arrays.update ws (unat offset) w) (h_val hp base)) hp)"
    apply (rule ext)
    apply (subst user_data_upd)
    apply (subst hval)
    apply (unfold base_def uoffset)
    apply simp
    apply (subst heap_update_Array_element)
     apply (insert ptr_mask_less)[1]
     apply (simp add: word_less_nat_alt)
    apply (simp add: ptr_add_def word_shift_by_3 shiftr_shiftl1)
    apply (simp add: al is_aligned_andI1)
    apply (simp add: word_plus_and_or_coroll2 add.commute)
    done

  have x': "\<And>x::9 word. (ucast x * 8::machine_word) && ~~ mask pageBits = 0"
  proof -
    fix x::"9 word"
    have "ucast x * 8 = (ucast x << 3 :: machine_word)"
      by (simp add: shiftl_t2n)
    thus "?thesis x"
      apply simp
      apply (rule word_eqI)
      apply (clarsimp simp: word_size nth_shiftl word_ops_nth_size nth_ucast)
      apply (drule test_bit_size)
      apply (clarsimp simp: word_size pageBits_def)
      apply arith
      done
  qed

  have x: "\<And>(x::machine_word) (y::9 word).
    is_aligned x pageBits \<Longrightarrow> x + ucast y * 8 && ~~ mask pageBits = x"
    apply (subst mask_out_add_aligned [symmetric], assumption)
    apply (clarsimp simp: x')
    done

  from piud al
  have relrl: "cmap_relation (heap_to_user_data (ksPSpace \<sigma>)
                                 (underlying_memory (ksMachineState \<sigma>)))
                             (cslift s) Ptr cuser_user_data_relation
    \<Longrightarrow> cmap_relation
        (heap_to_user_data (ksPSpace \<sigma>)
          ((underlying_memory (ksMachineState \<sigma>))(
             ptr := word_rsplit (w::machine_word) ! 7, ptr + 1 := word_rsplit w ! 6,
             ptr + 2 := word_rsplit w ! 5, ptr + 3 := word_rsplit w ! 4,
             ptr + 4 := word_rsplit (w::machine_word) ! 3, ptr + 5 := word_rsplit w ! 2,
             ptr + 6 := word_rsplit w ! 1, ptr + 7 := word_rsplit w ! 0)))
        (\<lambda>y. if ptr_val y = (ptr_val ?ptr) && ~~ mask pageBits
             then Some (user_data_C.words_C_update
                         (\<lambda>ws. Arrays.update ws (unat (ucast ((ptr && mask pageBits) >> 3) :: 9 word)) w)
                         (the (cslift s y)))
             else cslift s y)
        Ptr cuser_user_data_relation"
    apply -
    apply (rule cmap_relationI)
     apply (clarsimp simp: dom_heap_to_user_data cmap_relation_def dom_if_Some
                   intro!: Un_absorb1 [symmetric])
     apply (clarsimp simp: pointerInUserData_def)
     apply (drule user_data_at_ko)
     apply (drule ko_at_projectKO_opt)
     apply (case_tac x)
     apply clarsimp
     apply fastforce
    apply clarsimp
    apply (case_tac "x = ptr && ~~ mask pageBits")
     apply (fastforce simp: heap_to_user_data_def Let_def user_data_relation_upd cmap_relation_def
                     dest: bspec)
    apply clarsimp
    apply (subgoal_tac "Some v = heap_to_user_data (ksPSpace \<sigma>)
                             (underlying_memory (ksMachineState \<sigma>)) x")
     apply (clarsimp simp: heap_to_user_data_def Let_def map_option_case
                    split: option.split_asm)
     apply (fastforce simp: cmap_relation_def dest: bspec)
    apply (clarsimp simp: heap_to_user_data_def Let_def)
    apply (frule (1) cmap_relation_cs_atD)
     apply simp
    apply clarsimp
    apply (drule map_to_ko_atI)
      apply (rule pal)
     apply (rule pdst)
    apply (subgoal_tac "is_aligned x pageBits")
     prefer 2
     apply (clarsimp simp: obj_at'_def objBits_simps simp: projectKOs)
    apply (subgoal_tac "is_aligned x 3")
     prefer 2
     apply (erule is_aligned_weaken)
     apply (simp add: pageBits_def)
    apply (rule ext)
    apply (subst byte_to_word_heap_upd_neq, assumption+, clarsimp simp: x, simp)+
    apply (subst byte_to_word_heap_upd_neq [where n=0, simplified], assumption+)
     apply (clarsimp simp: x)
    apply simp
    done

  have hrs_mem:
    "\<And>f hp'.
    hrs_mem_update (\<lambda>hp. heap_update base (f (h_val hp base)) hp) hp'
    = hrs_mem_update (heap_update base (f (h_val (hrs_mem hp') base))) hp'"
    by (simp add: hrs_mem_update_def split_def hrs_mem_def)

  from page
  have rl': "typ_uinfo_t TYPE(user_data_C) \<bottom>\<^sub>t typ_uinfo_t TYPE('t :: mem_type) \<Longrightarrow>
    (clift (hrs_mem_update (heap_update ?ptr w) (t_hrs_' (globals s))) :: ('t :: mem_type) typ_heap)
    = cslift s"
    apply (subst heap_upd)
    apply (subst hrs_mem)
    apply (simp add: typ_heap_simps clift_heap_update_same)
    done

  have subset: "{ptr..+ 2 ^ 3} \<subseteq> {ptr && ~~ mask pageBits ..+ 2 ^ pageBits}"
    apply (simp only: upto_intvl_eq al is_aligned_neg_mask2)
    apply (cut_tac ptr="ptr && ~~ mask pageBits" and x="ptr && mask pageBits"
      in aligned_range_offset_subset, rule is_aligned_neg_mask2)
       apply (rule is_aligned_andI1[OF al])
      apply (simp add: pageBits_def)
     apply (rule and_mask_less', simp add: pageBits_def)
     apply (erule order_trans[rotated])
    apply (simp add: mask_out_sub_mask)
    done

  hence zr: "\<And>rs. zero_ranges_are_zero rs (hrs_mem_update (heap_update ?ptr w) (t_hrs_' (globals s)))
        = zero_ranges_are_zero rs (t_hrs_' (globals s))"
    using page
    apply (clarsimp simp: zero_ranges_are_zero_def hrs_mem_update base_def
                          heap_update_def
          intro!: ball_cong[OF refl] conj_cong[OF refl])
    apply (drule region_actually_is_bytes)
    apply (frule(1) region_is_bytes_disjoint[rotated 2, OF h_t_valid_clift])
     apply simp
    apply (subst heap_list_update_disjoint_same, simp_all)
    apply ((subst Int_commute)?, erule disjoint_subset2[rotated])
    apply (simp add: pageBits_def)
    done

  have cmap_relation_heap_cong:
    "\<And>as cs cs' f rel. \<lbrakk> cmap_relation as cs f rel; cs = cs' \<rbrakk> \<Longrightarrow> cmap_relation as cs' f rel"
    by simp

  from rf have "cpspace_relation (ksPSpace \<sigma>) (underlying_memory (ksMachineState \<sigma>)) (t_hrs_' (globals s))"
    unfolding rf_sr_def cstate_relation_def by (simp add: Let_def)
  hence "cpspace_relation (ksPSpace \<sigma>) (underlying_memory ?ms) ?ks'"
    unfolding cpspace_relation_def using page
    apply -
    apply (clarsimp simp: rl' tag_disj_via_td_name)
    apply (drule relrl)
    apply (simp add: heap_upd)
    apply (subst hrs_mem)
    apply (simp add: base_def offset_def)
    apply (rule conjI)
     apply (erule cmap_relation_heap_cong)
     apply (simp add: typ_heap_simps')
     apply (rule ext)
     apply clarsimp
     apply (case_tac y)
     apply (clarsimp split: if_split)
    apply (rule cmap_relationI)
    apply (clarsimp simp: dom_heap_to_device_data cmap_relation_def dom_if_Some
                  intro!: Un_absorb1 [symmetric])
    using pal
    apply (subst(asm) heap_to_device_data_seperate)
      apply (simp add:piud al du_ptr_disjoint pal pdst)+
    apply (subst(asm) heap_to_device_data_seperate)
      apply (simp add:piud al du_ptr_disjoint pal pdst)+
    apply (subst(asm) heap_to_device_data_seperate)
      apply (simp add:piud al du_ptr_disjoint pal pdst)+
    apply (subst(asm) heap_to_device_data_seperate)
      apply (simp add:piud al du_ptr_disjoint pal pdst)+
    apply (subst(asm) heap_to_device_data_seperate)
      apply (simp add:piud al du_ptr_disjoint pal pdst)+
    apply (subst(asm) heap_to_device_data_seperate)
      apply (simp add:piud al du_ptr_disjoint pal pdst)+
    apply (subst(asm) heap_to_device_data_seperate)
      apply (simp add:piud al du_ptr_disjoint pal pdst)+
    apply (subst(asm) heap_to_device_data_seperate)
      apply (simp add:piud al du_ptr_disjoint pal pdst)+
    apply (erule cmap_relation_relI[where rel = cuser_user_data_device_relation])
     apply simp+
    done

  thus ?thesis using rf
    apply (simp add: rf_sr_def cstate_relation_def Let_def rl' tag_disj_via_td_name)
    apply (simp add: carch_state_relation_def cmachine_state_relation_def carch_globals_def)
    apply (simp add: rl' tag_disj_via_td_name zr)
    done
qed


lemma storeWordDevice_rf_sr_upd':
  shows "\<forall>\<sigma> s.
   (\<sigma>, s) \<in> rf_sr \<and> pspace_aligned' \<sigma> \<and> pspace_distinct' \<sigma>
                   \<and> pointerInDeviceData ptr \<sigma> \<and> is_aligned ptr 3 \<longrightarrow>
   (\<sigma>\<lparr>ksMachineState := underlying_memory_update (\<lambda>m.
           m(ptr := word_rsplit (w::machine_word) ! 7, ptr + 1 := word_rsplit w ! 6,
             ptr + 2 := word_rsplit w ! 5, ptr + 3 := word_rsplit w ! 4,
             ptr + 4 := word_rsplit (w::machine_word) ! 3, ptr + 5 := word_rsplit w ! 2,
             ptr + 6 := word_rsplit w ! 1, ptr + 7 := word_rsplit w ! 0))
                   (ksMachineState \<sigma>)\<rparr>,
    s\<lparr>globals := globals s\<lparr>t_hrs_' := hrs_mem_update (heap_update (Ptr ptr) w) (t_hrs_' (globals s))\<rparr>\<rparr>) \<in> rf_sr"
  (is "\<forall>\<sigma> s. ?P \<sigma> s \<longrightarrow>
    (\<sigma>\<lparr>ksMachineState := ?ms \<sigma>\<rparr>,
     s\<lparr>globals := globals s\<lparr>t_hrs_' := ?ks' s\<rparr>\<rparr>) \<in> rf_sr")
proof (intro allI impI)
  fix \<sigma> s
  let ?thesis = "(\<sigma>\<lparr>ksMachineState := ?ms \<sigma>\<rparr>, s\<lparr>globals := globals s\<lparr>t_hrs_' := ?ks' s\<rparr>\<rparr>) \<in> rf_sr"
  let ?ms = "?ms \<sigma>"
  let ?ks' = "?ks' s"
  let ?ptr = "Ptr ptr :: machine_word ptr"
  let ?hp = "t_hrs_' (globals s)"

  assume "?P \<sigma> s"
  hence rf: "(\<sigma>, s) \<in> rf_sr" and al: "is_aligned ptr 3"
    and pal: "pspace_aligned' \<sigma>" and pdst: "pspace_distinct' \<sigma>"
    and piud: "pointerInDeviceData ptr \<sigma>"
    by simp_all

  define offset where "offset \<equiv> ucast ((ptr && mask pageBits) >> 3) :: 9 word"
  define base where "base \<equiv> Ptr (ptr && ~~ mask  pageBits) :: user_data_device_C ptr"

  from piud
  obtain old_w where
    old_w: "heap_to_device_data (ksPSpace \<sigma>) (underlying_memory (ksMachineState \<sigma>)) (ptr_val base) = Some old_w"
    apply (clarsimp simp: heap_to_device_data_def pointerInDeviceData_def Let_def)
    apply (drule device_data_at_ko)
    apply (drule ko_at_projectKO_opt)
    apply (simp add: base_def)
    done

  from rf
  obtain page :: user_data_device_C
    where page: "cslift s base = Some page"
    apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def cpspace_relation_def)
    apply (erule cmap_relationE1, rule old_w)
    apply simp
    done

  from page
  have page_def: "page = the (cslift s base)" by simp

  have size_td_list_map[rule_format, OF order_refl]:
    "\<And>f xs v S. set xs \<subseteq> S \<longrightarrow> (\<forall>x. x \<in> S \<longrightarrow> size_td_pair (f x) = v)
        \<longrightarrow> size_td_list (map f xs) = v * length xs"
    apply (induct_tac xs)
     apply simp_all
    done

  have user_data_upd:
    "\<And>A f v. heap_update base (user_data_device_C.words_C_update f v) =
            heap_update (ptr_coerce base) (f (user_data_device_C.words_C v))"
    apply (rule ext)
    apply (simp add: heap_update_def to_bytes_def)
    apply (simp add: user_data_device_C_typ_tag user_data_device_C_tag_def)
    apply (simp add: final_pad_def Let_def)
    apply (simp add: align_td_array' cong: if_cong)
    apply (simp add: ti_typ_pad_combine_def Let_def ti_typ_combine_def adjust_ti_def empty_typ_info_def size_td_array cong: if_cong)
    apply (simp add: padup_def)
    apply (simp add: typ_info_array')
    apply (simp add: size_of_def size_td_list_map)
    done

  have ud_split: "\<And>x z. user_data_device_C.words_C_update (\<lambda>_. x) z = user_data_device_C x"
    by (case_tac z, simp)

  have map_td_list_map:
    "\<And>f xs. map_td_list f xs = map (map_td_pair f) xs"
    by (induct_tac xs, simp_all)

  have update_ti_t_Cons_foo:
  "\<And>Cons upd adjs f v v'. \<lbrakk> v = Cons v'; \<And>a ys v. length ys = size_td_pair a
            \<Longrightarrow> update_ti_pair (map_td_pair f a) ys (Cons v) = Cons (update_ti_pair a ys v) \<rbrakk>
      \<Longrightarrow> \<forall>xs. update_ti_list_t (map_td_list f adjs) xs v
     = Cons (update_ti_list_t adjs xs v')"
    apply (simp add: update_ti_list_t_def split: if_split)
    apply (induct_tac adjs)
     apply simp
    apply clarsimp
    done

  note if_cong[cong]
  have hval:
    "\<And>hp. h_val hp base = user_data_device_C (h_val hp (ptr_coerce base))"
    apply (simp add: h_val_def base_def from_bytes_def)
    apply (simp add: user_data_device_C_typ_tag user_data_device_C_tag_def)
    apply (simp add: final_pad_def Let_def)
    apply (simp add: align_td_array' cong: if_cong)
    apply (simp add: ti_typ_pad_combine_def Let_def ti_typ_combine_def adjust_ti_def empty_typ_info_def size_td_array)
    apply (simp add: padup_def size_of_def typ_info_array' size_td_list_map)
    apply (simp add: map_td_list_map)
    apply (rule injD[where f=user_data_device_C.words_C])
     apply (rule injI)
     apply (case_tac x, case_tac y, simp)
    apply (simp add: map_td_list_map del: map_map)
    apply (rule trans, rule_tac acc=user_data_device_C.words_C
                          and f="map_td_pair (K (K (update_desc user_data_device_C (\<lambda>a b. user_data_device_C.words_C a))))"
                          in update_ti_t_acc_foo[rule_format])
      apply (clarsimp simp: map_td_list_map typ_info_word
                            adjust_ti_def update_desc_def)
     apply simp
    apply simp
    apply (simp add: update_ti_list_array'[where g="\<lambda>n. typ_info_t TYPE(machine_word)", OF refl]
                     typ_info_word adjust_ti_def update_desc_def)
    apply (rule Arrays.cart_eq[THEN iffD2], clarsimp)
    apply (subst index_fold_update | clarsimp)+
    apply (subst if_P, arith)+
    apply simp
    done

  from and_mask_less_size [of pageBits ptr]
  have ptr_mask_less: "ptr && mask pageBits >> 3 < 2^9"
    apply -
    apply (rule shiftr_less_t2n)
    apply (simp add: pageBits_def word_size)
    done
  hence uoffset:
    "unat offset = unat (ptr && mask pageBits >> 3)"
    apply (simp add: offset_def)
    apply (simp add: unat_ucast)
    apply (simp add: word_less_nat_alt)
    done

  have heap_upd:
    "heap_update ?ptr w =
    (\<lambda>hp. heap_update base (user_data_device_C.words_C_update (\<lambda>ws. Arrays.update ws (unat offset) w) (h_val hp base)) hp)"
    apply (rule ext)
    apply (subst user_data_upd)
    apply (subst hval)
    apply (unfold base_def uoffset)
    apply simp
    apply (subst heap_update_Array_element)
     apply (insert ptr_mask_less)[1]
     apply (simp add: word_less_nat_alt)
    apply (simp add: ptr_add_def word_shift_by_3 shiftr_shiftl1)
    apply (simp add: al is_aligned_andI1)
    apply (simp add: word_plus_and_or_coroll2 add.commute)
    done

  have x': "\<And>x::9 word. (ucast x * 8::machine_word) && ~~ mask pageBits = 0"
  proof -
    fix x::"9 word"
    have "ucast x * 8 = (ucast x << 3 :: machine_word)"
      by (simp add: shiftl_t2n)
    thus "?thesis x"
      apply simp
      apply (rule word_eqI)
      apply (clarsimp simp: word_size nth_shiftl word_ops_nth_size nth_ucast)
      apply (drule test_bit_size)
      apply (clarsimp simp: word_size pageBits_def)
      apply arith
      done
  qed

  have x: "\<And>(x::machine_word) (y::9 word).
    is_aligned x pageBits \<Longrightarrow> x + ucast y * 8 && ~~ mask pageBits = x"
    apply (subst mask_out_add_aligned [symmetric], assumption)
    apply (clarsimp simp: x')
    done

  from piud al
  have relrl: "cmap_relation (heap_to_device_data (ksPSpace \<sigma>)
                                 (underlying_memory (ksMachineState \<sigma>)))
                             (cslift s) Ptr cuser_user_data_device_relation
    \<Longrightarrow> cmap_relation
        (heap_to_device_data (ksPSpace \<sigma>)
          ((underlying_memory (ksMachineState \<sigma>))(
             ptr := word_rsplit (w::machine_word) ! 7, ptr + 1 := word_rsplit w ! 6,
             ptr + 2 := word_rsplit w ! 5, ptr + 3 := word_rsplit w ! 4,
             ptr + 4 := word_rsplit (w::machine_word) ! 3, ptr + 5 := word_rsplit w ! 2,
             ptr + 6 := word_rsplit w ! 1, ptr + 7 := word_rsplit w ! 0)))
        (\<lambda>y. if ptr_val y = (ptr_val ?ptr) && ~~ mask pageBits
             then Some (user_data_device_C.words_C_update
                         (\<lambda>ws. Arrays.update ws (unat (ucast ((ptr && mask pageBits) >> 3) :: 9 word)) w)
                         (the (cslift s y)))
             else cslift s y)
        Ptr cuser_user_data_device_relation"
    apply -
    apply (rule cmap_relationI)
     apply (clarsimp simp: dom_heap_to_device_data cmap_relation_def dom_if_Some
                   intro!: Un_absorb1 [symmetric])
     apply (clarsimp simp: pointerInDeviceData_def)
     apply (drule device_data_at_ko)
     apply (drule ko_at_projectKO_opt)
     apply (case_tac x)
     apply clarsimp
     apply fastforce
    apply clarsimp
    apply (case_tac "x = ptr && ~~ mask pageBits")
     apply (fastforce simp: heap_to_device_data_def Let_def user_data_device_relation_upd cmap_relation_def
                     dest: bspec)
    apply clarsimp
    apply (subgoal_tac "Some v = heap_to_device_data (ksPSpace \<sigma>)
                             (underlying_memory (ksMachineState \<sigma>)) x")
     apply (clarsimp simp: heap_to_device_data_def Let_def map_option_case
                    split: option.split_asm)
     apply (fastforce simp: cmap_relation_def dest: bspec)
    apply (clarsimp simp: heap_to_device_data_def Let_def)
    apply (frule (1) cmap_relation_cs_atD)
     apply simp
    apply clarsimp
    apply (drule map_to_ko_atI)
      apply (rule pal)
     apply (rule pdst)
    apply (subgoal_tac "is_aligned x pageBits")
     prefer 2
     apply (clarsimp simp: obj_at'_def objBits_simps simp: projectKOs)
    apply (subgoal_tac "is_aligned x 3")
     prefer 2
     apply (erule is_aligned_weaken)
     apply (simp add: pageBits_def)
    apply (rule ext)
    apply (subst byte_to_word_heap_upd_neq, assumption+, clarsimp simp: x, simp)+
    apply (subst byte_to_word_heap_upd_neq [where n=0, simplified], assumption+)
     apply (clarsimp simp: x)
    apply simp
    done

  have hrs_mem:
    "\<And>f hp'.
    hrs_mem_update (\<lambda>hp. heap_update base (f (h_val hp base)) hp) hp'
    = hrs_mem_update (heap_update base (f (h_val (hrs_mem hp') base))) hp'"
    by (simp add: hrs_mem_update_def split_def hrs_mem_def)

  from page
  have rl': "typ_uinfo_t TYPE(user_data_device_C) \<bottom>\<^sub>t typ_uinfo_t TYPE('t :: mem_type) \<Longrightarrow>
    (clift (hrs_mem_update (heap_update ?ptr w) (t_hrs_' (globals s))) :: ('t :: mem_type) typ_heap)
    = cslift s"
    apply (subst heap_upd)
    apply (subst hrs_mem)
    apply (simp add: typ_heap_simps clift_heap_update_same)
    done

  have subset: "{ptr..+ 2 ^ 3} \<subseteq> {ptr && ~~ mask pageBits ..+ 2 ^ pageBits}"
    apply (simp only: upto_intvl_eq al is_aligned_neg_mask2)
    apply (cut_tac ptr="ptr && ~~ mask pageBits" and x="ptr && mask pageBits"
      in aligned_range_offset_subset, rule is_aligned_neg_mask2)
       apply (rule is_aligned_andI1[OF al])
      apply (simp add: pageBits_def)
     apply (rule and_mask_less', simp add: pageBits_def)
     apply (erule order_trans[rotated])
    apply (simp add: mask_out_sub_mask)
    done

  hence zr: "\<And>rs. zero_ranges_are_zero rs (hrs_mem_update (heap_update ?ptr w) (t_hrs_' (globals s)))
        = zero_ranges_are_zero rs (t_hrs_' (globals s))"
    using page
    apply (clarsimp simp: zero_ranges_are_zero_def hrs_mem_update base_def
                          heap_update_def
          intro!: ball_cong[OF refl] conj_cong[OF refl])
    apply (drule region_actually_is_bytes)
    apply (frule(1) region_is_bytes_disjoint[rotated 2, OF h_t_valid_clift])
     apply simp
    apply (subst heap_list_update_disjoint_same, simp_all)
    apply ((subst Int_commute)?, erule disjoint_subset2[rotated])
    apply (simp add: pageBits_def)
    done

  have cmap_relation_heap_cong:
    "\<And>as cs cs' f rel. \<lbrakk> cmap_relation as cs f rel; cs = cs' \<rbrakk> \<Longrightarrow> cmap_relation as cs' f rel"
    by simp

  from rf have "cpspace_relation (ksPSpace \<sigma>) (underlying_memory (ksMachineState \<sigma>)) (t_hrs_' (globals s))"
    unfolding rf_sr_def cstate_relation_def by (simp add: Let_def)
  hence "cpspace_relation (ksPSpace \<sigma>) (underlying_memory ?ms) ?ks'"
    unfolding cpspace_relation_def using page
    apply -
    apply (clarsimp simp: rl' tag_disj_via_td_name)
    apply (drule relrl)
    apply (simp add: heap_upd)
    apply (subst hrs_mem)
    apply (simp add: base_def offset_def)
    apply (rule conjI[rotated])
     apply (erule cmap_relation_heap_cong)
     apply (simp add: typ_heap_simps')
     apply (rule ext)
     apply clarsimp
     apply (case_tac y)
     apply (clarsimp split: if_split)
    apply (rule cmap_relationI)
    apply (clarsimp simp: dom_heap_to_user_data cmap_relation_def dom_if_Some
                   intro!: Un_absorb1 [symmetric])
    using pal
    apply (subst(asm) heap_to_user_data_seperate)
      apply (simp add: piud al du_ptr_disjoint pal pdst)+
    apply (subst(asm) heap_to_user_data_seperate)
      apply (simp add: piud al du_ptr_disjoint pal pdst)+
    apply (subst(asm) heap_to_user_data_seperate)
      apply (simp add: piud al du_ptr_disjoint pal pdst)+
    apply (subst(asm) heap_to_user_data_seperate)
      apply (simp add: piud al du_ptr_disjoint pal pdst)+
    apply (subst(asm) heap_to_user_data_seperate)
      apply (simp add: piud al du_ptr_disjoint pal pdst)+
    apply (subst(asm) heap_to_user_data_seperate)
      apply (simp add: piud al du_ptr_disjoint pal pdst)+
    apply (subst(asm) heap_to_user_data_seperate)
      apply (simp add: piud al du_ptr_disjoint pal pdst)+
    apply (subst(asm) heap_to_user_data_seperate)
      apply (simp add: piud al du_ptr_disjoint pal pdst)+
    apply (erule cmap_relation_relI[where rel = cuser_user_data_relation])
     apply simp+
    done

  thus ?thesis using rf
    apply (simp add: rf_sr_def cstate_relation_def Let_def rl' tag_disj_via_td_name)
    apply (simp add: carch_state_relation_def cmachine_state_relation_def carch_globals_def)
    apply (simp add: rl' tag_disj_via_td_name zr)
    done
qed

lemma storeWord_rf_sr_upd:
  "\<lbrakk> (\<sigma>, s) \<in> rf_sr; pspace_aligned' \<sigma>;  pspace_distinct' \<sigma>;
     pointerInUserData ptr \<sigma> \<or> pointerInDeviceData ptr \<sigma>; is_aligned ptr 3\<rbrakk> \<Longrightarrow>
   (\<sigma>\<lparr>ksMachineState := underlying_memory_update (\<lambda>m.
           m(ptr := word_rsplit (w::machine_word) ! 7, ptr + 1 := word_rsplit w ! 6,
             ptr + 2 := word_rsplit w ! 5, ptr + 3 := word_rsplit w ! 4,
             ptr + 4 := word_rsplit (w::machine_word) ! 3, ptr + 5 := word_rsplit w ! 2,
             ptr + 6 := word_rsplit w ! 1, ptr + 7 := word_rsplit w ! 0))
                   (ksMachineState \<sigma>)\<rparr>,
    globals_update (t_hrs_'_update (hrs_mem_update
                    (heap_update (Ptr ptr) w))) s) \<in> rf_sr"
  apply (elim disjE)
   apply (cut_tac storeWordUser_rf_sr_upd' [rule_format, where s=s and \<sigma>=\<sigma>])
    prefer 2
    apply fastforce
   apply simp
   apply (erule iffD1 [OF rf_sr_upd, rotated -1], simp_all)[1]
  apply (cut_tac storeWordDevice_rf_sr_upd' [rule_format, where s=s and \<sigma>=\<sigma>])
   prefer 2
   apply fastforce
  apply simp
  apply (erule iffD1 [OF rf_sr_upd, rotated -1], simp_all)[1]
  done

(* The following should be also true for pointerInDeviceData,
   but the reason why it is true is different *)
lemma storeByteUser_rf_sr_upd:
  assumes asms: "(\<sigma>, s) \<in> rf_sr" "pspace_aligned' \<sigma>" "pspace_distinct' \<sigma>"
                "pointerInUserData ptr \<sigma>"
  shows "(ksMachineState_update (underlying_memory_update (\<lambda>m. m(ptr := b))) \<sigma>,
          globals_update (t_hrs_'_update (hrs_mem_update (\<lambda>m. m(ptr := b)))) s)
         \<in> rf_sr"
proof -
  have horrible_helper:
    "\<And>v p. v \<le> 7 \<Longrightarrow> (7 - unat (p && mask 3 :: machine_word) = v) =
                     (p && mask 3 = 7 - of_nat v)"
    apply (simp add: unat_arith_simps unat_of_nat)
    apply (cut_tac p=p in unat_mask_3_less_8)
    apply arith
    done

  have horrible_helper2:
    "\<And>n x p. n < 8 \<Longrightarrow> (unat (x - p :: machine_word) = n) = (x = (p + of_nat n))"
    apply (subst unat64_eq_of_nat)
     apply (simp add:word_bits_def)
    apply (simp only:field_simps)
    done

  from asms
  show ?thesis
    apply (frule_tac ptr="ptr && ~~ mask 3"
                 and w="word_rcat (list_update
                                    (map (underlying_memory (ksMachineState \<sigma>))
                                      [(ptr && ~~ mask 3) + 7,
                                       (ptr && ~~ mask 3) + 6,
                                       (ptr && ~~ mask 3) + 5,
                                       (ptr && ~~ mask 3) + 4,
                                       (ptr && ~~ mask 3) + 3,
                                       (ptr && ~~ mask 3) + 2,
                                       (ptr && ~~ mask 3) + 1,
                                       (ptr && ~~ mask 3)])
                                    (7 - unat (ptr && mask 3)) b)"
                  in storeWord_rf_sr_upd)
        apply simp+
      apply (simp add: pointerInUserData_def pointerInDeviceData_def mask_lower_twice pageBits_def)
     apply (simp add: Aligned.is_aligned_neg_mask)
    apply (erule iffD1[rotated],
           rule_tac f="\<lambda>a b. (a, b) \<in> rf_sr" and c="globals_update f s"
                 for f s in arg_cong2)
     apply (rule kernel_state.fold_congs[OF refl refl], simp only:)
     apply (rule machine_state.fold_congs[OF refl refl], simp only:)
     apply (cut_tac p=ptr in unat_mask_3_less_8)
     apply (simp del: list_update.simps
                 add: word_rsplit_rcat_size word_size nth_list_update
                      horrible_helper)
     apply (subgoal_tac "(ptr && ~~ mask 3) + (ptr && mask 3) = ptr")
      apply (subgoal_tac "(ptr && mask 3) \<in> {0, 1, 2, 3,4,5,6,7}")
       subgoal by (auto split: if_split simp: fun_upd_idem) (* long *)
      apply (simp add: word_unat.Rep_inject[symmetric]
                  del: word_unat.Rep_inject)
      apply arith
     apply (subst add.commute, rule word_plus_and_or_coroll2)
    apply (rule StateSpace.state.fold_congs[OF refl refl])
    apply (rule globals.fold_congs[OF refl refl])
    apply (clarsimp simp: hrs_mem_update_def simp del: list_update.simps)
    apply (rule ext)
    apply (simp add: heap_update_def to_bytes_def typ_info_word
                     word_rsplit_rcat_size word_size heap_update_list_value'
                     nth_list_update nth_rev TWO
                del: list_update.simps)
    apply (subgoal_tac "length (rev ([underlying_memory (ksMachineState \<sigma>)
                                        ((ptr && ~~ mask 2) + 7),
                                      underlying_memory (ksMachineState \<sigma>)
                                        ((ptr && ~~ mask 2) + 6),
                                      underlying_memory (ksMachineState \<sigma>)
                                        ((ptr && ~~ mask 2) + 5),
                                      underlying_memory (ksMachineState \<sigma>)
                                        ((ptr && ~~ mask 2) + 4),
                                      underlying_memory (ksMachineState \<sigma>)
                                        ((ptr && ~~ mask 2) + 3),
                                      underlying_memory (ksMachineState \<sigma>)
                                        ((ptr && ~~ mask 2) + 2),
                                      underlying_memory (ksMachineState \<sigma>)
                                        ((ptr && ~~ mask 2) + 1),
                                      underlying_memory (ksMachineState \<sigma>)
                                        (ptr && ~~ mask 2)]
                                     [3 - unat (ptr && mask 2) := b]))
                        < addr_card")
     prefer 2
     apply (simp add: addr_card del: list_update.simps)
    apply (simp add: heap_update_def to_bytes_def typ_info_word
                     word_rsplit_rcat_size word_size heap_update_list_value'
                     nth_list_update nth_rev TWO
                del: list_update.simps   cong: if_cong)
    apply (simp only: If_rearrage)
    apply (subgoal_tac "P" for P)
     apply (rule if_cong)
       apply assumption
      apply simp
     apply (clarsimp simp: nth_list_update split: if_split)
     apply (frule_tac ptr=x in memory_cross_over, simp+)
      apply (clarsimp simp: pointerInUserData_def pointerInDeviceData_def)
      apply (cut_tac p="ptr && ~~ mask 3" and n=3 and d="x - (ptr && ~~ mask 3)"
                  in is_aligned_add_helper)
        apply (simp add: Aligned.is_aligned_neg_mask)
       apply (simp add: word_less_nat_alt)
      apply clarsimp
      apply (cut_tac x=x in mask_lower_twice[where n=3 and m=pageBits])
       apply (simp add: pageBits_def)
      apply (cut_tac x=ptr in mask_lower_twice[where n=3 and m=pageBits])
       apply (simp add: pageBits_def)
      apply simp
     apply (auto simp add: eval_nat_numeral horrible_helper2 take_bit_Suc simp del: unsigned_numeral
                 elim!: less_SucE)[1]
    apply (rule iffI)
     apply clarsimp
     apply (cut_tac p=ptr in unat_mask_3_less_8)
     apply (subgoal_tac "unat (x - (ptr && ~~ mask 3)) = unat (ptr && mask 3)")
      prefer 2
      apply arith
     apply (simp add: unat_mask_3_less_8 field_simps word_plus_and_or_coroll2)
    apply (simp add: subtract_mask TWO unat_mask_3_less_8)
    done
qed

lemma storeWord_ccorres':
  "ccorres dc xfdc
     (pspace_aligned' and pspace_distinct' and
               K (is_aligned ptr 3) and (\<lambda>s. pointerInUserData ptr s \<or> pointerInDeviceData ptr s))
     (UNIV \<inter> {s. ptr' s = Ptr ptr} \<inter> {s. c_guard (ptr' s)} \<inter> {s. val' s = val}) hs
     (doMachineOp $ storeWord ptr val)
     (Basic (\<lambda>s. globals_update (t_hrs_'_update
           (hrs_mem_update (heap_update (ptr' s) (val' s)))) s))"
  supply if_cong[cong]
  apply (clarsimp simp: storeWordUser_def)
  apply (rule ccorres_from_vcg_nofail)
  apply (rule allI)
  apply (rule conseqPre, vcg)
  apply (clarsimp split: if_split_asm)
  apply (rule bexI[rotated])
   apply (subst in_doMachineOp)
   apply (fastforce simp: storeWord_def in_monad is_aligned_mask)
  apply (simp add: upto0_7_def)
  apply (fold fun_upd_def One_nat_def)+
  apply (fastforce elim: storeWord_rf_sr_upd)
  done

lemma storeWord_ccorres:
  "ccorres dc xfdc
     (valid_pspace' and K (is_aligned ptr 3) and pointerInUserData ptr)
     (UNIV \<inter> {s. ptr' s = Ptr ptr} \<inter> {s. c_guard (ptr' s)} \<inter> {s. val' s = val}) hs
     (doMachineOp $ storeWord ptr val)
     (Basic (\<lambda>s. globals_update (t_hrs_'_update
           (hrs_mem_update (heap_update (ptr' s) (val' s)))) s))"
  apply (rule ccorres_guard_imp2, rule storeWord_ccorres')
  apply fastforce
  done

lemma pointerInUserData_c_guard:
  "\<lbrakk> valid_pspace' s; pointerInUserData ptr s  \<or> pointerInDeviceData ptr s ; is_aligned ptr 3 \<rbrakk>
   \<Longrightarrow> c_guard (Ptr ptr :: machine_word ptr)"
  apply (simp add: pointerInUserData_def pointerInDeviceData_def)
  apply (simp add: c_guard_def ptr_aligned_def is_aligned_def c_null_guard_def)
  apply (fold is_aligned_def [where n=3, simplified])[1]
  apply (rule contra_subsetD)
   apply (rule order_trans [rotated])
    apply (rule_tac x="ptr && mask pageBits" and y=8 and z=4096 in intvl_sub_offset)
    apply (cut_tac y=ptr and a="mask pageBits && (~~ mask 3)" in word_and_le1)
    apply (subst(asm) word_bw_assocs[symmetric], subst(asm) is_aligned_neg_mask_eq,
           erule is_aligned_andI1)
    apply (simp add: word_le_nat_alt mask_def pageBits_def)
   apply (subst word_plus_and_or_coroll2 [where w="~~ mask pageBits", simplified])
   apply simp
  apply (fastforce dest: intvl_le_lower
                 intro: is_aligned_no_overflow' [where n=12, simplified]
                        is_aligned_andI2
                  simp: mask_def pageBits_def is_aligned_def word_bits_def)
  done

lemma pointerInUserData_h_t_valid:
  "\<lbrakk> valid_pspace' s; pointerInUserData ptr s ;
       is_aligned ptr 3; (s, s') \<in> rf_sr \<rbrakk>
      \<Longrightarrow> hrs_htd (t_hrs_' (globals s')) \<Turnstile>\<^sub>t (Ptr ptr :: machine_word ptr)"
  apply (frule_tac p=ptr in
     user_word_at_cross_over[rotated, OF _ refl])
   apply (simp add: user_word_at_def)
  apply simp
  done

lemma storeWordUser_ccorres:
  "ccorres dc xfdc (valid_pspace' and (\<lambda>_. is_aligned ptr 3))
              (UNIV \<inter> {s. ptr' s = Ptr ptr} \<inter> {s. w' s = w}) hs
      (storeWordUser ptr w)
      (Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t \<acute>(\<lambda>s. ptr' s)\<rbrace>
          (Basic (\<lambda>s. globals_update (t_hrs_'_update
           (hrs_mem_update (heap_update (ptr' s) (w' s)))) s)))"
  apply (simp add: storeWordUser_def)
  apply (rule ccorres_symb_exec_l'[OF _ stateAssert_inv stateAssert_sp empty_fail_stateAssert])
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_Guard)
   apply (rule storeWord_ccorres[unfolded fun_app_def])
  apply (clarsimp simp: pointerInUserData_c_guard pointerInUserData_h_t_valid)
  done

end

end
