(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory FieldAccessors
  imports
    Lib.Lib
    CParser.LemmaBucket_C
begin

lemma h_val_mono:
  "\<lbrakk> field_lookup (typ_info_t TYPE('a)) f 0 = Some tp;
      h_val hp (p::'a::mem_type ptr) = v;
      export_uinfo (fst tp) = typ_uinfo_t TYPE('b) \<rbrakk> \<Longrightarrow>
          h_val hp (Ptr (&(p\<rightarrow>f))::'b::mem_type ptr) = (from_bytes (access_ti\<^sub>0 (fst tp) v))"
  using lift_t_mono[where p=p and f=f and v=v and g="\<lambda>_. True" and g'="\<lambda>_. True"
                        and t="fst tp" and n="snd tp" and 'b='b
                        and s="(hp, ptr_retyp p undefined)"]
  by (simp add: lift_t_if ptr_retyp_h_t_valid split: if_split_asm)

lemma h_val_mono_to_field_rewrite:
  "\<lbrakk> field_lookup (typ_info_t TYPE('a)) [s] 0
        \<equiv> field_lookup (adjust_ti (typ_info_t TYPE('b)) f upds) [] n;
      export_uinfo (adjust_ti (typ_info_t TYPE('b)) f upds)
        = export_uinfo (typ_info_t TYPE('b)) \<rbrakk>
    \<Longrightarrow> from_bytes (access_ti\<^sub>0 (adjust_ti (typ_info_t TYPE('b)) f upds)
               (h_val hp (p::'a::mem_type ptr)))
         = h_val hp (Ptr (&(p\<rightarrow>[s]))::'b::mem_type ptr)"
  by (simp add: h_val_mono typ_uinfo_t_def)

lemma heap_list_rotate:
  "heap_list (\<lambda>x. hp (x + offs)) n p
     = heap_list hp n (p + offs)"
  by (induct n arbitrary: p, simp_all add: field_simps)

lemma heap_update_list_rotate:
  "heap_update_list p xs (\<lambda>x. hp (x + offs))
     = (\<lambda>x. heap_update_list (p + offs) xs hp (x + offs))"
  apply (induct xs arbitrary: p hp, simp_all)
  apply (erule_tac x="p + 1" in meta_allE)
  apply (simp add: field_simps)
  apply (erule meta_allE, erule trans[rotated])
  apply (simp add: fun_upd_def)
  done

lemma heap_update_rotate:
  "heap_update p v hp
    = (\<lambda>x. (heap_update q v (\<lambda>x. hp (x + (ptr_val p - ptr_val q))))
             (x + (ptr_val q - ptr_val p)))"
  by (simp add: heap_update_def heap_list_rotate
                heap_update_list_rotate)

lemma c_guard_align_of:
  "\<lbrakk> align_of TYPE('a :: c_type) + size_of TYPE('a) < 2 ^ word_bits; align_of TYPE('a) \<noteq> 0 \<rbrakk> \<Longrightarrow>
   c_guard (Ptr (of_nat (align_of TYPE('a))) :: 'a ptr)"
  unfolding c_guard_def
  supply word_neq_0_conv[simp del]
  apply (simp add: ptr_aligned_def unat_of_nat c_null_guard_def)
  apply (clarsimp simp: intvl_def word_bits_conv take_bit_nat_eq_self)
  apply (drule trans[rotated], rule sym, rule Abs_fnat_hom_add)
  apply (subst(asm) of_nat_neq_0, simp_all)
  done

lemma heap_update_field2:
  "\<lbrakk> field_ti TYPE('a :: packed_type) f = Some t;
     align_of TYPE('a) + size_of TYPE('a) < 2 ^ word_bits; align_of TYPE('a) \<noteq> 0;
     export_uinfo t = export_uinfo (typ_info_t TYPE('b :: packed_type))\<rbrakk>
   \<Longrightarrow> heap_update (Ptr &(p\<rightarrow>f)) (v :: 'b) hp =
       heap_update p (update_ti t (to_bytes_p v) (h_val hp p)) hp"
  apply (rule trans,
         rule_tac q="Ptr &(Ptr (of_nat (align_of TYPE('a))) \<rightarrow> f)"
            in heap_update_rotate)
  apply (rule trans[rotated], rule sym,
         rule_tac q="Ptr (of_nat (align_of TYPE('a)))" in heap_update_rotate)
  apply (erule field_ti_field_lookupE)
  apply (subst packed_heap_super_field_update, assumption,
         simp_all add: typ_uinfo_t_def)
   apply (simp add: c_guard_align_of)
  apply (simp add: h_val_def heap_list_rotate)
  apply (simp add: field_lvalue_def field_simps)
  done

lemma final_pad_id:
  "padup (2 ^ align_td tp) (size_td tp) = 0 \<Longrightarrow> final_pad tp = tp"
  by (simp add: final_pad_def)

lemma ti_typ_pad_combine_ti_typ_combine:
  "padup (align_of TYPE('a :: c_type)) (size_td tag) = 0
      \<Longrightarrow> ti_typ_pad_combine (t_b :: 'a itself) f_ab f_upd_ab fn tag
         = ti_typ_combine t_b f_ab f_upd_ab fn tag"
  by (simp add: ti_typ_pad_combine_def)

lemma field_access_take_drop_general:
  "\<forall>s m n f bs. field_lookup t f m = Some (s,n) \<longrightarrow> wf_fd t \<longrightarrow>
      length bs = size_td t \<longrightarrow>
      take (size_td s) (drop (n - m) (access_ti t v bs)) =
        access_ti s v (take (size_td s) (drop (n - m) bs))"
  "\<forall>s m n f bs. field_lookup_struct st f m = Some (s,n) \<longrightarrow> wf_fd_struct st \<longrightarrow>
      length bs = size_td_struct st \<longrightarrow>
      take (size_td s) (drop (n - m) (access_ti_struct st v bs)) =
        access_ti s v (take (size_td s) (drop (n - m) bs))"
  "\<forall>s m n f bs. field_lookup_list ts f m = Some (s,n) \<longrightarrow> wf_fd_list ts \<longrightarrow>
      length bs = size_td_list ts \<longrightarrow>
      take (size_td s) (drop (n - m) (access_ti_list ts v bs)) =
        access_ti s v (take (size_td s) (drop (n - m) bs))"
  "\<forall>s m n f bs. field_lookup_pair x f m = Some (s,n) \<longrightarrow> wf_fd_pair x \<longrightarrow>
      length bs = size_td_pair x \<longrightarrow>
      take (size_td s) (drop (n - m) (access_ti_pair x v bs)) =
        access_ti s v (take (size_td s) (drop (n - m) bs))"
 apply (induct t and st and ts and x)
       apply auto[4]
    apply(thin_tac "All P" for P)+
    apply(drule wf_fd_cons_structD)
    apply(clarsimp simp: fd_cons_struct_def fd_cons_desc_def fd_cons_length_def)
   apply simp
   apply(clarsimp simp: min_def)?
   apply(frule wf_fd_cons_pairD)
   apply(clarsimp simp: fd_cons_pair_def fd_cons_desc_def fd_cons_length_def)
   apply(clarsimp split: option.splits)
    apply(subst drop_all)
     apply clarsimp
     apply(drule field_lookup_offset_le, clarsimp)
     apply(case_tac dt_pair)
     apply(clarsimp simp: fd_cons_length_def)
     apply arith
    apply simp
    apply(rotate_tac -3)
    apply(drule_tac x=s in spec)
    apply(drule_tac x="m + size_td (dt_fst dt_pair)" in spec)
    apply(drule_tac x=n in spec)
    apply(erule impE)
     apply fast
    apply(subgoal_tac "(size_td_pair dt_pair - (n - m)) = 0")
     apply simp
     apply(case_tac dt_pair, simp)
     apply(drule field_lookup_offset_le, clarsimp)
    apply(case_tac dt_pair, simp)
    apply(drule field_lookup_offset_le, clarsimp)
    apply simp
   apply(subgoal_tac "(size_td s - (size_td_pair dt_pair - (n - m))) = 0")
    prefer 2
    apply clarsimp
    apply(drule td_set_pair_field_lookup_pairD)
    apply(drule td_set_pair_offset_size_m)
    apply simp
   apply simp
   apply(drule_tac x=s in spec)
   apply(drule_tac x=m in spec)
   apply(drule_tac x=n in spec)
   apply(drule mp, fast)
   apply(frule(1) wf_fd_field_lookup)
   apply (case_tac "size_td s = 0")
    apply (simp add: ex_with_length)
   apply(rule trans, drule spec, erule mp)
    apply simp
   apply(simp add: take_drop)
  apply auto
  done

lemma field_lookup_to_bytes:
  "\<lbrakk> field_lookup (typ_info_t TYPE('a :: mem_type)) f 0
        \<equiv> Some (adjust_ti (typ_info_t TYPE('b :: mem_type)) accsr
           (updtr \<circ> (\<lambda>x _. x)),
          n);
        size_of TYPE('a) = length bs \<rbrakk>
    \<Longrightarrow> take (size_of TYPE('b)) (drop n (to_bytes v bs))
        = to_bytes (accsr v) (take (size_of TYPE ('b)) (drop n bs))"
  apply (drule meta_eq_to_obj_eq)
  apply (simp add: to_bytes_def)
  apply (frule_tac v=v and bs="bs"
    in field_access_take_drop_general(1)[rule_format])
    apply (simp add: size_of_def)+
  done

lemma field_lookup_to_bytes_split:
  "\<lbrakk> field_lookup (typ_info_t TYPE('a :: mem_type)) f 0
        \<equiv> Some (adjust_ti (typ_info_t TYPE('b :: mem_type)) accsr
           (updtr \<circ> (\<lambda>x _. x)), n);
        m = n + size_of TYPE('b) \<rbrakk>
    \<Longrightarrow> drop n (to_bytes v (heap_list hp (size_of TYPE('a)) addr))
        = to_bytes (accsr v) (heap_list hp (size_of TYPE ('b)) (addr + of_nat n))
            @ drop m (to_bytes v (heap_list hp (size_of TYPE('a)) addr))"
  apply clarsimp
  apply (rule trans, rule_tac n="size_of TYPE('b)" in append_take_drop_id[symmetric])
  apply (rule arg_cong2[where f=append])
   apply (rule trans, rule field_lookup_to_bytes, simp+)
   apply (drule field_lookup_offset_size[OF meta_eq_to_obj_eq])
   apply (simp add: drop_heap_list_le take_heap_list_le size_of_def)
  apply (simp add: add.commute)
  done

lemma field_lookup_to_bytes_split_step:
  "\<lbrakk> to_bytes v (heap_list hp (size_of TYPE('a)) addr)
            = xs @ drop n (to_bytes v (heap_list hp (size_of TYPE('a)) addr));
        field_lookup (typ_info_t TYPE('a :: mem_type)) f 0
            \<equiv> Some (adjust_ti (typ_info_t TYPE('b :: mem_type)) accsr
                (updtr \<circ> (\<lambda>x _. x)), n);
        m = n + size_of TYPE('b) \<rbrakk>
    \<Longrightarrow> to_bytes v (heap_list hp (size_of TYPE('a)) addr)
        = (xs @ to_bytes (accsr v) (heap_list hp (size_of TYPE ('b)) (addr + of_nat n)))
            @ drop m (to_bytes v (heap_list hp (size_of TYPE('a)) addr))"
  by (simp add: field_lookup_to_bytes_split)

lemma field_lookup_to_bytes_split_init:
  "to_bytes v (heap_list hp (size_of TYPE('a :: c_type)) addr)
            = [] @ drop 0 (to_bytes v (heap_list hp (size_of TYPE('a)) addr))"
  by simp

lemma to_bytes_array:
  "length xs = (size_of TYPE('a :: c_type) * CARD('b :: finite))
    \<Longrightarrow> to_bytes (v :: 'a['b]) xs
        = concat (map (\<lambda>i. to_bytes (index v i) (take (size_of TYPE('a))
            (drop (size_of TYPE('a) * i) xs))) [0 ..< CARD ('b)])"
  apply (simp add: to_bytes_def typ_info_array'
                   foldl_conv_concat[where xs=Nil, simplified, symmetric])
  apply (subst fcp_eta[where g=v, symmetric], rule access_ti_list_array)
    apply simp
   apply (simp add: size_of_def)
  apply (clarsimp simp: size_of_def)
  done

lemma take_heap_list_min:
  "take n (heap_list hp m addr) = heap_list hp (min n m) addr"
  by (simp add: min_def take_heap_list_le)

lemma drop_heap_list_general:
  "drop n (heap_list hp m addr) = heap_list hp (m - n) (addr + of_nat n)"
  apply (cases "n \<le> m")
   apply (simp_all add: drop_heap_list_le)
  done

lemma heap_update_mono_to_field_rewrite:
  "\<lbrakk> field_lookup (typ_info_t TYPE('a)) [s] 0
        \<equiv> field_lookup (adjust_ti (typ_info_t TYPE('b)) f upds) [] n;
      export_uinfo (adjust_ti (typ_info_t TYPE('b)) f upds)
        = export_uinfo (typ_info_t TYPE('b));
      align_of TYPE('a) + size_of TYPE('a) < 2 ^ word_bits; align_of TYPE('a) \<noteq> 0 \<rbrakk>
    \<Longrightarrow> heap_update (p::'a::packed_type ptr)
           (update_ti_t (adjust_ti (typ_info_t TYPE('b)) f upds) (to_bytes_p v)
               str) hp
         = heap_update (Ptr (&(p\<rightarrow>[s]))::'b::packed_type ptr) v (heap_update p str hp)"
  by (simp add: typ_uinfo_t_def heap_update_field2
                packed_heap_update_collapse h_val_heap_update
                field_ti_def update_ti_t_def size_of_def)

ML \<open>
fun get_field_h_val_rewrites lthy =
  (simpset_of lthy |> dest_ss |> #simps |> map snd
    |> map (Thm.transfer (Proof_Context.theory_of lthy))
               RL @{thms h_val_mono_to_field_rewrite
                         heap_update_mono_to_field_rewrite[
                            unfolded align_of_def size_of_def word_bits_conv] })
    |> map (asm_full_simplify lthy);

fun add_field_h_val_rewrites lthy =
  Local_Theory.note ((@{binding field_h_val_rewrites}, []),
      get_field_h_val_rewrites lthy) lthy |> snd
\<close>

ML \<open>
fun get_field_lookup_Somes lthy =
    Global_Theory.facts_of (Proof_Context.theory_of lthy)
    |> Facts.dest_static false []
    |> filter (fn (s, _) => String.isSuffix "_fl_Some" s)
    |> maps snd
    |> map (Thm.transfer (Proof_Context.theory_of lthy))

local
fun and_THEN thm thm' = thm' RS thm
in
fun get_field_offset_rewrites lthy =
    get_field_lookup_Somes lthy
    |> map (and_THEN @{thm meta_eq_to_obj_eq} #> and_THEN @{thm field_lookup_offset_eq})
end

fun add_field_offset_rewrites lthy =
    Local_Theory.note ((@{binding field_offset_rewrites}, []),
      get_field_offset_rewrites lthy) lthy |> snd

fun get_field_to_bytes_rewrites lthy = let
    val fl_thms = get_field_lookup_Somes lthy
    val init1 = @{thm field_lookup_to_bytes_split_init}
    val step = @{thm field_lookup_to_bytes_split_step}
    val init = (fl_thms RL [init1 RS step])
        |> map (simp_tac lthy 1 #> Seq.hd)
    fun proc thm = case (fl_thms RL [thm RS step]) of
            (thm :: _) => proc (simp_tac lthy 1 thm |> Seq.hd)
        | [] => thm
    fun test concl = (Term.exists_Const (fn (s, _) => s = @{const_name "drop"}) concl
        andalso (warning ("padding: " ^ (HOLogic.dest_Trueprop concl
            |> HOLogic.dest_eq |> fst |> strip_comb |> snd |> hd
            |> fastype_of |> dest_Type |> fst)); true))
  in map (proc #> simplify lthy) init
    |> filter_out (Thm.concl_of #> test) end

fun add_field_to_bytes_rewrites lthy =
  Local_Theory.note ((@{binding field_to_bytes_rewrites}, []),
      get_field_to_bytes_rewrites lthy) lthy |> snd
\<close>

end
