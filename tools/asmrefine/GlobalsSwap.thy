(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory GlobalsSwap
imports
  "Lib.Lib"
  "CParser.CTranslation"
  "CParser.PackedTypes"
begin

datatype 'g global_data =
    GlobalData "string" "nat" "addr \<Rightarrow> bool" "'g \<Rightarrow> word8 list"
        "word8 list \<Rightarrow> 'g \<Rightarrow> 'g"
  | ConstGlobalData "string" "nat" "addr \<Rightarrow> bool"
        "word8 list" "word8 list \<Rightarrow> bool"
  | AddressedGlobalData "string" "nat" "addr \<Rightarrow> bool"
  (* in each case the symbol name, length in bytes, tag and constraint on
     address. for active globals a getter/setter, for const globals
     a sample value and a way to check a value *)

definition
  is_const_global_data :: "'g global_data \<Rightarrow> bool"
where
  "is_const_global_data gd =
    (case gd of ConstGlobalData nm m ok v chk \<Rightarrow> True | _ \<Rightarrow> False)"

definition
  is_addressed_global_data :: "'g global_data \<Rightarrow> bool"
where
  "is_addressed_global_data gd =
    (case gd of AddressedGlobalData _ _ _ \<Rightarrow> True | _ \<Rightarrow> False)"

definition
  is_global_data :: "'g global_data \<Rightarrow> bool"
where
  "is_global_data gd =
    (case gd of GlobalData _ _ _ _ _ \<Rightarrow> True | _ \<Rightarrow> False)"

definition
  "global_data_region symtab gd = (case gd of
    GlobalData name m b g s \<Rightarrow> {symtab name ..+ m}
  | ConstGlobalData name m b v chk \<Rightarrow> {symtab name ..+ m}
  | AddressedGlobalData name m b \<Rightarrow> {})"

definition
  "global_data_ok symtab gd =
    (case gd of GlobalData nm _ ok _ _ \<Rightarrow> ok (symtab nm)
        | ConstGlobalData nm _ ok _ _ \<Rightarrow> ok (symtab nm)
        | AddressedGlobalData nm _ ok \<Rightarrow> ok (symtab nm))"

definition
  global_data :: "string \<Rightarrow>
        ('g \<Rightarrow> ('a :: packed_type)) \<Rightarrow>
        (('a \<Rightarrow> 'a) \<Rightarrow> 'g \<Rightarrow> 'g) \<Rightarrow> 'g global_data"
where
 "global_data name getter updator
    = GlobalData name (size_of TYPE('a))
          (\<lambda>addr. c_guard (Ptr addr :: 'a ptr))
          (to_bytes_p o getter)
          (updator o K o from_bytes)"

type_synonym 'g hrs_update = "(heap_raw_state \<Rightarrow> heap_raw_state) \<Rightarrow> 'g \<Rightarrow> 'g"

definition
  global_swap :: "('g \<Rightarrow> heap_raw_state) \<Rightarrow> 'g hrs_update
        \<Rightarrow> (string \<Rightarrow> addr) \<Rightarrow> 'g global_data \<Rightarrow> 'g \<Rightarrow> 'g"
where
 "global_swap g_hrs g_hrs_upd symtab gd \<equiv>
    (case gd of GlobalData name len n g p \<Rightarrow> \<lambda>gs.
      g_hrs_upd (\<lambda>_. hrs_mem_update (heap_update_list (symtab name)
            (take len (g (g_hrs_upd (K undefined) gs)))) (g_hrs gs))
        (p (heap_list (hrs_mem (g_hrs gs)) len (symtab name))
        (g_hrs_upd (K undefined) gs))
    | _ \<Rightarrow> id)"

definition
  globals_swap :: "('g \<Rightarrow> heap_raw_state) \<Rightarrow> 'g hrs_update
        \<Rightarrow> (string \<Rightarrow> addr) \<Rightarrow> 'g global_data list \<Rightarrow> 'g \<Rightarrow> 'g"
where
 "globals_swap g_hrs g_hrs_upd symtab gds
    = foldr (global_swap g_hrs g_hrs_upd symtab) gds"

lemma foldr_does_nothing_to_xf:
  "\<lbrakk> \<And>x s. x \<in> set xs \<Longrightarrow> xf (f x s) = xf s \<rbrakk>
       \<Longrightarrow> xf (foldr f xs s) = xf s"
  by (induct xs, simp_all)

lemma intvl_empty2:
  "({p ..+ n} = {}) = (n = 0)"
  by (auto simp add: intvl_def)

lemma heap_update_list_commute:
  "{p ..+ length xs} \<inter> {q ..+ length ys} = {}
      \<Longrightarrow> heap_update_list p xs (heap_update_list q ys hp)
        = heap_update_list q ys (heap_update_list p xs hp)"
  apply (cases "length xs < addr_card")
   apply (cases "length ys < addr_card")
    apply (rule ext, simp add: heap_update_list_value)
    apply blast
   apply (simp_all add: addr_card intvl_overflow intvl_empty2)
  done

lemma heap_update_commute:
  "\<lbrakk>d,g \<Turnstile>\<^sub>t p; d,g' \<Turnstile>\<^sub>t q; \<not> TYPE('a) <\<^sub>\<tau> TYPE('b); \<not> field_of_t q p;
       wf_fd (typ_info_t TYPE('a)); wf_fd (typ_info_t TYPE('b)) \<rbrakk>
        \<Longrightarrow> heap_update p v (heap_update q (u :: 'b :: c_type) h)
              = heap_update q u (heap_update p (v :: 'a :: c_type) h)"
  apply (drule(3) h_t_valid_neq_disjoint)
  apply (simp add: heap_update_def)
  apply (simp add: heap_update_list_commute heap_list_update_disjoint_same
                   to_bytes_def length_fa_ti size_of_def Int_commute)
  done

definition
  global_data_swappable :: "'g global_data \<Rightarrow> 'g global_data \<Rightarrow> bool"
where
 "global_data_swappable gd gd' \<equiv> case (gd, gd') of
    (GlobalData _ _ _ g s, GlobalData _ _ _ g' s') \<Rightarrow>
      (\<forall>v v' gs. s v (s' v' gs) = s' v' (s v gs))
         \<and> (\<forall>v gs. g (s' v gs) = g gs)
         \<and> (\<forall>v gs. g' (s v gs) = g' gs)
  | _ \<Rightarrow> True"

definition
  global_data_valid :: "('g \<Rightarrow> heap_raw_state) \<Rightarrow> 'g hrs_update
        \<Rightarrow> 'g global_data \<Rightarrow> bool"
where
 "global_data_valid g_hrs g_hrs_upd gd \<equiv>
    (case gd of GlobalData _ l _ g s \<Rightarrow>
       (\<forall>gs. length (g gs) = l)
         \<and> (\<forall>v v' gs. s v (s v' gs) = s v gs)
         \<and> (\<forall>gs. s (g gs) gs = gs)
         \<and> (\<forall>v gs. length v = l \<longrightarrow> g (s v gs) = v)
         \<and> (\<forall>v f gs. (s v (g_hrs_upd f gs)) = g_hrs_upd f (s v gs))
         \<and> (\<forall>v gs. g_hrs (s v gs) = g_hrs gs)
         \<and> (\<forall>f gs. g (g_hrs_upd f gs) = g gs)
         \<and> l < addr_card
    | _ \<Rightarrow> True)"

definition
  "global_acc_valid g_hrs g_hrs_upd \<equiv>
    (\<forall>f s. g_hrs (g_hrs_upd f s) = f (g_hrs s))
    \<and> (\<forall>f f' s. g_hrs_upd f (g_hrs_upd f' s) = g_hrs_upd (f o f') s)
    \<and> (\<forall>s. g_hrs_upd (\<lambda>_. g_hrs s) s = s)"

lemma global_swap_swap:
  "\<lbrakk> global_data_region symtab gd \<inter> global_data_region symtab gd' = {};
     global_acc_valid g_hrs g_hrs_upd; global_data_swappable gd gd';
     global_data_valid g_hrs g_hrs_upd gd; global_data_valid g_hrs g_hrs_upd gd' \<rbrakk>
  \<Longrightarrow> global_swap g_hrs g_hrs_upd symtab gd (global_swap g_hrs g_hrs_upd symtab gd' gs)
    = global_swap g_hrs g_hrs_upd symtab gd' (global_swap g_hrs g_hrs_upd symtab gd gs)"
  apply (clarsimp simp add: global_swap_def hrs_mem_update
                            global_data_swappable_def global_data_valid_def
                            global_acc_valid_def o_def
                     split: global_data.split_asm)
  apply (clarsimp simp: global_data_region_def K_def)
  apply (simp add: heap_list_update_disjoint_same Int_commute)
  apply (simp add: hrs_mem_update_def split_def)
  apply (subst heap_update_list_commute, simp_all)
  done

lemma heap_update_list_double_id:
  "\<lbrakk> heap_list hp n ptr = xs; length xs' = length xs;
         length xs < addr_card \<rbrakk> \<Longrightarrow>
    heap_update_list ptr xs (heap_update_list ptr xs' hp) = hp"
  apply (rule ext, simp add: heap_update_list_value')
  apply (clarsimp simp: heap_list_nth intvl_def)
  done

lemma global_swap_cancel:
  "\<lbrakk> global_acc_valid g_hrs g_hrs_upd;
         global_data_valid g_hrs g_hrs_upd gd \<rbrakk>
  \<Longrightarrow> global_swap g_hrs g_hrs_upd symtab gd (global_swap g_hrs g_hrs_upd symtab gd gs) = gs"
  apply (insert heap_list_update[where
                v="case gd of GlobalData _ _ _ g _ \<Rightarrow> g gs"])
  apply (clarsimp simp: global_swap_def hrs_mem_update
                        global_data_valid_def global_acc_valid_def
                 split: global_data.split)
  apply (simp add: hrs_mem_update_def split_def o_def)
  apply (simp add: heap_update_list_double_id hrs_mem_def)
  done

lemma foldr_update_commutes:
  "\<lbrakk> \<And>x s. x \<in> set xs \<Longrightarrow> f (g x s) = g x (f s) \<rbrakk>
       \<Longrightarrow> f (foldr g xs s) = foldr g xs (f s)"
  by (induct xs, simp_all)

definition
 "globals_list_valid symtab g_hrs g_hrs_upd xs =
    (distinct_prop global_data_swappable xs
        \<and> (\<forall>x \<in> set xs. global_data_valid g_hrs g_hrs_upd x)
        \<and> (\<forall>x \<in> set xs. global_data_ok symtab x))"

lemma global_data_swappable_sym:
  "global_data_swappable x y = global_data_swappable y x"
  by (auto simp add: global_data_swappable_def
              split: global_data.split)

lemma hrs_htd_globals_swap:
  "\<lbrakk> global_acc_valid g_hrs g_hrs_upd;
        \<forall>x \<in> set xs. global_data_valid g_hrs g_hrs_upd x \<rbrakk>
    \<Longrightarrow> hrs_htd (g_hrs (globals_swap g_hrs g_hrs_upd symtab xs gs))
        = hrs_htd (g_hrs gs)"
  unfolding globals_swap_def
  apply (rule foldr_does_nothing_to_xf)
  apply (simp add: global_swap_def global_acc_valid_def
            split: global_data.split prod.split bool.split)
  done

lemmas foldr_hrs_htd_global_swap = hrs_htd_globals_swap[unfolded globals_swap_def]

definition
  globals_list_distinct :: "addr set \<Rightarrow> (string \<Rightarrow> addr)
        \<Rightarrow> 'g global_data list \<Rightarrow> bool"
where
  "globals_list_distinct D symtab gds = distinct_prop (\<lambda>S T. S \<inter> T = {})
    (D # map (global_data_region symtab) gds)"

lemma globals_swap_twice_helper:
  "\<lbrakk> globals_list_valid symtab g_hrs g_hrs_upd xs;
        global_acc_valid g_hrs g_hrs_upd;
        globals_list_distinct D symtab xs \<rbrakk>
   \<Longrightarrow> globals_swap g_hrs g_hrs_upd symtab xs (globals_swap g_hrs g_hrs_upd symtab xs gs) = gs"
  apply (simp add: globals_swap_def)
  apply (clarsimp simp: foldr_hrs_htd_global_swap globals_list_valid_def)
  apply (induct xs)
   apply simp
  apply (clarsimp simp: globals_list_distinct_def)
  apply (subst foldr_update_commutes[where f="global_swap g_hrs g_hrs_upd symtab v" for v])
   apply (rule global_swap_swap, auto)[1]
  apply (simp add: global_swap_cancel foldr_hrs_htd_global_swap)
  done

lemma disjoint_int_intvl_min:
  "\<lbrakk> S \<inter> {p ..+ n} = {} \<rbrakk>
      \<Longrightarrow> S \<inter> {p ..+ min m n} = {}"
  using intvl_start_le[where x="min m n" and y=n]
  by auto

lemma ptr_set_disjoint_footprint:
  "(s_footprint (p :: ('a :: c_type) ptr) \<inter> (S \<times> UNIV) = {})
    \<Longrightarrow> ({ptr_val p ..+ size_of TYPE('a)} \<inter> S = {})"
  by (auto simp add: s_footprint_intvl[symmetric])

lemma disjoint_heap_list_globals_swap_filter:
  "\<lbrakk> global_acc_valid g_hrs g_hrs_upd;
     globals_list_distinct D symtab (filter is_global_data xs);
     {p ..+ n} \<subseteq> D \<rbrakk>
     \<Longrightarrow> heap_list (hrs_mem (g_hrs (globals_swap g_hrs g_hrs_upd symtab xs gs))) n p
            = heap_list (hrs_mem (g_hrs gs)) n p"
  apply (clarsimp simp: globals_swap_def)
  apply (rule foldr_does_nothing_to_xf)
  apply (clarsimp simp: global_swap_def hrs_mem_update
                        global_acc_valid_def globals_list_distinct_def
                 split: global_data.split)
  apply (subst heap_list_update_disjoint_same, simp_all)
  apply (drule spec, drule mp, erule conjI, simp add: is_global_data_def)
  apply (simp add: Int_commute global_data_region_def)
  apply (rule disjoint_int_intvl_min)
  apply blast
  done

lemma disjoint_h_val_globals_swap_filter:
  "\<lbrakk> global_acc_valid g_hrs g_hrs_upd;
     globals_list_distinct D symtab (filter is_global_data xs);
     s_footprint p \<subseteq> D \<times> UNIV \<rbrakk>
     \<Longrightarrow> h_val (hrs_mem (g_hrs (globals_swap g_hrs g_hrs_upd symtab xs gs))) p
            = h_val (hrs_mem (g_hrs gs)) p"
  apply (clarsimp simp: h_val_def)
  apply (subst disjoint_heap_list_globals_swap_filter[where g_hrs=g_hrs], assumption+)
   apply (auto simp: s_footprint_intvl[symmetric])[1]
  apply simp
  done

lemma distinct_prop_filter:
  "distinct_prop P (filter Q xs)
    = distinct_prop (\<lambda>x y. Q x \<and> Q y \<longrightarrow> P x y) xs"
  by (induct xs, auto)

lemma distinct_prop_weaken:
  "\<lbrakk> distinct_prop P xs; \<And>x y. P x y \<Longrightarrow> Q x y \<rbrakk>
    \<Longrightarrow> distinct_prop Q xs"
  by (induct xs, simp_all)

lemma globals_list_distinct_filter:
  "globals_list_distinct D symtab xs
    \<Longrightarrow> globals_list_distinct D symtab (filter P xs)"
  by (clarsimp simp: globals_list_distinct_def
                     distinct_prop_map distinct_prop_filter
              elim!: distinct_prop_weaken)

lemmas disjoint_h_val_globals_swap
    = disjoint_h_val_globals_swap_filter[OF _ globals_list_distinct_filter]

lemma disjoint_heap_update_globals_swap_filter:
  "\<lbrakk> global_acc_valid g_hrs g_hrs_upd;
     globals_list_distinct D symtab (filter is_global_data xs);
     s_footprint (p :: ('a :: wf_type) ptr) \<subseteq> D \<times> UNIV \<rbrakk>
     \<Longrightarrow> g_hrs_upd (hrs_mem_update (heap_update p v)) (globals_swap g_hrs g_hrs_upd symtab xs gs)
         = globals_swap g_hrs g_hrs_upd symtab xs (g_hrs_upd (hrs_mem_update (heap_update p v)) gs)"
  apply (clarsimp simp: globals_swap_def global_acc_valid_def)
  apply (rule foldr_update_commutes)
  apply (clarsimp simp: global_swap_def hrs_mem_update h_val_def
                        heap_update_def o_def K_def
                        globals_list_distinct_def
                 split: global_data.split)
  apply (drule spec, drule mp, erule conjI, simp add: is_global_data_def)
  apply (rule_tac f="g_hrs_upd" in arg_cong2[rotated])

   apply (subst heap_list_update_disjoint_same, simp_all)
   apply (rule ptr_set_disjoint_footprint)
   apply (simp add: global_data_region_def)
   apply blast

  apply (clarsimp simp: hrs_mem_update_def split_def)
  apply (subst heap_update_list_commute)
   apply (simp add: to_bytes_def length_fa_ti size_of_def
                    global_data_region_def)
   apply (intro disjoint_int_intvl_min
                ptr_set_disjoint_footprint[unfolded size_of_def])
   apply blast

  apply (subst heap_list_update_disjoint_same,
         simp_all add: global_data_region_def)
  apply (simp add: Int_commute)
  apply (intro disjoint_int_intvl_min
               ptr_set_disjoint_footprint)
  apply blast
  done

lemmas disjoint_heap_update_globals_swap
    = disjoint_heap_update_globals_swap_filter[OF _ globals_list_distinct_filter]

lemma to_bytes_p_from_bytes:
  "length xs = size_of TYPE ('a :: packed_type)
    \<Longrightarrow> to_bytes_p (from_bytes xs :: 'a) = xs"
  by (simp add: to_bytes_p_def to_bytes_def from_bytes_def
                update_ti_t_def size_of_def
                field_access_update_same td_fafu_idem)

lemma to_bytes_p_inj:
  "inj (to_bytes_p :: ('a :: packed_type) \<Rightarrow> _)"
  apply (rule inj_onI)
  apply (drule_tac f=from_bytes in arg_cong)
  apply (simp add: to_bytes_p_def)
  apply (subst(asm) CTypes.inv | simp)+
  done

lemma global_data_valid:
  "global_data_valid g_hrs g_hrs_upd (global_data p (g :: 'g \<Rightarrow> ('a :: packed_type)) s)
    = (
        (\<forall>v v' gs. s (\<lambda>_. v) (s (\<lambda>_. v') gs) = s (\<lambda>_. v) gs)
            \<and> (\<forall>gs. s (\<lambda>_. g gs) gs = gs)
            \<and> (\<forall>v f gs. s (\<lambda>_. v) (g_hrs_upd f gs) = g_hrs_upd f (s (\<lambda>_. v) gs))
            \<and> (\<forall>f gs. g (g_hrs_upd f gs) = g gs)
            \<and> (\<forall>v gs. g_hrs (s (\<lambda>_. v) gs) = g_hrs gs)
            \<and> (\<forall>v gs. g (s (\<lambda>_. v) gs) = v))"
proof -
  have all_to_xs: "\<And>P. (\<forall>(v :: 'a). P v) = (\<forall>xs. P (from_bytes xs))"
    apply (safe, simp_all)
    apply (drule_tac x="to_bytes_p v" in spec)
    apply (simp add: to_bytes_p_from_bytes)
    done
  show ?thesis
    apply (simp add: global_data_valid_def global_data_def)
    apply (simp add: all_to_xs order_less_imp_le[OF max_size]
                     inj_eq[OF to_bytes_p_inj] conj_comms K_def)
    apply (safe, simp_all add: to_bytes_p_from_bytes)
    apply (drule_tac x="to_bytes_p (from_bytes xs :: 'a)" in spec, drule mp)
     apply simp
    apply (simp add: inj_eq[OF to_bytes_p_inj])
    done
qed

lemma globals_swap_reorder_append:
  "\<lbrakk> globals_list_valid symtab g_hrs g_hrs_upd (xs @ ys);
        global_acc_valid g_hrs g_hrs_upd;
        globals_list_distinct D symtab (xs @ ys) \<rbrakk>
    \<Longrightarrow> globals_swap g_hrs g_hrs_upd symtab (xs @ ys) = globals_swap g_hrs g_hrs_upd symtab (ys @ xs)"
  apply (induct xs)
   apply simp
  apply (rule ext)
  apply (clarsimp simp: globals_swap_def foldr_hrs_htd_global_swap
                        fun_eq_iff)
  apply (drule meta_mp, simp add: globals_list_valid_def)
  apply (clarsimp simp: globals_list_distinct_def)
  apply (rule foldr_update_commutes)
  apply (clarsimp simp: ball_Un globals_list_valid_def)
  apply (rule global_swap_swap, simp_all)
  done

lemma globals_swap_reorder_append_n:
  "\<lbrakk> globals_list_valid symtab g_hrs g_hrs_upd xs; global_acc_valid g_hrs g_hrs_upd;
        globals_list_distinct D symtab xs \<rbrakk> \<Longrightarrow>
    globals_swap g_hrs g_hrs_upd symtab xs = globals_swap g_hrs g_hrs_upd symtab (drop n xs @ take n xs)"
  using globals_swap_reorder_append
    [where xs="take n xs" and ys="drop n xs"]
  by simp

lemma heap_update_list_overwrite:
  "\<lbrakk> length xs = length ys; length ys < addr_card \<rbrakk>
    \<Longrightarrow> heap_update_list w xs (heap_update_list w ys hp)
        = heap_update_list w xs hp"
  by (rule ext, simp add: heap_update_list_value)

lemma heap_list_update_eq:
  "\<lbrakk> n = length v; n \<le> addr_card \<rbrakk>
    \<Longrightarrow> heap_list (heap_update_list p v h) n p = v"
  by (simp add: heap_list_update)

lemma globals_swap_absorb_update:
  "\<lbrakk> global_acc_valid g_hrs g_hrs_upd;
     \<forall>s. v (g_hrs s) = v'; length v' = m;
     globals_list_valid symtab g_hrs g_hrs_upd (GlobalData nm m ok g s # xs);
     globals_list_distinct D symtab (GlobalData nm m ok g s # xs) \<rbrakk>
    \<Longrightarrow> s v' (globals_swap g_hrs g_hrs_upd symtab (GlobalData nm m ok g s # xs) gs)
        = globals_swap g_hrs g_hrs_upd symtab (GlobalData nm m ok g s # xs)
               (g_hrs_upd (\<lambda>hrs. hrs_mem_update (heap_update_list (symtab nm) (v hrs)) hrs) gs)"
  apply (induct xs)
   apply (simp add: globals_swap_def global_acc_valid_def)
   apply (simp add: global_swap_def global_data_def hrs_mem_update)
   apply (simp add: globals_list_valid_def global_data_valid_def K_def o_def)
   apply (simp add: hrs_mem_def hrs_mem_update_def split_def
                    heap_update_def h_val_def heap_update_list_overwrite
                    heap_list_update_eq order_less_imp_le
               del: SepCode.inv_p)
  apply (drule meta_mp, simp add: globals_list_valid_def globals_list_distinct_def)+
  apply (rename_tac x xs)
  apply (subgoal_tac "\<forall>gs.
                globals_swap g_hrs g_hrs_upd symtab (GlobalData nm m ok g s # x # xs) gs
                 = global_swap g_hrs g_hrs_upd symtab x (globals_swap g_hrs g_hrs_upd symtab (GlobalData nm m ok g s # xs) gs)")
   apply (subgoal_tac "\<forall>gs. s v' (global_swap g_hrs g_hrs_upd symtab x gs) = global_swap g_hrs g_hrs_upd symtab x (s v' gs)")
    apply (simp add: global_acc_valid_def)
   apply (clarsimp simp: globals_list_valid_def global_data_swappable_def
                         global_data_def global_swap_def K_def
                         global_data_valid_def order_less_imp_le
               simp del: SepCode.inv_p split: global_data.split_asm prod.split bool.split)
  apply (clarsimp simp: globals_swap_def globals_list_distinct_def
                        global_data_def globals_list_valid_def)
  apply (rule global_swap_swap, simp+)
  done

lemma append_2nd_simp_backward:
  "xs @ y # ys = (xs @ [y]) @ ys"
  by simp

lemma globals_swap_access_mem_raw:
  "\<lbrakk> global_acc_valid g_hrs g_hrs_upd;
     globals_list_valid symtab g_hrs g_hrs_upd xs; globals_list_distinct D symtab xs;
     GlobalData nm m ok g s \<in> set xs; size_of TYPE('a) = m \<rbrakk>
    \<Longrightarrow> h_val (hrs_mem (g_hrs gs)) (Ptr (symtab nm) :: ('a :: c_type) ptr)
            = from_bytes (g (globals_swap g_hrs g_hrs_upd symtab xs gs))"
  apply (clarsimp simp: in_set_conv_decomp)
  apply (subst append_2nd_simp_backward)
  apply (subst globals_swap_reorder_append, simp+)
  apply (simp add: globals_swap_def del: foldr_append split del: if_split)
  apply (subgoal_tac "global_data_valid g_hrs g_hrs_upd
                             (GlobalData nm (size_of TYPE('a)) ok g s)")
   apply (subst append_assoc[symmetric], subst foldr_append)
   apply (subst foldr_does_nothing_to_xf[where xf=g])
    apply (subgoal_tac "global_data_swappable (GlobalData nm (size_of TYPE('a)) ok g s) x")
     apply (clarsimp simp: global_data_swappable_def global_data_def
                           global_swap_def global_data_valid_def
                    split: global_data.split_asm prod.split bool.split)
    apply (simp add: globals_list_valid_def distinct_prop_append)
    apply (auto simp: global_data_swappable_sym)[1]
   apply (simp add: global_data_valid_def)
   apply (simp add: global_data_def global_swap_def h_val_def K_def
                    )
  apply (simp_all add: globals_list_valid_def)
  done

lemma globals_swap_access_mem:
  "\<lbrakk> global_data nm g u \<in> set xs;
     global_acc_valid g_hrs g_hrs_upd;
     globals_list_valid symtab g_hrs g_hrs_upd xs;
     globals_list_distinct D symtab xs \<rbrakk>
    \<Longrightarrow> g (globals_swap g_hrs g_hrs_upd symtab xs gs) = h_val (hrs_mem (g_hrs gs)) (Ptr (symtab nm))"
  by (simp add: global_data_def globals_swap_access_mem_raw)

lemma globals_swap_access_mem2:
  "\<lbrakk> global_data nm g u \<in> set xs;
     global_acc_valid g_hrs g_hrs_upd;
     globals_list_valid symtab g_hrs g_hrs_upd xs;
     globals_list_distinct D symtab xs \<rbrakk>
    \<Longrightarrow> g gs = h_val (hrs_mem (g_hrs (globals_swap g_hrs g_hrs_upd symtab xs gs))) (Ptr (symtab nm))"
  using globals_swap_twice_helper globals_swap_access_mem
  by metis

lemma globals_swap_update_mem_raw:
  "\<lbrakk> global_acc_valid g_hrs g_hrs_upd;
     \<forall>hmem. (v hmem) = v'; length v' = m;
     globals_list_valid symtab g_hrs g_hrs_upd xs;
     globals_list_distinct D symtab xs;
     GlobalData nm m ok g st \<in> set xs \<rbrakk>
    \<Longrightarrow> globals_swap g_hrs g_hrs_upd symtab xs (g_hrs_upd (hrs_mem_update
            (\<lambda>hmem. heap_update_list (symtab nm) (v hmem) hmem)) gs)
        = st v' (globals_swap g_hrs g_hrs_upd symtab xs gs)"
  apply (clarsimp simp: in_set_conv_decomp)
  apply (subst globals_swap_reorder_append, simp+)+
  apply (rule globals_swap_absorb_update[symmetric, where D=D], simp_all)
   apply (simp add: globals_list_valid_def distinct_prop_append)
   apply (insert global_data_swappable_sym)
   apply blast
  apply (simp add: globals_list_distinct_def ball_Un distinct_prop_append)
  apply blast
  done

lemma to_bytes_p_from_bytes_eq:
  "\<lbrakk> from_bytes ys = (v :: 'a :: packed_type); length ys = size_of TYPE('a) \<rbrakk>
        \<Longrightarrow> to_bytes_p v = ys"
  by (clarsimp simp: to_bytes_p_from_bytes)

lemma globals_swap_update_mem:
  "\<lbrakk> global_data nm g u \<in> set xs;
     global_acc_valid g_hrs g_hrs_upd;
     globals_list_valid symtab g_hrs g_hrs_upd xs;
     globals_list_distinct D symtab xs \<rbrakk>
    \<Longrightarrow> u (\<lambda>_. v) (globals_swap g_hrs g_hrs_upd symtab xs gs)
        = globals_swap g_hrs g_hrs_upd symtab xs (g_hrs_upd (hrs_mem_update
            (\<lambda>hrs. heap_update (Ptr (symtab nm)) v hrs)) gs)"
  unfolding global_data_def
  apply (simp add: heap_update_def)
  apply (subst globals_swap_update_mem_raw[where v'="to_bytes_p v", rotated -1],
         assumption, simp_all add: K_def o_def)
  apply clarsimp
  apply (rule to_bytes_p_from_bytes_eq[symmetric], simp+)
  done

lemma globals_swap_update_mem2:
  assumes prems: "global_data nm g u \<in> set xs"
     "global_acc_valid g_hrs g_hrs_upd"
     "globals_list_valid symtab g_hrs g_hrs_upd xs"
     "globals_list_distinct D symtab xs"
  shows "globals_swap g_hrs g_hrs_upd symtab xs (u (\<lambda>_. v) gs)
        = g_hrs_upd (hrs_mem_update (\<lambda>hrs. heap_update (Ptr (symtab nm)) v hrs))
            (globals_swap g_hrs g_hrs_upd symtab xs gs)"
  using prems globals_swap_twice_helper globals_swap_update_mem
  by metis

lemma globals_swap_hrs_htd_update:
  "\<lbrakk> global_acc_valid g_hrs g_hrs_upd;
        globals_list_valid symtab g_hrs g_hrs_upd xs \<rbrakk>
    \<Longrightarrow> g_hrs_upd (hrs_htd_update ufn) (globals_swap g_hrs g_hrs_upd symtab xs gs)
         = globals_swap g_hrs g_hrs_upd symtab xs (g_hrs_upd (hrs_htd_update ufn) gs)"
  apply (clarsimp simp: globals_swap_def hrs_htd_update
                        global_acc_valid_def)
  apply (rule foldr_update_commutes)
  apply (clarsimp simp: globals_list_valid_def, drule(1) bspec)
  apply (simp add: global_swap_def o_def global_data_valid_def
                   hrs_htd_update
            split: global_data.split_asm prod.split bool.split)
  apply (simp add: hrs_htd_update_def hrs_mem_update_def split_def)
  done

definition
  const_global_data :: "string \<Rightarrow> ('a :: c_type)  \<Rightarrow> 'g global_data"
where
 "const_global_data name v = ConstGlobalData name (size_of TYPE('a))
    (\<lambda>addr. c_guard (Ptr addr :: 'a ptr))
    (to_bytes_p v) (\<lambda>xs. from_bytes xs = v)"

definition
  addressed_global_data :: "string \<Rightarrow> ('a :: c_type) itself \<Rightarrow> 'g global_data"
where
 "addressed_global_data name tp =
    AddressedGlobalData name (size_of tp) (\<lambda>addr. c_guard (Ptr addr :: 'a ptr))"

lemma is_global_data_simps[simp]:
  "is_global_data (global_data nm g s)"
  "\<not> is_global_data (const_global_data nm v)"
  "\<not> is_global_data (addressed_global_data nm tp)"
  by (simp_all add: global_data_def const_global_data_def
                    is_global_data_def addressed_global_data_def)

lemma is_const_global_data_simps[simp]:
  "is_const_global_data (const_global_data nm v)"
  "\<not> is_const_global_data (global_data nm g s)"
  "\<not> is_const_global_data (addressed_global_data nm tp)"
  by (simp_all add: global_data_def const_global_data_def
                    is_const_global_data_def addressed_global_data_def)

lemma distinct_prop_swappable_optimisation:
  "distinct_prop global_data_swappable (filter is_global_data gs)
    \<Longrightarrow> distinct_prop (\<lambda>x y. global_data_swappable x y) gs"
  apply (simp add: distinct_prop_filter is_global_data_def
                   global_data_swappable_def)
  apply (erule distinct_prop_weaken)
  apply (simp split: global_data.splits)
  done

lemma globals_list_valid_optimisation:
  "distinct_prop global_data_swappable (filter is_global_data gs)
    \<Longrightarrow> \<forall>g \<in> set gs. global_data_valid g_hrs g_hrs_upd g
    \<Longrightarrow> \<forall>g \<in> set gs. global_data_ok symtab g
    \<Longrightarrow> globals_list_valid symtab g_hrs g_hrs_upd gs"
  using globals_list_valid_def distinct_prop_swappable_optimisation
  by blast

definition
  const_globals_in_memory :: "(string \<Rightarrow> addr) \<Rightarrow> 'g global_data list
        \<Rightarrow> heap_mem \<Rightarrow> bool"
where
  "const_globals_in_memory symtab xs hmem =
    (\<forall>gd \<in> set xs. case gd of
        ConstGlobalData nm l ok v chk \<Rightarrow> chk (heap_list hmem l (symtab nm))
    | _ \<Rightarrow> True)"

lemma const_globals_in_memory_h_val_eq:
  "const_globals_in_memory symtab (const_global_data nm v # xs) hmem
    = (h_val hmem (Ptr (symtab nm)) = v \<and> const_globals_in_memory symtab xs hmem)"
  by (simp add: const_globals_in_memory_def const_global_data_def h_val_def)

lemma const_globals_in_memory_other_eqs:
  "const_globals_in_memory symtab (global_data nm g s # xs) hmem
    = const_globals_in_memory symtab xs hmem"
  "const_globals_in_memory symtab (addressed_global_data nm tp # xs) hmem
    = const_globals_in_memory symtab xs hmem"
  "const_globals_in_memory symtab [] hmem"
  by (auto simp add: const_globals_in_memory_def
                     global_data_def addressed_global_data_def)

lemmas const_globals_in_memory_eqs
    = const_globals_in_memory_h_val_eq const_globals_in_memory_other_eqs

lemma const_globals_in_memory_h_val:
  "\<lbrakk> const_global_data nm v \<in> set xs;
    const_globals_in_memory symtab xs hmem \<rbrakk>
    \<Longrightarrow> h_val hmem (Ptr (symtab nm)) = v"
  apply (simp add: const_globals_in_memory_def const_global_data_def)
  apply (drule (1) bspec)
  apply (clarsimp simp: h_val_def)
  done

lemma const_globals_in_memory_heap_update_list:
  "\<lbrakk> const_globals_in_memory symtab xs hmem;
    globals_list_distinct D symtab (filter is_const_global_data xs);
    {p ..+ length ys} \<subseteq> D \<rbrakk>
    \<Longrightarrow> const_globals_in_memory symtab xs (heap_update_list p ys hmem)"
  apply (clarsimp simp: const_globals_in_memory_def globals_list_distinct_def
                 split: global_data.split)
  apply (drule(1) bspec)
  apply (drule spec, drule mp, erule conjI, simp add: is_const_global_data_def)
  apply (simp add: global_data_region_def)
  apply (subst heap_list_update_disjoint_same)
   apply blast
  apply simp
  done

definition
  htd_safe :: "addr set \<Rightarrow> heap_typ_desc \<Rightarrow> bool"
where
  "htd_safe D htd = (dom_s htd \<subseteq> D \<times> UNIV)"

lemma const_globals_in_memory_heap_update:
  "\<lbrakk> const_globals_in_memory symtab gs hmem;
    globals_list_distinct D symtab gs;
    ptr_safe (p :: ('a :: wf_type) ptr) htd; htd_safe D htd \<rbrakk>
     \<Longrightarrow> const_globals_in_memory symtab gs (heap_update p val hmem)"
  apply (simp add: split_def heap_update_def)
  apply (erule const_globals_in_memory_heap_update_list,
         erule globals_list_distinct_filter)
  apply (clarsimp simp: ptr_safe_def htd_safe_def s_footprint_intvl[symmetric])
  apply blast
  done

lemma distinct_prop_memD:
  "\<lbrakk> x \<in> set zs; y \<in> set zs; distinct_prop P zs \<rbrakk>
    \<Longrightarrow> x = y \<or> P x y \<or> P y x"
  by (induct zs, auto)

lemma const_globals_in_memory_heap_update_global:
  "\<lbrakk> const_globals_in_memory symtab gs hmem;
     global_data nm (getter :: 'g \<Rightarrow> 'a) setter \<in> set gs;
     globals_list_distinct D symtab gs \<rbrakk>
    \<Longrightarrow> const_globals_in_memory symtab gs
        (heap_update (Ptr (symtab nm)) (v :: 'a :: packed_type) hmem)"
  apply (simp add: heap_update_def split_def)
  apply (erule const_globals_in_memory_heap_update_list[OF _ _ order_refl])
  apply (clarsimp simp: globals_list_distinct_def distinct_prop_map
                        distinct_prop_filter)
  apply (simp add: distinct_prop_weaken)
  apply clarsimp
  apply (drule(2) distinct_prop_memD)
  apply (auto simp: global_data_region_def global_data_def
                    is_const_global_data_def)
  done

lemma const_globals_in_memory_after_swap:
  "global_acc_valid t_hrs_' t_hrs_'_update
    \<Longrightarrow> globals_list_distinct D symbol_table gxs
    \<Longrightarrow> const_globals_in_memory symbol_table gxs
            (hrs_mem (t_hrs_' (globals_swap t_hrs_' t_hrs_'_update symbol_table gxs gs)))
        = const_globals_in_memory symbol_table gxs (hrs_mem (t_hrs_' gs))"
  apply (simp add: const_globals_in_memory_def)
  apply (rule ball_cong, simp_all)
  apply (clarsimp split: global_data.split)
  apply (subst disjoint_heap_list_globals_swap_filter[OF _ _ order_refl],
    assumption+, simp_all)
  apply (clarsimp simp: globals_list_distinct_def distinct_prop_map
                        distinct_prop_filter distinct_prop_weaken)
  apply (drule(2) distinct_prop_memD)
  apply (clarsimp simp: is_global_data_def ball_Un distinct_prop_append
                        global_data_region_def Int_commute
                 split: global_data.split_asm)
  done

ML \<open>
structure DefineGlobalsList = struct

fun dest_conjs t = (t RS @{thm conjunct1})
        :: dest_conjs (t RS @{thm conjunct2})
    handle THM _ => [t]

fun define_globals_list (mungedb:CalculateState.mungedb) globloc globty thy = let
    open CalculateState NameGeneration

    val sT = @{typ string}
    val gdT = Type (@{type_name global_data}, [globty])

    val ctxt = Target_Context.context_begin_named_cmd [] (globloc, Position.none) thy

    fun glob (_, _, _, Local _) = error "define_globals_list: Local"
      | glob (nm, typ, _, UntouchedGlobal) = let
            val cname = NameGeneration.untouched_global_name nm
            val init = Syntax.read_term ctxt (MString.dest cname)
        in Const (@{const_name "const_global_data"}, sT --> typ --> gdT)
            $ HOLogic.mk_string (MString.dest nm) $ init end
      | glob (nm, typ, _, NSGlobal) = let
            (* FIXME: _' hackery (or more generally, hackery) *)
            val acc = (Sign.intern_const thy (global_rcd_name ^ "." ^
                                              MString.dest nm ^ "_'"),
                       globty --> typ)
            val upd = (Sign.intern_const thy
                          (global_rcd_name ^ "." ^ MString.dest nm ^ "_'" ^
                           Record.updateN),
                (typ --> typ) --> globty --> globty)
        in Const (@{const_name "global_data"}, sT
                --> snd acc --> snd upd --> gdT)
            $ HOLogic.mk_string (MString.dest nm) $ Const acc $ Const upd end
      | glob (nm, typ, _, AddressedGlobal) =
        Const (@{const_name "addressed_global_data"},
                sT --> Term.itselfT typ --> gdT)
            $ HOLogic.mk_string (MString.dest nm) $ Logic.mk_type typ

    val naming = Binding.name o NameGeneration.global_data_name
    val globs = CNameTab.dest mungedb |> map snd
        |> filter (fn v => case #4 v of Local _ => false | _ => true)
        |> map (fn g => (g |> #1 |> MString.dest |> naming, glob g))

    val (xs, ctxt) = fold_map (fn (nm, tm) => Local_Theory.define
        ((nm, NoSyn), ((Thm.def_binding nm, []), tm))) globs ctxt

    val gdTs = HOLogic.mk_list gdT (map fst xs)

    val ((gdl, (_, gdl_def)), ctxt) = Local_Theory.define
        ((@{binding global_data_list}, NoSyn),
            ((@{binding global_data_list_def}, []), gdTs)) ctxt

    val (_, ctxt) = Local_Theory.note ((@{binding "global_data_defs"}, []),
            map (snd #> snd) xs) ctxt

    val lT = HOLogic.listT gdT
    val setT = HOLogic.mk_setT gdT
    val setC = Const (@{const_name set}, lT --> setT)
    val thm = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop
            (Const (@{const_name less_eq}, setT --> setT --> HOLogic.boolT)
                $ (setC $ gdTs) $ (setC $ gdl)))
        (K (simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms order_refl}
                addsimps [gdl_def]) 1))

    val mems = simplify (put_simpset HOL_basic_ss ctxt addsimps
            @{thms set_simps insert_subset empty_subsetI simp_thms}) thm
        |> dest_conjs

    val (_, ctxt) = Local_Theory.note ((@{binding "global_data_mems"}, []),
            mems) ctxt

  in Local_Theory.exit_global ctxt end

fun define_globals_list_i s globty thy = let
    val {base = localename,...} = OS.Path.splitBaseExt (OS.Path.file s)
    val globloc = suffix HPInter.globalsN localename
  in define_globals_list (CalculateState.get_mungedb thy s |> the)
        globloc globty thy
  end

end

\<close>

lemma globals_list_distinct_filter_member:
  "x \<in> set xs \<Longrightarrow> globals_list_distinct D symtab xs
    \<Longrightarrow> \<not> P x
    \<Longrightarrow> globals_list_distinct (global_data_region symtab x) symtab
        (filter P xs)"
  apply (clarsimp simp: globals_list_distinct_def)
  apply (rule conjI)
   apply (clarsimp simp: in_set_conv_decomp[where x="x"]
                         distinct_prop_append)
   apply auto[1]
  apply (simp add: distinct_prop_map distinct_prop_filter)
  apply (erule distinct_prop_weaken, simp)
  done

lemma s_footprint_intvl_subset:
  "s_footprint (p :: 'a ptr) \<subseteq> {ptr_val p ..+ size_of TYPE ('a :: c_type)} \<times> UNIV"
  by (auto simp: s_footprint_def s_footprint_untyped_def
                 intvl_def size_of_def)

lemma h_val_globals_swap_in_const_global:
  "\<lbrakk> global_acc_valid g_hrs g_hrs_upd;
        globals_list_distinct D symtab xs;
        const_global_data s (v :: 'a :: c_type) \<in> set xs;
        unat offs + size_of TYPE('b) \<le> size_of TYPE('a) \<rbrakk>
    \<Longrightarrow> h_val (hrs_mem (g_hrs (globals_swap g_hrs g_hrs_upd symtab xs gs)))
            (Ptr (symtab s + offs) :: ('b :: c_type) ptr)
         = h_val (hrs_mem (g_hrs gs)) (Ptr (symtab s + offs))"
  apply (erule disjoint_h_val_globals_swap_filter,
    erule(1) globals_list_distinct_filter_member)
   apply simp
  apply (rule order_trans, rule s_footprint_intvl_subset)
  apply (simp add: global_data_region_def const_global_data_def
                   Times_subset_cancel2)
  apply (erule intvl_sub_offset)
  done

lemmas h_val_globals_swap_in_const_global_both
    = h_val_globals_swap_in_const_global
        h_val_globals_swap_in_const_global[where offs=0, simplified]

lemma const_globals_in_memory_to_h_val_with_swap:
  "\<lbrakk> global_acc_valid g_hrs g_hrs_upd;
    globals_list_distinct D symtab xs;
    const_global_data nm v \<in> set xs;
    const_globals_in_memory symtab xs (hrs_mem (g_hrs gs)) \<rbrakk>
    \<Longrightarrow> v = h_val (hrs_mem (g_hrs (globals_swap g_hrs g_hrs_upd symtab xs gs)))
        (Ptr (symtab nm))"
  apply (subst disjoint_h_val_globals_swap_filter, assumption,
    erule(1) globals_list_distinct_filter_member)
    apply simp
   apply (simp add: global_data_region_def const_global_data_def)
   apply (rule order_trans, rule s_footprint_intvl_subset)
   apply simp
  apply (erule(1) const_globals_in_memory_h_val[symmetric])
  done

text \<open>This alternative ptr_safe definition will apply to all
  global pointers given globals_list_distinct etc. It supports
  the same nonoverlapping properties with h_t_valid as h_t_valid
  itself.\<close>
definition
  ptr_inverse_safe :: "('a :: mem_type) ptr \<Rightarrow> heap_typ_desc \<Rightarrow> bool"
where
  "ptr_inverse_safe p htd = (c_guard p
        \<and> (fst ` s_footprint p \<inter> fst ` dom_s htd = {}))"

lemma global_data_implies_ptr_inverse_safe:
  "\<lbrakk>  global_data nm (accr :: 'a \<Rightarrow> ('b :: packed_type)) updr \<in> set glist;
        globals_list_distinct D symtab glist;
        globals_list_valid symtab t_hrs t_hrs_upd glist;
        htd_safe D htd
        \<rbrakk>
    \<Longrightarrow> ptr_inverse_safe (Ptr (symtab nm) :: 'b ptr) htd"
  apply (clarsimp simp add: ptr_inverse_safe_def globals_list_valid_def
                            htd_safe_def globals_list_distinct_def)
  apply (drule(1) bspec)+
  apply (simp add: global_data_region_def global_data_ok_def global_data_def)
  apply (auto dest!: s_footprint_intvl_subset[THEN subsetD])
  done

ML \<open>
fun add_globals_swap_rewrites member_thms ctxt = let
    fun cpat pat = Thm.cterm_of ctxt (Proof_Context.read_term_pattern ctxt pat)
    val gav = Proof_Context.get_thm ctxt "global_acc_valid"
    val glv = Proof_Context.get_thm ctxt "globals_list_valid"
    val gld = Proof_Context.get_thm ctxt "globals_list_distinct"
    val acc = [Thm.trivial (cpat "PROP ?P"), gav, glv, gld]
        MRS @{thm globals_swap_access_mem2}
    val upd = [Thm.trivial (cpat "PROP ?P"), gav, glv, gld]
        MRS @{thm globals_swap_update_mem2}
    val cg_with_swap = [gav, gld]
        MRS @{thm const_globals_in_memory_to_h_val_with_swap}
    val pinv_safe = [Thm.trivial (cpat "PROP ?P"), gld, glv]
        MRS @{thm global_data_implies_ptr_inverse_safe}
    val empty_ctxt = put_simpset HOL_basic_ss ctxt
    fun unfold_mem thm = let
        val (x, _) = HOLogic.dest_mem (HOLogic.dest_Trueprop (Thm.concl_of thm))
        val (s, _) = dest_Const (head_of x)
      in if s = @{const_name global_data} orelse s = @{const_name const_global_data}
        orelse s = @{const_name addressed_global_data}
        then thm
        else simplify (empty_ctxt addsimps [Proof_Context.get_thm ctxt (s ^ "_def")]) thm
      end

    val member_thms = map unfold_mem member_thms

    val globals_swap_rewrites = member_thms RL [acc, upd]
    val const_globals_rewrites = member_thms RL @{thms const_globals_in_memory_h_val[symmetric]}
    val const_globals_swap_rewrites = member_thms RL [cg_with_swap]
    val pinv_safe_intros = member_thms RL [pinv_safe]
  in ctxt
    |> Local_Theory.note ((@{binding "globals_swap_rewrites"}, []),
            globals_swap_rewrites)
    |> snd
    |> Local_Theory.note ((@{binding "const_globals_rewrites"}, []),
            const_globals_rewrites)
    |> snd
    |> Local_Theory.note ((@{binding "const_globals_rewrites_with_swap"}, []),
            const_globals_swap_rewrites)
    |> snd
    |> Local_Theory.note ((@{binding "pointer_inverse_safe_global_rules"}, []),
            pinv_safe_intros)
    |> snd
  end
\<close>

end
