(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
 * Proofs regarding the State Translation.
 *)

theory StateTranslationProofs_DR
imports StateTranslation_D
begin

context begin interpretation Arch . (*FIXME: arch-split*)

declare transform_current_domain_def [simp]

lemma asid_high_bits [simp]:
  "Types_D.asid_high_bits = asid_high_bits"
  by (simp add:Types_D.asid_high_bits_def asid_high_bits_def)

lemma asid_low_bits [simp]:
  "Types_D.asid_low_bits = asid_low_bits"
  by (simp add:Types_D.asid_low_bits_def asid_low_bits_def)

lemma asid_bits [simp]:
  "Types_D.asid_bits = asid_bits"
  by (simp add:Types_D.asid_bits_def asid_bits_def)

lemma get_obj_simps [simp]:
  "get_obj (s\<lparr>cur_thread := a\<rparr>) = get_obj s"
  apply (rule ext)
  apply (clarsimp simp: get_obj_def)
  done

lemma transform_objects_simps [simp]:
  "transform_objects (s\<lparr>cur_thread := a\<rparr>) = transform_objects s"
  apply (rule ext)
  apply (clarsimp simp: transform_objects_def transform_object_def)
  done

lemma transform_cdt_simps [simp]:
  "transform_cdt (s\<lparr>cur_thread := a\<rparr>) = transform_cdt s"
  apply (rule ext)+
  apply (clarsimp simp: transform_cdt_def split_def)
  done

(* Aggressive simp rules, using explictly *)
abbreviation
"update_machine ms s \<equiv> machine_state_update (\<lambda>_. ms) s"

abbreviation
"update_kheap kh s \<equiv> kheap_update (\<lambda>_. kh) s"

abbreviation
"tcb_set_mi tcb msg \<equiv>
  tcb \<lparr>tcb_context := modify_registers (\<lambda>rs. rs(msg_info_register := msg)) (tcb_context tcb)\<rparr>"

abbreviation
"update_tcb_cxt_badge msg tcb\<equiv>
  tcb \<lparr>tcb_context := modify_registers (\<lambda>rs. rs(badge_register := msg)) (tcb_context tcb)\<rparr>"

abbreviation
"update_tcb_state state tcb \<equiv> tcb \<lparr>tcb_state := state\<rparr>"

abbreviation
"update_tcb_boundntfn ntfn_opt tcb \<equiv> tcb \<lparr>tcb_bound_notification := ntfn_opt\<rparr>"

abbreviation
"dupdate_cdl_object ptr obj s \<equiv>  cdl_objects_update (\<lambda>_. (cdl_objects s)(ptr \<mapsto> obj)) s"

abbreviation
"dupdate_tcb_intent intent tcb\<equiv> tcb \<lparr>cdl_tcb_intent := intent\<rparr>"

lemma update_kheap_triv[simp]:
  "kheap s y = Some obj\<Longrightarrow> update_kheap ((kheap s)(y \<mapsto> obj)) s = s"
  apply (case_tac s,clarsimp)
  apply (rule ext,clarsimp)
done

lemma msg_registers_lt_msg_max_length [simp]:
  "length msg_registers < msg_max_length"
  by (simp add: msg_registers_def msgRegisters_def upto_enum_def
                fromEnum_def enum_register msg_max_length_def)

lemma get_tcb_mrs_update_state :
  "get_tcb_mrs ms (tcb_state_update f tcb) = get_tcb_mrs ms tcb"
  by (clarsimp simp:get_tcb_mrs_def Suc_le_eq get_tcb_message_info_def get_ipc_buffer_words_def)

lemma msg_info_badge_register_no_overlap:
  "badge_register \<noteq> msg_info_register"
  by (clarsimp simp:badge_register_def msg_info_register_def
    ARM.badgeRegister_def
                  ARM.msgInfoRegister_def)

lemma badge_cap_register_overlap:
  "badge_register = cap_register"
by (clarsimp simp:badge_register_def cap_register_def
                  ARM.badgeRegister_def
                  ARM.capRegister_def)

lemma cap_msg_info_register_no_overlap:
  "cap_register \<noteq> msg_info_register"
by (clarsimp simp:msg_info_register_def cap_register_def
                  ARM.msgInfoRegister_def
                  ARM.capRegister_def)

lemmas register_overlap_check = msg_info_badge_register_no_overlap
                                cap_msg_info_register_no_overlap
                                badge_cap_register_overlap

lemma transform_full_intent_cong:
  "\<lbrakk>ms = ms'; ptr = ptr';
    arch_tcb_context_get (tcb_arch tcb) = arch_tcb_context_get (tcb_arch tcb');
    tcb_ipc_buffer tcb = tcb_ipc_buffer tcb'; tcb_ipcframe tcb = tcb_ipcframe tcb'\<rbrakk>
  \<Longrightarrow> transform_full_intent ms ptr tcb = transform_full_intent ms' ptr' tcb'"
  by (simp add: transform_full_intent_def get_tcb_message_info_def get_tcb_mrs_def Suc_le_eq get_ipc_buffer_words_def)

lemma caps_of_state_eq_lift:
  "\<forall>cap. cte_wp_at ((=) cap) p s = cte_wp_at ((=) cap) p s' \<Longrightarrow>  caps_of_state s p = caps_of_state s' p"
  apply (simp add:cte_wp_at_def caps_of_state_def)
  done

lemma caps_of_state_irrelavent_simp:
  "ref \<noteq> epptr \<Longrightarrow> caps_of_state (update_kheap (kh(epptr \<mapsto> obj)) s) (ref, cref) = caps_of_state (update_kheap kh s) (ref, cref)"
  apply (rule caps_of_state_eq_lift)
  apply (clarsimp simp: cte_wp_at_cases)
  done

(* This doesn't satisfy the obvious transformation into capDL because of
   pagetables etc. *)
fun
   caps_of_object :: "kernel_object \<Rightarrow> (bool list \<rightharpoonup> cap)"
where
    "caps_of_object (Structures_A.CNode sz c) = (if well_formed_cnode_n sz c then c else Map.empty)"
  | "caps_of_object (Structures_A.TCB t) = (\<lambda>n. option_map (\<lambda>(f, _). f t) (tcb_cap_cases n))"
  | "caps_of_object _                    = Map.empty"

lemma caps_of_state_def2:
  "caps_of_state s = (\<lambda>ptr. case (option_map caps_of_object (kheap s (fst ptr))) of
                                None \<Rightarrow> None
                              | Some f \<Rightarrow> f (snd ptr))"
  unfolding caps_of_state_def get_cap_def tcb_cnode_map_def
  apply (rule ext)
  apply (clarsimp simp add: split_def get_object_def bind_def gets_def get_def return_def assert_def fail_def)
  apply (case_tac y, simp_all add: bind_def assert_def return_def assert_opt_def fail_def tcb_cap_cases_def
                              split: option.splits)
  done

lemma caps_of_state_update_same_caps:
  assumes kh: "kh ptr = Some ko"
  and    coo: "caps_of_object ko' = caps_of_object ko"
  shows  "caps_of_state (update_kheap (kh(ptr \<mapsto> ko')) s) = caps_of_state (update_kheap kh s)"
  using kh coo
  apply -
  apply (rule ext)
  apply (clarsimp simp add: caps_of_state_def2)
  done

lemma caps_of_state_update_tcb:
  "\<lbrakk> kh thread = Some (TCB tcb);
     (tcb_ctable tcb) =  (tcb_ctable (f tcb));
     (tcb_vtable tcb) =  (tcb_vtable (f tcb));
     (tcb_reply tcb) =  (tcb_reply (f tcb));
     (tcb_caller tcb) =  (tcb_caller (f tcb));
     (tcb_ipcframe tcb) =  (tcb_ipcframe (f tcb)) \<rbrakk>
    \<Longrightarrow>
      caps_of_state (update_kheap (kh(thread \<mapsto> (TCB (f tcb)))) s) =
      caps_of_state (update_kheap kh s)"
  apply (erule caps_of_state_update_same_caps)
  apply (rule ext)
  apply (simp add: tcb_cap_cases_def split: if_split)
  done

lemmas caps_of_state_upds = caps_of_state_update_tcb caps_of_state_update_same_caps

lemma transform_cdt_kheap_update [simp]:
  "transform_cdt (kheap_update f s) = transform_cdt s"
  by (clarsimp simp: transform_cdt_def)

lemma transform_cdt_update_machine [simp]:
  "transform_cdt (update_machine ms s) = transform_cdt s "
  by (clarsimp simp: transform_cdt_def)

lemma transform_cdt_update_original_cap [simp]:
  "transform_cdt (b\<lparr>is_original_cap := x\<rparr>) = transform_cdt b"
  by (clarsimp simp: transform_cdt_def)

lemma transform_asid_table_kheap_update [simp]:
  "transform_asid_table (kheap_update f s) = transform_asid_table s"
  by (clarsimp simp: transform_asid_table_def)

lemma transform_asid_table_update_machine [simp]:
  "transform_asid_table (update_machine ms s) = transform_asid_table s "
  by (clarsimp simp: transform_asid_table_def)

lemma transform_asid_table_update_original_cap [simp]:
  "transform_asid_table (b\<lparr>is_original_cap := x\<rparr>) = transform_asid_table b"
  by (clarsimp simp: transform_asid_table_def)

lemma transform_objects_update_kheap_same_caps:
  "\<lbrakk> kh ptr = Some ko; caps_of_object ko' = caps_of_object ko; a_type ko' = a_type ko\<rbrakk> \<Longrightarrow>
  transform_objects (update_kheap (kh(ptr \<mapsto> ko')) s) =
  (if ptr = idle_thread s then
         transform_objects (update_kheap kh s)
  else
         (transform_objects (update_kheap kh s))(ptr \<mapsto> transform_object (machine_state s) ptr ko'))"
  unfolding transform_objects_def
  apply (rule ext)
  apply (simp add: map_option_case restrict_map_def map_add_def )
  done

lemma transform_objects_update_same:
  "\<lbrakk> kheap s ptr = Some ko; transform_object (machine_state s) ptr ko = ko'; ptr \<noteq> idle_thread s \<rbrakk>
  \<Longrightarrow> (transform_objects s)(ptr \<mapsto> ko') = transform_objects s"
  unfolding transform_objects_def
  by (rule ext) (simp)

text \<open>Facts about map_lift_over\<close>

lemma map_lift_over_eq_Some:
  "(map_lift_over f m x = Some y)
         = (\<exists>x' y'. x = f x' \<and> y = f y' \<and> inj_on f (dom m \<union> ran m)
                   \<and> m x' = Some y')"
proof -
  have P: "inj_on f (dom m \<union> ran m) \<longrightarrow> inj_on f (dom m)"
    by (auto elim: subset_inj_on)
  have Q: "\<And>x y. \<lbrakk> m x = Some y; inj_on f (dom m \<union> ran m) \<rbrakk>
                  \<Longrightarrow> inv_into (dom m) f (f x) = x"
    using P
    by (blast intro: inv_into_f_f)
  show ?thesis
    by (auto simp add: map_lift_over_def Q)
qed

lemma map_lift_over_eq_None:
  "(map_lift_over f m x = None)
         = (inj_on f (dom m \<union> ran m) \<longrightarrow>
                (\<forall>x'. x = f x' \<longrightarrow> m x' = None))"
proof -
  have P: "inj_on f (dom m \<union> ran m) \<Longrightarrow> inj_on f (dom m)"
    by (auto elim: subset_inj_on)
  show ?thesis
    by (auto simp add: map_lift_over_def P[THEN inv_into_f_f] domI
                       inj_on_eq_iff[where f=f]
           | rule ccontr[where P="v = None" for v])+
qed

lemma map_lift_over_f_eq:
  "inj_on f ({x} \<union> dom m \<union> ran m) \<Longrightarrow>
   (map_lift_over f m (f x) = v) = (v = map_option f (m x))"
  apply (cases v, simp_all add: map_lift_over_eq_None map_lift_over_eq_Some)
   apply (auto simp: option_map_def split: option.split)
  done

lemma map_lift_over_eq_cases[unfolded map_lift_over_eq_None map_lift_over_eq_Some]:
  "(map_lift_over f m x = v)
       = (case v of None \<Rightarrow> map_lift_over f m x = None
                | Some z \<Rightarrow> map_lift_over f m x = Some z)"
  by (simp split: option.split)

lemma map_lift_over_upd:
  assumes inj_f: "inj_on f ({x} \<union> set_option y \<union> dom m \<union> ran m)"
  shows "(map_lift_over f (m(x := y)))
           = ((map_lift_over f m) (f x := map_option f y))"
proof -
  have Q: "inj_on f (dom m \<union> ran m)"
      "inj_on f (insert x (dom m \<union> ran (m(x := y))))"
      "inj_on f (dom m)"
      "inj_on f (insert x (dom m))"
      "inj_on f (dom m - {x} \<union> ran (m(x := None)))"
      "inj_on f (dom m - {x})"
    apply (safe intro!: subset_inj_on[OF inj_f])
    apply (auto simp: ran_def split: if_split_asm)
    done
  show ?thesis
    apply (simp add: map_lift_over_def Q del: inj_on_insert)
    apply (safe; rule ext; simp add: Q[THEN inv_into_f_f] domI cong del: imp_cong)
     apply (auto simp add: Q[THEN inv_into_f_f] domI inj_on_eq_iff[OF inj_f] ranI
                 simp del: inj_on_insert)
    done
qed

lemma map_lift_over_if_eq_twice:
  assumes inj_f: "inj_on f (dom m \<union> ran m \<union> {y, y'} \<union> set_option z \<union> set_option z')"
  shows
  "map_lift_over f (\<lambda>x. if m x = Some y then z else if m x = Some y' then z' else m x)
       = (\<lambda>x. if map_lift_over f m x = Some (f y) then map_option f z
              else if map_lift_over f m x = Some (f y') then map_option f z'
              else map_lift_over f m x)"
  (is "map_lift_over f ?ifeq = ?rhs")
proof -
  from inj_f
  have 1: "inj_on f (dom m \<union> ran m)" "inj_on f (dom m)"
    by (auto simp: inj_on_Un)
  have "dom ?ifeq \<subseteq> dom m"
    by (auto split: if_split_asm)
  with inj_f
  have 2: "inj_on f (dom ?ifeq)"
    by (auto elim!: subset_inj_on)
  have "dom ?ifeq \<union> ran ?ifeq \<subseteq> dom m \<union> ran m \<union> set_option z \<union> set_option z'"
    by (auto simp: ran_def)
  with inj_f
  have "inj_on f (dom ?ifeq \<union> ran ?ifeq)"
    by (auto elim!: subset_inj_on)
  note Q = 1 2 this
  note if_split[split del] if_cong[cong]
  show ?thesis
    apply (simp add: map_lift_over_def Q)
    apply (rule ext)
    apply (case_tac "x \<in> f ` dom ?ifeq")
     apply clarsimp
     apply (subst if_P, fastforce split: if_split_asm)+
     apply (simp add: Q[THEN inv_into_f_f] domI ranI inj_on_eq_iff[OF inj_f]
               split: if_split_asm)
    apply (subst if_not_P, simp, rule allI, fastforce)+
    apply (auto simp: option_map_def Q[THEN inv_into_f_f] domI ranI
                      inj_on_eq_iff[OF inj_f]
               split: if_split option.split)
    done
qed

lemma map_lift_over_if_eq:
  assumes inj_f: "inj_on f (dom m \<union> ran m \<union> {y} \<union> set_option z)"
  shows
  "map_lift_over f (\<lambda>x. if m x = Some y then z else m x)
       = (\<lambda>x. if map_lift_over f m x = Some (f y) then map_option f z
              else map_lift_over f m x)"
  using inj_f map_lift_over_if_eq_twice[where f=f and m=m and y=y and z=z and y'=y and z'=z]
  apply (simp del: inj_on_insert)
  done

end

end
