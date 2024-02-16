(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Helpers_SD
imports
  "Lookups_D"
  "Lib.SimpStrategy"
  "Lib.LemmaBucket"
  "Sep_Algebra.Map_Extra"
begin

(* Functions we need from capDL, but can't have yet (until we change capDL).
 * Maybe they aren't actually needed for the proof.
 * (If capDL doesn't have them, then we might not need them to prove conformance.)
 *)

consts tcb_priority :: "cdl_tcb \<Rightarrow> word8 \<times> word8"
consts tcb_ip :: "cdl_tcb \<Rightarrow> word32"
consts tcb_sp :: "cdl_tcb \<Rightarrow> word32"
consts opt_vmattribs :: "cdl_object \<Rightarrow> cdl_raw_vmattrs option"

(* We don't need to know anything about this except that it isn't 0. *)
definition tcb_ipc_buffer_address :: "cdl_tcb \<Rightarrow> word32"
where "tcb_ipc_buffer_address tcb = 1"

lemma tcb_ipc_buffer_address_non_zero:
  "tcb_ipc_buffer_address tcb \<noteq> 0"
  by (clarsimp simp: tcb_ipc_buffer_address_def)

(* Helper funtions. These possibly should be moved somewhere else. *)


(***************************************************
 * Generic Isabelle lemmas. Could be moved to lib. *
 ***************************************************)
lemma map_upd_nonempty' [simp]: "Map.empty \<noteq> t(k\<mapsto>x)"
  by (rule not_sym, simp)

lemma insert_unit_set [simp]:
  "insert () A = UNIV"
  by auto

lemma restrict_map_not_empty [simp]:
  "f p = Some v \<Longrightarrow> f |` {p} \<noteq> Map.empty"
  "f p = Some v \<Longrightarrow> Map.empty \<noteq> f |` {p}"
  by (clarsimp simp: restrict_map_def fun_eq_iff split: if_split_asm)+

(* This lets us compose a total and a partial function in the obvious manner. *)
definition
  map_comp' :: "('b \<Rightarrow> 'c) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> 'a \<rightharpoonup> 'c"  (infixl "o'_M" 55) where
  "f o_M g = (\<lambda>k. case g k of None \<Rightarrow> None | Some v \<Rightarrow> Some (f v))"

notation (xsymbols)
  map_comp'  (infixl "\<circ>\<^sub>M" 55)

lemma map_comp'_apply [simp]: "(f \<circ>\<^sub>M g) x = case_option None (\<lambda>x. Some (f x)) (g x)"
  by (clarsimp simp: map_comp'_def)

lemma map_comp'_empty [simp]:
  "m \<circ>\<^sub>M Map.empty = Map.empty"
  by auto

lemma dom_map_comp' [simp]:
  "dom (f \<circ>\<^sub>M m) = dom m"
  by (clarsimp simp: dom_def split: option.splits)

lemma restrict_map_comp' [simp]:
  "f \<circ>\<^sub>M g |` S = (f \<circ>\<^sub>M g) |` S"
  by (rule ext, clarsimp simp: map_comp'_def restrict_map_def)


(**************************
 * Rules about intervals. *
 **************************)

lemma nat_list_not_UNIV [simp]:
  "set (xs::nat list) \<noteq> UNIV"
  by (metis UNIV_I gt_ex leD maximum_ge)

(***********************************
 * End of generic Isabelle lemmas. *
 ***********************************)


(*************************************
 * Rules that should go in MapExtra. *
 *************************************)

lemma map_add_self:
  "m ++ m = m"
  by (auto simp add:map_add_def split:option.splits)

(* This lemma is strictly weaker than restrict_map_disj. *)
lemma restrict_map_disj':
  "S \<inter> T = {} \<Longrightarrow> h |` S \<bottom> h' |` T"
  by (auto simp: map_disj_def restrict_map_def dom_def)

lemma map_add_restrict_comm:
  "S \<inter> T = {} \<Longrightarrow> h |` S ++ h' |` T = h' |` T ++ h |` S"
  apply (drule restrict_map_disj')
  apply (erule map_add_com)
  done

lemma restrict_map_not_self_UNIV [simp]:
  "h |` (UNIV - dom h) = Map.empty"
  by (rule ext, clarsimp simp: restrict_map_def)

lemma map_add_emptyE [elim!]:
  "\<lbrakk>a ++ b = Map.empty; \<lbrakk>a = Map.empty; b = Map.empty\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (metis map_add_None)

lemma restrict_map_sub_singleton [simp]:
  "s \<noteq> t \<Longrightarrow> h `- {t} |` {s} = h |` {s}"
  by (rule ext)(clarsimp simp: restrict_map_def sub_restrict_map_def)

lemma restrict_map_sub_add': "h `- S ++ h |` S = h"
  by (fastforce simp: sub_restrict_map_def map_add_def
               split: option.splits)

lemma map_add_restrict_singleton:
  "s \<noteq> t \<Longrightarrow> (m |` {s} ++ m' |` {t}) |` {s} = m |` {s}"
  apply (rule ext)
  apply (clarsimp simp: map_add_def restrict_map_def split: option.splits)
  done

lemma map_add_restrict_singleton':
  "s \<noteq> t \<Longrightarrow> (m |` {s} ++ m' |` {t}) |` {t} = m' |` {t}"
  apply (rule ext)
  apply (clarsimp simp: map_add_def restrict_map_def split: option.splits)
  done

(********************************************
 * End of rules that should go in MapExtra. *
 ********************************************)



(**********************************************************
 * CapDL specific lemmas, that could be moved into capDL. *
 * These have nothing to do with the separation logic.    *
 **********************************************************)

definition
  all_caps :: "cdl_state \<Rightarrow> cdl_cap set"
where
"all_caps spec = {cap. \<exists>obj_id slot. opt_cap (obj_id,slot) spec = Some cap \<and> cap \<noteq> NullCap}"

lemma all_capsE [elim!]:
  "\<lbrakk>opt_cap (obj_id, slot) spec = Some cap; cap \<noteq> NullCap\<rbrakk> \<Longrightarrow> cap \<in> all_caps spec"
  "\<lbrakk>opt_cap cap_ref spec = Some cap; cap \<noteq> NullCap\<rbrakk> \<Longrightarrow> cap \<in> all_caps spec"
  apply (clarsimp simp: all_caps_def|fast)+
  by (metis surj_pair)


lemma default_tcb_slots:
 "[0 ..< tcb_pending_op_slot] = [0,1,2,3,4]"
 "[0 ..< 5] = [0,1,2,3,4]"
 "[0 .e. tcb_pending_op_slot] = [0,1,2,3,4,5]"
 "[0 .e. (5::nat)] = [0,1,2,3,4,5]"
 "[0..< 6] = [0,1,2,3,4,5]"
 "[0..< 7] = [0,1,2,3,4,5,6]"
  by (clarsimp simp: tcb_pending_op_slot_def upt_rec)+

definition "update_tcb_fault_endpoint fault_ep = cdl_tcb_fault_endpoint_update (\<lambda>_. fault_ep)"

lemma update_tcb_fault_endpoint_id [simp]:
  "cdl_tcb_fault_endpoint tcb = fault_ep
  \<Longrightarrow> update_tcb_fault_endpoint fault_ep tcb = tcb"
  by (clarsimp simp: update_tcb_fault_endpoint_def)

definition tcb_has_fault :: "cdl_object \<Rightarrow> bool"
where
  "tcb_has_fault obj \<equiv> case obj of Tcb tcb \<Rightarrow> cdl_tcb_has_fault tcb | _ \<Rightarrow> False"

definition tcb_domain :: "cdl_object \<Rightarrow> word8"
where
  "tcb_domain obj \<equiv> case obj of Tcb tcb \<Rightarrow> cdl_tcb_domain tcb | _ \<Rightarrow> 0"

definition update_cap_object :: "cdl_object_id \<Rightarrow> cdl_cap \<Rightarrow> cdl_cap"
where
  "update_cap_object obj_id cap \<equiv> case cap of
    IOPageTableCap _ \<Rightarrow> IOPageTableCap obj_id
  | IOSpaceCap _ \<Rightarrow> IOSpaceCap obj_id
  | IOPortsCap _ f2 \<Rightarrow> IOPortsCap obj_id f2
  | AsidPoolCap _ f2 \<Rightarrow> AsidPoolCap obj_id f2
  | PageDirectoryCap _ f2 f3 \<Rightarrow> PageDirectoryCap obj_id f2 f3
  | PageTableCap _ f2 f3 \<Rightarrow> PageTableCap obj_id f2 f3
  | FrameCap dev _ f2 f3 f4 f5 \<Rightarrow> FrameCap dev obj_id f2 f3 f4 f5
  | TcbCap _ \<Rightarrow> TcbCap obj_id
  | CNodeCap _ f2 f3 f4 \<Rightarrow> CNodeCap obj_id f2 f3 f4
  | MasterReplyCap _ \<Rightarrow> MasterReplyCap obj_id
  | ReplyCap _ f2 \<Rightarrow> ReplyCap obj_id f2
  | NotificationCap _ f2 f3 \<Rightarrow> NotificationCap obj_id f2 f3
  | EndpointCap _ f2 f3 \<Rightarrow> EndpointCap obj_id f2 f3
  | ZombieCap _ \<Rightarrow> ZombieCap obj_id
  | PendingSyncSendCap _ f2 f3 f4 f5 f6 \<Rightarrow> PendingSyncSendCap obj_id f2 f3 f4 f5 f6
  | PendingSyncRecvCap _ f2 f3 \<Rightarrow> PendingSyncRecvCap obj_id f2 f3
  | PendingNtfnRecvCap _ \<Rightarrow> PendingNtfnRecvCap obj_id
  | BoundNotificationCap _ \<Rightarrow> BoundNotificationCap obj_id
  | _ \<Rightarrow> cap"

definition update_cap_objects :: "cdl_object_id set \<Rightarrow> cdl_cap \<Rightarrow> cdl_cap"
where
    "update_cap_objects obj_ids cap \<equiv> case cap of
    UntypedCap d _ a \<Rightarrow> UntypedCap d obj_ids a
  | _ \<Rightarrow> cap"

lemma slots_of_cdl_objects:
  "slots_of obj_id s slot = Some cap \<Longrightarrow> \<exists>obj. cdl_objects s obj_id = Some obj"
  by (clarsimp simp: slots_of_def split: option.splits)

lemma opt_cap_cdl_objects:
  "opt_cap (obj_id, slot) s = Some cap \<Longrightarrow> \<exists>obj. cdl_objects s obj_id = Some obj"
  by (clarsimp simp: opt_cap_def slots_of_cdl_objects)

lemma object_slots_slots_of:
  "\<lbrakk>slots_of obj_id spec slot = Some cap; cdl_objects spec obj_id = Some obj\<rbrakk>
  \<Longrightarrow> object_slots obj slot = Some cap"
  by (clarsimp simp: slots_of_def)

lemma object_slots_opt_cap:
  "\<lbrakk>opt_cap cap_ref spec = Some cap; cdl_objects spec obj_id = Some obj; cap_ref = (obj_id, slot)\<rbrakk>
  \<Longrightarrow> object_slots obj slot = Some cap"
  by (clarsimp simp: opt_cap_def object_slots_slots_of split: prod.split_asm)+

lemma object_slots_opt_capI:
  "\<lbrakk>opt_cap (obj_id, slot) spec = Some cap; cdl_objects spec obj_id = Some obj\<rbrakk>
  \<Longrightarrow> object_slots obj slot = Some cap"
  by (clarsimp simp: opt_cap_def object_slots_slots_of split: prod.split_asm)

lemma object_slots_opt_capD:
  "\<lbrakk>opt_cap cap_ref spec = Some cap; cdl_objects spec (fst cap_ref) = Some obj\<rbrakk>
  \<Longrightarrow> object_slots obj (snd cap_ref) = Some cap"
  by (clarsimp simp: opt_cap_def object_slots_slots_of split: prod.split_asm)

lemma object_slots_has_slots:
  "object_slots obj \<noteq> Map.empty \<Longrightarrow> has_slots obj"
  by (clarsimp simp: has_slots_def object_slots_def split: cdl_object.splits)

lemma slots_of_dom_cdl_objects [elim!]:
  "slots_of obj_id spec slot = Some cap \<Longrightarrow> obj_id \<in> dom (cdl_objects spec)"
  "slots_of obj_id spec slot = Some cap \<Longrightarrow> \<exists>slot. cdl_objects spec obj_id = Some slot"
 by (clarsimp simp: slots_of_def split:option.splits)+

lemma opt_cap_dom_cdl_objects [elim]:
  "opt_cap (obj_id, slot) spec = Some cap \<Longrightarrow> obj_id \<in> dom (cdl_objects spec)"
  "opt_cap cap_ref spec = Some cap \<Longrightarrow> fst cap_ref \<in> dom (cdl_objects spec)"
  by (clarsimp simp: opt_cap_def split: prod.split_asm)+

lemma opt_cap_dom_slots_of [elim]:
  "opt_cap (obj_id, slot) spec = Some cap \<Longrightarrow> slot \<in> dom (slots_of obj_id spec)"
  "opt_cap cap_ref spec = Some cap \<Longrightarrow> snd cap_ref \<in> dom (slots_of (fst cap_ref) spec)"
  by (clarsimp simp: opt_cap_def split: prod.split_asm)+

(*
 * Untyped cap rules.
 *)

definition
  well_formed_untyped_cap :: "cdl_cap \<Rightarrow> bool"
where
  "well_formed_untyped_cap cap \<equiv> case cap of
    UntypedCap _ cover_ids available_ids \<Rightarrow> available_ids \<subseteq> cover_ids
  | _ \<Rightarrow> True"

lemma cap_free_ids_simps:
  "cap_free_ids (UntypedCap d cover_ids available_ids) = available_ids"
  by (clarsimp simp: cap_free_ids_def)


lemma cap_objects_remove_free_ids [simp]:
  "cap_objects (remove_free_ids cap obj_ids) = cap_objects cap"
  by (clarsimp simp: cap_objects_def remove_free_ids_def
              split: cdl_cap.splits)

lemma cap_free_ids_remove_free_ids:
  "cap_free_ids (remove_free_ids cap obj_ids) = cap_free_ids cap - obj_ids"
  by (clarsimp simp: remove_free_ids_def cap_free_ids_def
              split: cdl_cap.splits)

lemma cap_type_remove_free_ids [simp]:
  "cap_type (remove_free_ids cap obj_ids) = cap_type cap"
  by (clarsimp simp: cap_type_def remove_free_ids_def
              split: cdl_cap.splits)

definition
  is_device_cap :: "cdl_cap \<Rightarrow> bool"
where  "is_device_cap cap \<equiv> case cap of
   (UntypedCap dev cover_ids available_ids) \<Rightarrow> dev
   | (FrameCap dev _ _ _ _ _) \<Rightarrow> dev
   | _ \<Rightarrow> False"

lemmas is_device_cap_simps[simp] = is_device_cap_def[split_simps cdl_cap.split]

lemma remove_free_ids_simps:
  "\<lbrakk>is_untyped_cap cap; available_ids \<subseteq> cap_free_ids cap\<rbrakk>
  \<Longrightarrow> remove_free_ids cap (cap_free_ids cap - available_ids)
    = UntypedCap (is_device_cap cap) (cap_objects cap) available_ids"
  by (auto simp: remove_free_ids_def cap_free_ids_def cap_type_def
          split: cdl_cap.splits)

definition
  is_full_untyped_cap :: "cdl_cap \<Rightarrow> bool"
where
  "is_full_untyped_cap cap \<equiv> case cap of
     UntypedCap dev cover_ids available_ids \<Rightarrow> cover_ids = available_ids
   | _ \<Rightarrow> False"

lemma is_full_untyped_cap_is_untyped_cap:
  "is_full_untyped_cap cap \<Longrightarrow> is_untyped_cap cap"
  by (clarsimp simp: is_full_untyped_cap_def split: cdl_cap.splits)

lemma is_full_untyped_cap_simps:
  "is_full_untyped_cap cap \<Longrightarrow> cap_objects cap = cap_free_ids cap"
  by (auto simp: is_full_untyped_cap_def cap_free_ids_def
          split: cdl_cap.splits)

lemma is_full_untyped_cap_eq:
  "is_untyped_cap cap
  \<Longrightarrow> is_full_untyped_cap cap = (cap_objects cap = cap_free_ids cap)"
  by (auto simp: is_full_untyped_cap_def cap_free_ids_def
                 cap_objects_def cap_type_def
          split: cdl_cap.splits)

lemma well_formed_untyped_cap_remove_free_ids:
  "well_formed_untyped_cap cap
  \<Longrightarrow> well_formed_untyped_cap (remove_free_ids cap obj_ids)"
  by (auto simp: well_formed_untyped_cap_def remove_free_ids_def
          split: cdl_cap.splits)

lemma well_formed_untyped_cap_simps:
  "is_untyped_cap cap
  \<Longrightarrow> well_formed_untyped_cap cap = (cap_free_ids cap \<subseteq> cap_objects cap)"
  by (clarsimp simp: well_formed_untyped_cap_def cap_free_ids_def
                     cap_objects_def cap_type_def
              split: cdl_cap.splits)


definition
  some_nat :: "nat option \<Rightarrow> nat"
where
  "some_nat n \<equiv> case n of Some n \<Rightarrow> n | None \<Rightarrow> 0"

lemma some_nat_Some [simp]:
  "some_nat (Some n) = n"
  by (simp add: some_nat_def)

lemma some_nat_None [simp]:
  "some_nat None = 0"
  by (simp add: some_nat_def)

definition
  is_untyped :: "cdl_object \<Rightarrow> bool" where
 "is_untyped v \<equiv> case v of Untyped \<Rightarrow> True | _ \<Rightarrow> False"

definition
  is_ep :: "cdl_object \<Rightarrow> bool" where
 "is_ep v \<equiv> case v of Endpoint \<Rightarrow> True | _ \<Rightarrow> False"

definition
  is_ntfn :: "cdl_object \<Rightarrow> bool" where
 "is_ntfn v \<equiv> case v of Notification \<Rightarrow> True | _ \<Rightarrow> False"

definition
  is_tcb :: "cdl_object \<Rightarrow> bool" where
 "is_tcb v \<equiv> case v of Tcb _ \<Rightarrow> True | _ \<Rightarrow> False"

definition
  is_cnode :: "cdl_object \<Rightarrow> bool" where
 "is_cnode v \<equiv> case v of CNode _ \<Rightarrow> True | _ \<Rightarrow> False"

definition
  is_irq_node :: "cdl_object \<Rightarrow> bool" where
 "is_irq_node v \<equiv> case v of IRQNode _ \<Rightarrow> True | _ \<Rightarrow> False"

definition
  is_asidpool :: "cdl_object \<Rightarrow> bool" where
 "is_asidpool v \<equiv> case v of AsidPool _ \<Rightarrow> True | _ \<Rightarrow> False"

definition
  is_pt :: "cdl_object \<Rightarrow> bool" where
 "is_pt v \<equiv> case v of PageTable _ \<Rightarrow> True | _ \<Rightarrow> False"

definition
  is_pd :: "cdl_object \<Rightarrow> bool" where
 "is_pd v \<equiv> case v of PageDirectory _ \<Rightarrow> True | _ \<Rightarrow> False"

definition
  is_frame :: "cdl_object \<Rightarrow> bool" where
 "is_frame v \<equiv> case v of Frame _ \<Rightarrow> True | _ \<Rightarrow> False"


definition
  object_domain :: "cdl_object \<Rightarrow> word8"
where
  "object_domain obj \<equiv> case obj of
      Tcb tcb \<Rightarrow> cdl_tcb_domain tcb
    | _ \<Rightarrow> 0"

lemma is_object_simps [simp]:
  "is_untyped Untyped"
  "is_ep Endpoint"
  "is_ntfn Notification"
  "is_tcb (Tcb tcb)"
  "is_cnode (CNode c)"
  "is_asidpool (AsidPool a)"
  "is_pd (PageDirectory pd)"
  "is_pt (PageTable pt)"
  "is_frame (Frame f)"
  by (clarsimp simp: is_untyped_def is_ep_def is_ntfn_def is_tcb_def is_cnode_def
                     is_asidpool_def is_pt_def is_pd_def is_frame_def)+


(* These sizes are needed for ARM *)
definition pt_size :: nat
where
  "pt_size = 8"

definition pd_size :: nat
where
  "pd_size = 12"

definition small_frame_size :: nat
where
  "small_frame_size = 12"

definition
  object_size_bits :: "cdl_object \<Rightarrow> cdl_size_bits"
where
  "object_size_bits obj \<equiv> case obj of
      CNode cnode \<Rightarrow> cdl_cnode_size_bits cnode
    | AsidPool ap \<Rightarrow> asid_low_bits
    | Frame frame \<Rightarrow> cdl_frame_size_bits frame
    | PageTable cdl_page_table \<Rightarrow> pt_size
    | PageDirectory cdl_page_directory \<Rightarrow> pd_size
    | _ \<Rightarrow> 0"

lemma object_size_bits_default_tcb [simp]:
  "object_size_bits (Tcb (default_tcb domain)) = 0"
  by (clarsimp simp: object_size_bits_def default_tcb_def)

lemma object_size_bits_empty_cnode [simp]:
  "object_size_bits (CNode (empty_cnode sz)) = sz"
  by (clarsimp simp: object_size_bits_def empty_cnode_def)

lemma is_pt_pt_size[simp]: "is_pt obj \<Longrightarrow> object_size_bits obj = pt_size"
  by (clarsimp simp: object_size_bits_def pt_size_def is_pt_def split: cdl_object.splits)

lemma is_pd_pd_size[simp]: "is_pd obj \<Longrightarrow> object_size_bits obj = pd_size"
  by (clarsimp simp: object_size_bits_def pt_size_def is_pd_def split: cdl_object.splits)

definition
  object_at_pointer_size_bits :: "cdl_state \<Rightarrow> cdl_object_id \<Rightarrow> cdl_size_bits"
where
  "object_at_pointer_size_bits spec obj_id \<equiv>
   some_nat (option_map object_size_bits (cdl_objects spec obj_id))"

lemma object_at_pointer_size_bits_simp [simp]:
  "cdl_objects spec obj_id = Some object
  \<Longrightarrow> object_at_pointer_size_bits spec obj_id = object_size_bits object"
  by (simp add: object_at_pointer_size_bits_def)

definition
  object_at :: "(cdl_object \<Rightarrow> bool) \<Rightarrow> cdl_object_id \<Rightarrow> cdl_state \<Rightarrow> bool"
where
  "object_at P obj_id s \<equiv> \<exists>object. cdl_objects s obj_id = Some object \<and> P object"

abbreviation
  "untyped_at \<equiv> object_at is_untyped"
abbreviation
  "ep_at \<equiv> object_at is_ep"
abbreviation
  "ntfn_at \<equiv> object_at is_ntfn"
abbreviation
  "tcb_at \<equiv> object_at is_tcb"
abbreviation
  "cnode_at \<equiv> object_at is_cnode"
abbreviation
  "irq_node_at \<equiv> object_at is_irq_node"
abbreviation
  "asidpool_at \<equiv> object_at is_asidpool"
abbreviation
  "pt_at \<equiv> object_at is_pt"
abbreviation
  "pd_at \<equiv> object_at is_pd"
abbreviation
  "frame_at \<equiv> object_at is_frame"

(* Threads that are waiting to run. *)
definition
  is_waiting_thread :: "cdl_object \<Rightarrow> bool"
where
  "is_waiting_thread obj \<equiv> is_tcb obj \<and> object_slots obj tcb_pending_op_slot = Some RestartCap"

abbreviation
  "is_waiting_thread_at \<equiv> object_at is_waiting_thread"

definition
  irq_nodes :: "cdl_state \<Rightarrow> cdl_object_id set"
where
  "irq_nodes \<equiv> \<lambda>s. {obj_id. irq_node_at obj_id s}"

definition
  bound_irqs :: "cdl_state \<Rightarrow> cdl_irq set"
where
  "bound_irqs \<equiv> \<lambda>s. {irq. \<exists>cap. slots_of (cdl_irq_node s irq) s 0 = Some cap \<and> cap \<noteq> NullCap}"

definition
  bound_irq_list :: "cdl_state \<Rightarrow> cdl_irq list"
where
  "bound_irq_list \<equiv>
     \<lambda>s. [irq \<leftarrow> [0 .e. maxBound].
            case slots_of (cdl_irq_node s irq) s 0 of
              None \<Rightarrow> False
            | Some cap \<Rightarrow> cap \<noteq> NullCap]"

lemma bound_irq_list_set[simp]: "set (bound_irq_list s) = bound_irqs s"
  apply (clarsimp simp: bound_irqs_def bound_irq_list_def image_def)
  apply (intro set_eqI iffI)
   apply (fastforce split: option.splits)
  apply (unat_arith, clarsimp)
  done

lemma bound_irq_list_distinct[intro]: "distinct (bound_irq_list s)"
  by (clarsimp simp: bound_irq_list_def)

definition
  used_irqs :: "cdl_state \<Rightarrow> cdl_irq set"
where
  "used_irqs \<equiv> \<lambda>s. {irq. \<exists>cap. cap \<in> all_caps s \<and> is_irqhandler_cap cap \<and> cap_irq cap = irq}"

definition
  used_irq_list :: "cdl_state \<Rightarrow> cdl_irq list"
where
  "used_irq_list \<equiv> \<lambda>s. sorted_list_of_set (used_irqs s)"

definition
  used_irq_nodes :: "cdl_state \<Rightarrow> cdl_object_id set"
where
  "used_irq_nodes \<equiv> \<lambda>s. cdl_irq_node s ` used_irqs s"

(* Distinctions between "real objects" and IRQ objects. *)
definition
  "real_object_at \<equiv> \<lambda> obj_id s. obj_id \<in> dom (cdl_objects s) \<and> obj_id \<notin> irq_nodes s"


(* Aggregate object types. *)
abbreviation
  "table_at \<equiv> \<lambda>obj_id s. pt_at obj_id s \<or> pd_at obj_id s"
abbreviation
  "capless_at \<equiv> \<lambda>obj_id s. untyped_at obj_id s \<or> ep_at obj_id s \<or> ntfn_at obj_id s \<or> frame_at obj_id s"
abbreviation
  "cnode_or_tcb_at \<equiv> \<lambda>obj_id spec. cnode_at obj_id spec \<or> tcb_at obj_id spec"
abbreviation
  "memory_object_at \<equiv> \<lambda>obj_id spec. pt_at obj_id spec \<or> pd_at obj_id spec \<or> frame_at obj_id spec"

lemma capless_at_def2:
  "capless_at p s = object_at (\<lambda>obj. \<not> (has_slots obj)) p s"
  apply (clarsimp simp: has_slots_def object_at_def)
  apply (fastforce simp: is_untyped_def is_ep_def is_ntfn_def is_frame_def
                 split: cdl_object.splits)
  done

abbreviation
  "ko_at k \<equiv> object_at ((=) k)"

lemma ko_at_tcb_at:
  "ko_at (Tcb t) p s \<Longrightarrow> tcb_at p s"
  by (simp add: object_at_def is_tcb_def)

abbreviation
  "type_at T \<equiv> object_at (\<lambda>ob. object_type ob = T)"

lemma length_used_irq_list [simp]:
  "length (used_irq_list spec) = card (used_irqs spec)"
  by (clarsimp simp: used_irq_list_def)

lemma distinct_used_irq_list [simp]:
  "distinct (used_irq_list spec)"
  by (simp add: used_irq_list_def)

lemma set_used_irq_list [simp]:
  "set (used_irq_list spec) = used_irqs spec"
  by (simp add: used_irq_list_def)


lemma object_type_is_object:
  "is_untyped obj  = (object_type obj = UntypedType)"
  "is_ep obj       = (object_type obj = EndpointType)"
  "is_ntfn obj      = (object_type obj = NotificationType)"
  "is_tcb obj      = (object_type obj = TcbType)"
  "is_cnode obj    = (object_type obj = CNodeType)"
  "is_irq_node obj = (object_type obj = IRQNodeType)"
  "is_asidpool obj = (object_type obj = AsidPoolType)"
  "is_pt obj       = (object_type obj = PageTableType)"
  "is_pd obj       = (object_type obj = PageDirectoryType)"
  "is_frame obj    = (\<exists>n. object_type obj = FrameType n)"
  by (simp_all add: object_type_def is_untyped_def is_ep_def is_ntfn_def is_tcb_def
                    is_cnode_def is_irq_node_def is_asidpool_def is_pt_def is_pd_def is_frame_def
             split: cdl_object.splits)

lemma is_ptD[dest]: "is_pt obj \<Longrightarrow> \<exists>x. obj = PageTable x"
  by (clarsimp simp: is_pt_def split: cdl_object.splits)

lemma object_at_object_type:
  "\<lbrakk>cdl_objects spec obj_id = Some obj; untyped_at obj_id spec\<rbrakk> \<Longrightarrow> object_type obj = UntypedType"
  "\<lbrakk>cdl_objects spec obj_id = Some obj; ep_at obj_id spec\<rbrakk> \<Longrightarrow> object_type obj = EndpointType"
  "\<lbrakk>cdl_objects spec obj_id = Some obj; ntfn_at obj_id spec\<rbrakk> \<Longrightarrow> object_type obj = NotificationType"
  "\<lbrakk>cdl_objects spec obj_id = Some obj; tcb_at obj_id spec\<rbrakk> \<Longrightarrow> object_type obj = TcbType"
  "\<lbrakk>cdl_objects spec obj_id = Some obj; cnode_at obj_id spec\<rbrakk> \<Longrightarrow> object_type obj = CNodeType"
  "\<lbrakk>cdl_objects spec obj_id = Some obj; irq_node_at obj_id spec\<rbrakk> \<Longrightarrow> object_type obj = IRQNodeType"
  "\<lbrakk>cdl_objects spec obj_id = Some obj; asidpool_at obj_id spec\<rbrakk> \<Longrightarrow> object_type obj = AsidPoolType"
  "\<lbrakk>cdl_objects spec obj_id = Some obj; pt_at obj_id spec\<rbrakk> \<Longrightarrow> object_type obj = PageTableType"
  "\<lbrakk>cdl_objects spec obj_id = Some obj; pd_at obj_id spec\<rbrakk> \<Longrightarrow> object_type obj = PageDirectoryType"
  "\<lbrakk>cdl_objects spec obj_id = Some obj; frame_at obj_id spec\<rbrakk> \<Longrightarrow> \<exists>n. object_type obj = FrameType n"
  by (simp_all add: object_at_def object_type_is_object)

lemma object_type_object_at:
  "\<lbrakk>cdl_objects spec obj_id = Some obj; object_type obj = UntypedType\<rbrakk> \<Longrightarrow> untyped_at obj_id spec"
  "\<lbrakk>cdl_objects spec obj_id = Some obj; object_type obj = EndpointType\<rbrakk> \<Longrightarrow> ep_at obj_id spec"
  "\<lbrakk>cdl_objects spec obj_id = Some obj; object_type obj = NotificationType\<rbrakk> \<Longrightarrow> ntfn_at obj_id spec"
  "\<lbrakk>cdl_objects spec obj_id = Some obj; object_type obj = TcbType\<rbrakk> \<Longrightarrow> tcb_at obj_id spec"
  "\<lbrakk>cdl_objects spec obj_id = Some obj; object_type obj = CNodeType\<rbrakk> \<Longrightarrow> cnode_at obj_id spec"
  "\<lbrakk>cdl_objects spec obj_id = Some obj; object_type obj = IRQNodeType\<rbrakk> \<Longrightarrow> irq_node_at obj_id spec"
  "\<lbrakk>cdl_objects spec obj_id = Some obj; object_type obj = AsidPoolType\<rbrakk> \<Longrightarrow> asidpool_at obj_id spec"
  "\<lbrakk>cdl_objects spec obj_id = Some obj; object_type obj = PageTableType\<rbrakk> \<Longrightarrow> pt_at obj_id spec"
  "\<lbrakk>cdl_objects spec obj_id = Some obj; object_type obj = PageDirectoryType\<rbrakk> \<Longrightarrow> pd_at obj_id spec"
  by (simp_all add: object_at_def object_type_is_object)

lemma set_object_type [simp]:
  "{obj_id \<in> dom (cdl_objects spec). object_at P obj_id spec} = {obj_id. object_at P obj_id spec}"
  "{obj_id \<in> dom (cdl_objects spec). table_at obj_id spec} = {obj_id. table_at obj_id spec}"
  "{obj_id \<in> dom (cdl_objects spec). capless_at obj_id spec} = {obj_id. capless_at obj_id spec}"
  "{obj_id \<in> dom (cdl_objects spec). cnode_or_tcb_at obj_id spec} = {obj_id. cnode_or_tcb_at obj_id spec}"
  "{obj_id \<in> dom (cdl_objects spec). cnode_at obj_id spec} = {obj_id. cnode_at obj_id spec}"
  "{obj_id \<in> dom (cdl_objects spec). real_object_at obj_id spec} = {obj_id. real_object_at obj_id spec}"
  by (auto simp: object_at_def real_object_at_def)

lemma pt_at_is_real[simp]: "pt_at pt_id spec \<Longrightarrow> pt_id \<in> {obj_id. real_object_at obj_id spec}"
  apply (clarsimp simp: object_at_def is_pt_def real_object_at_def dom_def
                        irq_nodes_def is_irq_node_def)
  by (clarsimp split: cdl_object.splits)

lemma pd_at_is_real[simp]: "pd_at pt_id spec \<Longrightarrow> pt_id \<in> {obj_id. real_object_at obj_id spec}"
  apply (clarsimp simp: object_at_def is_pd_def real_object_at_def dom_def
                        irq_nodes_def is_irq_node_def)
  by (clarsimp split: cdl_object.splits)

definition
  real_objects :: "cdl_state \<Rightarrow> cdl_object_id set"
where
  "real_objects \<equiv> \<lambda>s. {obj_id. real_object_at obj_id s}"


lemma cnode_or_tcb_at_simps:
  "(cnode_or_tcb_at obj_id spec \<and> cnode_at obj_id spec) = cnode_at obj_id spec"
  "(cnode_or_tcb_at obj_id spec \<and> \<not> cnode_at obj_id spec) = tcb_at obj_id spec"
  by (auto simp: object_at_def object_type_is_object)

(******************************
 * Cap types and default caps *
 ******************************)
definition cap_at :: "(cdl_cap \<Rightarrow> bool) \<Rightarrow> cdl_cap_ref \<Rightarrow> cdl_state \<Rightarrow> bool"
where
  "cap_at P ref s \<equiv> \<exists>cap. opt_cap ref s = Some cap \<and> P cap"

definition is_fake_pt_cap :: "cdl_cap \<Rightarrow> bool"
where "is_fake_pt_cap cap \<equiv> case cap of
    PageTableCap _ Fake _ \<Rightarrow> True
  | _ \<Rightarrow> False"

definition is_real_vm_cap :: "cdl_cap \<Rightarrow> bool"
where
  "is_real_vm_cap cap \<equiv>
       (case cap of
           FrameCap _ _ _ _ Real _     \<Rightarrow> True
         | PageTableCap _ Real _     \<Rightarrow> True
         | PageDirectoryCap _ Real _ \<Rightarrow> True
         | _                         \<Rightarrow> False)"

definition is_fake_vm_cap :: "cdl_cap \<Rightarrow> bool"
where
  "is_fake_vm_cap cap \<equiv>
       (case cap of
           FrameCap _ _ _ _ Fake _     \<Rightarrow> True
         | PageTableCap _ Fake _     \<Rightarrow> True
         | PageDirectoryCap _ Fake _ \<Rightarrow> True
         | _                         \<Rightarrow> False)"

abbreviation
  "fake_frame_cap dev ptr rights n \<equiv> FrameCap dev ptr rights n Fake None"
abbreviation
  "is_fake_frame_cap cap \<equiv> (case cap of FrameCap _ _ _ _ Fake None \<Rightarrow> True | _ \<Rightarrow> False)"

definition dev_of :: "cdl_cap \<Rightarrow> bool option" where
  "dev_of cap = (case cap of FrameCap dev ptr _ n _ _ \<Rightarrow> Some dev | _ \<Rightarrow> None)"
definition cap_size_bits :: "cdl_cap \<Rightarrow> nat" where
  "cap_size_bits cap = (case cap of FrameCap _ _ _ n _ _ \<Rightarrow> n | _ \<Rightarrow> 0)"

lemma is_fake_pt_cap_is_pt_cap [elim!]:
  "is_fake_pt_cap cap \<Longrightarrow> is_pt_cap cap"
  by (clarsimp simp: is_fake_pt_cap_def split: cdl_cap.splits)

abbreviation "pd_cap_at \<equiv> cap_at is_pd_cap"
abbreviation "pt_cap_at \<equiv> cap_at is_pt_cap"
abbreviation "fake_pt_cap_at \<equiv> cap_at is_fake_pt_cap"
abbreviation "irqhandler_cap_at \<equiv> cap_at is_irqhandler_cap"

lemma is_cnode_cap_simps:
  "is_cnode_cap (UntypedCap dev ids ids') = False"
  "is_cnode_cap (IOPageTableCap x) = False"
  "is_cnode_cap (IOSpaceCap x) = False"
  "is_cnode_cap (IOPortsCap x a) = False"
  "is_cnode_cap (AsidPoolCap x b) = False"
  "is_cnode_cap (PageDirectoryCap x c d) = False"
  "is_cnode_cap (PageTableCap x e f) = False"
  "is_cnode_cap (FrameCap dev x g h i j) = False"
  "is_cnode_cap (TcbCap x) = False"
  "is_cnode_cap (MasterReplyCap x) = False"
  "is_cnode_cap (ReplyCap x q) = False"
  "is_cnode_cap (NotificationCap x m n) = False"
  "is_cnode_cap (EndpointCap x p q) = False"
  "is_cnode_cap (ZombieCap x) = False"
  "is_cnode_cap (PendingSyncSendCap x s t u v w) = False"
  "is_cnode_cap (PendingSyncRecvCap x t w) = False"
  "is_cnode_cap (PendingNtfnRecvCap x) = False"

  "is_cnode_cap (CNodeCap x k l sz) = True"
  by (unfold cap_type_def, simp_all split: cdl_object_type.splits)

(* This is to be rarely used. original_cap_at is what you probably want. *)
definition cap_at_has_no_parents_in_cdt :: "cdl_cap_ref \<Rightarrow> cdl_state \<Rightarrow> bool"
where
  "cap_at_has_no_parents_in_cdt cap_ref \<equiv> \<lambda>spec. opt_parent cap_ref spec = None"

(* This predicate decides which capabilities should be moved, or copied.
 * The actual definition of this function is rarely used by the initialiser,
 * only to know that IRQ Handler caps are move, and so the definition can be
 * updated if newer caps are added that need to be moved.
 *)
definition
  original_cap_at :: "cdl_cap_ref \<Rightarrow> cdl_state \<Rightarrow> bool"
where
  "original_cap_at cap_ref \<equiv> \<lambda>spec. cap_at_has_no_parents_in_cdt cap_ref spec \<or>
                                     irqhandler_cap_at cap_ref spec"

definition is_default_cap :: "cdl_cap \<Rightarrow> bool"
where
  "is_default_cap cap \<equiv>
  (\<exists>type dev. cap_type cap = Some type \<and>
   cap = default_cap type (cap_objects cap) (cnode_cap_size cap) dev) \<or>
   is_irqhandler_cap cap"

lemma default_cap_eq:
  "\<lbrakk>is_default_cap cap; is_default_cap cap';
    cap_type cap = cap_type cap'; cap_objects cap = cap_objects cap';
    cnode_cap_size cap = cnode_cap_size cap';
    cap_irq cap = cap_irq cap'; is_device_cap cap = is_device_cap cap'\<rbrakk>
  \<Longrightarrow> cap = cap'"
  by (auto simp: is_default_cap_def cap_type_def cap_irq_def default_cap_def
          split: cdl_cap.splits )


lemma cnode_cap_size_non_cnode [simp]:
  "\<not> is_cnode_cap cap \<Longrightarrow> cnode_cap_size cap = 0"
  by (clarsimp simp: cap_type_def cnode_cap_size_def split: cdl_cap.splits)

lemma irqhandler_cap_irq_non_irqhandler [simp]:
  "\<not> is_irqhandler_cap cap \<Longrightarrow> cap_irq cap = undefined"
  by (clarsimp simp: cap_irq_def split: cdl_cap.splits)

lemma default_cap_eq_non_cnode:
  "\<lbrakk>is_default_cap cap; is_default_cap cap';
   \<not> is_cnode_cap cap; \<not> is_irqhandler_cap cap;
    cap_type cap = cap_type cap'; cap_objects cap = cap_objects cap';
    is_device_cap cap = is_device_cap cap'\<rbrakk>
  \<Longrightarrow> cap = cap'"
  apply (rule default_cap_eq)
   apply simp+
  done

lemma cap_type_default_cap [simp]:
  "cap_type (default_cap type {obj_id} sz dev) = Some type"
  by (clarsimp simp: default_cap_def cap_type_def split: cdl_object_type.splits)

lemma is_tcb_update_slots [simp]:
  "is_tcb (update_slots slots obj) = is_tcb obj"
  by (clarsimp simp: is_tcb_def update_slots_def split: cdl_object.splits)

lemma tcb_has_slots [elim!]:
  "is_tcb obj \<Longrightarrow> has_slots obj"
  by (clarsimp simp: is_tcb_def has_slots_def split: cdl_object.splits)

lemma cnode_has_slots [elim!]:
  "is_cnode obj \<Longrightarrow> has_slots obj"
  by (clarsimp simp: is_cnode_def has_slots_def split: cdl_object.splits)

lemma pt_has_slots [elim!]:
  "is_pt obj \<Longrightarrow> has_slots obj"
  by (clarsimp simp: is_pt_def has_slots_def split: cdl_object.splits)

lemma pd_has_slots [elim!]:
  "is_pd obj \<Longrightarrow> has_slots obj"
  by (clarsimp simp: is_pd_def has_slots_def split: cdl_object.splits)

lemma asidpool_has_slots [elim!]:
  "is_asidpool obj \<Longrightarrow> has_slots obj"
  by (clarsimp simp: is_asidpool_def has_slots_def split: cdl_object.splits)

lemma object_type_has_slots [elim!]:
  "object_type obj = TcbType \<Longrightarrow> has_slots obj"
  "object_type obj = CNodeType \<Longrightarrow> has_slots obj"
  "object_type obj = IRQNodeType \<Longrightarrow> has_slots obj"
  "object_type obj = PageTableType \<Longrightarrow> has_slots obj"
  "object_type obj = PageDirectoryType \<Longrightarrow> has_slots obj"
  "object_type obj = AsidPoolType \<Longrightarrow> has_slots obj"
  by (clarsimp simp: object_type_def has_slots_def split: cdl_object.splits)+

lemma cap_type_update_cap_objects [simp]:
  "cap_type (update_cap_objects x cap) = cap_type cap"
  apply (clarsimp simp: cap_type_def update_cap_objects_def)
  apply (cases cap, simp_all)
  done

lemma cap_type_update_cap_object [simp]:
  "cap_type (update_cap_object x cap) = cap_type cap"
  by (clarsimp simp: update_cap_object_def cap_type_def
              split: cdl_cap.splits)

lemma cap_has_object_update_cap_objects [simp]:
  "cap_has_object (update_cap_objects x cap) = cap_has_object cap"
  apply (clarsimp simp: update_cap_object_def
                        cap_has_object_def update_cap_objects_def)
  apply (cases cap, simp_all)
  done

lemma cap_has_object_update_cap_object [simp]:
  "cap_has_object (update_cap_object x cap) = cap_has_object cap"
  by (clarsimp simp: update_cap_object_def cap_has_object_def
              split: cdl_cap.splits)

lemma cap_object_default_cap' [simp]:
  "\<lbrakk>\<not>is_untyped obj; \<not>is_irq_node obj\<rbrakk>
  \<Longrightarrow> cap_object (default_cap (object_type obj) {obj_id} sz dev) = obj_id"
  by (clarsimp simp: default_cap_def  object_type_def is_untyped_def is_irq_node_def
              split: cdl_object_type.splits cdl_object.splits)

lemma cap_object_default_cap [simp]:
  "\<lbrakk>type \<noteq> UntypedType; type \<noteq> IRQNodeType\<rbrakk>
  \<Longrightarrow> cap_object (default_cap type {obj_id} sz dev) = obj_id"
  by (clarsimp simp: default_cap_def  object_type_def is_untyped_def
              split: cdl_object_type.splits cdl_object.splits)

lemma cap_object_default_cap_frame:
  "is_frame_cap cap \<Longrightarrow> cap_object (default_cap (the (cap_type cap)) {obj_id} sz dev) = obj_id"
  by clarsimp

lemma is_pd_default_cap[simp]:
  "is_pd obj \<Longrightarrow>
   cdl_objects spec ptr = Some obj \<Longrightarrow>
   default_cap (object_type obj) {ptr'} n b = PageDirectoryCap ptr' Real None"
  by (clarsimp simp: object_type_is_object default_cap_def)

lemma pd_at_default_cap[simp]:
  "pd_at ptr spec \<Longrightarrow>
   cdl_objects spec ptr = Some obj \<Longrightarrow>
   default_cap (object_type obj) {ptr'} n b = PageDirectoryCap ptr' Real None"
  by (fastforce simp: object_at_def)

lemma pt_at_default_cap[simp]:
  "pt_at ptr spec \<Longrightarrow>
   cdl_objects spec ptr = Some obj \<Longrightarrow>
   default_cap (object_type obj) {ptr'} n b = PageTableCap ptr' Real None"
  by (clarsimp simp: object_type_is_object default_cap_def object_at_def)

lemma default_cap_not_null [elim!]:
  "default_cap type obj_ids sz dev = NullCap \<Longrightarrow> False"
  "NullCap = default_cap type obj_ids sz dev\<Longrightarrow> False"
  by (simp add: default_cap_def split: cdl_object_type.splits)+

lemma cap_objects_update_cap_object [simp]:
  "\<lbrakk>cap_has_object cap; \<not>is_untyped_cap cap\<rbrakk>
  \<Longrightarrow> cap_objects (update_cap_object obj_id cap) = {obj_id}"
  by (clarsimp simp: cap_has_object_def update_cap_object_def
              split: cdl_cap.splits)

lemma cap_has_object_default_cap [simp]:
  "type \<noteq> IRQNodeType \<Longrightarrow> cap_has_object (default_cap type ids sz dev)"
  by (clarsimp simp: default_cap_def cap_has_object_def split: cdl_object_type.splits)

lemma all_cdl_rights_UNIV [simp]:
  "all_cdl_rights = UNIV"
  by (fastforce intro: rights.exhaust simp: all_cdl_rights_def)

lemma cap_rights_default_cap_cnode [simp]:
  "cap_rights (default_cap CNodeType ids sz dev) = UNIV"
  by (clarsimp simp: cap_rights_def default_cap_def)

lemma cap_rights_cnode_cap [simp]:
  "is_cnode_cap cap \<Longrightarrow> cap_rights cap = UNIV"
  by (clarsimp simp: cap_type_def cap_rights_def
              split: cdl_cap.splits)

lemma cap_has_object_simps [simp]:
  "cap_has_object (IOPageTableCap x)"
  "cap_has_object (IOSpaceCap x)"
  "cap_has_object (IOPortsCap x a)"
  "cap_has_object (AsidPoolCap x b)"
  "cap_has_object (PageDirectoryCap x c d)"
  "cap_has_object (PageTableCap x e f)"
  "cap_has_object (FrameCap dev x g h i j)"
  "cap_has_object (TcbCap x)"
  "cap_has_object (CNodeCap x k l sz)"
  "cap_has_object (MasterReplyCap x)"
  "cap_has_object (ReplyCap x q)"
  "cap_has_object (NotificationCap x m n)"
  "cap_has_object (EndpointCap x p q)"
  "cap_has_object (ZombieCap x)"
  "cap_has_object (PendingSyncSendCap x s t u v w)"
  "cap_has_object (PendingSyncRecvCap x t w)"
  "cap_has_object (PendingNtfnRecvCap x)"
  "cap_has_object (UntypedCap dev ids ids') = True"
  by (simp_all add:cap_has_object_def)

lemma is_cap_NullCap [simp]:
  "\<not> is_untyped_cap NullCap"
  "\<not> is_ep_cap NullCap"
  "\<not> is_ntfn_cap NullCap"
  "\<not> is_cnode_cap NullCap"
  "\<not> is_tcb_cap NullCap"
  "\<not> is_asidpool_cap NullCap"
  "\<not> is_pt_cap NullCap"
  "\<not> is_pd_cap NullCap"
  "\<not> is_frame_cap NullCap"
  "\<not> is_fake_pt_cap NullCap"
  "\<not> is_irqhandler_cap NullCap"
  by (clarsimp simp: cap_type_def is_fake_pt_cap_def)+

definition
  object_slots_list :: "cdl_object \<Rightarrow> cdl_cnode_index list"
where
  "object_slots_list obj \<equiv> case obj of
    PageDirectory _ \<Rightarrow> [0..<2^pd_size]
  | PageTable _ \<Rightarrow> [0..<2^pt_size]
  | AsidPool _ \<Rightarrow> [0..<2^asid_low_bits]
  | CNode cnode \<Rightarrow> [0..<2^(cdl_cnode_size_bits cnode)]
  | Tcb _ \<Rightarrow> tcb_slots_list
  | IRQNode _ \<Rightarrow> [0]
  | _ \<Rightarrow> []"

(* The slots of an object, returns an empty list for non-existing objects
   or objects that do not have caps *)
definition
  slots_of_list :: "cdl_state \<Rightarrow> cdl_object_id \<Rightarrow> cdl_cnode_index list"
where
  "slots_of_list spec obj_id \<equiv>
     case cdl_objects spec obj_id of
       Some obj \<Rightarrow> object_slots_list obj
     | None \<Rightarrow> []"

(* Encode the guard and guard size for passing to the kernel. *)
definition guard_as_rawdata :: "cdl_cap \<Rightarrow> cdl_raw_capdata"
where
  "guard_as_rawdata cap \<equiv>
  let
    reserved_bits = 3;
    guard_size_bits = 5
  in
    (cap_guard cap << (reserved_bits + guard_size_bits))
    + (of_nat (cap_guard_size cap) << reserved_bits)"

definition cap_data :: "cdl_cap \<Rightarrow> cdl_raw_capdata"
where
  "cap_data cap \<equiv>
  if (is_ep_cap cap) then
    cap_badge cap
  else if (is_ntfn_cap cap) then
    cap_badge cap
  else
    guard_as_rawdata cap"

(*
 * Deterministic version of update_cap_data used by the capDL kernel.
 * This is used in the specification of the CSpace kernel calls.
 *)
definition guard_update :: "cdl_cap \<Rightarrow> word32 \<Rightarrow> cdl_cap"
where "guard_update cap data  \<equiv>
  case cap of cdl_cap.CNodeCap oid _ _ sz \<Rightarrow>
    (let reserved_bits = 3; guard_bits = 18; guard_size_bits = 5; new_guard_size = unat ((data >> reserved_bits) && mask guard_size_bits);
        new_guard =
          (data >> reserved_bits + guard_size_bits) && mask (min (unat ((data >> reserved_bits) && mask guard_size_bits)) guard_bits)
    in CNodeCap oid new_guard new_guard_size sz)
  | _ \<Rightarrow> cap"

definition
  update_cap_data_det :: "cdl_raw_capdata \<Rightarrow> cdl_cap \<Rightarrow> cdl_cap"
where
  "update_cap_data_det raw_data cap \<equiv>
   case cap of
        EndpointCap _ b _      \<Rightarrow> badge_update raw_data cap
      | NotificationCap _ b _ \<Rightarrow> badge_update raw_data cap
      | CNodeCap object g gs _  \<Rightarrow> guard_update cap raw_data
      | _ \<Rightarrow> cap"

definition "valid_src_cap cap data \<equiv>
   is_cnode_cap cap \<longrightarrow> (
         unat ((data >> 3) && mask 5) + cnode_cap_size cap \<le> word_bits)"

(* MOVE TO KHeap.thy in capDL and fix get_thread *)
(* Get a thread from the given pointer. *)
definition
  opt_thread :: "cdl_object_id \<Rightarrow> cdl_state \<Rightarrow> cdl_tcb option"
where
  "opt_thread p s \<equiv>
      case cdl_objects s p of
          Some (Tcb tcb) \<Rightarrow> (Some tcb)
        | _ \<Rightarrow> None"



definition derived_cap :: "cdl_cap \<Rightarrow> cdl_cap"
where "derived_cap cap \<equiv> case cap of
          ReplyCap _ _ \<Rightarrow> NullCap
        | MasterReplyCap _ \<Rightarrow> NullCap
        | IrqControlCap \<Rightarrow> NullCap
        | FrameCap d p r sz b x \<Rightarrow> FrameCap d p r sz b None
        | ZombieCap _ \<Rightarrow> NullCap
        | _ \<Rightarrow> cap "

lemma derive_cap_wp:
  "\<lbrace> P (derived_cap cap) \<rbrace> derive_cap slot cap \<lbrace>P\<rbrace>, -"
  apply (clarsimp simp: derive_cap_def derived_cap_def)
  apply (clarsimp simp: validE_R_def derive_cap_def split:cdl_cap.splits)
  apply (safe, (wp whenE_wp |
                clarsimp simp: ensure_no_children_def)+ )
  done

definition safe_for_derive :: "cdl_cap \<Rightarrow> bool"
where "safe_for_derive cap \<equiv> case cap of
    NullCap \<Rightarrow> False
  | UntypedCap _ _ _ \<Rightarrow> False
  | PageTableCap _ _ _ \<Rightarrow> False
  | PageDirectoryCap _ _ _ \<Rightarrow> False
  | ReplyCap _ _ \<Rightarrow> False
  | MasterReplyCap _ \<Rightarrow> False
  | IrqControlCap \<Rightarrow> False
  | ZombieCap _ \<Rightarrow> False
  | _ \<Rightarrow> True"

lemma is_exclusive_cap_update_cap_rights [simp]:
  "safe_for_derive (update_cap_rights rights cap) = safe_for_derive cap"
  by (clarsimp simp: update_cap_rights_def safe_for_derive_def
              split: cdl_cap.splits)

lemma derive_cap_non_exclusive:
  "\<lbrace> P (derived_cap cap) and K (safe_for_derive cap) \<rbrace> derive_cap slot cap \<lbrace>P\<rbrace>, \<lbrace>Q\<rbrace>"
  apply (clarsimp simp: derive_cap_def derived_cap_def)
  apply (clarsimp simp: validE_R_def derive_cap_def
    safe_for_derive_def
    split:cdl_cap.splits)
  apply (intro conjI allI impI, wp+)
  done

lemma derived_cap_safe_for_derive[simp]:
  "safe_for_derive (derived_cap cap) = safe_for_derive cap"
  apply (case_tac cap)
  apply (simp_all add:derived_cap_def safe_for_derive_def)
  done

lemma safe_for_derive_not_non:
  "safe_for_derive cap \<Longrightarrow> cap \<noteq> NullCap"
  by (simp add:safe_for_derive_def split:cdl_cap.splits)




(* Given an object, this returns what the default state is for the object.
 * This should be the same as what is created by a retype operation.
 *)
definition
  object_default_state :: "cdl_object \<Rightarrow> cdl_object"
where
  "object_default_state object \<equiv>
  the $ default_object (object_type object)
                       (object_size_bits object)
                       (object_domain object)"

lemma object_default_state_def2:
  "object_default_state obj = (
    case obj of
        Untyped \<Rightarrow> Untyped
      | Endpoint \<Rightarrow> Endpoint
      | Notification \<Rightarrow> Notification
      | Tcb tcb \<Rightarrow> Tcb (default_tcb (cdl_tcb_domain tcb))
      | CNode cnode \<Rightarrow> CNode (empty_cnode (cdl_cnode_size_bits cnode))
      | IRQNode cnode \<Rightarrow> IRQNode empty_irq_node
      | AsidPool ap \<Rightarrow> AsidPool \<lparr>cdl_asid_pool_caps = empty_cap_map asid_low_bits\<rparr>
      | PageTable pt \<Rightarrow> PageTable \<lparr> cdl_page_table_caps = empty_cap_map 8 \<rparr>
      | PageDirectory pd \<Rightarrow> PageDirectory \<lparr> cdl_page_directory_caps = empty_cap_map 12 \<rparr>
      | Frame frame \<Rightarrow> Frame \<lparr> cdl_frame_size_bits = (cdl_frame_size_bits frame) \<rparr>)"
  by (clarsimp simp: object_default_state_def object_type_def default_object_def
                     object_size_bits_def object_domain_def
              split: cdl_object.splits)

(******************************************************
 * More rules, that should be put in the right place. *
 ******************************************************)

lemma object_type_update_slots [simp]:
  "object_type (update_slots slots x) = object_type x"
  by (clarsimp simp: object_type_def update_slots_def split: cdl_object.splits)

lemma object_slots_empty [simp]:
  "\<not> has_slots obj \<Longrightarrow> object_slots obj = Map.empty"
  by (clarsimp simp: object_slots_def has_slots_def split: cdl_object.splits)

lemma object_slots_update_slots [simp]:
  "has_slots obj \<Longrightarrow> object_slots (update_slots slots obj) = slots"
  by (clarsimp simp: object_slots_def update_slots_def has_slots_def
              split: cdl_object.splits)

lemma object_slots_update_slots_empty [simp]:
  "\<not>has_slots obj \<Longrightarrow> object_slots (update_slots slots obj) = Map.empty"
  by (clarsimp simp: object_slots_def update_slots_def has_slots_def
                 split: cdl_object.splits)

lemma update_slots_no_slots [simp]:
  "\<not>has_slots obj \<Longrightarrow> update_slots slots obj = obj"
  by (clarsimp simp: update_slots_def has_slots_def split: cdl_object.splits)

lemma update_slots_update_slots [simp]:
  "update_slots slots (update_slots slots' obj) = update_slots slots obj"
  by (clarsimp simp: update_slots_def split: cdl_object.splits)

lemma update_slots_same_object:
  "a = b \<Longrightarrow> update_slots a obj = update_slots b obj"
  by (erule arg_cong)

lemma update_slots_eq_slots:
  "\<lbrakk>has_slots obj; update_slots slots obj = update_slots slots' obj'\<rbrakk> \<Longrightarrow> slots = slots'"
  by (clarsimp simp: update_slots_def has_slots_def cdl_tcb.splits cdl_cnode.splits
                     cdl_asid_pool.splits cdl_irq_node.splits
                     cdl_page_table.splits cdl_page_directory.splits
              split: cdl_object.splits)

lemma has_slots_object_type_has_slots:
  "\<lbrakk>has_slots x; object_type x = object_type y\<rbrakk> \<Longrightarrow> has_slots y"
  by (clarsimp simp: object_type_def has_slots_def split: cdl_object.splits)

lemma object_type_has_slots_eq:
  "object_type y = object_type x \<Longrightarrow> has_slots x = has_slots y"
  by (clarsimp simp: object_type_def has_slots_def split: cdl_object.splits)


lemma object_type_object_default_state [simp]:
  "object_type (object_default_state obj) = object_type obj"
  by (clarsimp simp: object_default_state_def2 object_type_def split: cdl_object.splits)

lemma is_cnode_object_default_state [simp]:
  "is_cnode (object_default_state obj) = is_cnode obj"
  by (clarsimp simp: object_default_state_def2 is_cnode_def split: cdl_object.splits)


lemma update_slots_same [simp]:
  "object_slots obj = cap_map \<Longrightarrow> update_slots cap_map obj = obj"
  by (clarsimp simp: update_slots_def object_slots_def split: cdl_object.splits)

lemma dom_sub_restrict [simp]:
  "dom (m `- A) = dom m \<inter> -A"
  by (auto simp: sub_restrict_map_def dom_def split: if_split_asm)

lemma inter_empty_not_both:
"\<lbrakk>x \<in> A; A \<inter> B = {}\<rbrakk> \<Longrightarrow> x \<notin> B"
  by fastforce

lemma object_at_predicate_lift:
  "object_at P obj_id spec \<Longrightarrow> P (the (cdl_objects spec obj_id))"
  by (fastforce simp: object_at_def)

lemma object_at_cdl_objects_elim[elim]:
  "object_at P obj_id spec \<Longrightarrow> cdl_objects spec obj_id = Some (the (cdl_objects spec obj_id))"
  by (fastforce simp: object_at_def)

lemma opt_cap_object_slot:
  "cdl_objects spec obj_id = Some obj \<Longrightarrow>
   P (object_slots obj slot) \<Longrightarrow>
   P (opt_cap (obj_id, slot) spec)"
  by (fastforce simp: object_at_def opt_cap_def slots_of_def)

lemma opt_cap_object_slotE:
  "cdl_objects spec obj_id = Some obj \<Longrightarrow>
   object_slots obj slot = Some cap \<Longrightarrow>
   opt_cap (obj_id, slot) spec = Some cap"
  by (rule opt_cap_object_slot)

lemma slots_of_object_slot:
  "cdl_objects spec obj_id = Some obj \<Longrightarrow>
   P (object_slots obj slot) \<Longrightarrow>
   P (slots_of obj_id spec slot)"
   by (fastforce simp: object_at_def opt_cap_def slots_of_def)

lemma slots_of_object_slotE:
  "cdl_objects spec obj_id = Some obj \<Longrightarrow>
   object_slots obj slot = Some cap \<Longrightarrow>
   slots_of obj_id spec slot = Some cap"
   by (fastforce simp: object_at_def opt_cap_def slots_of_def)

lemma object_at_cdl_objects:
  "cdl_objects spec obj_id = Some obj \<Longrightarrow>
   P obj \<Longrightarrow>
   object_at P obj_id spec"
  by (fastforce simp: object_at_def)

lemma opt_cap_object_slot_simp:
  "cdl_objects spec obj_id = Some obj \<Longrightarrow>
   opt_cap (obj_id, slot) spec = object_slots obj slot"
   by (fastforce simp: object_at_def opt_cap_def slots_of_def)

lemma slots_of_object_slot_simp:
  "cdl_objects spec obj_id = Some obj \<Longrightarrow>
   slots_of obj_id spec slot = object_slots obj slot"
   by (fastforce simp: object_at_def opt_cap_def slots_of_def)

lemma is_fake_pt_cap_cap_has_object:
  "is_fake_pt_cap cap \<Longrightarrow> cap_has_object cap"
  by (clarsimp simp: cap_has_object_def is_fake_pt_cap_def split: cdl_cap.splits)

lemma is_fake_pt_cap_pt_cap:
  "is_fake_pt_cap (PageTableCap x R z) \<longleftrightarrow> R = Fake"
  by (clarsimp simp: is_fake_pt_cap_def split: cdl_frame_cap_type.splits)

lemma fake_vm_cap_simp:
  "is_fake_vm_cap (FrameCap x y z a R b) \<longleftrightarrow> R = Fake"
  by (clarsimp simp: is_fake_vm_cap_def split: cdl_frame_cap_type.splits)

lemma frame_not_pt[intro!]: "\<not> (is_frame x \<and> is_pt x)"
  by (cases x; clarsimp simp: is_frame_def is_pt_def)

lemma not_frame_and_pt: "is_frame x \<Longrightarrow> is_pt x \<Longrightarrow> False"
  by (fastforce simp: frame_not_pt[simplified])

lemma not_cap_at_cap_not_at:
  "(slot \<in> dom (slots_of obj_id spec) \<and> \<not> cap_at P (obj_id, slot) spec) \<longleftrightarrow>
   (slot \<in> dom (slots_of obj_id spec) \<and> cap_at (\<lambda>x. \<not> P x) (obj_id, slot) spec)"
  by (intro iffI; clarsimp simp: cap_at_def opt_cap_def)

end
