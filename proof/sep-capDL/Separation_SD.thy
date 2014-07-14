(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

(*
 * Separation logic definitions
 *
 * This file contains the definitions of the maps_to arrows
 * and their decompositions.
 *
 * It also contains the state lifting functions.
 *)

theory Separation_SD
imports
  AbstractSeparation_SD
  Sep_Tactic_Helper
  Types_SD
begin

(*
 * capDL and WordSetup both define word_bits.
 * These are equal, so let's just use WordSetup.
 *)
lemma word_bits_eq [simp]:
 "Types_D.word_bits = WordSetup.word_bits"
  by (simp add: Types_D.word_bits_def WordSetup.word_bits_def)

hide_const (open) Types_D.word_bits

lemma restrict_map_comp' [simp]:
  "f \<circ>\<^sub>M g |` S = (f \<circ>\<^sub>M g) |` S"
  by (rule ext, clarsimp simp: map_comp'_def restrict_map_def)

(********************
* Move to elsewhere *
*********************)

lemma sep_list_conj_impl:
  "\<lbrakk> list_all2 (\<lambda>x y. \<forall>s. x s \<longrightarrow> y s) xs ys; (\<And>* xs) s \<rbrakk> \<Longrightarrow> (\<And>* ys) s"
  apply (induct arbitrary: s rule: list_all2_induct)
   apply simp
  apply simp
  apply (erule sep_conj_impl, simp_all)
  done

lemma sep_list_conj_exists:
  "(\<exists>x. (\<And>* map (\<lambda>y s. P x y s) ys) s) \<Longrightarrow> ((\<And>* map (\<lambda>y s. \<exists>x. P x y s) ys) s)"
  apply clarsimp
  apply (erule sep_list_conj_impl[rotated])
  apply (rule list_all2I)
  apply simp_all
  apply (fastforce simp add: zip_map1 zip_map2 set_zip_same)
  done

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
      | AsyncEndpoint \<Rightarrow> AsyncEndpoint
      | Tcb tcb \<Rightarrow> Tcb (default_tcb (cdl_tcb_domain tcb))
      | CNode cnode \<Rightarrow> CNode (empty_cnode (cdl_cnode_size_bits cnode))
      | AsidPool ap \<Rightarrow> AsidPool \<lparr>cdl_asid_pool_caps = empty_cap_map asid_low_bits\<rparr>
      | PageTable pt \<Rightarrow> PageTable \<lparr> cdl_page_table_caps = empty_cap_map 8 \<rparr>
      | PageDirectory pd \<Rightarrow> PageDirectory \<lparr> cdl_page_directory_caps = empty_cap_map 12 \<rparr>
      | Frame frame \<Rightarrow> Frame \<lparr> cdl_frame_size_bits = (cdl_frame_size_bits frame) \<rparr>)"
  by (clarsimp simp: object_default_state_def object_type_def default_object_def
                     object_size_bits_def object_domain_def
              split: cdl_object.splits)

lemma object_type_object_default_state [simp]:
  "object_type (object_default_state obj) = object_type obj"
  by (clarsimp simp: object_default_state_def2 object_type_def split: cdl_object.splits)

lemma is_cnode_object_default_state [simp]:
  "is_cnode (object_default_state obj) = is_cnode obj"
  by (clarsimp simp: object_default_state_def2 is_cnode_def split: cdl_object.splits)

(* FIXME, is this a bad idea to add to the simpset? *)
lemma range_Slot [simp]:
  "(range Slot) = (UNIV - {Fields})"
   apply (clarsimp simp: image_def)
   apply rule
    apply clarsimp+
   apply (case_tac x)
    apply auto
   done

lemma update_slots_same [simp]:
  "object_slots obj = cap_map \<Longrightarrow> update_slots cap_map obj = obj"
  by (clarsimp simp: update_slots_def object_slots_def split: cdl_object.splits)

lemma dom_sub_restrict [simp]:
  "dom (m `- A) = dom m \<inter> -A"
  by (auto simp: sub_restrict_map_def dom_def split: split_if_asm)

lemma Slot_slot_union:
  "insert (Slot slot) (Slot ` (UNIV - {slot})) = UNIV - {Fields}"
   apply rule
    apply clarsimp+
   apply (case_tac x)
    apply auto
   done

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

lemma object_clean_fields_fields [simp]:
  "Fields \<in> cmps \<Longrightarrow> (object_clean_fields obj cmps) = obj"
  by (clarsimp simp: object_clean_fields_def)

lemma object_clean_fields_not_none_eq:
  "\<lbrakk>Fields \<notin> cmps; Fields \<notin> cmps'\<rbrakk>
  \<Longrightarrow> object_clean_fields obj cmps = object_clean_fields obj cmps'"
  by (clarsimp simp: object_clean_fields_def)

lemma clean_slots_map_addL [simp]:
  "cmps \<inter> cmps' = {}
  \<Longrightarrow> clean_slots (clean_slots slots cmps ++ clean_slots slots' cmps') cmps = clean_slots slots cmps"
  by (force simp: clean_slots_def map_add_def restrict_map_def)

lemma clean_slots_map_addR [simp]:
  "cmps \<inter> cmps' = {}
  \<Longrightarrow> clean_slots (clean_slots slots cmps ++ clean_slots slots' cmps') cmps' = clean_slots slots' cmps'"
  by (force simp: clean_slots_def map_add_def restrict_map_def
           split: option.splits)

lemma empty_fun_upd [simp]:
  "(\<lambda>x. {})(obj_id := {}) = (\<lambda>x. {})"
  by clarsimp

lemma clean_slots_UNIV [simp]:
  "clean_slots slots UNIV = slots"
  by (clarsimp simp: clean_slots_def)

lemma object_clean_slots_UNIV [simp]:
  "object_clean_slots obj UNIV = obj"
  by (clarsimp simp: object_clean_slots_def)

lemma object_clean_UNIV [simp]:
  "object_clean obj UNIV = obj"
  by (clarsimp simp: object_clean_def)

lemma object_clean_fields_object_clean:
  "object_clean_fields obj {Slot slot} = object_clean_fields obj' {Slot slot}
  \<Longrightarrow> object_clean obj {Slot slot} = object_clean obj' {Slot slot}"
  by (clarsimp simp: object_clean_def)

lemma object_clean_slots_object_clean:
  "object_clean_slots obj {Slot slot} = object_clean_slots obj' {Slot slot}
  \<Longrightarrow> object_clean obj {Slot slot} = object_clean obj' {Slot slot}"
  apply (subgoal_tac "object_type obj = object_type obj'")
   apply (clarsimp simp: object_clean_def object_clean_fields_def)
   apply (fastforce simp: object_clean_slots_def object_type_def object_slots_def
                          update_slots_def cdl_tcb.splits cdl_cnode.splits
                   split: cdl_object.splits)+
  done

(************************
* End of things to move *
*************************)



definition
  object_at_heap :: "(cdl_object \<Rightarrow> bool) \<Rightarrow> cdl_object_id \<Rightarrow> cdl_heap \<Rightarrow> bool"
where
  "object_at_heap P p s \<equiv> \<exists>object. s p = Some object \<and> P object"

abbreviation
  "ko_at_heap k \<equiv> object_at_heap (op = k)"


(* End of things to move *)

type_synonym sep_pred = "sep_state \<Rightarrow> bool"

(* Resets the intent of a TCB.
 * This lets us specify that we do not prove intent conformance.
 *)
definition
  intent_reset :: "cdl_object \<Rightarrow> cdl_object"
where
  "intent_reset \<equiv> \<lambda>object.
    case object  of
        Tcb tcb \<Rightarrow> Tcb (tcb\<lparr> cdl_tcb_intent := undefined \<rparr>)
      | other \<Rightarrow> other"

definition
  reset_cap_asid :: "cdl_cap \<Rightarrow> cdl_cap"
where
  "reset_cap_asid \<equiv> \<lambda>c. case c of
      FrameCap f1 f2 f3 f4 ad \<Rightarrow> FrameCap f1 f2 f3 f4 None
    | PageTableCap f1 f2 ad     \<Rightarrow> PageTableCap f1 f2 None
    | PageDirectoryCap f1 f2 ad \<Rightarrow> PageDirectoryCap f1 f2 None
    | _ \<Rightarrow> c"

definition
  asid_reset :: "cdl_object \<Rightarrow> cdl_object"
where
  "asid_reset \<equiv> \<lambda>obj. update_slots (reset_cap_asid \<circ>\<^sub>M object_slots obj) obj"

(* intent_reset is easier to bubble through object_slots,
   so is put on the outside. *)
definition
  object_lift :: "cdl_object \<Rightarrow> cdl_object"
where
  "object_lift \<equiv> intent_reset \<circ> asid_reset"

lemma object_lift_def2:
  "object_lift = asid_reset \<circ> intent_reset"
  apply (rule ext)
  apply (clarsimp simp: object_lift_def intent_reset_def asid_reset_def
                        map_comp'_def object_slots_def update_slots_def
                 split:  cdl_object.splits)
  done

definition
  heap_lift :: "cdl_heap \<Rightarrow> cdl_heap"
where
  "heap_lift heap \<equiv> \<lambda>obj_id. option_map object_lift (heap obj_id)"

definition object_project :: "cdl_component \<Rightarrow> cdl_object \<Rightarrow> sep_entity"
  where "object_project component obj \<equiv> case component of
     Fields \<Rightarrow> CDL_Object (object_clean_slots (object_lift obj) {})
   | Slot slot \<Rightarrow> CDL_Cap (object_slots (object_lift obj) slot)"

definition
  state_sep_projection :: "cdl_state \<Rightarrow> sep_state"
where
  "state_sep_projection s \<equiv> SepState
    (\<lambda>(ptr, component). option_map (object_project component) (cdl_objects s ptr))
    (\<lambda>irq. Some (cdl_irq_node s irq))"

definition
  state_sep_projection2 :: "user_state \<Rightarrow> sep_state"
where
  "state_sep_projection2 \<equiv> state_sep_projection \<circ> kernel_state"

abbreviation
  lift' :: "(sep_state \<Rightarrow> 'a) \<Rightarrow> cdl_state \<Rightarrow> 'a" ("<_>")
where
  "<P> s \<equiv> P (state_sep_projection s)"

abbreviation
  lift'' :: "(sep_state \<Rightarrow> 'a) \<Rightarrow> user_state \<Rightarrow> 'a" ("\<guillemotleft>_\<guillemotright>")
where
  "\<guillemotleft>P\<guillemotright> s \<equiv> P (state_sep_projection2 s)"

interpretation sep_lifted "state_sep_projection2" .
interpretation cdl: sep_lifted "state_sep_projection" .

definition
sep_state_to_entity_map :: "cdl_component_map \<Rightarrow> cdl_heap \<Rightarrow> sep_state_heap"
where
  "sep_state_to_entity_map component_map \<equiv> \<lambda>s (obj_id,component).
  if component \<in> component_map obj_id
  then Option.map (object_project component) (s obj_id)
  else None"

definition
 obj_to_sep_state :: "cdl_object_id \<Rightarrow> cdl_components \<Rightarrow> cdl_object \<Rightarrow> sep_state_heap"
where
  "obj_to_sep_state p cmp obj \<equiv> \<lambda>(ptr,component).
  if p = ptr \<and> component \<in> cmp
  then Some (object_project component obj)
  else None"

(*********************
 * Maps_to operators *
 *********************)
(* FIXME, use p and obj_id consistantly. *)

(* The generalisation of the maps to operator for separation logic. *)
definition
  sep_map_general :: "cdl_object_id \<Rightarrow> cdl_object \<Rightarrow> cdl_components \<Rightarrow> sep_pred"
where
  "sep_map_general p obj cmps \<equiv> \<lambda>s.
    sep_heap s = (obj_to_sep_state p cmps obj) \<and>
    sep_irq_node s = empty"

(* There is an object there. *)
definition
  sep_map_o :: "cdl_object_id \<Rightarrow> cdl_object \<Rightarrow> sep_pred" ("_ \<mapsto>o _" [76,71] 76)
where
  "p \<mapsto>o obj \<equiv> sep_map_general p obj UNIV"

(* The fields are there (and there are no caps). *)
definition
  sep_map_f :: "cdl_object_id \<Rightarrow> cdl_object \<Rightarrow> sep_pred" ("_ \<mapsto>f _" [76,71] 76)
where
  "p \<mapsto>f obj \<equiv> sep_map_general p obj {Fields}"

(* There is a clean object there that has the same caps in the same slots. *)
definition
  sep_map_S :: "cdl_object_id \<Rightarrow> cdl_object \<Rightarrow> sep_pred" ("_ \<mapsto>S _" [76,71] 76)
where
  "p \<mapsto>S obj \<equiv> sep_map_general p obj (UNIV - {Fields})"

(* There is a clean object there that has the same caps in the same slots, restricted to the slots "slots" *)
definition
  sep_map_S' :: "(cdl_object_id \<times> cdl_cnode_index set) \<Rightarrow> cdl_object \<Rightarrow> sep_pred" ("_ \<mapsto>S' _" [76,71] 76)
where
  "p \<mapsto>S' obj \<equiv> let (obj_id, slots) = p in sep_map_general obj_id obj (Slot ` slots)"

(* Consumes the ownership of the empty slots of an object. *)
definition
  sep_map_E :: "cdl_object_id \<Rightarrow> cdl_object \<Rightarrow> sep_pred" ("_ \<mapsto>E _" [76,71] 76)
where
  "p \<mapsto>E obj \<equiv> (p, UNIV- dom (object_slots obj)) \<mapsto>S' obj"

(* There is a clean object there that has the same cap in the same slot. *)
definition
  sep_map_s :: "cdl_cap_ref \<Rightarrow> cdl_object \<Rightarrow> sep_pred" ("_ \<mapsto>s _" [76,71] 76)
where
  "p \<mapsto>s obj \<equiv> let (obj_id, slot) = p in sep_map_general obj_id obj {Slot slot}"

(* There is that cap there. *)
definition
  sep_map_c :: "cdl_cap_ref \<Rightarrow> cdl_cap \<Rightarrow> sep_pred" ("_ \<mapsto>c _" [76,71] 76)
where
  "p \<mapsto>c cap \<equiv> \<lambda>s. let (obj_id, slot) = p in
  \<exists>obj. sep_map_general obj_id obj {Slot slot} s \<and> object_slots obj = [slot \<mapsto> cap]"

(* There is an IRQ entry *)
definition
  sep_map_irq :: "cdl_irq \<Rightarrow> cdl_object_id \<Rightarrow> sep_pred" ("_ \<mapsto>irq _" [76,71] 76)
where
  "sep_map_irq irq obj_id \<equiv> \<lambda>s.
    sep_heap s = empty \<and>
    sep_irq_node s irq = Some obj_id"

abbreviation "sep_any_map_o \<equiv> sep_any sep_map_o"
notation sep_any_map_o ("(_ \<mapsto>o -)" [1000] 76)

abbreviation "sep_any_map_f \<equiv> sep_any sep_map_f"
notation sep_any_map_f ("(_ \<mapsto>f -)" [1000] 76)

abbreviation "sep_any_map_S \<equiv> sep_any sep_map_S"
notation sep_any_map_S ("(_ \<mapsto>S -)" [1000] 76)

abbreviation "sep_any_map_S' \<equiv> sep_any sep_map_S'"
notation sep_any_map_S' ("(_ \<mapsto>S' -)" [1000] 76)

abbreviation "sep_any_map_s \<equiv> sep_any sep_map_s"
notation sep_any_map_s ("(_ \<mapsto>s -)" [1000] 76)

abbreviation "sep_any_map_c \<equiv> sep_any sep_map_c"
notation sep_any_map_c ("(_ \<mapsto>c -)" [1000] 76)

abbreviation "sep_any_map_irq \<equiv> sep_any sep_map_irq"
notation sep_any_map_irq ("(_ \<mapsto>irq -)" [1000] 76)

(* LaTeX notation. *)
notation  (latex output) sep_map_o ("_ \<mapsto>\<^sub>o _" [76,71] 76)
notation  (latex output) sep_map_f ("_ \<mapsto>\<^sub>f _" [76,71] 76)
notation  (latex output) sep_map_S ("_ \<mapsto>\<^sub>S _" [76,71] 76)
notation  (latex output) sep_map_S' ("_ \<mapsto>\<^sub>S\<^sub>' _" [76,71] 76)
notation  (latex output) sep_map_E ("_ \<mapsto>\<^sub>E _" [76,71] 76)
notation  (latex output) sep_map_s ("_ \<mapsto>\<^sub>s _" [76,71] 76)
notation  (latex output) sep_map_c ("_ \<mapsto>\<^sub>c _" [76,71] 76)

notation (latex output) sep_any_map_o  ("(_ \<mapsto>\<^sub>o -)"  [1000] 76)
notation (latex output) sep_any_map_f  ("(_ \<mapsto>\<^sub>f -)"  [1000] 76)
notation (latex output) sep_any_map_S  ("(_ \<mapsto>\<^sub>S -)"  [1000] 76)
notation (latex output) sep_any_map_S' ("(_ \<mapsto>\<^sub>S\<^sub>' -)" [1000] 76)
notation (latex output) sep_any_map_s  ("(_ \<mapsto>\<^sub>s -)"  [1000] 76)
notation (latex output) sep_any_map_c  ("(_ \<mapsto>\<^sub>c -)"  [1000] 76)

(********************************************************************
 * User level maps to pointers.                                     *
 *                                                                  *
 * These need to be cleaned up and redefined,                       *
 * namely we need to be able to share a CNode for multiple lookups. *
 *                                                                  *
 * This may involve taking a list of caps to look up.               *
 ********************************************************************)

definition offset :: "cdl_cptr \<Rightarrow> cdl_size_bits \<Rightarrow> cdl_cnode_index"
 where
  "offset cap_ptr radix \<equiv>  unat $ cap_ptr && mask radix"

definition one_lvl_lookup :: "cdl_cap \<Rightarrow> cdl_size_bits \<Rightarrow> cdl_size_bits \<Rightarrow> bool"
  where
   "one_lvl_lookup cnode_cap remaining_size radix \<equiv>
      let level_size = radix + cap_guard_size cnode_cap
      in remaining_size = level_size"

definition guard_equal :: "cdl_cap \<Rightarrow> cdl_cptr \<Rightarrow> cdl_size_bits \<Rightarrow> bool"
where
 "guard_equal cnode_cap cap_ptr remaining_size \<equiv>
      let guard_size = cap_guard_size cnode_cap;
          cap_guard' =  cap_guard cnode_cap
      in (cap_ptr >> remaining_size - guard_size) && mask guard_size = cap_guard'"

definition user_pointer_at :: "(cdl_size_bits * cdl_size_bits) \<Rightarrow> cdl_cap \<Rightarrow> cdl_cptr \<Rightarrow> cdl_cap \<Rightarrow> sep_pred " ("(\<box> _ : _ _ \<mapsto>u _)" [76,71] 76)
  where
   "user_pointer_at k_stuff cnode_cap cap_ptr cap  \<equiv> \<lambda>s.
    let (sz, remaining_size) = k_stuff;
        slot = offset cap_ptr sz;
        c = cap_object cnode_cap
    in ( c \<mapsto>f CNode (empty_cnode sz) \<and>*
        (c, slot) \<mapsto>c cap ) s \<and>
         (one_lvl_lookup cnode_cap remaining_size sz \<and>
           guard_equal cnode_cap cap_ptr remaining_size \<and>
           is_cnode_cap cnode_cap)"


lemma offset_0 [simp]:
  "offset 0 root_cnode_size = 0"
  by (clarsimp simp: offset_def)

lemma offset_slot':
  "\<lbrakk>slot < 2^radix\<rbrakk> \<Longrightarrow> offset slot radix = unat slot"
  by (clarsimp simp: offset_def Word.less_mask_eq)

lemma offset_slot:
  "\<lbrakk>slot < 2^radix; radix < word_bits\<rbrakk> \<Longrightarrow> offset (of_nat slot) radix = slot"
  apply (clarsimp simp: offset_def)
  apply (subst Word.less_mask_eq)
   apply (erule (1) of_nat_less_pow)
  apply (subst unat_of_nat_eq)
   apply (drule_tac a="2::nat" and n=radix and N = word_bits in power_strict_increasing)
    apply simp
   apply (simp add: word_bits_def)
  apply simp
  done

(* sep_map predcates are injective. *)

lemma sep_map_general_inj:
  "cmps \<noteq> {} \<Longrightarrow> inj (\<lambda>obj_id. sep_map_general obj_id obj cmps)"
  apply (clarsimp simp: inj_on_def fun_eq_iff sep_map_general_def)
  apply (erule_tac x="SepState (obj_to_sep_state x cmps obj) empty" in allE)
  apply (fastforce simp: obj_to_sep_state_def
                  split: split_if_asm)
  done

lemma sep_map_o_inj:
  "inj (\<lambda>obj_id. obj_id \<mapsto>o obj)"
  by (clarsimp simp: sep_map_o_def sep_map_general_inj)

lemma sep_map_f_inj:
  "inj (\<lambda>obj_id. obj_id \<mapsto>f obj)"
  by (clarsimp simp: sep_map_f_def sep_map_general_inj)

lemma sep_map_s_inj:
  "inj (\<lambda>obj_id. obj_id \<mapsto>s obj)"
  apply (clarsimp simp: inj_on_def fun_eq_iff sep_map_s_def sep_map_general_def)
  apply (erule_tac x="SepState (obj_to_sep_state a {Slot b} obj) empty" in allE)
  apply (fastforce simp: obj_to_sep_state_def
                  split: split_if_asm)
  done

lemma sep_map_c_inj:
  "inj (\<lambda>(obj_id,slot). (obj_id,slot) \<mapsto>c cap)"
  apply (clarsimp simp: inj_on_def fun_eq_iff sep_map_c_def sep_map_general_def)
  apply (erule_tac x="SepState (obj_to_sep_state a {Slot b}
                                                 (CNode \<lparr> cdl_cnode_caps = [b \<mapsto> cap],
                                                          cdl_cnode_size_bits = 0 \<rparr>))
                                empty" in allE)
  apply (auto simp: obj_to_sep_state_def object_project_def object_slots_def
             split: split_if_asm)
  done


(*****************************************
 * Unification of two maps_to predicates *
 *****************************************)

lemma object_type_intent_reset [simp]:
  "object_type (intent_reset obj) = object_type obj"
  by (clarsimp simp: intent_reset_def object_type_def split: cdl_object.splits)

lemma object_type_asid_reset [simp]:
  "object_type (asid_reset obj) = object_type obj"
  by (clarsimp simp: asid_reset_def)

lemma object_type_object_lift [simp]:
  "object_type (object_lift obj) = object_type obj"
  by (clarsimp simp: object_lift_def)

lemma dom_map_restrict:
  "dom (f |` a) \<subseteq> dom f"
  by auto

lemma sep_map_general_disjoint:
  "\<lbrakk>(sep_map_general obj_id obj cmps \<and>* sep_map_general obj_id obj' cmps') s\<rbrakk>
  \<Longrightarrow> cmps \<inter> cmps' = {}"
  apply (clarsimp simp:sep_map_general_def sep_conj_def)
  apply (case_tac x,case_tac y)
  apply (clarsimp simp:obj_to_sep_state_def map_disj_def
    sep_disj_sep_state_def sep_state_disj_def)
  apply (drule_tac a1 = "{obj_id}\<times>cmps" in
    disjoint_subset[OF dom_map_restrict])
  apply (drule_tac a1 = "{obj_id}\<times>cmps'" in
    disjoint_subset2[OF dom_map_restrict])
  apply (rule ccontr)
  apply (clarsimp dest!:int_not_emptyD)
  apply (erule_tac x = "(obj_id,x)" in in_empty_interE)
   apply (clarsimp simp:object_project_def split:cdl_component.splits)+
  done

(****************************************
 * Object_empty predicate decomposition *
 ****************************************)

lemma object_slots_intent_reset [simp]:
  "object_slots (intent_reset obj) = object_slots obj"
  by (clarsimp simp: intent_reset_def object_slots_def split: cdl_object.splits)

lemma update_slots_intent_reset [simp]:
  "intent_reset (update_slots slots obj) = update_slots slots (intent_reset obj)"
  by (clarsimp simp: intent_reset_def update_slots_def split: cdl_object.splits)

lemma object_clean_fields_intent_reset [simp]:
  "intent_reset (object_clean_fields obj cmps) =
  object_clean_fields (intent_reset obj) cmps"
  by (clarsimp simp: intent_reset_def object_clean_fields_def split: cdl_object.splits)

lemma object_clean_fields_asid_reset [simp]:
  "object_clean_fields (asid_reset obj) cmps = asid_reset (object_clean_fields obj cmps)"
  by (clarsimp simp: asid_reset_def)

lemma object_clean_slots_intent_reset [simp]:
  "intent_reset (object_clean_slots obj cmps)
  = object_clean_slots (intent_reset obj) cmps"
  by (clarsimp simp: object_clean_slots_def)

lemma object_clean_fields_object_lift [simp]:
  "object_clean_fields (object_lift obj) cmps = object_lift (object_clean_fields obj cmps)"
  by (clarsimp simp: object_lift_def2)

lemma object_clean_slots_asid_reset [simp]:
  "object_clean_slots (asid_reset obj) cmps = asid_reset (object_clean_slots obj cmps)"
  apply (clarsimp simp: object_clean_slots_def asid_reset_def clean_slots_def)
  apply (case_tac "has_slots obj", simp_all)
  done

lemma object_clean_intent_reset [simp]:
  "intent_reset (object_clean obj cmps) =
  object_clean (intent_reset obj) cmps"
  by (clarsimp simp: object_clean_def)

lemma object_clean_asid_reset [simp]:
  "object_clean (asid_reset obj) cmps = asid_reset (object_clean obj cmps)"
  by (clarsimp simp: object_clean_def)

lemma object_clean_object_lift [simp]:
  "object_clean (object_lift obj) cmps = object_lift (object_clean obj cmps)"
  by (clarsimp simp: object_lift_def2)

lemma object_slots_object_lift:
  "object_slots (object_lift obj) = reset_cap_asid \<circ>\<^sub>M object_slots obj"
  apply (clarsimp simp: object_lift_def)
  apply (clarsimp simp: asid_reset_def object_slots_def update_slots_def
                 split: cdl_object.splits)
  done

(* FIXME, fix restrict_map_remerge *)
lemma restrict_map_remerge':
  "(f |` S) ++ (f |` T) = f |` (S \<union> T)"
  apply (rule ext)
  apply (clarsimp simp: restrict_map_def map_add_def
                 split: split_if_asm option.splits)
  done


lemma "((reset_cap_asid \<circ>\<^sub>M object_slots obj |` the_set cmps) ++
           (reset_cap_asid \<circ>\<^sub>M object_slots obj |` the_set cmps'))
=
(reset_cap_asid \<circ>\<^sub>M
           object_slots
            (update_slots (object_slots obj |` (the_set cmps \<union> the_set cmps'))
              obj))"
  apply (case_tac "has_slots obj", simp_all)
  apply (rule restrict_map_remerge')
  done

lemma object_clean_fields_union [simp]:
  "Fields \<notin> cmps'
  \<Longrightarrow> object_clean_fields obj (cmps \<union> cmps') = object_clean_fields obj cmps"
  by (clarsimp simp: object_clean_fields_def)

lemma product_union:
  "{p} \<times> (cmps \<union> cmps') = ({p} \<times> cmps) \<union> ({p} \<times> cmps')"
  by (rule Sigma_Un_distrib2)

lemma obj_to_sep_state_add:
  "obj_to_sep_state p cmps obj ++ obj_to_sep_state p cmps' obj =
  obj_to_sep_state p (cmps \<union> cmps') obj"
  apply (rule ext)
  apply (clarsimp simp:obj_to_sep_state_def split_def
    map_add_def split:if_splits option.splits)
  done

lemma sep_map_decomp:
  "\<lbrakk>cmps \<inter> cmps' = {}\<rbrakk>
  \<Longrightarrow> (sep_map_general p obj cmps \<and>* sep_map_general p obj cmps') s =
      sep_map_general p obj (cmps \<union> cmps') s"
  apply (clarsimp simp: sep_conj_def map_disj_def
    sep_disj_sep_state_def sep_state_disj_def)
  apply (rule iffI)
  (* (p \<mapsto>L obj \<and>* p \<mapsto>R obj) \<Longrightarrow> p \<mapsto> obj *)
   apply (clarsimp simp: sep_map_general_def plus_sep_state_def
     sep_state_add_def obj_to_sep_state_add)
  apply (clarsimp simp:sep_map_general_def)
  apply (rule_tac x = "SepState (obj_to_sep_state p cmps obj) empty" in exI)
  apply (rule_tac x = "SepState (obj_to_sep_state p cmps' obj) empty" in exI)
  apply (clarsimp simp: plus_sep_state_def sep_state_add_def obj_to_sep_state_add)
  apply (intro conjI disjointI)
   apply (clarsimp simp:dom_def obj_to_sep_state_def
     split:if_splits)
   apply blast
  apply (case_tac s,simp)
  done

lemma sep_map_o_decomp:
  "p \<mapsto>o obj = (p \<mapsto>f obj \<and>* p \<mapsto>S obj)"
  apply (rule ext, rename_tac s)
  apply (clarsimp simp: sep_map_o_def sep_map_f_def sep_map_S_def)
  apply (subgoal_tac "{Fields} \<inter> (UNIV - {Fields}) = {}")
   apply (drule sep_map_decomp, fastforce+)
  done

lemma sep_map_c_def2:
  "((obj_id,slot) \<mapsto>c cap) s \<Longrightarrow> \<exists>obj. ((obj_id,slot) \<mapsto>s obj) s \<and> ((object_slots obj) slot = Some cap)"
  apply (clarsimp simp: sep_map_c_def sep_map_s_def sep_map_S_def sep_map_general_def)
  apply (rule_tac x="update_slots [slot \<mapsto> cap] obj" in exI)
  apply (case_tac "has_slots obj")
   apply (clarsimp simp: object_clean_def object_clean_slots_def)+
  done

lemma sep_map_c_sep_map_s:
  "\<lbrakk>((obj_id,slot) \<mapsto>s obj) s; (object_slots obj) slot = Some cap\<rbrakk> \<Longrightarrow>
   ((obj_id,slot) \<mapsto>c cap) s"
  apply (clarsimp simp: sep_map_c_def sep_map_s_def sep_map_S_def sep_map_general_def)
  apply (rule_tac x="update_slots (object_slots obj |` {slot}) obj" in exI)
  apply (rule conjI)
   apply (rule ext)+
   apply (case_tac obj)
   apply (clarsimp simp:obj_to_sep_state_def
     object_project_def update_slots_def
     object_lift_def intent_reset_def
     asid_reset_def object_slots_def)+
  apply (rule ext)
  apply (clarsimp simp: update_slots_def object_slots_def
                 split: cdl_object.splits)
  done

lemma intent_reset_has_slots[simp]:
  "has_slots (intent_reset obj) = has_slots obj"
  apply (simp add:intent_reset_def
    split:cdl_object.splits)
  apply (simp add:has_slots_def)
  done

lemma sep_map_s_sep_map_c:
  "\<lbrakk>((obj_id, slot) \<mapsto>c cap \<and>* obj_id \<mapsto>f obj') s;has_slots obj'\<rbrakk> \<Longrightarrow>
    \<exists>obj. ((obj_id, slot) \<mapsto>s obj \<and>* obj_id \<mapsto>f obj') s \<and>
          object_slots obj slot = Some cap \<and>
          object_type obj = object_type obj'"
  apply (rule_tac x="update_slots [slot \<mapsto> cap] obj'" in exI)
  apply (clarsimp simp: sep_map_c_def sep_map_f_def sep_conj_exists)
  apply (frule sep_map_general_disjoint)
  apply (clarsimp simp: sep_map_c_def sep_map_s_def sep_map_S_def sep_map_general_def)
  apply (clarsimp simp: sep_conj_def)
  apply (clarsimp simp: sep_disj_sep_state_def sep_state_disj_def)
  apply (rule_tac x = x in exI)
  apply (rule_tac x = y in exI)
  apply clarsimp
  apply (rule ext)
  apply (clarsimp simp:obj_to_sep_state_def
    object_project_def asid_reset_def object_slots_object_lift)
  done


lemma sep_map_s_object_slots_equal:
  "\<lbrakk>object_slots obj slot = object_slots obj' slot; object_type obj = object_type obj'\<rbrakk>
  \<Longrightarrow> ((obj_id, slot) \<mapsto>s obj) = ((obj_id, slot) \<mapsto>s obj')"
  apply (clarsimp simp: sep_map_s_def sep_map_general_def split: sep_state.splits)
  apply (intro iffI ext conjI |
         clarsimp simp: obj_to_sep_state_def object_project_def
                        object_slots_object_lift)+
  done

lemma sep_map_s_sep_map_c':
  "\<lbrakk>((obj_id, slot) \<mapsto>c cap \<and>* obj_id \<mapsto>f obj) s;
    object_slots obj slot = Some cap\<rbrakk>
  \<Longrightarrow> ((obj_id, slot) \<mapsto>s obj \<and>* obj_id \<mapsto>f obj) s"
  apply (drule sep_map_s_sep_map_c)
   apply (rule object_slots_has_slots, clarsimp)
  apply clarsimp
  apply (cut_tac obj=obja and obj'=obj and obj_id=obj_id and slot=slot in
         sep_map_s_object_slots_equal, simp+)
  done

lemma sep_map_S_def2:
  "(obj_id \<mapsto>S obj) = ((obj_id,UNIV) \<mapsto>S' obj)"
  by (clarsimp simp: sep_map_S_def sep_map_S'_def)

lemma sep_map_S'_def2:
  "(obj_id, {slot}) \<mapsto>S' obj = (obj_id, slot) \<mapsto>s obj"
  by (rule ext)(clarsimp simp: sep_map_S'_def sep_map_s_def)

lemma sep_map_S'_decomp':
  "\<lbrakk>slot \<notin> slots; slots \<noteq> {}\<rbrakk>
  \<Longrightarrow> (obj_id, insert slot slots) \<mapsto>S' obj =
      ((obj_id, slots) \<mapsto>S' obj \<and>* (obj_id, slot) \<mapsto>s obj)"
  apply (rule ext, rename_tac s)
  apply (clarsimp simp: sep_map_S'_def sep_map_s_def)
  apply (subgoal_tac "Slot ` slots \<inter> {Slot slot} = {}")
   apply (drule_tac p=obj_id and obj=obj and s=s in sep_map_decomp)
    apply clarsimp
   apply clarsimp
  done

lemma sep_map_S'_decomp_helper:
  "\<lbrakk>distinct slots; slots \<noteq> []\<rbrakk>
  \<Longrightarrow> (obj_id, set slots) \<mapsto>S' obj = \<And>* map (\<lambda>slot. (obj_id, slot) \<mapsto>s obj) slots"
  apply (induct slots arbitrary: obj)
   apply clarsimp
  apply (atomize)
  apply (case_tac "slots = []")
   apply (clarsimp simp: sep_map_S'_def sep_map_s_def)
  apply clarsimp
  apply (erule_tac x=obj in allE)
  apply (subgoal_tac "(obj_id, insert a (set slots)) \<mapsto>S' obj =
                      ((obj_id, set slots) \<mapsto>S' obj \<and>* (obj_id, a) \<mapsto>s obj)")
   apply (clarsimp simp: sep_conj_ac)
  apply (erule sep_map_S'_decomp')
  apply simp
  done

lemma sep_map_S'_decomp:
  "\<lbrakk>finite slots; slots \<noteq> {}\<rbrakk>
  \<Longrightarrow> (obj_id, slots) \<mapsto>S' obj = (\<And>* slot \<in> slots. (obj_id, slot) \<mapsto>s obj)"
  apply (drule sep_map_set_conj_sep_list_conj [where P="\<lambda>slot. (obj_id, slot) \<mapsto>s obj"])
  apply clarsimp
  apply (metis sep_map_S'_decomp_helper)
  done

lemma sep_map_S_decomp':
  "\<lbrakk>slots \<noteq> {}; slots \<noteq> UNIV\<rbrakk>
  \<Longrightarrow> obj_id \<mapsto>S obj = ((obj_id, slots) \<mapsto>S' obj \<and>* (obj_id, UNIV - slots) \<mapsto>S' obj)"
  apply (rule ext, rename_tac s)
  apply (clarsimp simp: sep_map_S_def sep_map_S'_def)
  apply (subgoal_tac "(Slot ` slots) \<inter> (Slot ` (UNIV - slots)) = {}")
   apply (drule_tac p=obj_id and obj=obj and s=s in sep_map_decomp)
    apply clarsimp
   apply (clarsimp simp: image_Un [THEN sym])
  apply fastforce
  done

lemma sep_map_S_decomp:
  "\<lbrakk>dom (object_slots obj) = slots; finite slots\<rbrakk> \<Longrightarrow>
   (obj_id \<mapsto>S obj) = ((\<And>* slot \<in> slots. (obj_id,slot) \<mapsto>s obj)  \<and>* obj_id \<mapsto>E obj)"
  apply (case_tac "slots = {}")
   apply clarsimp
  apply (clarsimp simp: sep_map_E_def sep_map_S'_def sep_map_S_def)
  apply (subst sep_map_S_decomp' [where slots = slots])
    apply clarsimp
   apply clarsimp
  apply (clarsimp simp: sep_map_E_def)
  apply (subst sep_map_S'_decomp, simp+)
  done

lemma sep_map_S_decomp_list:
  "\<lbrakk>dom (object_slots obj) = set slots; distinct slots\<rbrakk> \<Longrightarrow>
   (obj_id \<mapsto>S obj) = (\<And>* map (\<lambda>slot. (obj_id,slot) \<mapsto>s obj) slots  \<and>* obj_id \<mapsto>E obj)"
  by (metis sep_list_conj_sep_map_set_conj sep_map_S_decomp List.finite_set)

end
