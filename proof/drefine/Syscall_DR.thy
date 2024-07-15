(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Syscall_DR
imports
  Tcb_DR
  Schedule_DR
  Interrupt_DR
begin

context begin interpretation Arch . (*FIXME: arch_split*)

(*
 * Translate an abstract invocation into a corresponding
 * CDL invocation.
 *)

definition
  translate_invocation :: "Invocations_A.invocation \<Rightarrow> cdl_invocation"
where
  "translate_invocation x \<equiv>
    case x of
        Invocations_A.InvokeUntyped iu \<Rightarrow>
          Invocations_D.InvokeUntyped $
              translate_untyped_invocation iu
      | Invocations_A.InvokeEndpoint ep bdg grant grant_reply \<Rightarrow>
          Invocations_D.InvokeEndpoint $
              SyncMessage bdg grant grant_reply ep
      | Invocations_A.InvokeNotification ntfn aebdg \<Rightarrow>
          Invocations_D.InvokeNotification $
              Signal aebdg ntfn
      | Invocations_A.InvokeReply target_tcb reply_slot grant \<Rightarrow>
          Invocations_D.InvokeReply $
              ReplyMessage target_tcb (transform_cslot_ptr reply_slot) grant
      | Invocations_A.InvokeCNode icn \<Rightarrow>
          Invocations_D.InvokeCNode $
              translate_cnode_invocation icn
      | Invocations_A.InvokeTCB itcb \<Rightarrow>
          Invocations_D.InvokeTcb $ translate_tcb_invocation itcb
      | Invocations_A.InvokeDomain itcb d \<Rightarrow> Invocations_D.InvokeDomain $ SetDomain itcb d
      | Invocations_A.InvokeIRQControl irqc \<Rightarrow>
          Invocations_D.InvokeIrqControl $ translate_irq_control_invocation irqc
      | Invocations_A.InvokeIRQHandler irrqh \<Rightarrow>
          Invocations_D.InvokeIrqHandler $ translate_irq_handler_invocation irrqh
  "

definition
  cdl_invocation_relation :: "cdl_invocation \<Rightarrow> Invocations_A.invocation \<Rightarrow> bool"
where
  "cdl_invocation_relation x y \<equiv>
  case y of Invocations_A.InvokeArchObject invo \<Rightarrow> arch_invocation_relation x invo
  | _ \<Rightarrow> x = translate_invocation y"

(* we store the simplified version of this lemma, since the 'liftME's in
 * the goal are invariably simplified before this rule is applied *)
lemma dcorres_liftME_liftME [simplified]:
  "\<lbrakk>dcorres (dc \<oplus> rvrel) G G' m m';
    \<And> r r'. rvrel r r' \<Longrightarrow> rvrel' (f r) (f' r')\<rbrakk>
   \<Longrightarrow>
   dcorres (dc \<oplus> rvrel') G G' (liftME f m) (liftME f' m')"
  apply(simp, rule_tac r'="(dc \<oplus> rvrel)" and r="dc \<oplus> ((\<lambda> x. rvrel' x \<circ> f') \<circ> f)" in corres_rel_imp)
   apply(assumption)
  apply(case_tac x, simp)
  apply(case_tac y, simp_all)
done


(* Decoding NullCap invocations is equivalent. *)
lemma decode_invocation_nullcap_corres:
  "\<lbrakk> Some intent = transform_intent (invocation_type label) args';
     invoked_cap_ref = transform_cslot_ptr invoked_cap_ref';
     invoked_cap = transform_cap invoked_cap';
     excaps = transform_cap_list excaps';
     invoked_cap' = cap.NullCap \<rbrakk> \<Longrightarrow>
    dcorres (dc \<oplus> cdl_invocation_relation) \<top> \<top>
        (Decode_D.decode_invocation invoked_cap invoked_cap_ref excaps intent)
        (Decode_A.decode_invocation label' args' cap_index' invoked_cap_ref' invoked_cap' excaps')"
  apply (unfold  Decode_A.decode_invocation_def Decode_D.decode_invocation_def)
  apply (clarsimp simp: transform_cap_def)
  done

(* Decoding UntypedCap invocations is equivalent. *)
lemma decode_invocation_untypedcap_corres:
  "\<lbrakk> Some intent = transform_intent (invocation_type label') args';
     invoked_cap_ref = transform_cslot_ptr invoked_cap_ref';
     invoked_cap = transform_cap invoked_cap';
     excaps = transform_cap_list excaps';
     invoked_cap' = cap.UntypedCap dev a b idx \<rbrakk> \<Longrightarrow>
    dcorres (dc \<oplus> cdl_invocation_relation) \<top>
        (invs and cte_wp_at ((=) invoked_cap') invoked_cap_ref'
                 and (\<lambda>s. \<forall>x \<in> set (map fst excaps'). s \<turnstile> x)
                 and (\<lambda>s. \<forall>x \<in> set excaps'. cte_wp_at ((=) (fst x)) (snd x) s)
                 and valid_etcbs)
        (Decode_D.decode_invocation invoked_cap invoked_cap_ref excaps intent)
        (Decode_A.decode_invocation label' args' cap_index' invoked_cap_ref' invoked_cap' excaps')"
  apply (clarsimp simp: Decode_A.decode_invocation_def Decode_D.decode_invocation_def)
  apply (case_tac "\<exists> ui. intent = UntypedIntent ui")
   apply (clarsimp simp: throw_opt_def get_untyped_intent_def split: cdl_intent.splits option.splits)
   apply (rule dcorres_liftME_liftME)
    apply (rule corres_guard_imp, rule decode_untyped_corres, auto simp: transform_cap_def)[1]
   apply (clarsimp simp: cdl_invocation_relation_def translate_invocation_def)
  apply (clarsimp simp: throw_opt_def get_untyped_intent_def split: cdl_intent.split)
  apply (rule absorb_imp,clarsimp)+
  apply (rule dcorres_free_throw)
  apply (subst decode_untyped_label_not_match)
    apply simp+
done

(* Decoding Endpoint invocations is equivalent. *)
lemma decode_invocation_endpointcap_corres:
  "\<lbrakk> Some intent = transform_intent (invocation_type label') args';
     invoked_cap_ref = transform_cslot_ptr invoked_cap_ref';
     invoked_cap = transform_cap invoked_cap';
     excaps = transform_cap_list excaps';
     invoked_cap' = cap.EndpointCap a b c \<rbrakk> \<Longrightarrow>
    dcorres (dc \<oplus> cdl_invocation_relation) \<top> \<top>
        (Decode_D.decode_invocation invoked_cap invoked_cap_ref excaps intent)
        (Decode_A.decode_invocation label' args' cap_index' invoked_cap_ref' invoked_cap' excaps')"
  apply (clarsimp simp: Decode_A.decode_invocation_def
                        Decode_D.decode_invocation_def)
  apply (rule corres_returnOk)
  apply (clarsimp simp: cdl_invocation_relation_def translate_invocation_def)
  done

(* Decoding Async Endpoint invocations is equivalent. *)
lemma decode_invocation_notificationcap_corres:
  "\<lbrakk> Some intent = transform_intent (invocation_type label') args';
     invoked_cap_ref = transform_cslot_ptr invoked_cap_ref';
     invoked_cap = transform_cap invoked_cap';
     excaps = transform_cap_list excaps';
     invoked_cap' = cap.NotificationCap a b c \<rbrakk> \<Longrightarrow>
    dcorres (dc \<oplus> cdl_invocation_relation) \<top> \<top>
        (Decode_D.decode_invocation invoked_cap invoked_cap_ref excaps intent)
        (Decode_A.decode_invocation label' args' cap_index' invoked_cap_ref' invoked_cap' excaps')"
  apply (clarsimp simp: Decode_A.decode_invocation_def Decode_D.decode_invocation_def)
  apply (auto simp: cdl_invocation_relation_def translate_invocation_def
             split:rights.splits intro!:corres_returnOk)
  done

(* Decoding ReplyCap invocations is equivalent. *)
lemma decode_invocation_replycap_corres:
  "\<lbrakk> Some intent = transform_intent (invocation_type label') args';
     invoked_cap_ref = transform_cslot_ptr invoked_cap_ref';
     invoked_cap = transform_cap invoked_cap';
     excaps = transform_cap_list excaps';
     invoked_cap' = cap.ReplyCap a b c \<rbrakk> \<Longrightarrow>
    dcorres (dc \<oplus> cdl_invocation_relation) \<top> (cte_wp_at (Not\<circ> is_master_reply_cap) invoked_cap_ref' and
                                               cte_wp_at ((=) invoked_cap') invoked_cap_ref')
        (Decode_D.decode_invocation invoked_cap invoked_cap_ref excaps intent)
        (Decode_A.decode_invocation label' args' cap_index' invoked_cap_ref' invoked_cap' excaps')"
  apply (clarsimp simp: Decode_A.decode_invocation_def Decode_D.decode_invocation_def )
  apply (rule dcorres_expand_pfx)
  apply (clarsimp simp: cdl_invocation_relation_def translate_invocation_def
           split:rights.splits)
  apply (clarsimp simp:cte_wp_at_def is_master_reply_cap_def)
  apply (rule corres_guard_imp[OF dcorres_returnOk])
    apply (simp add:cdl_invocation_relation_def translate_invocation_def)+
done

(* Decoding CNode invocations is equivalent. *)
lemma decode_invocation_cnodecap_corres:
  "\<lbrakk> Some intent = transform_intent (invocation_type label') args';
     invoked_cap_ref = transform_cslot_ptr invoked_cap_ref';
     invoked_cap = transform_cap invoked_cap';
     excaps = transform_cap_list excaps';
     invoked_cap' = cap.CNodeCap a b c \<rbrakk> \<Longrightarrow>
    dcorres (dc \<oplus> cdl_invocation_relation) \<top>
        (invs and valid_cap invoked_cap' and (\<lambda>s. \<forall>e\<in>set excaps'. valid_cap (fst e) s) and valid_etcbs)
        (Decode_D.decode_invocation invoked_cap invoked_cap_ref excaps intent)
        (Decode_A.decode_invocation label' args' cap_index' invoked_cap_ref' invoked_cap' excaps')"
  apply (clarsimp simp: Decode_A.decode_invocation_def Decode_D.decode_invocation_def)
  apply (case_tac "\<exists> ui. intent = CNodeIntent ui")
   apply (rotate_tac -1, erule exE)
   apply (rotate_tac -1, drule sym)
   apply (clarsimp simp: get_cnode_intent_def throw_opt_def split: cdl_intent.split)
   apply (rule dcorres_liftME_liftME)
    apply (rule decode_cnode_corres, auto simp: transform_cap_def)[1]
   apply (clarsimp simp: cdl_invocation_relation_def translate_invocation_def)
  apply (clarsimp simp: throw_opt_def get_cnode_intent_def split: cdl_intent.split)
  apply (rule absorb_imp,clarsimp)+
  apply (rule dcorres_free_throw)
  apply (subst decode_cnode_label_not_match)
    apply simp+
done

(* Decoding TCB invocations is equivalent. *)
lemma decode_invocation_tcbcap_corres:
  "\<lbrakk> Some intent = transform_intent (invocation_type label') args';
     invoked_cap_ref = transform_cslot_ptr invoked_cap_ref';
     invoked_cap = transform_cap invoked_cap';
     excaps = transform_cap_list excaps';
     invoked_cap' = cap.ThreadCap a \<rbrakk> \<Longrightarrow>
    dcorres (dc \<oplus> cdl_invocation_relation) \<top> \<top>
        (Decode_D.decode_invocation invoked_cap invoked_cap_ref excaps intent)
        (Decode_A.decode_invocation label' args' cap_index' invoked_cap_ref' invoked_cap' excaps')"
  apply(case_tac "\<exists> ti. intent = (TcbIntent ti) ")
    apply (clarsimp simp: Decode_A.decode_invocation_def Decode_D.decode_invocation_def)
    apply (clarsimp simp: throw_opt_def get_cnode_intent_def get_tcb_intent_def split: cdl_intent.split)
    apply (rule corres_rel_imp[OF decode_tcb_corres],simp+)
      apply (case_tac x)
        apply (clarsimp simp:cdl_invocation_relation_def translate_invocation_def)+

    apply (clarsimp simp:Decode_D.decode_invocation_def throw_opt_def get_tcb_intent_def Decode_A.decode_invocation_def
      split:cdl_intent.splits)
    apply (rule absorb_imp,clarsimp)+
    apply (rule dcorres_free_throw)
    apply (rule decode_tcb_cap_label_not_match)
      apply (drule sym,clarsimp)
    apply simp
done

lemma fst_hd_map_eq: "\<lbrakk> xs \<noteq> []; fst (hd xs) = x \<rbrakk> \<Longrightarrow> fst (hd (map (\<lambda>(x, y). (f x, g y)) xs)) = f x"
  apply (case_tac xs)
  apply (auto simp: fst_def hd_def split: list.splits)
  done

lemma decode_domain_corres:
  "\<lbrakk> Some (DomainIntent i) = transform_intent (invocation_type label') args';
     excaps = transform_cap_list excaps' \<rbrakk> \<Longrightarrow>
   dcorres (dc \<oplus> ((\<lambda>x. cdl_invocation_relation x \<circ> (\<lambda>(x, y). Invocations_A.invocation.InvokeDomain x y)) \<circ> cdl_invocation.InvokeDomain)) \<top> \<top>
     (Tcb_D.decode_domain_invocation excaps i)
     (Decode_A.decode_domain_invocation label' args' excaps')"
  apply (unfold Tcb_D.decode_domain_invocation_def Decode_A.decode_domain_invocation_def)
  apply (unfold transform_cap_list_def)
  apply (case_labels "invocation_type label'"; simp add: gen_invocation_type_eq)
                                            apply (clarsimp simp: transform_intent_def option_map_def
                                                            split: option.splits)+
                  defer
                  apply (clarsimp simp: transform_intent_def option_map_def split: option.splits)+
  apply (clarsimp simp: transform_intent_domain_def)
  apply (case_tac "args'")
   apply simp
  apply (clarsimp simp: bindE_def lift_def)
  apply (rule_tac Q'="\<lambda>rv s. case rv of Inr b \<Rightarrow> ucast a = b | _ \<Rightarrow> True" in corres_symb_exec_r)
     apply (case_tac "rv")
      apply (simp add: lift_def)
      apply (rule corres_alternate2, simp)
     apply (simp add: lift_def)
     apply (fold bindE_def)
     apply (rule dcorres_whenE_throwError_abstract')
      apply (rule corres_alternate2)
      apply simp
     apply (case_tac "fst (hd (excaps'))"; simp)
               apply ((rule corres_alternate2, simp)+)[6]
         apply (rule corres_alternate1)
         apply (clarsimp simp: returnOk_def cdl_invocation_relation_def translate_invocation_def split: list.splits)
         apply (simp add: fst_hd_map_eq)
        apply (rule corres_alternate2, simp)+
   apply (rule validE_cases_valid)
   apply (wp whenE_inv| simp)+
  done

lemma decode_domain_cap_label_not_match:
  "\<lbrakk>\<forall>ui. Some (DomainIntent ui) \<noteq> transform_intent (invocation_type label') args'\<rbrakk>
    \<Longrightarrow> \<lbrace>(=) s\<rbrace> Decode_A.decode_domain_invocation label' args' excaps' \<lbrace>\<lambda>r. \<bottom>\<rbrace>,\<lbrace>\<lambda>e. (=) s\<rbrace>"
  apply (case_tac "invocation_type label' = GenInvocationLabel DomainSetSet")
   apply (clarsimp simp: Decode_A.decode_domain_invocation_def transform_intent_def gen_invocation_type_eq)+
   apply (clarsimp simp: transform_intent_domain_def split: option.splits list.splits)
   apply wp
  apply (simp add: Decode_A.decode_domain_invocation_def gen_invocation_type_eq)
  apply wp
  done

lemma decode_invocation_domaincap_corres:
  "\<lbrakk> Some intent = transform_intent (invocation_type label) args;
     invoked_cap_ref = transform_cslot_ptr slot;
     invoked_cap = transform_cap cap;
      excaps = transform_cap_list excaps';
     cap = cap.DomainCap\<rbrakk>
    \<Longrightarrow> dcorres (dc \<oplus> cdl_invocation_relation) \<top> \<top>
        (Decode_D.decode_invocation invoked_cap invoked_cap_ref excaps intent)
        (Decode_A.decode_invocation label args cap_index slot cap excaps')"
  apply (case_tac "\<exists>ti. intent = (DomainIntent ti)")
   apply (clarsimp simp: Decode_A.decode_invocation_def Decode_D.decode_invocation_def)
   apply (clarsimp simp: throw_opt_def get_domain_intent_def split: cdl_intent.split)
   apply (rule corres_rel_imp[OF decode_domain_corres],simp+)
  apply (clarsimp simp:Decode_D.decode_invocation_def throw_opt_def get_domain_intent_def Decode_A.decode_invocation_def
                  split:cdl_intent.splits)
  apply (rule absorb_imp,clarsimp)+
  apply (rule dcorres_free_throw)
  apply (rule decode_domain_cap_label_not_match)
  apply (drule sym,clarsimp)
  done

(* Decoding IRQ Control invocations is equivalent. *)
lemma decode_invocation_irqcontrolcap_corres:
  "\<lbrakk> Some intent = transform_intent (invocation_type label') args';

     invoked_cap_ref = transform_cslot_ptr invoked_cap_ref';
     invoked_cap = transform_cap invoked_cap';
     excaps = transform_cap_list excaps';
     invoked_cap' = cap.IRQControlCap \<rbrakk> \<Longrightarrow>
    dcorres (dc \<oplus> cdl_invocation_relation)
        \<top>
        (valid_objs and (\<lambda>s. \<forall>e\<in>set excaps'. valid_cap (fst e) s) and valid_global_refs and valid_idle and valid_etcbs)
        (Decode_D.decode_invocation invoked_cap invoked_cap_ref excaps intent)
        (Decode_A.decode_invocation label' args' cap_index' invoked_cap_ref' invoked_cap' excaps')"
  apply (clarsimp simp: Decode_A.decode_invocation_def Decode_D.decode_invocation_def)
  apply(case_tac "\<exists> ici. Some (IrqControlIntent ici) = transform_intent (invocation_type label') args'")
   apply(erule exE, rotate_tac -1, drule sym)
   apply(clarsimp simp: throw_opt_def get_irq_control_intent_def)
   apply (rule dcorres_liftME_liftME)
    apply (rule decode_irq_control_corres, auto simp: transform_cap_def)[1]
   apply (clarsimp simp: cdl_irq_control_invocation_relation_def)
   apply (clarsimp simp: cdl_invocation_relation_def translate_invocation_def)
  apply (rule corres_guard_imp)
    apply (clarsimp simp: throw_opt_def split: cdl_intent.split option.splits)
    apply (auto simp: get_irq_control_intent_def split: cdl_intent.split intro!: decode_irq_control_error_corres)
  done

(* Decoding IRQ Handler invocations is equivalent. *)
lemma decode_invocation_irqhandlercap_corres:
  "\<lbrakk> Some intent = transform_intent (invocation_type label') args';
     invoked_cap_ref = transform_cslot_ptr invoked_cap_ref';
     invoked_cap = transform_cap invoked_cap';
     excaps = transform_cap_list excaps';
     invoked_cap' = cap.IRQHandlerCap x \<rbrakk> \<Longrightarrow>
    dcorres (dc \<oplus> cdl_invocation_relation) \<top> \<top>
        (Decode_D.decode_invocation invoked_cap invoked_cap_ref excaps intent)
        (Decode_A.decode_invocation label' args' cap_index' invoked_cap_ref' invoked_cap' excaps')"
  apply (clarsimp simp: Decode_A.decode_invocation_def Decode_D.decode_invocation_def)
  apply (clarsimp simp: throw_opt_def get_irq_handler_intent_def split: option.splits)
  apply (rule conjI)
   apply (auto simp: decode_irq_handler_invocation_def transform_intent_def
               simp flip: gen_invocation_type_eq
               split del: if_split
               split: invocation_label.splits gen_invocation_labels.splits cdl_intent.splits list.splits)[1]
  apply clarsimp
  apply (simp split: cdl_intent.splits)
  apply (rule corres_rel_imp)
   apply (erule decode_irq_handler_corres, simp+)[1]
  apply clarsimp
  apply (case_tac xa, simp)
  apply (simp add: cdl_invocation_relation_def
                   cdl_irq_handler_invocation_relation_def
                   translate_invocation_def)
  done

lemma transform_type_eq_None:
  "(transform_type a = None) \<Longrightarrow> (data_to_obj_type a = throwError (ExceptionTypes_A.syscall_error.InvalidArgument 0))"
  apply (clarsimp simp:data_to_obj_type_def transform_type_def split:if_split_asm)
  apply (simp add:unat_arith_simps)
  apply (clarsimp simp:arch_data_to_obj_type_def)
  apply (rule conjI,arith,clarsimp)+
  done

lemma transform_intent_untyped_cap_None:
  "\<lbrakk>transform_intent (invocation_type label) args = None; cap = cap.UntypedCap dev w n idx\<rbrakk>
         \<Longrightarrow> \<lbrace>(=) s\<rbrace> Decode_A.decode_invocation label args cap_i slot cap excaps \<lbrace>\<lambda>r. \<bottom>\<rbrace>, \<lbrace>\<lambda>x. (=) s\<rbrace>"
  including no_pre
  supply gen_invocation_type_eq[symmetric, simp]
  apply (clarsimp simp:Decode_A.decode_invocation_def)
  apply wp
  apply (case_labels "invocation_type label")
      (* 46 subgoals *)
      apply (clarsimp simp:Decode_A.decode_untyped_invocation_def unlessE_def, wp)+
     apply (clarsimp simp:transform_intent_def Decode_A.decode_untyped_invocation_def unlessE_def split del:if_split)
     apply (clarsimp simp:transform_intent_untyped_retype_def split del:if_split)
     apply (case_tac "args")
      apply (clarsimp,wp)[1]
     apply (clarsimp split:list.split_asm split del:if_split)
          apply (wp+)[5]
     apply (clarsimp simp: transform_type_eq_None split del:if_split split:option.splits)
     apply (wp|clarsimp simp:whenE_def|rule conjI)+
    apply (clarsimp simp: Decode_A.decode_untyped_invocation_def unlessE_def split del:if_split,wp)+
  done

lemma transform_intent_cnode_cap_None:
  "\<lbrakk>transform_intent (invocation_type label) args = None; cap = cap.CNodeCap w n list\<rbrakk>
   \<Longrightarrow> \<lbrace>(=) s\<rbrace> Decode_A.decode_invocation label args cap_i slot cap excaps \<lbrace>\<lambda>r. \<bottom>\<rbrace>, \<lbrace>\<lambda>x. (=) s\<rbrace>"
  supply if_cong[cong]
  apply (clarsimp simp:Decode_A.decode_invocation_def)
  apply (simp add: Decode_A.decode_cnode_invocation_def unlessE_def upto_enum_def
                   fromEnum_def toEnum_def enum_invocation_label enum_gen_invocation_labels
                   whenE_def)
  apply (intro conjI impI;
           clarsimp simp: transform_intent_def transform_cnode_index_and_depth_def
                          transform_intent_cnode_copy_def
                          transform_intent_cnode_mint_def transform_intent_cnode_move_def
                          transform_intent_cnode_mutate_def transform_intent_cnode_rotate_def
                    simp flip: gen_invocation_type_eq
                    split: list.split_asm;
           (solves \<open>wpsimp\<close>)?)
  done

lemma transform_intent_thread_cap_None:
  "\<lbrakk>transform_intent (invocation_type label) args = None; cap = cap.ThreadCap w\<rbrakk>
             \<Longrightarrow> \<lbrace>(=) s\<rbrace> Decode_A.decode_invocation label args cap_i slot cap excaps \<lbrace>\<lambda>r. \<bottom>\<rbrace>, \<lbrace>\<lambda>x. (=) s\<rbrace>"
  including no_pre
  apply (clarsimp simp:Decode_A.decode_invocation_def)
  apply wp+
  apply (simp add:Decode_A.decode_tcb_invocation_def)
  apply (cases "gen_invocation_type label"; simp; wp?)
               apply (clarsimp simp: transform_intent_def decode_read_registers_def decode_write_registers_def
                                     decode_copy_registers_def decode_tcb_configure_def decode_set_priority_def
                                     decode_set_mcpriority_def decode_set_sched_params_def
                                     decode_set_ipc_buffer_def transform_intent_tcb_defs
                              simp flip: gen_invocation_type_eq
                              split: list.split_asm
                     | wp+)+
         apply (clarsimp simp: transform_intent_def decode_set_space_def decode_bind_notification_def
                               decode_unbind_notification_def transform_intent_tcb_set_space_def
                        split: list.split_asm
               , wp+
               | clarsimp simp: transform_intent_def simp flip: gen_invocation_type_eq)+
  done

lemma transform_intent_irq_control_None:
  "\<lbrakk>transform_intent (invocation_type label) args = None; cap = cap.IRQControlCap\<rbrakk>
      \<Longrightarrow> \<lbrace>(=) s\<rbrace> Decode_A.decode_invocation label args cap_i slot cap excaps \<lbrace>\<lambda>r. \<bottom>\<rbrace>,
          \<lbrace>\<lambda>x. (=) s\<rbrace>"
  including no_pre
  supply gen_invocation_type_eq[symmetric, simp] if_cong[cong]
  apply (clarsimp simp:Decode_A.decode_invocation_def)
  apply wp
  apply (clarsimp simp:decode_irq_control_invocation_def arch_decode_irq_control_invocation_def
                  split del:if_split)
  apply (case_labels "invocation_type label"; (clarsimp, wp)?)
   apply (clarsimp simp:transform_intent_issue_irq_handler_def transform_intent_def
                   split:list.split_asm split del:if_split,wp+)
  apply (clarsimp simp:arch_transform_intent_issue_irq_handler_def transform_intent_def
                  split:list.split_asm split del:if_split,wp+)
  done

lemma transform_intent_irq_handler_None:
  "\<lbrakk>transform_intent (invocation_type label) args = None; cap = cap.IRQHandlerCap w\<rbrakk>
             \<Longrightarrow> \<lbrace>(=) s\<rbrace> Decode_A.decode_invocation label args cap_i slot cap excaps \<lbrace>\<lambda>r. \<bottom>\<rbrace>, \<lbrace>\<lambda>x. (=) s\<rbrace>"
  supply gen_invocation_type_eq[symmetric, simp]
  apply (clarsimp simp:Decode_A.decode_invocation_def)
  apply (wp)
   apply (clarsimp simp:decode_irq_handler_invocation_def|rule conjI)+
    apply (clarsimp simp:transform_intent_def split: list.splits)+
   apply (clarsimp simp:transform_intent_def |rule conjI | wp)+
  done

lemma transform_intent_zombie_cap_None:
  "\<lbrakk>transform_intent (invocation_type label) args = None; cap = cap.Zombie w option n\<rbrakk>
         \<Longrightarrow> \<lbrace>(=) s\<rbrace> Decode_A.decode_invocation label args cap_i slot cap excaps \<lbrace>\<lambda>r. \<bottom>\<rbrace>, \<lbrace>\<lambda>x. (=) s\<rbrace>"
  apply (clarsimp simp:Decode_A.decode_invocation_def)
  apply (wp)
done

lemma transform_intent_domain_cap_None:
  "\<lbrakk>transform_intent (invocation_type label) args = None; cap = cap.DomainCap\<rbrakk>
     \<Longrightarrow> \<lbrace>(=) s\<rbrace> Decode_A.decode_invocation label args cap_i slot cap.DomainCap excaps \<lbrace>\<lambda>r. \<bottom>\<rbrace>, \<lbrace>\<lambda>x. (=) s\<rbrace>"
  including no_pre
  supply gen_invocation_type_eq[symmetric, simp]
  apply (clarsimp simp: Decode_A.decode_invocation_def)
  apply wp
  apply (case_tac excaps, simp_all)
   apply (clarsimp simp: decode_domain_invocation_def)
   apply (case_tac args, simp_all)
    apply (wp whenE_inv whenE_inv[THEN valid_validE] | simp)+
  apply (clarsimp simp: decode_domain_invocation_def)
  apply (case_tac args, simp_all)
   apply ((wp whenE_inv whenE_inv[THEN valid_validE] | simp)+)[1]
  apply (case_tac "invocation_type label \<noteq> GenInvocationLabel DomainSetSet", simp_all)
   apply wp
  apply (clarsimp simp: transform_intent_def transform_intent_domain_def)
  done

lemma transform_intent_arch_cap_None:
  "\<lbrakk>transform_intent (invocation_type label) args = None; cap = cap.ArchObjectCap arch_cap\<rbrakk>
         \<Longrightarrow> \<lbrace>(=) s\<rbrace> Decode_A.decode_invocation label args cap_i slot cap excaps \<lbrace>\<lambda>r. \<bottom>\<rbrace>, \<lbrace>\<lambda>x. (=) s\<rbrace>"
  including no_pre
  supply gen_invocation_type_eq[symmetric, simp]
  apply (clarsimp simp:Decode_A.decode_invocation_def)
  apply wp
  apply (simp add: arch_decode_invocation_def split del: if_split)
  apply (case_tac arch_cap)
      apply (case_labels "invocation_type label"; simp split del: if_split, wp?)
      apply (clarsimp split: if_splits | rule conjI)+
       apply (case_tac "excaps ! 0")
       apply (clarsimp split: cap.splits | rule conjI | wp)+
       apply (clarsimp split: arch_cap.splits | rule conjI | wp)+
       apply ((clarsimp simp: transform_intent_def | wp) +)[2]
     apply (case_labels "invocation_type label"
            ; wpsimp simp: arch_decode_invocation_def split_del: if_split)
     apply (case_tac "excaps ! 0")
     apply (clarsimp simp: transform_intent_def transform_cnode_index_and_depth_def
                    split: list.split_asm)
      apply wp+
    apply (case_labels "invocation_type label"
           ; wpsimp simp: arch_decode_invocation_def isPageFlushLabel_def split_del: if_split)
          apply (clarsimp simp: transform_intent_def transform_intent_page_map_def
                         split: list.split_asm )
            apply wp+
         apply (case_tac "excaps ! 0")
         apply (clarsimp simp:transform_intent_def split:list.split_asm)
        apply ((clarsimp simp:transform_intent_def | wp)+)
   apply (case_labels "invocation_type label"; simp)
                            apply (intro conjI impI | wp)+
       apply (clarsimp | rule conjI)+
       apply (clarsimp simp: transform_intent_def transform_intent_page_table_map_def
                      split: list.split_asm)
      apply (intro conjI impI | wp)+
  apply ((clarsimp simp: transform_intent_def split: list.split_asm | wp)+)[1]
  apply (case_labels "invocation_type label"; simp add: isPDFlushLabel_def)
                           apply (wp)+
  done

lemma decode_invocation_error_branch:
  "\<lbrakk>transform_intent (invocation_type label) args = None; \<not> ep_related_cap (transform_cap cap)\<rbrakk>
    \<Longrightarrow> \<lbrace>(=) s\<rbrace> Decode_A.decode_invocation label args cap_i slot cap excaps \<lbrace>\<lambda>r. \<bottom>\<rbrace>,\<lbrace>\<lambda>x. (=) s\<rbrace>"
  apply (case_tac cap)
    apply (simp_all add:ep_related_cap_def transform_cap_def split:if_split_asm)
    apply (clarsimp simp:Decode_A.decode_invocation_def,wp)
      apply (rule transform_intent_untyped_cap_None,fastforce+)
      apply (clarsimp simp:Decode_A.decode_invocation_def,wp)
      apply (rule transform_intent_cnode_cap_None,fastforce+)
      apply (rule transform_intent_thread_cap_None,fastforce+)
      apply (rule transform_intent_domain_cap_None,fastforce+)
     apply (rule transform_intent_irq_control_None,fastforce+)
    apply (rule transform_intent_irq_handler_None,fastforce+)
   apply (rule transform_intent_zombie_cap_None,fastforce+)
  apply (rule transform_intent_arch_cap_None,fastforce+)
  done

lemma decode_invocation_ep_related_branch:
  "\<lbrakk>ep_related_cap (transform_cap cap);\<not> is_master_reply_cap cap\<rbrakk>
  \<Longrightarrow> dcorres (dc \<oplus> cdl_invocation_relation) \<top> \<top>
    (Decode_D.decode_invocation (transform_cap cap) (transform_cslot_ptr ref) caps intent)
    (Decode_A.decode_invocation label args index ref cap caps')"
  apply (clarsimp simp:ep_related_cap_def transform_cap_def split:cdl_cap.split_asm cap.split_asm arch_cap.split_asm)
      apply (clarsimp simp:Decode_D.decode_invocation_def Decode_A.decode_invocation_def | rule conjI)+
      apply (rule corres_guard_imp[OF dcorres_returnOk],simp add:cdl_invocation_relation_def translate_invocation_def)
       apply simp+
     apply (clarsimp simp:Decode_D.decode_invocation_def Decode_A.decode_invocation_def split:if_split_asm | rule conjI)+
    apply (rule corres_guard_imp[OF dcorres_returnOk])
      apply (simp add:cdl_invocation_relation_def translate_invocation_def)+
   apply (clarsimp simp:Decode_D.decode_invocation_def Decode_A.decode_invocation_def is_master_reply_cap_def | rule conjI)+
  apply (rule corres_guard_imp[OF dcorres_returnOk])
    apply (simp add:cdl_invocation_relation_def translate_invocation_def)+
  done

(*
 * Decoding zombies invocations is equivalent.
 *
 *)
lemma decode_invocation_zombiecap_corres:
  "\<lbrakk> Some intent = transform_intent (invocation_type label') args';
     invoked_cap_ref = transform_cslot_ptr invoked_cap_ref';
     invoked_cap = transform_cap invoked_cap';
     excaps = transform_cap_list excaps';
     invoked_cap' = cap.Zombie x y z \<rbrakk> \<Longrightarrow>
    dcorres (dc \<oplus> cdl_invocation_relation) \<top> \<top>
        (Decode_D.decode_invocation invoked_cap invoked_cap_ref excaps intent)
        (Decode_A.decode_invocation label' args' cap_index' invoked_cap_ref' invoked_cap' excaps')"
  by (simp add:Decode_A.decode_invocation_def Decode_D.decode_invocation_def)

(*
 * Show that decoding of invocations corresponds.
 *)
lemma decode_invocation_corres:
  "\<lbrakk> (Some intent) = transform_intent (invocation_type label) args;
     invoked_cap_ref = transform_cslot_ptr slot;
     invoked_cap = transform_cap cap;
     excaps = transform_cap_list excaps' \<rbrakk> \<Longrightarrow>
     dcorres (dc \<oplus> cdl_invocation_relation) \<top>
      (invs and valid_cap cap and (\<lambda>s. \<forall>e\<in>set excaps'. valid_cap (fst e) s)
            and (cte_wp_at (Not \<circ> is_master_reply_cap) slot
            and cte_wp_at ((=) cap) slot)
            and (\<lambda>s. \<forall>x\<in>set excaps'. cte_wp_at ((=) (fst x)) (snd x) s)
            and valid_etcbs)
      (Decode_D.decode_invocation invoked_cap invoked_cap_ref excaps intent)
      (Decode_A.decode_invocation label args cap_index slot cap excaps')"
  apply(case_tac cap)
            apply (rule corres_guard_imp,rule decode_invocation_nullcap_corres, fastforce+)[1]
           apply (rule corres_guard_imp,rule decode_invocation_untypedcap_corres,
                     (fastforce elim: cte_wp_at_weakenE)+)[1]
          apply (rule corres_guard_imp,rule decode_invocation_endpointcap_corres, fastforce+)[1]
         apply (rule corres_guard_imp,rule decode_invocation_notificationcap_corres, fastforce+)[1]
        apply (rule corres_guard_imp,rule decode_invocation_replycap_corres, fastforce+)[1]
       apply (rule corres_guard_imp,rule decode_invocation_cnodecap_corres, fastforce+)[1]
      apply (rule corres_guard_imp, rule decode_invocation_tcbcap_corres, fastforce+)[1]
     apply (rule corres_guard_imp, rule decode_invocation_domaincap_corres, fastforce+)[1]
     apply (rule corres_guard_imp, rule decode_invocation_irqcontrolcap_corres, fastforce+)[1]
    apply (rule corres_guard_imp,rule decode_invocation_irqhandlercap_corres, fastforce+)[1]
   apply (rule corres_guard_imp,rule decode_invocation_zombiecap_corres, fastforce+)[1]
  apply (rule corres_guard_imp)
    apply (rule corres_rel_imp)
     apply (rule decode_invocation_archcap_corres, fastforce+)[1]
    apply clarsimp
    apply (case_tac x, simp)
    apply (clarsimp simp: cdl_invocation_relation_def)
   apply simp
  apply simp
  done

lemma ct_running_not_idle_etc:
  "\<lbrakk> invs s; ct_running s \<rbrakk> \<Longrightarrow> not_idle_thread (cur_thread s) s \<and> thread_is_running (cur_thread s) s"
  apply (simp add: not_idle_thread_def ct_in_state_def)
  apply (subgoal_tac "valid_idle s")
   apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
  apply (clarsimp simp: invs_def valid_state_def)
  done

lemma ct_active_not_idle_etc:
  "\<lbrakk> invs s; ct_active s \<rbrakk> \<Longrightarrow> not_idle_thread (cur_thread s) s"
  apply (simp add: not_idle_thread_def ct_in_state_def)
  apply (subgoal_tac "valid_idle s")
   apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)
  apply (clarsimp simp: invs_def valid_state_def)
  done

lemma dcorres_set_eobject_tcb:
  "\<lbrakk> \<exists>tcb'. (transform_tcb (machine_state s') p' tcb' etcb = Tcb tcb \<and> kheap s' p' = Some (TCB tcb'));
     p' \<noteq> idle_thread s'; kheap s' p' \<noteq> None; ekheap s' p' \<noteq> None \<rbrakk> \<Longrightarrow>
  dcorres dc ((=) (transform s')) ((=) s')
           (KHeap_D.set_object p' (Tcb tcb ))
           (set_eobject p' etcb)"
  supply if_cong[cong]
  apply (clarsimp simp: corres_underlying_def set_eobject_def in_monad)
  apply (clarsimp simp: KHeap_D.set_object_def simpler_modify_def)
  apply (clarsimp simp: transform_def transform_current_thread_def transform_cdt_def transform_asid_table_def)
  apply (clarsimp simp: transform_objects_def)
  apply (rule ext)
  apply clarsimp
  apply (clarsimp simp: option_map_def restrict_map_def map_add_def)
  done

lemma invoke_domain_corres:
  "\<lbrakk> i = cdl_invocation.InvokeDomain (SetDomain word1 word2);
     i' = Invocations_A.invocation.InvokeDomain word1 word2\<rbrakk>
       \<Longrightarrow> dcorres (dc \<oplus> dc) (\<lambda>_. True)
           (invs and ct_active and valid_pdpt_objs and valid_etcbs and
            invocation_duplicates_valid (Invocations_A.invocation.InvokeDomain word1 word2) and
            (tcb_at word1 and (\<lambda>s. word1 \<noteq> idle_thread s)))
           (Tcb_D.invoke_domain (SetDomain word1 word2)) (Tcb_A.invoke_domain word1 word2)"
  supply if_cong[cong]
  apply (clarsimp simp: Tcb_D.invoke_domain_def Tcb_A.invoke_domain_def)
  apply (rule corres_bind_return_r)
  apply (clarsimp simp: Tcb_D.set_domain_def Tcb_A.set_domain_def)
  apply (rule corres_symb_exec_r)
     apply (rule_tac Q=\<top> and Q'="tcb_at word1 and (\<lambda>s. word1 \<noteq> idle_thread s)" in dcorres_rhs_noop_above)
        apply (rule tcb_sched_action_dcorres)
       apply (rule dcorres_rhs_noop_below_True)
        apply (rule corres_noop)
         apply (wp reschedule_required_transform tcb_sched_action_transform | simp)+
       apply (simp add: update_thread_def ethread_set_def thread_set_domain_def)
       apply (rule dcorres_gets_the)
        apply clarsimp
        apply (drule get_tcb_at)
        apply (clarsimp simp: opt_object_tcb transform_tcb_def)
        apply (rule dcorres_set_eobject_tcb[simplified dc_def])
           apply (frule get_tcb_SomeD)
           apply (clarsimp simp: transform_tcb_def)
          apply simp
         apply (frule get_tcb_SomeD)
         apply simp
        apply (clarsimp simp: get_etcb_def split:option.splits)
       apply clarsimp
       apply (drule get_tcb_at)
       apply (clarsimp simp:opt_object_tcb)
      apply wp+
    apply simp
   apply wp
  apply simp
  done

(*
 * Show that invocation of a cap corresponds.
 *)
lemma perform_invocation_corres:
  "\<lbrakk>cdl_invocation_relation i i'\<rbrakk> \<Longrightarrow>
   dcorres (dc \<oplus> dc)
         \<top> (invs and ct_active and valid_pdpt_objs and valid_etcbs
            and invocation_duplicates_valid i' and valid_invocation i')
      (Syscall_D.perform_invocation call block i)
      (Syscall_A.perform_invocation block call i')"
  apply (clarsimp simp: cdl_invocation_relation_def)
  apply (case_tac i')
    apply (simp_all add: translate_invocation_def split: Invocations_A.invocation.splits)
  subgoal (* untyped *)
    apply (simp add: liftME_def[symmetric])
    apply (rule corres_guard_imp, rule invoke_untyped_corres)
     apply clarsimp
    apply clarsimp
    done

  subgoal (* send_ipc *)
    apply (clarsimp simp:invoke_endpoint_def)
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF get_cur_thread_corres])
        apply (rule corres_dummy_return_l)
        apply (rule corres_split)
           apply (rule send_sync_ipc_corres; simp)
          apply (rule corres_trivial[OF corres_free_return])
         apply (wp|clarsimp)+
    apply (clarsimp simp: ct_in_state_def obj_at_def pred_tcb_at_def not_idle_thread_def
                          valid_state_def invs_def valid_idle_def)
    done

  subgoal (* send_signal *)
    apply (clarsimp simp:invoke_notification_def liftE_bindE)
    apply (clarsimp simp:liftE_def bind_assoc returnOk_def)
    apply (rule corres_guard_imp)
      apply (rule corres_split)
         apply (rule send_signal_corres; simp)
        apply (rule corres_trivial)
        apply (simp add:dc_def corres_free_return)
       apply (wp | clarsimp)+
    done

  apply clarsimp
  subgoal for word a b c (* invoke_reply *)
    apply (clarsimp simp:invoke_reply_def)
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF get_cur_thread_corres])
        apply clarsimp
        apply (rule corres_dummy_return_l)
        apply (rule corres_split)
           apply (rule do_reply_transfer_corres, simp)
          apply (rule corres_trivial[OF  corres_free_return])
         apply (wp|clarsimp)+
    apply (simp add: ct_active_not_idle_etc)
    apply (rule conjI, fastforce)+
    apply (subgoal_tac "valid_idle s \<and> valid_reply_caps s \<and> has_reply_cap word s")
     apply clarsimp
     apply (drule (1) valid_reply_capsD)
     apply (clarsimp simp: valid_idle_def not_idle_thread_def pred_tcb_at_def obj_at_def)
    apply (fastforce simp: has_reply_cap_def is_reply_cap_to_def)
    done

  subgoal (* invoke_tcb *)
    apply (rule corres_guard_imp)
      apply (rule invoke_tcb_corres,simp+)
    done

  subgoal (* invoke_domain *)
    apply (rule corres_guard_imp)
      apply (rule invoke_domain_corres,simp+)
    done

  subgoal (* invoke_cnode *)
    apply (rule corres_guard_imp)
      apply (clarsimp simp:bindE_def returnOk_def lift_def bind_assoc)
      apply (rule corres_dummy_return_l)
      apply (rule corres_split[OF invoke_cnode_corres])
        apply (clarsimp simp:lift_def,case_tac rv',simp add: throwError_def)
        apply (simp)
       apply (rule hoare_triv[of \<top>], rule hoare_TrueI)+
     apply clarsimp+
    done

  subgoal for irq_control_invocation (* invoke_irq_control *)
    apply (simp add:liftE_def bindE_def)
    apply (case_tac irq_control_invocation)
     (* generic *)
     apply (rule corres_guard_imp)
       apply (rule corres_split[where r'=dc])
          apply (rule dcorres_invoke_irq_control)
         apply (rule_tac F = "\<exists>x. rv' = Inr x" in corres_gen_asm2)
         apply (rule corres_trivial)
         apply (clarsimp simp:lift_def returnOk_def)
        apply (rule hoare_triv[of \<top>], rule hoare_TrueI)+
       apply ((wp|simp add: liftE_def)+)
    (* arch *)
    apply (rename_tac arch_label)
    apply (case_tac arch_label)
    apply (rule corres_guard_imp)
      apply (rule corres_split[where r'=dc])
         apply (rule dcorres_arch_invoke_irq_control[simplified])
        apply (rule_tac F = "\<exists>x. rv' = Inr x" in corres_gen_asm2)
        apply (rule corres_trivial)
        apply (clarsimp simp:lift_def returnOk_def)
       apply (rule hoare_triv[of \<top>], rule hoare_TrueI)
      apply ((wp|simp add: liftE_def)+)
    done

  subgoal (* invoke_irq_handler *)
    apply (clarsimp simp:liftE_bindE,simp add:liftE_def returnOk_def)
    apply (rule corres_guard_imp)
      apply (rule corres_split)
         apply (rule dcorres_invoke_irq_handler)
        apply (rule corres_trivial)
        apply clarsimp
       apply (wp|clarsimp)+
    done

  subgoal (* invoke_arch *)
    apply (rule corres_guard_imp[OF invoke_arch_corres],fastforce+)
    done
  done (* invoke_tcb_corres *)

lemma sfi_generate_pending:
  "\<lbrace>st_tcb_at(\<lambda>st. \<not>(generates_pending st)) thread\<rbrace> Ipc_A.send_fault_ipc thread ft
  \<lbrace>\<lambda>t. \<top>\<rbrace>, \<lbrace>\<lambda>rv. st_tcb_at (\<lambda>st. \<not> (generates_pending st)) thread\<rbrace>"
   apply (clarsimp simp:send_fault_ipc_def Let_def lookup_cap_def)
   apply (wp hoare_drop_imps hoare_allI|wpc|clarsimp|rule hoare_conjI)+
   done

lemma dcorres_handle_double_fault:
  "dcorres dc \<top> (valid_mdb and not_idle_thread thread and valid_idle and valid_etcbs)
    (KHeap_D.set_cap (thread, tcb_pending_op_slot) cdl_cap.NullCap)
    (handle_double_fault thread ft' ft'a)"
  apply (simp add:handle_double_fault_def  )
  apply (rule corres_guard_imp)
    apply (rule set_thread_state_corres )
    apply simp+
  done

lemma handle_fault_corres:
  "dcorres dc \<top>
     (\<lambda>s. cur_thread s = thread \<and> not_idle_thread thread s \<and>
          st_tcb_at active thread s \<and> valid_fault ft' \<and>
          invs s \<and> valid_irq_node s \<and> valid_etcbs s)
     Endpoint_D.handle_fault
     (Ipc_A.handle_fault thread ft')"
  apply (simp add:Endpoint_D.handle_fault_def Ipc_A.handle_fault_def)
  apply (rule dcorres_gets_the)
   apply (clarsimp dest!:get_tcb_SomeD)
   apply (frule(1) valid_etcbs_tcb_etcb, clarsimp)
   apply (rule corres_guard_imp)
     apply (rule corres_split_catch[where r=dc and f = dc])
        apply (rule_tac tcb = obj' and etcb=etcb in send_fault_ipc_corres)
        apply (clarsimp simp:transform_def transform_current_thread_def
                             not_idle_thread_def)
       apply (rule_tac F = "obj = cur_thread s'" in corres_gen_asm2)
       apply simp
       apply (rule dcorres_handle_double_fault)
      apply (wp)
      apply (simp add:send_fault_ipc_def not_idle_thread_def Let_def)
      apply (wp hoare_drop_imps hoare_vcg_ball_lift | wpc)+
      apply (rule_tac Q'="\<lambda>r s. invs s \<and> valid_etcbs s \<and> obj\<noteq> idle_thread s \<and> obj = cur_thread s'"
        in hoare_strengthen_postE_R)
       apply wp
      apply (clarsimp simp:invs_mdb invs_valid_idle)
     apply wp
    apply simp
   apply (clarsimp simp:obj_at_def transform_def
     invs_mdb invs_valid_idle
     transform_current_thread_def not_idle_thread_def)
  apply (clarsimp dest!:get_tcb_SomeD
    simp: generates_pending_def not_idle_thread_def st_tcb_at_def obj_at_def)+
  apply (auto simp:transform_def transform_current_thread_def
    not_idle_thread_def  split:Structures_A.thread_state.splits)
   done

lemma get_tcb_mrs_wp:
  "\<lbrace>ko_at (TCB obj) thread and K_bind (evalMonad (lookup_ipc_buffer False thread) sa = Some (op_buf)) and (=) sa\<rbrace>
    get_mrs thread (op_buf) (data_to_message_info (arch_tcb_get_registers (tcb_arch obj) msg_info_register))
            \<lbrace>\<lambda>rv s. rv = get_tcb_mrs (machine_state sa) obj\<rbrace>"
  apply (case_tac op_buf)
    apply (clarsimp simp:get_mrs_def thread_get_def gets_the_def arch_tcb_get_registers_def)
    apply (wp|wpc)+
    apply (clarsimp simp:get_tcb_mrs_def Let_def)
    apply (clarsimp simp:Suc_leI[OF msg_registers_lt_msg_max_length] split del:if_split)
    apply (clarsimp simp:get_tcb_message_info_def get_ipc_buffer_words_empty)
    apply (clarsimp dest!:get_tcb_SomeD simp:obj_at_def arch_tcb_context_get_def)
  apply (clarsimp simp:get_mrs_def thread_get_def gets_the_def arch_tcb_get_registers_def)
  apply (clarsimp simp:Suc_leI[OF msg_registers_lt_msg_max_length] split del:if_split)
  apply (wp|wpc)+
  apply (rule_tac P = "tcb = obj" in hoare_gen_asm)
   apply (clarsimp simp: get_tcb_mrs_def Let_def get_tcb_message_info_def Suc_leI[OF msg_registers_lt_msg_max_length]
                         arch_tcb_context_get_def
                   split del:if_split)
    apply (rule_tac Q'="\<lambda>buf_mrs s. buf_mrs =
      (get_ipc_buffer_words (machine_state sa) obj ([Suc (length msg_registers)..<msg_max_length] @ [msg_max_length]))"
      in hoare_strengthen_post)
    apply (rule get_ipc_buffer_words[where thread=thread ])
    apply simp
  apply wp
  apply (clarsimp simp:get_tcb_SomeD obj_at_def)
  apply simp
done

lemma get_ipc_buffer_noop:
  "\<lbrace>P and (\<lambda>s. \<exists>s'. s = transform s' \<and> tcb_at t s' \<and> valid_etcbs s' \<and> not_idle_thread t s')\<rbrace>
     get_ipc_buffer t True \<exists>\<lbrace>\<lambda>r. P\<rbrace>"
  apply (simp add:gets_the_def gets_def bind_assoc get_def split_def get_ipc_buffer_def tcb_at_def
      exs_valid_def fail_def return_def bind_def assert_opt_def split:cdl_cap.splits)
  apply clarsimp
  apply (rule_tac x = "(the (opt_cap (t, tcb_ipcbuffer_slot) s),s)" for s in bexI)
   apply (rule conjI|fastforce simp:fail_def return_def split:option.splits)+
  apply (clarsimp split:option.splits simp:fail_def return_def)
  apply (frule(1) valid_etcbs_get_tcb_get_etcb)
  apply (clarsimp simp: opt_cap_tcb not_idle_thread_def)
  done

lemma dcorres_reply_from_kernel:
  "dcorres dc \<top> (invs and tcb_at oid and not_idle_thread oid and valid_etcbs) (corrupt_ipc_buffer oid True) (reply_from_kernel oid msg_rv)"
  apply (simp add:reply_from_kernel_def)
  apply (case_tac msg_rv)
  apply (clarsimp simp:corrupt_ipc_buffer_def)
  apply (rule dcorres_expand_pfx)
  apply (rule_tac Q' = "\<lambda>r. (=) s' and K_bind (evalMonad (lookup_ipc_buffer True oid) s' = Some r)"
                  in corres_symb_exec_r)
     apply (rule dcorres_expand_pfx)
     apply (clarsimp)
     apply (case_tac rv)
      apply (rule corres_symb_exec_l)
         apply (rule_tac F="rva = None" in corres_gen_asm)
         apply clarsimp
         apply (rule corres_guard_imp)
           apply (rule corres_corrupt_tcb_intent_dupl)
           apply (rule corres_split[OF set_register_corres])
             unfolding K_bind_def
             apply (rule corres_corrupt_tcb_intent_dupl)
             apply (rule corres_split[OF set_mrs_corres_no_recv_buffer])
               unfolding K_bind_def
               apply (rule set_message_info_corres)
              apply (wp | clarsimp simp:not_idle_thread_def)+
        apply (wp get_ipc_buffer_noop, clarsimp)
        apply (fastforce simp: not_idle_thread_def)
       apply (simp add: pred_conj_def)
       apply (strengthen refl[where t=True])
       apply (wp cdl_get_ipc_buffer_None  | simp)+
     apply clarsimp
     apply (drule lookup_ipc_buffer_SomeB_evalMonad)
     apply clarsimp
     apply (rule corres_symb_exec_l)
        apply (rule_tac F = "rv = Some ba" in corres_gen_asm)
        apply clarsimp
        apply (rule corrupt_frame_include_self[where y = oid])
         apply (rule corres_guard_imp)
           apply (rule corres_split[OF set_register_corres])
             unfolding K_bind_def
             apply (rule_tac y = oid in corrupt_frame_include_self')
              apply (rule corres_guard_imp)
                apply (rule corres_split[OF dcorres_set_mrs])
                  unfolding K_bind_def
                  apply (rule set_message_info_corres)
                 apply (wp| simp add:not_idle_thread_def)+
         apply (clarsimp simp:not_idle_thread_def)
         apply (clarsimp simp:invs_def not_idle_thread_def valid_state_def valid_pspace_def
                              ipc_frame_wp_at_def ipc_buffer_wp_at_def obj_at_def)
         apply (clarsimp simp:cte_wp_at_cases obj_at_def)
         apply (drule_tac s="cap.ArchObjectCap c" for c in sym)
         apply (clarsimp simp:ipc_frame_wp_at_def obj_at_def)
        apply (clarsimp simp:ipc_frame_wp_at_def obj_at_def cte_wp_at_cases)
        apply (drule_tac s="cap.ArchObjectCap c" for c in sym)
        apply simp
       apply (wp get_ipc_buffer_noop, clarsimp)
       apply fastforce
      apply simp
      apply (rule cdl_get_ipc_buffer_Some)
          apply fastforce
         apply (simp add:tcb_at_def not_idle_thread_def get_tcb_rev)+
    apply wp
     apply (rule evalMonad_wp)
      apply (simp add:empty_when_fail_lookup_ipc_buffer weak_det_spec_lookup_ipc_buffer)+
   apply (wp|clarsimp)+
  done

lemma dcorres_set_intent_error:
  "dcorres dc \<top>
    (invs and valid_etcbs and (\<lambda>s.  \<exists>tcb. guess_error (mi_label (get_tcb_message_info tcb)) = er
    \<and> ko_at (TCB tcb) oid s) and not_idle_thread oid) (mark_tcb_intent_error oid er) (return a)"
  apply (clarsimp simp:mark_tcb_intent_error_def bind_assoc
                       gets_the_def update_thread_def gets_def )
  apply (rule dcorres_absorb_get_l)
  apply (clarsimp simp: not_idle_thread_def)
  apply (frule ko_at_tcb_at)
  apply (frule(1) tcb_at_is_etcb_at)
  apply (clarsimp simp:tcb_at_def is_etcb_at_def, fold get_etcb_def)
  apply (clarsimp simp:opt_object_tcb assert_opt_def transform_tcb_def KHeap_D.set_object_def
                       simpler_modify_def corres_underlying_def)
  apply (simp add:transform_def return_def)
  apply (rule ext)
  apply (clarsimp simp:transform_objects_def transform_tcb_def
                  dest!:get_tcb_SomeD get_etcb_SomeD)
  apply (simp add:transform_full_intent_def Let_def obj_at_def)
  done

lemma dcorres_when_r:
  "\<lbrakk>R \<Longrightarrow> dcorres dc \<top> P l r; \<not> R \<Longrightarrow> dcorres dc \<top> Q l (return ())\<rbrakk>
    \<Longrightarrow> dcorres dc \<top> (\<lambda>s. (R \<longrightarrow> P s) \<and> (\<not> R \<longrightarrow> Q s)) l (when R r)"
  by (clarsimp simp:when_def)

lemma evalMonad_from_wp:
  "\<lbrakk>evalMonad f s = Some a;\<lbrace>P\<rbrace>f\<lbrace> \<lambda>rv s. R rv\<rbrace>;P s;empty_when_fail f;\<And>Q. weak_det_spec Q f \<rbrakk>\<Longrightarrow> R a"
  apply (clarsimp simp:evalMonad_def valid_def)
  apply (drule_tac x = "(=) s" in meta_spec)
  apply (fastforce simp:weak_det_spec_def empty_when_fail_def no_fail_def det_spec_def)
  done

lemma empty_when_fail_get_mrs:
  notes option.case_cong_weak [cong]
  shows "empty_when_fail (get_mrs a b c)"
  apply (clarsimp simp:get_mrs_def)
  apply (rule empty_when_fail_compose)+
      apply (simp add:empty_when_fail_return split:option.splits)+
     apply (rule conjI)
      apply clarsimp
      apply (rule empty_when_fail_mapM)
      apply (simp add:empty_when_fail_load_word_offs weak_det_spec_load_word_offs)
     apply clarsimp
     apply (rule empty_when_fail_mapM)
     apply (simp add:empty_when_fail_load_word_offs weak_det_spec_load_word_offs)
    apply (clarsimp simp:empty_when_fail_return weak_det_spec_simps split:option.splits)
    apply (rule conjI)
     apply clarsimp
     apply (rule weak_det_spec_mapM)
     apply (simp add:weak_det_spec_load_word_offs)
    apply clarsimp
    apply (rule weak_det_spec_mapM)
    apply (simp add:weak_det_spec_load_word_offs)
   apply (simp add:empty_when_fail_thread_get)
  apply (simp add:weak_det_spec_thread_get)
  done

lemma weak_det_spec_get_mrs:
  notes option.case_cong_weak [cong]
  shows "weak_det_spec P (get_mrs a b c)"
  apply (clarsimp simp:get_mrs_def)
  apply (rule weak_det_spec_compose)+
    apply (simp add:weak_det_spec_simps split:option.splits)+
   apply (rule conjI)
    apply clarsimp
    apply (rule weak_det_spec_mapM)
    apply (simp add:weak_det_spec_load_word_offs)
   apply clarsimp
   apply (rule weak_det_spec_mapM)
   apply (simp add:weak_det_spec_load_word_offs)
  apply (simp add:weak_det_spec_thread_get)
  done

lemma lookup_cap_and_slot_inv:
  "\<lbrace>P\<rbrace> CSpace_A.lookup_cap_and_slot t (to_bl (arch_tcb_get_registers (tcb_arch obj'a) cap_register)) \<lbrace>\<lambda>x. P\<rbrace>, \<lbrace>\<lambda>ft s. True\<rbrace>"
  apply (simp add:CSpace_A.lookup_cap_and_slot_def)
  apply (wp | clarsimp simp:liftE_bindE)+
  done

(* We need following lemma because we need to match get_mrs in abstract and cdl_intent_op in capdl after state s is fixed *)
lemma decode_invocation_corres':
  "\<lbrakk>(\<lambda>(cap, slot, extra) (slot', cap', extra', buffer).
     cap = transform_cap cap' \<and> slot = transform_cslot_ptr slot' \<and> extra = transform_cap_list extra')
     rv rv'; get_tcb (cur_thread s) s = Some ctcb; ct_running s;invs s\<rbrakk>
  \<Longrightarrow> dcorres (dc \<oplus> cdl_invocation_relation) \<top>
    ((=) s and (\<lambda>(slot,cap,excaps,buffer) s. \<not> is_master_reply_cap (cap) \<and> valid_cap cap s \<and> valid_etcbs s
    \<and> evalMonad (lookup_ipc_buffer False (cur_thread s)) s = Some buffer
    \<and> (\<forall>e\<in> set excaps. s \<turnstile> fst e) \<and> cte_wp_at (Not \<circ> is_master_reply_cap) slot s \<and> cte_wp_at ((=) cap) slot s
    \<and> (\<forall>e\<in> set excaps. cte_wp_at ((=) (fst e)) (snd e) s)) rv')
     ((\<lambda>(cap, cap_ref, extra_caps).
          case_option (if ep_related_cap cap then Decode_D.decode_invocation cap cap_ref extra_caps undefined else Monads_D.throw)
          (Decode_D.decode_invocation cap cap_ref extra_caps)
          (cdl_intent_op (transform_full_intent (machine_state s) (cur_thread s) ctcb)))
     rv)
     ((\<lambda>(slot, cap, extracaps, buffer).
          do args \<leftarrow> get_mrs (cur_thread s) buffer (data_to_message_info (arch_tcb_get_registers (tcb_arch ctcb) msg_info_register));
          Decode_A.decode_invocation (mi_label (data_to_message_info (arch_tcb_get_registers (tcb_arch ctcb) msg_info_register))) args
          (to_bl (arch_tcb_get_registers (tcb_arch ctcb) cap_register)) slot cap extracaps
         od)
     rv')"
  apply (rule dcorres_expand_pfx)
  apply (clarsimp split del:if_split)
  apply (rule_tac Q' ="\<lambda>r ns. ns = s
     \<and> r =  get_tcb_mrs (machine_state s) ctcb"
     in corres_symb_exec_r)
     apply (clarsimp split:option.split | rule conjI)+
       apply (rule corres_guard_imp[OF decode_invocation_ep_related_branch])
          apply clarsimp+
      defer
      apply clarsimp
      apply (rule dcorres_expand_pfx)
      apply (rule corres_guard_imp[OF decode_invocation_corres])
           apply (solves \<open>clarsimp simp: transform_full_intent_def Let_def get_tcb_message_info_def
                                         arch_tcb_get_registers_def arch_tcb_context_get_def\<close>)+
     apply (wp get_tcb_mrs_wp | clarsimp)+
  apply (rule dcorres_expand_pfx)
  apply (rule dcorres_free_throw[OF decode_invocation_error_branch])
   apply (clarsimp simp:transform_full_intent_def Let_def get_tcb_message_info_def
                        arch_tcb_get_registers_def arch_tcb_context_get_def)+
  done

lemma reply_from_kernel_error:
  notes option.case_cong_weak [cong]
  shows
  "\<lbrace>tcb_at oid and K (fst e \<le> mask 19 \<and> 0 < fst e = er)\<rbrace>reply_from_kernel oid e
    \<lbrace>\<lambda>rv s. (\<exists>tcb. guess_error (mi_label (get_tcb_message_info tcb)) = er \<and>
    ko_at (TCB tcb) oid s)\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (case_tac e)
  apply (clarsimp simp:reply_from_kernel_def guess_error_def split_def set_message_info_def)
  apply (rule hoare_pre)
   apply (wp)
      apply (simp add:as_user_def split_def set_object_def get_object_def)
      apply (wp set_object_at_obj)
     apply (rule hoare_strengthen_post[where Q'="\<lambda>x s. x \<le> mask 12"])
      apply (simp add:set_mrs_def)
      apply (wp|wpc)+
     apply (clarsimp simp:setRegister_def simpler_modify_def)
     apply (drule get_tcb_SomeD)
     apply (rule exI)
     apply (rule conjI[rotated])
      apply (simp add:obj_at_def)
     apply (simp add:get_tcb_message_info_def data_to_message_info_def word_neq_0_conv mask_def)
     apply (simp add:shiftr_over_or_dist le_mask_iff word_neq_0_conv)
     apply (subst shiftl_shiftr_id)
       apply (simp add:word_bits_def mask_def le_mask_iff[symmetric])+
      apply unat_arith
     apply (word_bitwise, simp)
    apply (wp hoare_drop_imp hoare_vcg_all_lift)+
  apply clarsimp
  apply (rule conjI)
   apply (rule word_of_nat_le)
   apply (rule le_trans[OF min.cobounded1])
   apply (simp add:mask_def)
   apply (rule le_trans)
    apply (rule less_imp_le[OF msg_registers_lt_msg_max_length])
   apply (simp add:msg_max_length_def)
  apply (rule plus_one_helper)
  apply (simp add:mask_def)
  apply (rule word_of_nat_less)
  apply (simp add:msg_max_length_def)
  done

lemma liftE_distrib':
  "liftE (do x \<leftarrow> A;B x od) =
  doE x \<leftarrow> liftE A;
  liftE (B x)
  odE"
  by (simp add:bindE_def liftE_def bind_assoc lift_def)

crunch reply_from_kernel
  for valid_etcbs[wp]: valid_etcbs

lemma dcorres_reply_from_syscall:
  "dcorres (dc \<oplus> dc) \<top> (invs and not_idle_thread thread and valid_idle and valid_etcbs)
    (do restart \<leftarrow> has_restart_cap thread;
      if restart then liftE (
      (do y \<leftarrow> corrupt_ipc_buffer thread True;
          y \<leftarrow>when call (mark_tcb_intent_error thread False);
          KHeap_D.set_cap (thread, tcb_pending_op_slot) RunningCap
      od ))
      else returnOk ()
    od)
    (liftE (do x \<leftarrow> get_thread_state thread;
      (case x of
        Structures_A.thread_state.Restart \<Rightarrow>
        do y \<leftarrow> when call (reply_from_kernel thread (0, reply));
           set_thread_state thread Structures_A.thread_state.Running
        od
      | _ \<Rightarrow> return ()) od))"
  apply (clarsimp simp:get_thread_state_def thread_get_def liftE_distrib' liftE_bindE)
  apply (rule dcorres_absorb_gets_the)
  apply (simp add:has_restart_cap_def get_thread_def gets_the_def
    gets_def bind_assoc liftE_distrib')
  apply (rule dcorres_absorb_get_l)
  apply (clarsimp, frule(1) valid_etcbs_get_tcb_get_etcb)
  apply (clarsimp simp:opt_object_tcb not_idle_thread_def
    liftE_bindE liftE_distrib' infer_tcb_pending_op_def tcb_slots
    transform_tcb_def assert_opt_def when_def returnOk_liftE[symmetric]
    split: Structures_A.thread_state.splits)
  apply (intro conjI impI)
          apply (rule dcorres_returnOk',simp)+
        apply (rule corres_guard_imp)
          apply (rule corres_split[OF dcorres_reply_from_kernel])
            apply (rule corres_dummy_return_pr)
            apply (rule corres_split[OF dcorres_set_intent_error])
              apply (simp add:liftE_bindE returnOk_liftE)
              apply (rule set_thread_state_corres[unfolded tcb_slots])
             apply (wp rfk_invs reply_from_kernel_error)+
          apply (simp add:not_idle_thread_def)
          apply (wp rfk_invs)
         apply simp
        apply (clarsimp simp: tcb_at_def st_tcb_at_def obj_at_def not_idle_thread_def
                       dest!: get_tcb_SomeD)
       apply (rule corres_dummy_return_pr)
       apply (rule corres_guard_imp[OF corres_split[where r' = "dc"]])
            apply (rule dcorres_dummy_corrupt_ipc_buffer)
           apply (simp add: returnOk_liftE)
           apply (rule set_thread_state_corres[unfolded tcb_slots])
          apply wp+
        apply simp
       apply (clarsimp simp: tcb_at_def invs_mdb st_tcb_at_def not_idle_thread_def obj_at_def
                      dest!: get_tcb_SomeD)
      apply (rule dcorres_returnOk', simp)+
  done

lemmas mapM_x_def_symmetric = mapM_x_def[symmetric]

crunch send_ipc
  for idle[wp]: "\<lambda>s::'z::state_ext state. P (idle_thread s)"
  (wp: crunch_wps dxo_wp_weak simp: crunch_simps  ignore:clearMemory)

crunch send_signal
  for idle[wp]: "\<lambda>s::'z::state_ext state. P (idle_thread s)"
  (wp: crunch_wps dxo_wp_weak simp: crunch_simps  ignore:clearMemory)

crunch do_reply_transfer
  for idle[wp]: "\<lambda>s::'z::state_ext state. P (idle_thread s)"
  (wp: crunch_wps dxo_wp_weak simp: crunch_simps  ignore:clearMemory)

lemma check_cap_at_idle:
 "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> check_cap_at a b (check_cap_at c d (cap_insert new_cap src_slot (target, ref)))
  \<lbrace>\<lambda>rv s. P (idle_thread s)\<rbrace>"
  apply (rule check_cap_at_stable)
  apply wp
done

lemmas cap_revoke_preservation_flat = cap_revoke_preservation[THEN validE_valid]

crunch invoke_tcb, cap_move, cap_swap, cap_revoke
  for idle[wp]: "\<lambda>s::'z::state_ext state. P (idle_thread s)"
  (rule: cap_revoke_preservation_flat wp: crunch_wps check_cap_at_idle dxo_wp_weak
    simp: crunch_simps ignore: check_cap_at)

lemma invoke_cnode_idle:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> invoke_cnode pa \<lbrace>\<lambda>r s. P (idle_thread s)\<rbrace>"
  apply (cases pa)
        apply (clarsimp simp:invoke_cnode_def
            | wpsimp wp: crunch_wps hoare_vcg_all_lift | rule conjI)+
  done

crunch arch_perform_invocation
  for idle[wp]: "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps simp: crunch_simps)

lemma invoke_domain_idle:
  "\<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> invoke_domain t d  \<lbrace>\<lambda>r s. P (idle_thread s)\<rbrace>"
  by  (clarsimp simp: Tcb_A.invoke_domain_def trans_state_def | wp dxo_wp_weak)+

crunch "Syscall_A.perform_invocation"
  for idle[wp]: "\<lambda>s. P (idle_thread s)"

lemma msg_from_syscall_error_simp:
  "fst (msg_from_syscall_error rv) \<le> mask 19"
  "0 < fst (msg_from_syscall_error rv)"
   apply (case_tac rv)
            apply (clarsimp simp:mask_def)+
  apply (case_tac rv)
           apply simp+
  done

lemma not_master_reply_cap_lcs[wp]:
  "\<lbrace>valid_reply_masters and valid_objs\<rbrace>CSpace_A.lookup_cap_and_slot t ptr
            \<lbrace>\<lambda>rv s. \<not> is_master_reply_cap (fst rv)\<rbrace>,-"
  apply (simp add:lookup_cap_and_slot_def)
  apply wp
    apply (simp add:split_def)
    apply wp
    apply (rule_tac Q'="\<lambda>cap. cte_wp_at (\<lambda>x. x = cap) (fst rv) and real_cte_at (fst rv)
                              and valid_reply_masters and valid_objs" in hoare_strengthen_post)
     apply (wp get_cap_cte_wp_at)
    apply clarify
    apply (drule real_cte_not_reply_masterD)
      apply clarsimp+
    apply (simp add:cte_wp_at_def)
   apply wp
  apply simp
  done

lemma not_master_reply_cap_lcs'[wp]:
  "\<lbrace>valid_reply_masters and valid_objs\<rbrace> CSpace_A.lookup_cap_and_slot t ptr
            \<lbrace>\<lambda>rv s. cte_wp_at (Not \<circ> is_master_reply_cap) (snd rv) s\<rbrace>,-"
  apply (rule_tac Q' = "\<lambda>rv s. \<not> is_master_reply_cap (fst rv) \<and> cte_wp_at ((=) (fst rv)) (snd rv) s"
           in hoare_strengthen_postE_R)
   apply (rule hoare_pre,wp,simp)
  apply (clarsimp simp:cte_wp_at_def)
  done

lemma set_thread_state_ct_active:
  "\<lbrace>\<lambda>s. cur_thread s = cur_thread s'\<rbrace>
   set_thread_state (cur_thread s') Structures_A.thread_state.Restart \<lbrace>\<lambda>rv. ct_active\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wp dxo_wp_weak
       | clarsimp simp: set_object_def get_object_def trans_state_def
                        ct_in_state_def st_tcb_at_def obj_at_def)+
  done

lemma invoke_cnode_valid_etcbs[wp]:
  "\<lbrace>valid_etcbs\<rbrace> invoke_cnode ci \<lbrace>\<lambda>_. valid_etcbs\<rbrace>"
  apply (simp add: invoke_cnode_def)
  apply (rule hoare_pre)
   apply (wp crunch_wps hoare_vcg_all_lift | wpc | simp add: split del: if_split)+
  done

crunch perform_invocation
  for valid_etcbs[wp]: valid_etcbs
  (wp: crunch_wps check_cap_inv simp: crunch_simps ignore: without_preemption)

(*
 * Show that handle_invocation is equivalent.
 *)
lemma handle_invocation_corres:
  "dcorres (dc \<oplus> dc) \<top>
      (invs and ct_running and valid_pdpt_objs and valid_etcbs)
      (Syscall_D.handle_invocation call block)
      (Syscall_A.handle_invocation call block)"
  apply (simp add: Syscall_A.handle_invocation_def Syscall_D.handle_invocation_def liftE_bindE)
  apply (clarsimp simp:gets_the_def gets_def bind_assoc)
  apply (rule dcorres_absorb_get_l)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp, frule ct_running_not_idle_etc,simp+)
  apply (clarsimp simp: cdl_current_thread transform_current_thread_def not_idle_thread_def assert_opt_def)
  apply (simp add:get_message_info_def select_f_get_register bind_assoc liftM_def get_thread_def)
  apply (rule dcorres_gets_the)
   apply (clarsimp, frule(1) valid_etcbs_get_tcb_get_etcb)
   prefer 2
   apply (clarsimp, frule(1) valid_etcbs_get_tcb_get_etcb)
   apply (clarsimp simp:opt_object_tcb transform_tcb_def)+
  apply (rule dcorres_absorb_gets_the)
  apply (clarsimp simp:Syscall_D.syscall_def Syscall_A.syscall_def liftE_bindE handle_elseE_def)
  apply (rule corres_guard_imp)
    apply (rule_tac P' = "(=) s'a" and P=\<top> and Q' = "(=) s'a" and Q=\<top> and
                    rr = "\<lambda>(cap,slot,extra) (slot',cap',extra',buffer).
                              cap = transform_cap cap' \<and> slot = transform_cslot_ptr slot'
                            \<and> extra = transform_cap_list extra'" in  corres_split_bind_case_sum)
        apply (rule_tac Q = "\<lambda>x. \<top>" and Q'="\<lambda>x. (=) s'a" in corres_initial_splitE)
           apply (clarsimp simp: transform_full_intent_def Let_def arch_tcb_get_registers_def
                                 arch_tcb_context_get_def)
           apply (rule corres_guard_imp[OF dcorres_lookup_cap_and_slot[simplified]])
              apply (clarsimp simp: word_bits_def not_idle_thread_def invs_def valid_state_def)+
          apply (rule dcorres_symb_exec_r_evalMonad)
             apply wp
            apply (rule corres_guard_imp)
              apply (rule corres_splitEE)
                 apply (rule dcorres_lookup_extra_caps; clarsimp simp:not_idle_thread_def)
                apply (rule dcorres_returnOk)
                apply simp
               apply (wp|clarsimp)+
           apply (simp add:empty_when_fail_lookup_ipc_buffer weak_det_spec_lookup_ipc_buffer)+
         apply (wp lookup_cap_and_slot_inv)+
       apply (simp add:liftE_bindE)
       apply (rule corres_when,simp)
       apply (rule handle_fault_corres)
      apply (rule corres_split_bind_case_sum)
          apply (rule decode_invocation_corres')
             apply (simp add: split_def)+
         apply (rule dcorres_when_r)
          apply (rule corres_dummy_return_r)
          apply (rule corres_guard_imp[OF corres_split[OF dcorres_reply_from_kernel]])
              apply (simp add:when_def)
              apply (rule dcorres_set_intent_error)
             apply (wp rfk_invs reply_from_kernel_error | simp add:not_idle_thread_def)+
         apply (rule dcorres_dummy_corrupt_ipc_buffer)
        apply (rule corres_split[OF dcorres_set_thread_state_Restart2])
          apply (rule corres_splitEE[where r' = dc])
             apply (rule perform_invocation_corres,simp)
            apply (simp add: whenE_def bind_assoc)
            apply (rule dcorres_reply_from_syscall)
           apply wp+
          apply (simp add: not_idle_thread_def)
          apply (strengthen invs_valid_idle)
          apply wp+
        \<comment> \<open>The following proof is quite fragile. If clarsimp is used, either on its own or as part
            of wpsimp, then it rewrites pairs and necessary rules no longer match.\<close>
        apply (simp add: not_idle_thread_def split_def)
        apply (wp sts_Restart_invs set_thread_state_ct_active)+
       apply (simp add: split_def msg_from_syscall_error_simp)
       apply (wp | simp add: split_def)+
      apply (rule_tac Q'="\<lambda>r s. s = s'a \<and>
                               evalMonad (lookup_ipc_buffer False (cur_thread s'a)) s'a = Some r \<and>
                               cte_wp_at (Not \<circ> is_master_reply_cap) (snd rv) s \<and>
                               cte_wp_at ((=) (fst rv)) (snd rv) s \<and>
                               real_cte_at (snd rv) s \<and>
                               s \<turnstile> fst rv \<and>
                               ex_cte_cap_wp_to (\<lambda>_. True) (snd rv) s \<and>
                               (\<forall>r\<in>zobj_refs (fst rv). ex_nonz_cap_to r s) \<and>
                               (\<forall>r\<in>cte_refs (fst rv) (interrupt_irq_node s). ex_cte_cap_wp_to \<top> r s)"
                      in hoare_strengthen_post)
       apply (wp evalMonad_wp)
         apply (simp add: empty_when_fail_lookup_ipc_buffer weak_det_spec_lookup_ipc_buffer)+
       apply wp
      apply (clarsimp simp: invs_def valid_state_def valid_pspace_def valid_idle_def st_tcb_ex_cap
                            ct_in_state_def pred_tcb_at_def not_idle_thread_def obj_at_def
                     dest!: get_tcb_SomeD)
     apply wp+
    apply (clarsimp simp:invs_def valid_state_def not_idle_thread_def pred_tcb_at_def obj_at_def)
   apply simp_all
  done

crunch complete_signal
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"

lemma receive_ipc_cur_thread:
  notes do_nbrecv_failed_transfer_def[simp]
        if_split[split del]
  shows
  " \<lbrace>\<lambda>s. valid_objs s \<and>  P (cur_thread (s :: det_ext state))\<rbrace> receive_ipc a b c \<lbrace>\<lambda>xg s. P (cur_thread s)\<rbrace>"
  apply (simp add:receive_ipc_def bind_assoc)
  apply (wp|wpc|clarsimp)+
                 apply (simp add:setup_caller_cap_def)
                 apply (wp dxo_wp_weak | simp)+
              apply (rule_tac Q'="\<lambda>r s. P (cur_thread s)" in hoare_strengthen_post)
              apply clarsimp
             apply (wp|wpc)+
           apply clarsimp
          apply (clarsimp simp:neq_Nil_conv)
          apply (rename_tac list queue sender)
          apply (rule_tac Q'="\<lambda>r s. P (cur_thread s) \<and> tcb_at (hd list) s" in hoare_strengthen_post)
           apply wp
          apply (clarsimp simp:st_tcb_at_def tcb_at_def)
         apply (wp get_simple_ko_wp[where f=Notification] gbn_wp | wpc | simp add: Ipc_A.isActive_def)+
   apply (rule_tac Q'="\<lambda>r s. valid_ep r s \<and> P (cur_thread s)" in hoare_strengthen_post)
    apply (wp get_simple_ko_valid[where f=Endpoint, simplified valid_ep_def2[symmetric]])
   apply (clarsimp simp:valid_ep_def)
   apply auto[1]
  apply (rule hoare_pre)
   apply (wp | wpc | simp)+
  done

lemma cap_delete_one_st_tcb_at_and_valid_etcbs:
  "\<lbrace>st_tcb_at P t and K (\<forall>st. active st \<longrightarrow> P st) and valid_etcbs\<rbrace> cap_delete_one ptr \<lbrace>\<lambda>rv s. st_tcb_at P t s \<and> valid_etcbs s\<rbrace>"
 by (wp cap_delete_one_st_tcb_at cap_delete_one_valid_etcbs | simp)+

crunch deleted_irq_handler, cap_delete_one
  for ct_it[wp]: "\<lambda>s::'z::state_ext state. P (cur_thread s) (idle_thread s)"
     (wp: crunch_wps set_thread_state_ext_extended.all_but_exst dxo_wp_weak
    simp: crunch_simps unless_def)

lemma handle_recv_corres:
  "dcorres dc \<top> (invs and (\<lambda>s. not_idle_thread (cur_thread s) s \<and> st_tcb_at active (cur_thread s) s) and valid_etcbs)
  Syscall_D.handle_recv (Syscall_A.handle_recv is_blocking)"
  apply (simp add: Syscall_D.handle_recv_def Syscall_A.handle_recv_def delete_caller_cap_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF get_cur_thread_corres])
      apply (simp add:liftM_def select_f_get_register get_thread_def bind_assoc)
      apply (rename_tac thread)
      apply (rule_tac P=\<top> and P'="invs and valid_etcbs and (\<lambda>s. thread = cur_thread s
                                   \<and> not_idle_thread thread s \<and> st_tcb_at active thread s)"
                     in dcorres_gets_the)
       apply (clarsimp simp: not_idle_thread_def, frule(1) valid_etcbs_get_tcb_get_etcb)
       apply (clarsimp simp:opt_object_tcb gets_def transform_tcb_def)
       apply (simp add:transform_full_intent_def Let_def cap_fault_injection)
       apply (rule corres_guard_imp)
         apply (rule corres_split_catch[where f= dc, OF _ handle_fault_corres])
           apply (rule dcorres_injection_handler_rhs)
           apply (rule_tac R' ="\<lambda>rv s. (\<forall>ref badge rights. rv = cap.EndpointCap ref badge rights \<longrightarrow>
                  (ep_at ref s)) \<and> not_idle_thread (cur_thread s') s
                 \<and> not_idle_thread (cur_thread s) s
                 \<and> (st_tcb_at active (cur_thread s') s \<and> invs s \<and> valid_etcbs s) \<and> ko_at (TCB obj') (cur_thread s') s " and R= "\<lambda>r. \<top>"
                       in corres_splitEE[where r'="\<lambda>x y. x = transform_cap y"])
              apply (simp add: arch_tcb_get_registers_def arch_tcb_context_get_def)
              apply (rule lookup_cap_corres, simp)
              apply (simp add: word_bits_def)
             apply (rule dcorres_expand_pfx)
             apply (clarsimp split:cap.splits arch_cap.splits split del: if_split simp:transform_cap_def)
               apply (rename_tac word1 word2 set)
               apply (rule corres_guard_imp)
                 apply (case_tac "AllowRead \<in> set"; simp split del: if_split)
                 apply (rule corres_alternate1)
                 apply clarsimp
                 apply (rule corres_split[where r'=dc])
                    apply (simp add: delete_caller_cap_def transform_tcb_slot_simp[symmetric])
                    apply (rule delete_cap_simple_corres)
                   apply (rule_tac epptr=word1 in recv_sync_ipc_corres
                                      [where ep_cap="cap.EndpointCap _ _ _", simplified];
                          simp)
                  apply (wp | clarsimp simp: delete_caller_cap_def not_idle_thread_def)+
                 apply (rule hoare_vcg_conj_lift)
                  apply (rule_tac t1="cur_thread s'" in hoare_post_imp[OF _ cap_delete_one_st_tcb_at_and_valid_etcbs])
                  apply (fastforce simp: obj_at_def generates_pending_def st_tcb_at_def)
                 apply (rule_tac Q'="\<lambda>rv. invs and valid_etcbs" in hoare_strengthen_post)
                  apply wp
                 apply (clarsimp simp: invs_def)
                apply clarsimp
               apply (clarsimp simp: emptyable_def not_idle_thread_def)
              defer(* NEED RECEIVE ASYNC IPC *)
              apply clarsimp
             apply wp+
            apply (rule hoare_vcg_conj_liftE_R')
             apply (rule hoare_strengthen_postE_R, rule lookup_cap_valid)
             apply (clarsimp simp: valid_cap_def)
            apply wp+
          apply (simp add:injection_handler_def)
          apply (wp get_simple_ko_wp |wpc)+
          apply (simp only: conj_ac)
          apply wp
          apply (rule hoare_vcg_conj_elimE)
           apply (simp add: lookup_cap_def lookup_slot_for_thread_def split_def)
           apply wp
            apply (rule hoare_strengthen_postE[OF resolve_address_bits_valid_fault])
             apply simp
            apply simp
           apply wp
          apply (rule validE_validE_R)
          apply (clarsimp simp:validE_def)
          apply (rule_tac Q'="\<lambda>r s. cur_thread s = cur_thread s' \<and>
                                not_idle_thread (cur_thread s) s \<and>
                                st_tcb_at active (cur_thread s) s \<and>
                                invs s \<and> valid_etcbs s \<and>
                                valid_irq_node s" in hoare_strengthen_post)
           apply wp
          apply (clarsimp simp add: valid_fault_def)
         apply clarsimp+
        apply (clarsimp dest!: get_tcb_SomeD
                         simp: invs_valid_tcb_ctable valid_state_def invs_def
                               obj_at_def valid_pspace_def not_idle_thread_def)
       apply (clarsimp, frule(1) valid_etcbs_get_tcb_get_etcb)
       apply (clarsimp simp:opt_object_tcb not_idle_thread_def)
      apply wp+
    apply simp
   apply (clarsimp simp:emptyable_def not_idle_thread_def)
  apply (clarsimp simp: liftE_bindE get_simple_ko_def get_object_def gets_def bind_assoc)
  apply (rule dcorres_absorb_get_r)
  apply (clarsimp simp: assert_def corres_free_fail partial_inv_def a_type_def
                 split: Structures_A.kernel_object.splits)
  apply safe[1]
    apply (rule corres_alternate1, clarsimp, rule corres_guard_imp[OF recv_signal_corres], (clarsimp simp: transform_cap_def)+)+
  apply (rule corres_alternate2)
  apply clarsimp
  done

(* Show that handle_reply is equivalent. *)
lemma handle_reply_corres:
  "dcorres dc \<top> (invs and (\<lambda>s. not_idle_thread (cur_thread s) s \<and> ct_running s) and valid_etcbs)
  Syscall_D.handle_reply Syscall_A.handle_reply"
  apply (simp add: Syscall_D.handle_reply_def Syscall_A.handle_reply_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF get_cur_thread_corres])
      apply simp
      apply (rename_tac thread)
      apply (rule_tac R="\<lambda>_. \<top>" and
                      R'="\<lambda>cap. invs and valid_etcbs and ct_running and tcb_at thread
                                and not_idle_thread thread
                                and cte_wp_at ((=) cap) (thread, tcb_cnode_index 3)"
                  in  corres_split)
         apply (rule get_cap_corres)
         apply (clarsimp simp: simp: transform_tcb_slot_simp)
        apply (simp add: transform_cap_def corres_fail split: cap.split)
        apply (clarsimp simp: corres_fail dc_def[symmetric] split: bool.split)
        apply (rename_tac word rights)
        apply (rule corres_guard_imp)
          apply (rule do_reply_transfer_corres)
          apply (simp add: transform_tcb_slot_simp)
         apply simp
        apply (clarsimp simp:ct_running_not_idle_etc)
        apply (frule caps_of_state_valid(1))
         apply (clarsimp simp:cte_wp_at_caps_of_state)
         apply (simp add:valid_cap_def)+
        apply (clarsimp simp:valid_state_def invs_def valid_reply_caps_def dest!:has_reply_cap_cte_wpD)
        apply (drule_tac x = word in spec, simp add: cte_wp_at_def)
        apply (clarsimp simp:not_idle_thread_def pred_tcb_at_def obj_at_def valid_idle_def
                             cte_wp_at_def has_reply_cap_def is_reply_cap_to_def)
        apply blast
       apply (wpsimp wp: get_cap_wp)+
  apply (clarsimp simp:ct_in_state_def invs_def valid_state_def pred_tcb_at_def tcb_at_def obj_at_def)
  done

lemma handle_vm_fault_wp:
  "\<lbrace>P\<rbrace> handle_vm_fault thread vmfault_type \<lbrace>\<lambda>_. Q\<rbrace>,\<lbrace>\<lambda>rv. P\<rbrace>"
  apply (case_tac vmfault_type)
   apply (simp)
   apply wp
     apply (clarsimp simp:do_machine_op_def getDFSR_def)
     apply wp
       apply (case_tac rv)
       apply clarsimp
       apply (rule_tac P="P and (\<lambda>x. snd (aa,ba) = machine_state x)" in  hoare_post_imp)
        apply (assumption)
       apply (clarsimp simp:valid_def simpler_modify_def return_def bind_def)
      apply wp+
    apply (clarsimp simp:gets_def alternative_def get_def bind_def select_def return_def)
    apply (clarsimp simp:do_machine_op_def getFAR_def)
    apply wp
      apply (case_tac rv)
      apply clarsimp
      apply (rule_tac P="P and (\<lambda>x. snd (aa,ba) = machine_state x)" in  hoare_post_imp)
       apply (assumption)
      apply (clarsimp simp:valid_def simpler_modify_def return_def bind_def)
     apply wp+
   apply (clarsimp simp:gets_def alternative_def select_def bind_def get_def return_def)
  apply simp
  apply wp
    apply (clarsimp simp:do_machine_op_def getIFSR_def)
    apply wp
      apply (case_tac rv)
      apply clarsimp
      apply (rule_tac P="P and (\<lambda>x. snd (aa,ba) = machine_state x)" in  hoare_post_imp)
       apply (assumption)
      apply (clarsimp simp:valid_def simpler_modify_def return_def bind_def)
     apply wp+
  apply (clarsimp simp:gets_def alternative_def select_def bind_def get_def return_def)
  done

lemma get_active_irq_corres:
  "dcorres (\<lambda>r r'. r' = r) \<top> \<top> get_active_irq (do_machine_op (getActiveIRQ in_kernel))"
  apply (clarsimp simp: corres_underlying_def do_machine_op_def
                        select_f_def bind_def in_monad getActiveIRQ_def
                        return_def get_active_irq_def select_def
                 split: if_splits)
   apply (rule_tac x="(None, transform b)" in bexI
       , (simp add: in_alternative)+)
  apply (rule_tac x="(Some (irq_oracle (Suc (irq_state (machine_state b)))),
                      transform b)" in bexI
       , (simp add: in_alternative)+)
  done


crunch "handle_reply"
  for valid_etcbs[wp]: "valid_etcbs"
  (wp: crunch_wps simp: crunch_simps)

lemma hr_ct_active_and_valid_etcbs:
  "\<lbrace>invs and ct_active and valid_etcbs\<rbrace> Syscall_A.handle_reply \<lbrace>\<lambda>rv. ct_active and valid_etcbs\<rbrace>"
  by (wp, simp+)

declare tcb_sched_action_transform[wp]

crunch reschedule_required
  for transform_inv[wp]: "\<lambda>s. transform s = cs"

lemma handle_hypervisor_fault_corres:
  "dcorres dc (\<lambda>_. True)
           (invs and (\<lambda>s. \<forall>x\<in>ran (kheap s). obj_valid_pdpt x) and ct_running and valid_etcbs)
           Syscall_D.handle_hypervisor_fault (do y \<leftarrow> local.handle_hypervisor_fault thread w; return () od)"
  by (cases w; simp add: Syscall_D.handle_hypervisor_fault_def returnOk_def2)

lemma handle_event_corres:
  "dcorres (dc \<oplus> dc) \<top>
     (invs and valid_pdpt_objs and (\<lambda>s. ev \<noteq> Interrupt \<longrightarrow> ct_running s) and valid_etcbs)
     (Syscall_D.handle_event ev) (Syscall_A.handle_event ev)"
  apply (cases ev, simp_all add: Syscall_D.handle_event_def)
       apply (rename_tac syscall)
       apply (case_tac syscall)
              apply (simp_all add:handle_syscall_def handle_send_def handle_call_def)
              apply (rule handle_invocation_corres[THEN corres_guard_imp] | simp)+
             apply (rule corres_guard_imp)
               apply (rule corres_split[OF handle_reply_corres handle_recv_corres])
                apply (wp handle_reply_cur_thread_idle_thread)
               apply (simp add:not_idle_thread_def)
               apply (wp handle_reply_cur_thread_idle_thread handle_reply_valid_etcbs)
               apply (rule hoare_post_imp[OF _ hr_ct_active_and_valid_etcbs])
               apply (clarsimp simp:ct_in_state_def)
              apply clarsimp+
             apply (frule (1) ct_running_not_idle_etc)
             apply ((clarsimp simp: handle_yield_def returnOk_def liftE_def not_idle_thread_def
                                    ct_in_state_def st_tcb_at_def obj_at_def)+)[1]
            apply (rule handle_invocation_corres[THEN corres_guard_imp] | simp)+
          apply (rule corres_guard_imp[OF handle_recv_corres])
           apply simp+
          apply (simp add: ct_running_not_idle_etc)
          apply (clarsimp simp: ct_in_state_def st_tcb_at_def obj_at_def generates_pending_def)
         apply (rule corres_guard_imp[OF handle_reply_corres])
          apply simp
         apply (simp add: ct_running_not_idle_etc)
        apply (clarsimp simp:not_idle_thread_def ct_in_state_def st_tcb_at_def)
        apply ((clarsimp simp: handle_yield_def returnOk_def liftE_def not_idle_thread_def
                               ct_in_state_def st_tcb_at_def obj_at_def)+)
        apply (rule dcorres_symb_exec_r)
          apply (rule dcorres_return, simp)
         apply (wp hoare_TrueI)+
       apply (rule corres_guard_imp)
         apply (rule handle_recv_corres, simp)
       apply clarsimp
       apply (frule (1) ct_running_not_idle_etc)
       apply (clarsimp simp: not_idle_thread_def ct_in_state_def st_tcb_at_def obj_at_def)
      apply (rule corres_symb_exec_r[OF handle_fault_corres])
        apply wp[1]
        apply clarsimp
        apply (frule (1) ct_running_not_idle_etc)
        apply (fastforce simp: st_tcb_at_def obj_at_def generates_pending_def gets_def get_def
                               valid_fault_def
                        split: Structures_A.thread_state.splits)+
     apply (rule corres_symb_exec_r[OF handle_fault_corres])
       apply wp[1]
       apply clarsimp
       apply (frule (1) ct_running_not_idle_etc)
       apply (fastforce simp: st_tcb_at_def obj_at_def generates_pending_def valid_fault_def
                       split: thread_state.splits)+
    apply (simp add:handle_pending_interrupts_def)
    apply (rule corres_guard_imp)
      apply (rule corres_split[OF get_active_irq_corres])
        apply (clarsimp simp:option.splits)
        apply (rule handle_interrupt_corres)
       apply (wp | simp)+
   apply (rule corres_symb_exec_r)
      apply (rule corres_symb_exec_catch_r)
         apply (rule handle_fault_corres)
        apply (simp only: conj_comms)
        apply (rule hoare_vcg_conj_liftE_E)
         apply (wp handle_vm_fault_wp | rule hoare_vcg_conj_liftE_E)+
      apply (simp add:no_fail_def)
     apply wp
     apply clarsimp
     apply (frule (1) ct_running_not_idle_etc)
     apply (clarsimp simp:invs_def valid_state_def st_tcb_at_def generates_pending_def obj_at_def)
    apply wpsimp+
  apply (rule corres_symb_exec_r[OF handle_hypervisor_fault_corres[simplified]]; wpsimp)
  done

end

end
