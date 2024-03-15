(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Decode_D
imports
  Asid_D
  CNode_D
  Interrupt_D
  PageTable_D
  Tcb_D
  Untyped_D
begin

definition
  get_cnode_intent :: "cdl_intent \<Rightarrow> cdl_cnode_intent option"
where
  "get_cnode_intent intent \<equiv>
    case intent of
        CNodeIntent x \<Rightarrow> Some x
      | _ \<Rightarrow> None"

definition
  get_tcb_intent :: "cdl_intent \<Rightarrow> cdl_tcb_intent option"
where
  "get_tcb_intent intent \<equiv>
    case intent of
        TcbIntent x \<Rightarrow> Some x
      | _ \<Rightarrow> None"

definition
  get_irq_control_intent :: "cdl_intent \<Rightarrow> cdl_irq_control_intent option"
where
  "get_irq_control_intent intent \<equiv>
    case intent of
        IrqControlIntent x \<Rightarrow> Some x
      | _ \<Rightarrow> None"

definition
  get_irq_handler_intent :: "cdl_intent \<Rightarrow> cdl_irq_handler_intent option"
where
  "get_irq_handler_intent intent \<equiv>
    case intent of
        IrqHandlerIntent x \<Rightarrow> Some x
      | _ \<Rightarrow> None"

definition
  get_asid_pool_intent :: "cdl_intent \<Rightarrow> cdl_asid_pool_intent option"
where
  "get_asid_pool_intent intent \<equiv>
    case intent of
        AsidPoolIntent x \<Rightarrow> Some x
      | _ \<Rightarrow> None"


definition
  get_asid_control_intent :: "cdl_intent \<Rightarrow> cdl_asid_control_intent option"
where
  "get_asid_control_intent intent \<equiv>
    case intent of
        AsidControlIntent x \<Rightarrow> Some x
      | _ \<Rightarrow> None"

definition
  get_page_intent :: "cdl_intent \<Rightarrow> cdl_page_intent option"
where
  "get_page_intent intent \<equiv>
    case intent of
        PageIntent x \<Rightarrow> Some x
      | _ \<Rightarrow> None"

definition
  get_page_table_intent :: "cdl_intent \<Rightarrow> cdl_page_table_intent option"
where
  "get_page_table_intent intent \<equiv>
    case intent of
        PageTableIntent x \<Rightarrow> Some x
      | _ \<Rightarrow> None"

definition
  get_page_directory_intent :: "cdl_intent \<Rightarrow> cdl_page_directory_intent option"
where
  "get_page_directory_intent intent \<equiv>
    case intent of
        PageDirectoryIntent x \<Rightarrow> Some x
      | _ \<Rightarrow> None"

definition
  get_untyped_intent :: "cdl_intent \<Rightarrow> cdl_untyped_intent option"
where
  "get_untyped_intent intent \<equiv>
    case intent of
        UntypedIntent x \<Rightarrow> Some x
      | _ \<Rightarrow> None"

definition
  get_domain_intent :: "cdl_intent \<Rightarrow> cdl_domain_intent option"
where
  "get_domain_intent intent \<equiv>
     case intent of
         DomainIntent x \<Rightarrow> Some x
       | _ \<Rightarrow> None"

(*
 * Decode and validate the given intent, turning it into an
 * invocation.
 *)
definition
  decode_invocation :: "cdl_cap \<Rightarrow> cdl_cap_ref \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) list \<Rightarrow> cdl_intent \<Rightarrow> cdl_invocation except_monad"
where
  "decode_invocation invoked_cap invoked_cap_ref caps intent \<equiv>
    case invoked_cap of
       \<comment> \<open>For endpoint-like caps, we always perform an operation,
          regardless of the user's actual intent.\<close>
         EndpointCap o_id badge rights \<Rightarrow>
           (if Write \<in> rights then
             returnOk $ InvokeEndpoint (SyncMessage badge (Grant \<in> rights) (GrantReply \<in> rights) o_id)
           else
             throw)
       | NotificationCap o_id badge rights \<Rightarrow>
           (if Write \<in> rights then
             returnOk $ InvokeNotification (Signal badge o_id)
           else
             throw)
       | ReplyCap o_id rights \<Rightarrow>
           returnOk $ InvokeReply (ReplyMessage o_id invoked_cap_ref (Grant \<in> rights))

       \<comment> \<open>
         For other operations, we only perform the user's intent
         if it matches up with the cap.

         Note that this does not currently match the current
         implementation: instead, the user's message will be
         decoded into a new (undefined) intent for what the
         cap happened to be. I propose modifying labels used to
         avoid overlaps between different items so that we can
         recognise when the user is invoking the wrong item.
       \<close>
       | CNodeCap _ _ _ _ \<Rightarrow>
           doE
             cnode_intent \<leftarrow> throw_opt undefined $ get_cnode_intent intent;
             liftME InvokeCNode $ decode_cnode_invocation invoked_cap invoked_cap_ref caps cnode_intent
           odE
       | TcbCap _ \<Rightarrow>
           doE
             tcb_intent \<leftarrow> throw_opt undefined $ get_tcb_intent intent;
             liftME InvokeTcb $ decode_tcb_invocation invoked_cap invoked_cap_ref caps tcb_intent
           odE
       | IrqControlCap \<Rightarrow>
           doE
             irq_control_intent \<leftarrow> throw_opt undefined $ get_irq_control_intent intent;
             liftME InvokeIrqControl $ decode_irq_control_invocation
                 invoked_cap invoked_cap_ref caps irq_control_intent
           odE
       | IrqHandlerCap _ \<Rightarrow>
           doE
             irq_handler_intent \<leftarrow> throw_opt undefined $ get_irq_handler_intent intent;
             liftME InvokeIrqHandler $ decode_irq_handler_invocation
                 invoked_cap invoked_cap_ref caps irq_handler_intent
           odE
       | SGISignalCap _ _ \<Rightarrow>
             returnOk $ InvokeSGISignal SGISignalGenerate
       | AsidPoolCap _ _\<Rightarrow>
           doE
             asid_pool_intent \<leftarrow> throw_opt undefined $ get_asid_pool_intent intent;
             liftME InvokeAsidPool $ decode_asid_pool_invocation
                 invoked_cap invoked_cap_ref caps asid_pool_intent
           odE
       | AsidControlCap \<Rightarrow>
           doE
             asid_control_intent \<leftarrow> throw_opt undefined $ get_asid_control_intent intent;
             liftME InvokeAsidControl $ decode_asid_control_invocation
                 invoked_cap invoked_cap_ref caps asid_control_intent
           odE
       | UntypedCap _ _ _ \<Rightarrow>
           doE
             untyped_intent \<leftarrow> throw_opt undefined $ get_untyped_intent intent;
             liftME InvokeUntyped $ decode_untyped_invocation
                 invoked_cap invoked_cap_ref caps untyped_intent
           odE
       | FrameCap _ _ _ _ _ _ \<Rightarrow>
           doE
             page_intent \<leftarrow> throw_opt undefined $ get_page_intent intent;
             liftME InvokePage $ decode_page_invocation
                 invoked_cap invoked_cap_ref caps page_intent
           odE
       | PageTableCap _ _ _ \<Rightarrow>
           doE
             page_table_intent \<leftarrow> throw_opt undefined $ get_page_table_intent intent;
             liftME InvokePageTable $ decode_page_table_invocation
                 invoked_cap invoked_cap_ref caps page_table_intent
           odE
       | PageDirectoryCap _ _ _ \<Rightarrow>
          doE
             page_directory_intent \<leftarrow> throw_opt undefined $ get_page_directory_intent intent;
             liftME InvokePageDirectory $ decode_page_directory_invocation
                 invoked_cap invoked_cap_ref caps page_directory_intent
           odE
       | DomainCap \<Rightarrow>
          doE
            domain_intent \<leftarrow> throw_opt undefined $ get_domain_intent intent;
            liftME InvokeDomain $ decode_domain_invocation caps domain_intent
          odE

       \<comment> \<open>Don't support operations on other types of caps.\<close>
       | _ \<Rightarrow> throw"

end
