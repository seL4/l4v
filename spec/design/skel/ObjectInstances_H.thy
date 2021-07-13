(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
    Defines the instances of pspace_storable objects.
*)

chapter "Storable Object Instances"

theory ObjectInstances_H
imports
  Structures_H
  "./$L4V_ARCH/State_H"
  PSpaceStorable_H
  Config_H
begin

context begin interpretation Arch .
requalify_consts
  VPtr
  newContext
end

lemma projectKO_eq2:
  "(projectKO ko s = Some obj) = (projectKO_opt ko = Some obj)"
  by (auto simp: projectKO_def ofail_def oreturn_def oassert_opt_def split: option.splits)


\<comment> \<open>-----------------------------------\<close>

instantiation endpoint :: pre_storable
begin

definition
  projectKO_opt_ep:
  "projectKO_opt e \<equiv> case e of KOEndpoint e \<Rightarrow> Some e | _ \<Rightarrow> None"

definition
  injectKO_ep [simp]:
  "injectKO e \<equiv> KOEndpoint e"

definition
  koType_ep [simp]:
  "koType (t::endpoint itself) \<equiv> EndpointT"

instance
  by (intro_classes,
      auto simp: projectKO_opt_ep split: kernel_object.splits)

end

instantiation reply :: pre_storable
begin

definition
  projectKO_opt_reply:
  "projectKO_opt e \<equiv> case e of KOReply e \<Rightarrow> Some e | _ \<Rightarrow> None"

definition
  injectKO_reply [simp]:
  "injectKO e \<equiv> KOReply e"

definition
  koType_reply [simp]:
  "koType (t::reply itself) \<equiv> ReplyT"

instance
  by (intro_classes,
      auto simp: projectKO_opt_reply split: kernel_object.splits)

end

instantiation sched_context :: pre_storable
begin

definition
  projectKO_opt_sc:
  "projectKO_opt e \<equiv> case e of KOSchedContext e \<Rightarrow> Some e | _ \<Rightarrow> None"

definition
  injectKO_sc [simp]:
  "injectKO e \<equiv> KOSchedContext e"

definition
  koType_sc [simp]:
  "koType (t::sched_context itself) \<equiv> SchedContextT"

instance
  by (intro_classes,
      auto simp: projectKO_opt_sc split: kernel_object.splits)

end

instantiation notification :: pre_storable
begin

definition
  projectKO_opt_ntfn:
  "projectKO_opt e \<equiv> case e of KONotification e \<Rightarrow> Some e | _ \<Rightarrow> None"

definition
  injectKO_ntfn [simp]:
  "injectKO e \<equiv> KONotification e"

definition
  koType_ntfn [simp]:
  "koType (t::notification itself) \<equiv> NotificationT"

instance
  by (intro_classes,
      auto simp: projectKO_opt_ntfn split: kernel_object.splits)

end


instantiation cte :: pre_storable
begin

definition
  projectKO_opt_cte:
  "projectKO_opt e \<equiv> case e of KOCTE e \<Rightarrow> Some e | _ \<Rightarrow> None"

definition
  injectKO_cte [simp]:
  "injectKO c \<equiv> KOCTE c"

definition
  koType_cte [simp]:
  "koType (t::cte itself) \<equiv> CTET"

instance
  by (intro_classes,
      auto simp: projectKO_opt_cte split: kernel_object.splits)

end

instantiation user_data_device :: pre_storable
begin

definition
  projectKO_opt_user_data_device:
  "projectKO_opt e \<equiv> case e of KOUserDataDevice \<Rightarrow> Some UserDataDevice | _ \<Rightarrow> None"

definition
  injectKO_user_data_device [simp]:
  "injectKO (t :: user_data_device) \<equiv> KOUserDataDevice"

definition
  koType_user_data_device [simp]:
  "koType (t::user_data_device itself) \<equiv> UserDataDeviceT"

instance
  by (intro_classes,
      auto simp: projectKO_opt_user_data_device split: kernel_object.splits)
end

instantiation user_data :: pre_storable
begin

definition
  projectKO_opt_user_data:
  "projectKO_opt e \<equiv> case e of KOUserData \<Rightarrow> Some UserData | _ \<Rightarrow> None"

definition
  injectKO_user_data [simp]:
  "injectKO (t :: user_data) \<equiv> KOUserData"

definition
  koType_user_data [simp]:
  "koType (t::user_data itself) \<equiv> UserDataT"

instance
  by (intro_classes,
      auto simp: projectKO_opt_user_data split: kernel_object.splits)

end


instantiation tcb :: pre_storable
begin

definition
  projectKO_opt_tcb:
  "projectKO_opt e \<equiv> case e of KOTCB e \<Rightarrow> Some e | _ \<Rightarrow> None"

definition
  injectKO_tcb [simp]:
  "injectKO t \<equiv> KOTCB t"

definition
  koType_tcb [simp]:
  "koType (t::tcb itself) \<equiv> TCBT"

instance
  by (intro_classes,
      auto simp: projectKO_opt_tcb split: kernel_object.splits)

end


lemmas projectKO_opts_defs =
  projectKO_opt_tcb projectKO_opt_cte projectKO_opt_ntfn projectKO_opt_ep
  projectKO_opt_reply projectKO_opt_sc
  projectKO_opt_user_data projectKO_opt_user_data_device

lemmas injectKO_defs =
  injectKO_tcb injectKO_cte injectKO_ntfn injectKO_ep injectKO_user_data injectKO_user_data_device

lemmas koType_defs =
  koType_tcb koType_cte koType_ntfn koType_ep koType_user_data koType_user_data_device

\<comment> \<open>-----------------------------------\<close>

instantiation endpoint :: pspace_storable
begin

#INCLUDE_HASKELL SEL4/Object/Instances.lhs instanceproofs bodies_only ONLY Endpoint

instance
  apply (intro_classes)
  apply simp
  apply (case_tac ko, auto simp: projectKO_opt_ep updateObject_default_def
                                 in_monad projectKO_eq2
                           split: kernel_object.splits)
  done

end

instantiation reply :: pspace_storable
begin

#INCLUDE_HASKELL SEL4/Object/Instances.lhs instanceproofs bodies_only ONLY Reply

instance
  apply (intro_classes)
  apply simp
  apply (case_tac ko, auto simp: projectKO_opt_reply updateObject_default_def
                                 in_monad projectKO_eq2
                           split: kernel_object.splits)
  done

end

instantiation sched_context :: pspace_storable
begin

(* sched_context extra instance defs *)

definition
  "minRefillLength \<equiv> refillAbsoluteMax' minSchedContextBits"

definition
  makeObject_sc:
  "(makeObject :: sched_context) \<equiv>
     SchedContext 0 0 0 Nothing Nothing Nothing 0 False Nothing 0 0 0 (replicate minRefillLength emptyRefill)"

definition
  loadObject_sc[simp]:
  "(loadObject p q n obj) :: sched_context kernel_r \<equiv>
     loadObject_default p q n obj"

definition
  updateObject_sc[simp]:
  "updateObject (val :: sched_context) \<equiv>
     updateObject_default val"


instance
  apply (intro_classes)
  apply simp
  apply (case_tac ko, auto simp: projectKO_opt_sc updateObject_default_def
                                 in_monad projectKO_eq2
                           split: kernel_object.splits)
  done

end

instantiation notification :: pspace_storable
begin

#INCLUDE_HASKELL SEL4/Object/Instances.lhs instanceproofs bodies_only ONLY Notification

instance
  apply (intro_classes)
  apply (case_tac ko, auto simp: projectKO_opt_ntfn updateObject_default_def
                                 in_monad projectKO_eq2
                           split: kernel_object.splits)
  done

end


instantiation cte :: pspace_storable
begin

#INCLUDE_HASKELL SEL4/Object/Instances.lhs instanceproofs bodies_only ONLY CTE

instance
  apply (intro_classes)
  apply (case_tac ko, auto simp: projectKO_opt_cte updateObject_cte objBitsKO_def
                                 in_monad projectKO_eq2 typeError_def alignError_def
                           split: kernel_object.splits if_split_asm)
  done

end


instantiation user_data :: pspace_storable
begin

#INCLUDE_HASKELL SEL4/Object/Instances.lhs instanceproofs bodies_only ONLY UserData

instance
  apply (intro_classes)
  apply (case_tac ko, auto simp: projectKO_opt_user_data updateObject_default_def
                                 in_monad projectKO_eq2
                           split: kernel_object.splits)
  done

end


instantiation user_data_device :: pspace_storable
begin

#INCLUDE_HASKELL SEL4/Object/Instances.lhs instanceproofs bodies_only ONLY UserDataDevice

instance
  apply (intro_classes)
  apply (case_tac ko, auto simp: projectKO_opt_user_data_device updateObject_default_def
                                 in_monad projectKO_eq2
                           split: kernel_object.splits)
  done

end


instantiation tcb :: pspace_storable
begin

#INCLUDE_HASKELL SEL4/Object/Instances.lhs instanceproofs bodies_only ONLY TCB

instance
  apply (intro_classes)
  apply (case_tac ko, auto simp: projectKO_opt_tcb updateObject_default_def
                                 in_monad projectKO_eq2
                           split: kernel_object.splits)
  done

end


end
