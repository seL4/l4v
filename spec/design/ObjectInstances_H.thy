(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file ObjectInstances_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
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
  "((obj,s') \<in> fst (projectKO ko s)) = (projectKO_opt ko = Some obj \<and> s' = s)"
  by (auto simp: projectKO_def fail_def return_def split: option.splits)


-- -----------------------------------

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
  projectKO_opt_user_data projectKO_opt_user_data_device

lemmas injectKO_defs = 
  injectKO_tcb injectKO_cte injectKO_ntfn injectKO_ep injectKO_user_data injectKO_user_data_device

lemmas koType_defs = 
  koType_tcb koType_cte koType_ntfn koType_ep koType_user_data koType_user_data_device

-- -----------------------------------

instantiation endpoint :: pspace_storable
begin

(* endpoint extra instance defs *)


definition
  makeObject_endpoint: "(makeObject :: endpoint)  \<equiv> IdleEP"

definition
  loadObject_endpoint[simp]:
 "(loadObject p q n obj) :: endpoint kernel \<equiv>
    loadObject_default p q n obj"

definition
  updateObject_endpoint[simp]:
 "updateObject (val :: endpoint) \<equiv>
    updateObject_default val"


instance
  apply (intro_classes)
  apply simp
  apply (case_tac ko, auto simp: projectKO_opt_ep updateObject_default_def 
                                 in_monad projectKO_eq2 
                           split: kernel_object.splits)
  done

end


instantiation notification :: pspace_storable
begin

(* notification extra instance defs *)


definition
  makeObject_notification: "(makeObject :: notification)  \<equiv> NTFN IdleNtfn Nothing"

definition
  loadObject_notification[simp]:
 "(loadObject p q n obj) :: notification kernel \<equiv>
    loadObject_default p q n obj"

definition
  updateObject_notification[simp]:
 "updateObject (val :: notification) \<equiv>
    updateObject_default val"


instance
  apply (intro_classes)
  apply (case_tac ko, auto simp: projectKO_opt_ntfn updateObject_default_def 
                                 in_monad projectKO_eq2 
                           split: kernel_object.splits)
  done

end


instantiation cte :: pspace_storable
begin

(* cte extra instance defs *)


definition
  makeObject_cte: "(makeObject :: cte)  \<equiv> CTE_ \<lparr>
        cteCap= NullCap,
        cteMDBNode= nullMDBNode \<rparr>"

definition
  loadObject_cte:
"    loadObject ptr ptr' next obj \<equiv>
        let
            toOffset = (\<lambda>  slot. slot `~shiftL~` objBits (undefined ::cte));
            offsetReturn = (\<lambda>  x tcb.
                if
                x = toOffset tcbVTableSlot then return $ tcbVTable tcb
                else if
                x = toOffset tcbCTableSlot then return $ tcbCTable tcb
                else if
                x = toOffset tcbReplySlot then return $ tcbReply tcb
                else if
                x = toOffset tcbCallerSlot then return $ tcbCaller tcb
                else if
                x = toOffset tcbIPCBufferSlot then return $ tcbIPCBufferFrame tcb
                else if
                True      then haskell_fail []
                else undefined)
        in
                                          (case obj of
          KOCTE cte \<Rightarrow>   (do
            unless (ptr = ptr') $ haskell_fail [];
            alignCheck ptr (objBits cte);
            magnitudeCheck ptr next (objBits cte);
            return cte
          od)
        | KOTCB tcb \<Rightarrow>   (do
            alignCheck ptr' (objBits tcb);
            magnitudeCheck ptr' next (objBits tcb);
            offsetReturn (ptr - ptr') tcb
        od)
        | _ \<Rightarrow>   typeError [] obj
        )"

definition
  updateObject_cte:
 "updateObject (cte :: cte) oldObj ptr ptr' next \<equiv>
        let
            toOffset = (\<lambda>  slot. slot `~shiftL~` objBits (undefined ::cte));
            offsetAdjust = (\<lambda>  x tcb.
                if
                x = toOffset tcbVTableSlot then return $ KOTCB (tcb \<lparr>tcbVTable := cte\<rparr>)
                else if
                x = toOffset tcbCTableSlot then return $ KOTCB (tcb \<lparr>tcbCTable := cte\<rparr>)
                else if
                x = toOffset tcbReplySlot then return $ KOTCB (tcb \<lparr> tcbReply := cte \<rparr>)
                else if
                x = toOffset tcbCallerSlot then return $ KOTCB (tcb \<lparr> tcbCaller := cte \<rparr>)
                else if
                x = toOffset tcbIPCBufferSlot then return $ KOTCB (tcb \<lparr> tcbIPCBufferFrame := cte \<rparr>)
                else if
                True      then haskell_fail []
                else undefined)
        in
                                                   (case oldObj of
          KOCTE v3 \<Rightarrow>   (do
            unless (ptr = ptr') $ haskell_fail [];
            alignCheck ptr (objBits cte);
            magnitudeCheck ptr next (objBits cte);
            return (KOCTE cte)
          od)
        | KOTCB tcb \<Rightarrow>   (do
            alignCheck ptr' (objBits tcb);
            magnitudeCheck ptr' next (objBits tcb);
            offsetAdjust (ptr - ptr') tcb
        od)
        | _ \<Rightarrow>   typeError [] oldObj
        )"


instance
  apply (intro_classes)
  apply (case_tac ko, auto simp: projectKO_opt_cte updateObject_cte 
                                 in_monad projectKO_eq2 typeError_def alignError_def
                           split: kernel_object.splits if_split_asm)
  done

end


instantiation user_data :: pspace_storable
begin

(* user_data extra instance defs *)


definition
  makeObject_user_data: "(makeObject :: user_data)  \<equiv> UserData"

definition
  loadObject_user_data[simp]:
 "(loadObject p q n obj) :: user_data kernel \<equiv>
    loadObject_default p q n obj"

definition
  updateObject_user_data[simp]:
 "updateObject (val :: user_data) \<equiv>
    updateObject_default val"


instance
  apply (intro_classes)
  apply (case_tac ko, auto simp: projectKO_opt_user_data updateObject_default_def 
                                 in_monad projectKO_eq2 
                           split: kernel_object.splits)
  done

end


instantiation user_data_device :: pspace_storable
begin

(* user_data_device extra instance defs *)


definition
  makeObject_user_data_device: "(makeObject :: user_data_device)  \<equiv> UserDataDevice"

definition
  loadObject_user_data_device[simp]:
 "(loadObject p q n obj) :: user_data_device kernel \<equiv>
    loadObject_default p q n obj"

definition
  updateObject_user_data_device[simp]:
 "updateObject (val :: user_data_device) \<equiv>
    updateObject_default val"


instance
  apply (intro_classes)
  apply (case_tac ko, auto simp: projectKO_opt_user_data_device updateObject_default_def 
                                 in_monad projectKO_eq2 
                           split: kernel_object.splits)
  done

end


instantiation tcb :: pspace_storable
begin

(* tcb extra instance defs *)


definition
  makeObject_tcb: "(makeObject :: tcb)  \<equiv> Thread_ \<lparr>
        tcbCTable= makeObject,
        tcbVTable= makeObject,
        tcbReply= makeObject,
        tcbCaller= makeObject,
        tcbIPCBufferFrame= makeObject,
        tcbDomain= minBound,
        tcbState= Inactive,
        tcbMCP= minBound,
        tcbPriority= minBound,
        tcbQueued= False,
        tcbFault= Nothing,
        tcbTimeSlice= timeSlice,
        tcbFaultHandler= CPtr 0,
        tcbIPCBuffer= VPtr 0,
        tcbBoundNotification= Nothing,
        tcbArch= newArchTCB \<rparr>"

definition
  loadObject_tcb[simp]:
 "(loadObject p q n obj) :: tcb kernel \<equiv>
    loadObject_default p q n obj"

definition
  updateObject_tcb[simp]:
 "updateObject (val :: tcb) \<equiv>
    updateObject_default val"


instance
  apply (intro_classes)
  apply (case_tac ko, auto simp: projectKO_opt_tcb updateObject_default_def 
                                 in_monad projectKO_eq2 
                           split: kernel_object.splits)
  done

end


end
