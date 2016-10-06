(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file PSpaceStorable_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory PSpaceStorable_H
imports
  Structures_H
  KernelStateData_H
  "../../lib/DataMap"
begin

context begin interpretation Arch .
requalify_types
  arch_kernel_object_type

requalify_consts
  archTypeOf
end

lemma UserData_singleton [simp]:
  "(v = UserData) = True" "(UserData = v) = True" 
  by (cases v, simp)+

lemma UserDataDevice_singleton [simp]:
  "(v = UserDataDevice) = True" "(UserDataDevice = v) = True" 
  by (cases v, simp)+

datatype 
  kernel_object_type = 
    EndpointT
  | NotificationT
  | CTET
  | TCBT
  | UserDataT
  | UserDataDeviceT
  | KernelDataT
  | ArchT arch_kernel_object_type

primrec
  koTypeOf :: "kernel_object \<Rightarrow> kernel_object_type"
where
  "koTypeOf (KOEndpoint e) = EndpointT"
| "koTypeOf (KONotification e) = NotificationT"
| "koTypeOf (KOCTE e) = CTET"
| "koTypeOf (KOTCB e) = TCBT"
| "koTypeOf (KOUserData) = UserDataT"
| "koTypeOf (KOUserDataDevice) = UserDataDeviceT"
| "koTypeOf (KOKernelData) = KernelDataT"
| "koTypeOf (KOArch e) = ArchT (archTypeOf e)"

definition
  typeError :: "unit list \<Rightarrow> kernel_object \<Rightarrow> 'a kernel" where
  "typeError t1 t2 \<equiv> fail"

definition
  alignError :: "nat \<Rightarrow> 'a kernel" where
  "alignError n \<equiv> fail"

definition
  alignCheck :: "machine_word \<Rightarrow> nat \<Rightarrow> unit kernel" where
  "alignCheck x n \<equiv> unless ((x && mask n) = 0) $ alignError n"

definition
  magnitudeCheck :: "machine_word \<Rightarrow> machine_word option \<Rightarrow> nat \<Rightarrow> unit kernel"
where
 "magnitudeCheck x y n \<equiv> case y of None \<Rightarrow> return ()
               | Some z \<Rightarrow> when (z - x < 1 << n) fail"

class pre_storable =
  fixes injectKO :: "'a \<Rightarrow> kernel_object"
  fixes projectKO_opt :: "kernel_object \<Rightarrow> 'a option"
  fixes koType :: "'a itself \<Rightarrow> kernel_object_type"

  assumes project_inject: "(projectKO_opt ko = Some v) = (injectKO v = ko)"
  assumes project_koType: "(\<exists>v. projectKO_opt ko = Some (v::'a)) = (koTypeOf ko = koType TYPE('a))"
begin

definition
  projectKO :: "kernel_object \<Rightarrow> 'a kernel"
where
  "projectKO e \<equiv> 
  case projectKO_opt e of None \<Rightarrow> fail | Some k \<Rightarrow> return k"

definition
  objBits :: "'a \<Rightarrow> nat"
where
  "objBits v \<equiv> objBitsKO (injectKO v)"

definition
  loadObject_default :: "machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word option \<Rightarrow> kernel_object \<Rightarrow> 'a kernel"
where
  "loadObject_default ptr ptr' next obj \<equiv> do
     assert (ptr = ptr');
     val \<leftarrow> projectKO obj;
     alignCheck ptr (objBits val);
     magnitudeCheck ptr next (objBits val);
     return val
  od"

definition
  updateObject_default :: "'a \<Rightarrow> kernel_object \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word option \<Rightarrow> kernel_object kernel"
where
  "updateObject_default val oldObj ptr ptr' next \<equiv> do
     assert (ptr = ptr');
     (_ :: 'a) \<leftarrow> projectKO oldObj;
     alignCheck ptr (objBits val);
     magnitudeCheck ptr next (objBits val);
     return (injectKO val)
  od"

end

class pspace_storable = pre_storable +
  fixes makeObject :: 'a
  fixes loadObject :: "machine_word \<Rightarrow> machine_word \<Rightarrow> machine_word option \<Rightarrow> kernel_object \<Rightarrow> 'a kernel"
  fixes updateObject :: "'a \<Rightarrow> kernel_object \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> 
                              machine_word option \<Rightarrow> kernel_object kernel"
  assumes updateObject_type: 
  "(ko', s') \<in> fst (updateObject v ko p p' p'' s) \<Longrightarrow> koTypeOf ko' = koTypeOf ko"

end
