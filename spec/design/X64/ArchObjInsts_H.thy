(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file ArchObjInsts_H.thy *)
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

chapter "Storable Arch Object Instances"

theory ArchObjInsts_H
imports
  ArchTypes_H
  "../PSpaceStorable_H"
  "../ObjectInstances_H"
begin
qualify X64 

instantiation pde :: pre_storable
begin
interpretation X64 .

definition
  projectKO_opt_pde:
  "projectKO_opt e \<equiv> case e of KOArch (KOPDE e) \<Rightarrow> Some e | _ \<Rightarrow> None"

definition
  injectKO_pde [simp]:
  "injectKO e \<equiv> KOArch (KOPDE e)"

definition
  koType_pde [simp]:
  "koType (t::pde itself) \<equiv> ArchT PDET"

instance
  by (intro_classes,
      auto simp: projectKO_opt_pde split: kernel_object.splits arch_kernel_object.splits)

end


instantiation pte :: pre_storable
begin
interpretation X64 .

definition
  projectKO_opt_pte:
  "projectKO_opt e \<equiv> case e of (KOArch (KOPTE e)) \<Rightarrow> Some e | _ \<Rightarrow> None"

definition
  injectKO_pte [simp]:
  "injectKO e \<equiv> KOArch (KOPTE e)"

definition
  koType_pte [simp]:
  "koType (t::pte itself) \<equiv> ArchT PTET"

instance
  by (intro_classes,
      auto simp: projectKO_opt_pte split: kernel_object.splits arch_kernel_object.splits)

end

instantiation pdpte :: pre_storable
begin
interpretation X64 .

definition
  projectKO_opt_pdpte:
  "projectKO_opt e \<equiv> case e of (KOArch (KOPDPTE e)) \<Rightarrow> Some e | _ \<Rightarrow> None"

definition
  injectKO_pdpte [simp]:
  "injectKO e \<equiv> KOArch (KOPDPTE e)"

definition
  koType_pdpte [simp]:
  "koType (t::pdpte itself) \<equiv> ArchT PDPTET"

instance
  by (intro_classes,
      auto simp: projectKO_opt_pdpte split: kernel_object.splits arch_kernel_object.splits)

end

instantiation pml4e :: pre_storable
begin
interpretation X64 .

definition
  projectKO_opt_pml4e:
  "projectKO_opt e \<equiv> case e of (KOArch (KOPML4E e)) \<Rightarrow> Some e | _ \<Rightarrow> None"

definition
  injectKO_pml4e [simp]:
  "injectKO e \<equiv> KOArch (KOPML4E e)"

definition
  koType_pml4e [simp]:
  "koType (t::pml4e itself) \<equiv> ArchT PML4ET"

instance
  by (intro_classes,
      auto simp: projectKO_opt_pml4e split: kernel_object.splits arch_kernel_object.splits)

end

instantiation iopte :: pre_storable
begin
interpretation X64 .

definition
  projectKO_opt_iopte:
  "projectKO_opt e \<equiv> case e of (KOArch (KOIOPTE e)) \<Rightarrow> Some e | _ \<Rightarrow> None"

definition
  injectKO_iopte [simp]:
  "injectKO e \<equiv> KOArch (KOIOPTE e)"

definition
  koType_iopte [simp]:
  "koType (t::iopte itself) \<equiv> ArchT IOPTET"

instance
  by (intro_classes,
      auto simp: projectKO_opt_iopte split: kernel_object.splits arch_kernel_object.splits)

end


instantiation asidpool :: pre_storable
begin
interpretation X64 .

definition
  injectKO_asidpool [simp]:
  "injectKO e \<equiv> KOArch (KOASIDPool e)"

definition
  koType_asidpool [simp]:
  "koType (t::asidpool itself) \<equiv> ArchT ASIDPoolT"

definition
  projectKO_opt_asidpool:
  "projectKO_opt e \<equiv> case e of (KOArch (KOASIDPool e)) \<Rightarrow> Some e | _ \<Rightarrow> None"

instance
  by (intro_classes,
      auto simp: projectKO_opt_asidpool split: kernel_object.splits arch_kernel_object.splits)

end

lemmas projectKO_opts_defs = 
  projectKO_opt_pde projectKO_opt_pte 
  projectKO_opt_pdpte projectKO_opt_pml4e
  projectKO_opt_iopte
  projectKO_opt_asidpool
  ObjectInstances_H.projectKO_opts_defs


-- --------------------------------------



instantiation pde :: pspace_storable
begin
interpretation X64 .

(* pde extra instance defs *)


definition
  makeObject_pde: "(makeObject :: pde)  \<equiv> InvalidPDE"

definition
  loadObject_pde[simp]:
 "(loadObject p q n obj) :: pde kernel \<equiv>
    loadObject_default p q n obj"

definition
  updateObject_pde[simp]:
 "updateObject (val :: pde) \<equiv>
    updateObject_default val"


instance
  apply (intro_classes)
  apply (clarsimp simp add: updateObject_default_def in_monad projectKO_opts_defs
                            projectKO_eq2
                     split: kernel_object.splits arch_kernel_object.splits)
  done

end

instantiation pte :: pspace_storable
begin
interpretation X64 .

(* pte extra instance defs *)


definition
  makeObject_pte: "(makeObject :: pte)  \<equiv> InvalidPTE"

definition
  loadObject_pte[simp]:
 "(loadObject p q n obj) :: pte kernel \<equiv>
    loadObject_default p q n obj"

definition
  updateObject_pte[simp]:
 "updateObject (val :: pte) \<equiv>
    updateObject_default val"


instance
  apply (intro_classes)
  apply (clarsimp simp add: updateObject_default_def in_monad projectKO_opts_defs
                            projectKO_eq2
                     split: kernel_object.splits arch_kernel_object.splits)
  done

end


instantiation pdpte :: pspace_storable
begin
interpretation X64 .

(* pdpte extra instance defs *)


definition
  makeObject_pdpte: "(makeObject :: pdpte)  \<equiv> InvalidPDPTE"

definition
  loadObject_pdpte[simp]:
 "(loadObject p q n obj) :: pdpte kernel \<equiv>
    loadObject_default p q n obj"

definition
  updateObject_pdpte[simp]:
 "updateObject (val :: pdpte) \<equiv>
    updateObject_default val"


instance
  apply (intro_classes)
  apply (clarsimp simp add: updateObject_default_def in_monad projectKO_opts_defs
                            projectKO_eq2
                     split: kernel_object.splits arch_kernel_object.splits)
  done

end

instantiation pml4e :: pspace_storable
begin
interpretation X64 .

(* pml4e extra instance defs *)


definition
  makeObject_pml4e: "(makeObject :: pml4e)  \<equiv> InvalidPML4E"

definition
  loadObject_pml4e[simp]:
 "(loadObject p q n obj) :: pml4e kernel \<equiv>
    loadObject_default p q n obj"

definition
  updateObject_pml4e[simp]:
 "updateObject (val :: pml4e) \<equiv>
    updateObject_default val"


instance
  apply (intro_classes)
  apply (clarsimp simp add: updateObject_default_def in_monad projectKO_opts_defs
                            projectKO_eq2
                     split: kernel_object.splits arch_kernel_object.splits)
  done

end

instantiation iopte :: pspace_storable
begin
interpretation X64 .

(* iopte extra instance defs *)


definition
  makeObject_iopte: "(makeObject :: iopte)  \<equiv> InvalidIOPTE"

definition
  loadObject_iopte[simp]:
 "(loadObject p q n obj) :: iopte kernel \<equiv>
    loadObject_default p q n obj"

definition
  updateObject_iopte[simp]:
 "updateObject (val :: iopte) \<equiv>
    updateObject_default val"


instance
  apply (intro_classes)
  apply (clarsimp simp add: updateObject_default_def in_monad projectKO_opts_defs
                            projectKO_eq2
                     split: kernel_object.splits arch_kernel_object.splits)
  done

end

(* This is hard coded since using funArray in haskell for 2^32 bound is risky *)

instantiation asidpool :: pspace_storable
begin
interpretation X64 .

definition
  makeObject_asidpool: "(makeObject :: asidpool)  \<equiv> ASIDPool $
        funArray (const Nothing)"

definition
  loadObject_asidpool[simp]:
 "(loadObject p q n obj) :: asidpool kernel \<equiv>
    loadObject_default p q n obj"

definition
  updateObject_asidpool[simp]:
 "updateObject (val :: asidpool) \<equiv>
    updateObject_default val"

instance
  apply (intro_classes)
  apply (clarsimp simp add: updateObject_default_def in_monad projectKO_opts_defs
                            projectKO_eq2
                     split: kernel_object.splits arch_kernel_object.splits)
  done

end

end
