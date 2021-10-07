(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
    Defines the instances of pspace_storable objects.
*)

chapter "Storable Arch Object Instances"

theory ArchObjInsts_H
imports
  ArchTypes_H
  PSpaceStorable_H
  ObjectInstances_H
begin
qualify X64_H (in Arch)

instantiation X64_H.pde :: pre_storable
begin
interpretation Arch .

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


instantiation X64_H.pte :: pre_storable
begin
interpretation Arch .

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

instantiation X64_H.pdpte :: pre_storable
begin
interpretation Arch .

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

instantiation X64_H.pml4e :: pre_storable
begin
interpretation Arch .

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

instantiation X64_H.asidpool :: pre_storable
begin
interpretation Arch .

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

lemmas (in Arch) projectKO_opts_defs =
  projectKO_opt_pte projectKO_opt_pde
  projectKO_opt_pdpte projectKO_opt_pml4e
  projectKO_opt_asidpool
  ObjectInstances_H.projectKO_opts_defs

lemmas (in Arch) [simp] =
  injectKO_pte koType_pte
  injectKO_pde koType_pde
  injectKO_pdpte koType_pdpte
  injectKO_pml4e koType_pml4e
  injectKO_asidpool koType_asidpool


\<comment> \<open>--------------------------------------\<close>

#INCLUDE_SETTINGS keep_constructor = asidpool

#INCLUDE_HASKELL_PREPARSE SEL4/Object/Structures/X64.lhs
#INCLUDE_HASKELL_PREPARSE SEL4/Machine/Hardware/X64.lhs


instantiation X64_H.pde :: pspace_storable
begin
interpretation Arch .

#INCLUDE_HASKELL SEL4/Object/Instances/X64.lhs instanceproofs bodies_only ONLY PDE

instance
  apply (intro_classes)
  apply (clarsimp simp add: updateObject_default_def in_monad projectKO_opts_defs
                            projectKO_eq2
                     split: kernel_object.splits arch_kernel_object.splits)
  done

end

instantiation X64_H.pte :: pspace_storable
begin
interpretation Arch .

#INCLUDE_HASKELL SEL4/Object/Instances/X64.lhs instanceproofs bodies_only ONLY PTE

instance
  apply (intro_classes)
  apply (clarsimp simp add: updateObject_default_def in_monad projectKO_opts_defs
                            projectKO_eq2
                     split: kernel_object.splits arch_kernel_object.splits)
  done

end


instantiation X64_H.pdpte :: pspace_storable
begin
interpretation Arch .

#INCLUDE_HASKELL SEL4/Object/Instances/X64.lhs instanceproofs bodies_only ONLY PDPTE

instance
  apply (intro_classes)
  apply (clarsimp simp add: updateObject_default_def in_monad projectKO_opts_defs
                            projectKO_eq2
                     split: kernel_object.splits arch_kernel_object.splits)
  done

end

instantiation X64_H.pml4e :: pspace_storable
begin
interpretation Arch .

#INCLUDE_HASKELL SEL4/Object/Instances/X64.lhs instanceproofs bodies_only ONLY PML4E

instance
  apply (intro_classes)
  apply (clarsimp simp add: updateObject_default_def in_monad projectKO_opts_defs
                            projectKO_eq2
                     split: kernel_object.splits arch_kernel_object.splits)
  done

end

(* This is hard coded since using funArray in haskell for 2^32 bound is risky *)

instantiation X64_H.asidpool :: pspace_storable
begin
interpretation Arch .

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

lemmas load_update_defs =
  loadObject_pte updateObject_pte
  loadObject_pde updateObject_pde
  loadObject_pdpte updateObject_pdpte
  loadObject_pml4e updateObject_pml4e
  loadObject_asidpool updateObject_asidpool

declare load_update_defs[simp del]

end_qualify

declare (in Arch) load_update_defs[simp]

end
