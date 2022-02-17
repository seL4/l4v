(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2022, Proofcraft Pty Ltd
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

qualify AARCH64_H (in Arch)

instantiation AARCH64_H.pte :: pre_storable
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

instantiation AARCH64_H.vcpu :: pre_storable
begin
interpretation Arch .

definition
  projectKO_opt_vcpu:
  "projectKO_opt e \<equiv> case e of KOArch (KOVCPU e) \<Rightarrow> Some e | _ \<Rightarrow> None"

definition
  injectKO_vcpu [simp]:
  "injectKO e \<equiv> KOArch (KOVCPU e)"

definition
  koType_vcpu [simp]:
  "koType (t::vcpu itself) \<equiv> ArchT VCPUT"

instance
  by (intro_classes,
      auto simp: projectKO_opt_vcpu injectKO_vcpu koType_vcpu
          split: kernel_object.splits arch_kernel_object.splits)

end

instantiation AARCH64_H.asidpool :: pre_storable
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
  projectKO_opt_pte
  projectKO_opt_vcpu
  projectKO_opt_asidpool
  ObjectInstances_H.projectKO_opts_defs

lemmas (in Arch) [simp] =
  injectKO_pte koType_pte
  injectKO_asidpool koType_asidpool


\<comment> \<open>--------------------------------------\<close>

#INCLUDE_SETTINGS keep_constructor = asidpool

#INCLUDE_HASKELL_PREPARSE SEL4/Object/Structures/AARCH64.hs
#INCLUDE_HASKELL_PREPARSE SEL4/Machine/Hardware/AARCH64.hs
#INCLUDE_HASKELL_PREPARSE SEL4/Object/VCPU/AARCH64.hs

instantiation AARCH64_H.pte :: pspace_storable
begin
interpretation Arch .

#INCLUDE_HASKELL SEL4/Object/Instances/AARCH64.hs instanceproofs bodies_only ONLY PTE

instance
  apply (intro_classes)
  apply (clarsimp simp add: updateObject_default_def in_monad projectKO_opts_defs
                            projectKO_eq2
                     split: kernel_object.splits arch_kernel_object.splits)
  done

end

instantiation AARCH64_H.vcpu :: pspace_storable
begin
interpretation Arch .

#INCLUDE_HASKELL_PREPARSE SEL4/Object/Structures/AARCH64.hs
#INCLUDE_HASKELL_PREPARSE SEL4/Object/VCPU/AARCH64.hs
#INCLUDE_HASKELL SEL4/Object/Instances/AARCH64.hs instanceproofs bodies_only ONLY VCPU

instance
  apply (intro_classes)
  apply (clarsimp simp add: updateObject_default_def in_monad projectKO_opts_defs
                            projectKO_eq2
                     split: kernel_object.splits arch_kernel_object.splits)
  done

end

(* This is hard coded since using funArray in haskell for 2^32 bound is risky *)

instantiation AARCH64_H.asidpool :: pspace_storable
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
  loadObject_asidpool updateObject_asidpool

declare load_update_defs[simp del]

end_qualify

declare (in Arch) load_update_defs[simp]

end
