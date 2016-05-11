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
qualify ARM_H (in Arch)

instantiation ARM_H.pde :: pre_storable
begin
interpretation Arch .

definition
  projectKO_opt_pde:
  "projectKO_opt e \<equiv> case e of KOArch (KOPDE e) \<Rightarrow> Some e | _ \<Rightarrow> None"

definition
  injectKO_pde:
  "injectKO e \<equiv> KOArch (KOPDE e)"

definition
  koType_pde:
  "koType (t::pde itself) \<equiv> ArchT PDET"

instance
  by (intro_classes,
      auto simp: projectKO_opt_pde injectKO_pde koType_pde 
          split: kernel_object.splits arch_kernel_object.splits)

end

instantiation ARM_H.pte :: pre_storable
begin
interpretation Arch .

definition
  projectKO_opt_pte:
  "projectKO_opt e \<equiv> case e of (KOArch (KOPTE e)) \<Rightarrow> Some e | _ \<Rightarrow> None"

definition
  injectKO_pte:
  "injectKO e \<equiv> KOArch (KOPTE e)"

definition
  koType_pte:
  "koType (t::pte itself) \<equiv> ArchT PTET"

instance
  by (intro_classes,
      auto simp: projectKO_opt_pte injectKO_pte koType_pte
          split: kernel_object.splits arch_kernel_object.splits)

end


instantiation ARM_H.asidpool :: pre_storable
begin
interpretation Arch .

definition
  injectKO_asidpool:
  "injectKO e \<equiv> KOArch (KOASIDPool e)"

definition
  koType_asidpool:
  "koType (t::asidpool itself) \<equiv> ArchT ASIDPoolT"

definition
  projectKO_opt_asidpool:
  "projectKO_opt e \<equiv> case e of (KOArch (KOASIDPool e)) \<Rightarrow> Some e | _ \<Rightarrow> None"

instance
  by (intro_classes,
      auto simp: projectKO_opt_asidpool injectKO_asidpool koType_asidpool 
          split: kernel_object.splits arch_kernel_object.splits)

end

lemmas (in Arch) projectKO_opts_defs = 
  projectKO_opt_pde projectKO_opt_pte projectKO_opt_asidpool
  ObjectInstances_H.projectKO_opts_defs

lemmas (in Arch) [simp] =
  injectKO_pde koType_pde
  injectKO_pte koType_pte
  injectKO_asidpool koType_asidpool

-- --------------------------------------



instantiation ARM_H.pde :: pspace_storable
begin
interpretation Arch .

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

instantiation ARM_H.pte :: pspace_storable
begin
interpretation Arch .

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

(* This is hard coded since using funArray in haskell for 2^32 bound is risky *)

instantiation ARM_H.asidpool :: pspace_storable
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
  loadObject_pde updateObject_pde
  loadObject_pte updateObject_pte
  loadObject_asidpool updateObject_asidpool

declare load_update_defs[simp del]

end_qualify

declare (in Arch) load_update_defs[simp]

end
