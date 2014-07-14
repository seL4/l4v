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

header "Storable Arch Object Instances"

theory ArchObjInsts_H
imports
  ArchTypes_H
  PSpaceStorable_H
  ObjectInstances_H
begin

instantiation pde :: pre_storable
begin

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


instantiation asidpool :: pre_storable
begin

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
  projectKO_opt_pde projectKO_opt_pte projectKO_opt_asidpool
  ObjectInstances_H.projectKO_opts_defs


-- --------------------------------------

#INCLUDE_HASKELL_PREPARSE SEL4/Object/Structures/ARM.lhs
#INCLUDE_HASKELL_PREPARSE SEL4/Machine/Hardware/ARM.lhs


instantiation pde :: pspace_storable
begin

#INCLUDE_HASKELL SEL4/Object/Instances/ARM.lhs instanceproofs bodies_only ONLY PDE

instance
  apply (intro_classes)
  apply (clarsimp simp add: updateObject_default_def in_monad projectKO_opts_defs
                            projectKO_eq2
                     split: kernel_object.splits arch_kernel_object.splits)
  done

end

instantiation pte :: pspace_storable
begin

#INCLUDE_HASKELL SEL4/Object/Instances/ARM.lhs instanceproofs bodies_only ONLY PTE

instance
  apply (intro_classes)
  apply (clarsimp simp add: updateObject_default_def in_monad projectKO_opts_defs
                            projectKO_eq2
                     split: kernel_object.splits arch_kernel_object.splits)
  done

end

instantiation asidpool :: pspace_storable
begin

#INCLUDE_HASKELL SEL4/Object/Instances/ARM.lhs instanceproofs bodies_only ONLY ASIDPool

instance
  apply (intro_classes)
  apply (clarsimp simp add: updateObject_default_def in_monad projectKO_opts_defs
                            projectKO_eq2
                     split: kernel_object.splits arch_kernel_object.splits)
  done

end

end
