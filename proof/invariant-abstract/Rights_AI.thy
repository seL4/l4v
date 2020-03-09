(*
 * Copyright 2018, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Rights_AI
 imports "ASpec.VMRights_A"
begin

lemma validate_vm_rights_idem[simp]:
  "validate_vm_rights (validate_vm_rights rights) = validate_vm_rights rights"
  by (clarsimp simp: validate_vm_rights_def vm_kernel_only_def vm_read_only_def vm_read_write_def)

lemma validate_vm_rights_inter_rw:
  "validate_vm_rights (vm_read_write \<inter> rights) = validate_vm_rights rights"
  apply (rule set_eqI)
  apply (clarsimp simp: validate_vm_rights_def vm_read_write_def)
  done

lemma valid_validate_vm_rights[simp]:
  "validate_vm_rights rs \<in> valid_vm_rights"
and validate_vm_rights_subseteq[simp]:
  "validate_vm_rights rs \<subseteq> rs"
and validate_vm_rights_simps[simp]:
  "validate_vm_rights vm_read_write = vm_read_write"
  "validate_vm_rights vm_read_only = vm_read_only"
  "validate_vm_rights vm_kernel_only = vm_kernel_only"
  by (simp_all add: validate_vm_rights_def valid_vm_rights_def
                    vm_read_write_def vm_read_only_def vm_kernel_only_def)

lemma validate_vm_rights_inter:
  "validate_vm_rights (validate_vm_rights fun \<inter> msk) =
   validate_vm_rights (fun \<inter> msk)"
  by (simp add: validate_vm_rights_def vm_read_write_def vm_read_only_def
                vm_kernel_only_def)

lemma validate_vm_rights_eq[simp]:
  "rs \<in> valid_vm_rights \<Longrightarrow> validate_vm_rights rs = rs"
  by (auto simp add: validate_vm_rights_def valid_vm_rights_def
                     vm_read_write_def vm_read_only_def vm_kernel_only_def)

lemma validate_vm_rights_def':
  "validate_vm_rights rs =
   (THE rs'. rs' \<subseteq> rs \<and> rs' : valid_vm_rights \<and>
     (\<forall>rs''. rs'' \<subseteq> rs \<longrightarrow> rs'' : valid_vm_rights \<longrightarrow> rs'' \<subseteq> rs'))"
  apply (rule the_equality[symmetric])
   apply  (auto simp add: validate_vm_rights_def valid_vm_rights_def
                       vm_read_write_def vm_read_only_def vm_kernel_only_def)[1]
  apply (simp add: validate_vm_rights_def valid_vm_rights_def
                 vm_read_write_def vm_read_only_def vm_kernel_only_def)
  apply safe
            apply simp+
       apply (drule_tac x="{AllowRead, AllowWrite}" in spec, simp+)
    apply (drule_tac x="{AllowRead, AllowWrite}" in spec, simp+)
   apply (drule_tac x="{AllowRead, AllowWrite}" in spec, simp+)
  apply (drule_tac x="{AllowRead}" in spec, simp)
  done

end