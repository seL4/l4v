(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
   Types visible in the API.
*)

chapter "Arch-dependant Types visible in the API"

theory ArchTypes_H
imports
  State_H
  Hardware_H
  "Lib.Lib"
begin

#INCLUDE_HASKELL SEL4/API/Types/Universal.lhs all_bits

context Arch begin arch_global_naming (H)

#INCLUDE_HASKELL SEL4/API/Types/X64.lhs CONTEXT X64_H

end

text \<open>object\_type instance proofs\<close>

qualify X64_H (in Arch)
instantiation X64_H.object_type :: enum
begin
interpretation Arch .
definition
  enum_object_type: "enum_class.enum \<equiv>
    map APIObjectType (enum_class.enum :: apiobject_type list) @
     [PDPointerTableObject,
      PML4Object,
      HugePageObject,
      SmallPageObject,
      LargePageObject,
      PageTableObject,
      PageDirectoryObject
    ]"

definition
  "enum_class.enum_all (P :: object_type \<Rightarrow> bool) \<longleftrightarrow> Ball UNIV P"

definition
  "enum_class.enum_ex (P :: object_type \<Rightarrow> bool) \<longleftrightarrow> Bex UNIV P"

  instance
    apply intro_classes
     apply (safe, simp)
     apply (case_tac x)
    apply (simp_all add: enum_object_type)
    apply (auto intro: distinct_map_enum
                 simp: enum_all_object_type_def enum_ex_object_type_def)
    done
end


instantiation X64_H.object_type :: enum_alt
begin
interpretation Arch .
definition
  enum_alt_object_type: "enum_alt \<equiv>
    alt_from_ord (enum :: object_type list)"
instance ..
end

instantiation X64_H.object_type :: enumeration_both
begin
interpretation Arch .
instance by (intro_classes, simp add: enum_alt_object_type)
end

end
