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
   Types visible in the API. 
*)

chapter "Arch-dependant Types visible in the API"

theory ArchTypes_H
imports
  State_H
  Hardware_H
  "../../../lib/Lib"
begin
context ARM begin

#INCLUDE_HASKELL SEL4/API/Types/Universal.lhs NOT instanceproofs

end

qualify ARM

#INCLUDE_HASKELL SEL4/API/Types/ARM.lhs 

end_qualify

text {* object\_type instance proofs *}

instantiation object_type :: enum
begin
interpretation ARM .

definition
  enum_object_type: "enum_class.enum \<equiv> 
    map APIObjectType (enum_class.enum :: apiobject_type list) @ 
     [SmallPageObject,
      LargePageObject,
      SectionObject,
      SuperSectionObject,
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


instantiation object_type :: enum_alt
begin
definition
  enum_alt_object_type: "enum_alt \<equiv>
    alt_from_ord (enum :: object_type list)"
instance ..
end

instantiation object_type :: enumeration_both
begin
instance by (intro_classes, simp add: enum_alt_object_type)
end

end_qualify
end
