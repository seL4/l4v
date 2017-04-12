(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file ArchTypes_H.thy *)
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

datatype apiobject_type =
    Untyped
  | TCBObject
  | EndpointObject
  | NotificationObject
  | CapTableObject
(* apiobject_type instance proofs *)
(*<*)
instantiation apiobject_type :: enum begin
definition
  enum_apiobject_type: "enum_class.enum \<equiv> 
    [ 
      Untyped,
      TCBObject,
      EndpointObject,
      NotificationObject,
      CapTableObject
    ]"


definition
  "enum_class.enum_all (P :: apiobject_type \<Rightarrow> bool) \<longleftrightarrow> Ball UNIV P"

definition
  "enum_class.enum_ex (P :: apiobject_type \<Rightarrow> bool) \<longleftrightarrow> Bex UNIV P"

  instance
  apply intro_classes
   apply (safe, simp)
   apply (case_tac x)
  apply (simp_all add: enum_apiobject_type enum_all_apiobject_type_def enum_ex_apiobject_type_def)
  by fast+
end

instantiation apiobject_type :: enum_alt
begin
definition
  enum_alt_apiobject_type: "enum_alt \<equiv> 
    alt_from_ord (enum :: apiobject_type list)"
instance ..
end

instantiation apiobject_type :: enumeration_both
begin
instance by (intro_classes, simp add: enum_alt_apiobject_type)
end

(*>*)


definition
tcbBlockSizeBits :: "nat"
where
"tcbBlockSizeBits \<equiv> 9"

definition
epSizeBits :: "nat"
where
"epSizeBits \<equiv> 5"

definition
ntfnSizeBits :: "nat"
where
"ntfnSizeBits \<equiv> 5"

definition
cteSizeBits :: "nat"
where
"cteSizeBits \<equiv> 5"

definition
apiGetObjectSize :: "apiobject_type \<Rightarrow> nat \<Rightarrow> nat"
where
"apiGetObjectSize x0 magnitude\<equiv> (case x0 of
    Untyped \<Rightarrow>    magnitude
  | TCBObject \<Rightarrow>    tcbBlockSizeBits
  | EndpointObject \<Rightarrow>    epSizeBits
  | NotificationObject \<Rightarrow>    ntfnSizeBits
  | CapTableObject \<Rightarrow>    cteSizeBits + magnitude
  )"


context Arch begin global_naming X64_H

datatype object_type =
    APIObjectType apiobject_type
  | SmallPageObject
  | LargePageObject
  | HugePageObject
  | PageTableObject
  | PageDirectoryObject
  | PDPointerTableObject
  | PML4Object

definition
"fromAPIType \<equiv> APIObjectType"

definition
"toAPIType x0\<equiv> (case x0 of
    (APIObjectType a) \<Rightarrow>    Just a
  | _ \<Rightarrow>    Nothing
  )"

definition
"pageType \<equiv> SmallPageObject"

definition
getObjectSize :: "object_type \<Rightarrow> nat \<Rightarrow> nat"
where
"getObjectSize x0 magnitude\<equiv> (case x0 of
    SmallPageObject \<Rightarrow>    pageBitsForSize X64SmallPage
  | LargePageObject \<Rightarrow>    pageBitsForSize X64LargePage
  | HugePageObject \<Rightarrow>    pageBitsForSize X64HugePage
  | PageTableObject \<Rightarrow>    ptBits
  | PageDirectoryObject \<Rightarrow>    ptBits
  | PDPointerTableObject \<Rightarrow>    ptBits
  | PML4Object \<Rightarrow>    ptBits
  | (APIObjectType apiObjectType) \<Rightarrow>    apiGetObjectSize apiObjectType magnitude
  )"

definition
isFrameType :: "object_type \<Rightarrow> bool"
where
"isFrameType x0\<equiv> (case x0 of
    SmallPageObject \<Rightarrow>    True
  | LargePageObject \<Rightarrow>    True
  | HugePageObject \<Rightarrow>    True
  | _ \<Rightarrow>    False
  )"


end

text {* object\_type instance proofs *}

qualify X64_H (in Arch)
instantiation X64_H.object_type :: enum
begin
interpretation Arch .
definition
  enum_object_type: "enum_class.enum \<equiv>
    map APIObjectType (enum_class.enum :: apiobject_type list) @
     [SmallPageObject,
      LargePageObject,
      HugePageObject,
      PageTableObject,
      PageDirectoryObject,
      PDPointerTableObject,
      PML4Object
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

context begin interpretation Arch .
requalify_types object_type
end

end
