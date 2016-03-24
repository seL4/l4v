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
  keywords "instantiation'" :: thy_decl
begin

ML
  \<open>val _ =
  Outer_Syntax.command @{command_keyword instantiation2'} "instantiate and prove type arity"
   (Parse.opt_target -- Parse.multi_arity --| Parse.begin
     >> (fn (opt_target, arities) => 
          Toplevel.local_theory NONE opt_target (fn lthy =>
            let
              val thy = Proof_Context.theory_of lthy;
              val lthy' = Class.instantiation_cmd arities thy;
            in
              lthy'
            end)));
\<close>

ML \<open>
val _ =
  Outer_Syntax.command @{command_keyword instantiation'} "instantiate and prove type arity"
   (Parse.opt_target -- Parse.multi_arity --| Parse.begin
     >> (fn (opt_target, arities) => 
            Toplevel.generic_theory (
              (fn (Context.Theory thy) =>
                    let
                      val lthy = Class.instantiation_cmd arities thy;
                      val gthy = Context.Proof lthy;
                      val _ =
                        (case Local_Theory.pretty lthy of
                          [] => ()
                        | prts => Output.state (Pretty.string_of (Pretty.chunks prts)));
                    in gthy end
              | (Context.Proof lthy) =>
                     let
                       val thy = Proof_Context.theory_of lthy;
                       val lthy' = Class.instantiation_cmd arities thy;
                       val gthy = Context.Proof lthy';
                       val _ =
                        (case Local_Theory.pretty lthy' of
                          [] => ()
                        | prts => Output.state (Pretty.string_of (Pretty.chunks prts)));
                      in gthy end))));
\<close>

ML \<open>Local_Theory.init\<close>
context ARM begin

datatype apiobject_type = Foo

(* apiobject_type instance proofs *)
(*<*)
instantiation' ARM.apiobject_type :: enum begin
interpretation ARM .

definition
  enum_apiobject_type: "enum_class.enum \<equiv> 
    [ 
      Foo
    ]"


definition
  "enum_class.enum_all (P :: ARM.apiobject_type \<Rightarrow> bool) \<longleftrightarrow> Ball UNIV P"

definition
  "enum_class.enum_ex (P :: ARM.apiobject_type \<Rightarrow> bool) \<longleftrightarrow> Bex UNIV P"

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


end

qualify ARM

datatype object_type =
    APIObjectType apiobject_type
  | SmallPageObject
  | LargePageObject
  | SectionObject
  | SuperSectionObject
  | PageTableObject
  | PageDirectoryObject

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
    SmallPageObject \<Rightarrow>    pageBitsForSize ARMSmallPage
  | LargePageObject \<Rightarrow>    pageBitsForSize ARMLargePage
  | SectionObject \<Rightarrow>    pageBitsForSize ARMSection
  | SuperSectionObject \<Rightarrow>    pageBitsForSize ARMSuperSection
  | PageTableObject \<Rightarrow>    ptBits
  | PageDirectoryObject \<Rightarrow>    pdBits
  | (APIObjectType apiObjectType) \<Rightarrow>    apiGetObjectSize apiObjectType magnitude
  )"


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
