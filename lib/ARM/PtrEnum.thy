(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory PtrEnum
imports "../tools/c-parser/CTranslation"
begin

instantiation ptr :: (type) enum
begin

  definition "enum_ptr \<equiv> map Ptr (enum_class.enum :: 32 word list)"
  definition "enum_all_ptr P \<equiv> enum_class.enum_all (\<lambda>v :: 32 word. P (Ptr v))"
  definition "enum_ex_ptr P \<equiv> enum_class.enum_ex (\<lambda>v :: 32 word. P (Ptr v))"

  instance
    apply (intro_classes)
       apply (clarsimp simp: enum_ptr_def)
       apply (metis ptr.exhaust surj_def)
      apply (clarsimp simp: enum_ptr_def distinct_map)
      apply (metis injI ptr.inject)
     apply (clarsimp simp: enum_all_ptr_def)
     apply (rule iffI)
      apply (rule allI)
      apply (erule_tac x="ptr_val x" in allE)
      apply force
     apply force
    apply (clarsimp simp: enum_ex_ptr_def)
    apply (rule iffI)
     apply force
    apply clarsimp
    apply (rule_tac x="ptr_val x" in exI)
    apply clarsimp
    done
end

end
