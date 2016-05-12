(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Generic_Separation_Algebras
imports Sep_Algebra_L4v 
begin
             

instantiation "prod" :: (stronger_sep_algebra,stronger_sep_algebra) zero
begin
  definition "zero_prod \<equiv> (0,0)"
  instance ..
end

instantiation "prod" :: (stronger_sep_algebra,stronger_sep_algebra) stronger_sep_algebra
begin

definition "sep_disj_prod x y \<equiv> sep_disj (fst x) (fst y) \<and> sep_disj (snd x) (snd y)"
definition "plus_prod x y \<equiv> ( (fst x) + (fst y) ,  (snd x) + (snd y))"

instance
  apply intro_classes
       apply (metis fst_conv sep_disj_prod_def sep_disj_zero snd_conv zero_prod_def)
      apply (metis (full_types) sep_disj_commuteI sep_disj_prod_def)
     apply (clarsimp simp: plus_prod_def zero_prod_def)
    apply (clarsimp simp: plus_prod_def sep_disj_prod_def)
    apply safe
       apply (metis sep_add_commute)
      apply (metis sep_add_commute)
     apply (clarsimp simp: plus_prod_def sep_disj_prod_def)
     apply (metis sep_add_assoc)
    apply (clarsimp simp: plus_prod_def sep_disj_prod_def)
   apply (clarsimp simp: plus_prod_def sep_disj_prod_def)
  apply (clarsimp simp: plus_prod_def sep_disj_prod_def)
  done

end


instantiation "option" :: (type) zero
begin
  definition "zero_option \<equiv> None"
  instance ..
end

definition
  orelse :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option"
where
  "orelse x y \<equiv> case x of Some x' => Some x' | None => y"

definition
  onlyone :: "'a option => 'a option => bool"
where
  "onlyone x y \<equiv> case x of 
                   Some x' => (case y of Some y' => False | _ => True)
                 | None => True"


instantiation "option" :: (type) stronger_sep_algebra
begin

definition "sep_disj_option \<equiv> onlyone "
definition "plus_option  \<equiv> orelse"

instance
  by intro_classes
     (clarsimp simp: sep_disj_option_def zero_option_def plus_option_def onlyone_def orelse_def 
               split: option.splits)+
end


record 'a generic_heap_record =
    heap :: "'a "

instantiation "generic_heap_record_ext" :: (stronger_sep_algebra, stronger_sep_algebra) stronger_sep_algebra
begin

definition "zero_generic_heap_record_ext \<equiv> Abs_generic_heap_record_ext 0"
definition "plus_generic_heap_record_ext h1 h2 \<equiv>
                Abs_generic_heap_record_ext (Rep_generic_heap_record_ext h1 + Rep_generic_heap_record_ext h2)"
definition "sep_disj_generic_heap_record_ext h1 h2 \<equiv> Rep_generic_heap_record_ext h1 ## Rep_generic_heap_record_ext h2"

instance
  apply intro_classes
       apply (fastforce simp:  sep_add_left_commute sep_disj_commute Rep_generic_heap_record_ext_inverse
                               sep_disj_commuteI sep_add_assoc sep_add_commute Abs_generic_heap_record_ext_inverse 
                               zero_generic_heap_record_ext_def sep_disj_generic_heap_record_ext_def
                               plus_generic_heap_record_ext_def)+
  done

end



end
