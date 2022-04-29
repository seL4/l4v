(*
 * Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory StaticDerivations_SI
imports
  "DSpecProofs.Retype_DP"
  Sep_Algebra.Extended_Separation_Algebra
begin


definition "spec_object_size spec ptr =
  (let obj = (the (cdl_objects spec ptr)) in obj_bits_cdl (object_type obj) (object_size_bits obj))"

definition "next_allocation spec previous current =
   alignUp previous (spec_object_size spec current) + 2 ^ (spec_object_size spec current)"

fun previous :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a option"  where
  "previous v [] = None" |
  "previous v [x] = None" |
  "previous v (x#y#xs) =  (if y = v then Some x else previous v (y#xs))"

primrec allocate where
   "allocate base_ptr spec [] = Map.empty" |
   "allocate ptr spec (x#xs) = [x \<mapsto> ptr] + allocate (next_allocation spec ptr x ) spec xs"

declare allocate.simps[simp del]

definition "mapp g f = (\<lambda>x. map_option (g x) (f x))"

definition "aligned_allocations spec base_ptr children =
      mapp (\<lambda>ptr ptr'. alignUp ptr' (spec_object_size spec ptr)) (allocate base_ptr spec children)"

lemma [simp]:
  "mapp g (x + y) = mapp g x + mapp g y"
  apply (intro ext iffI; clarsimp simp: mapp_def plus_fun_def plus_option_def split: option.splits)
  done

lemma [simp]:
  "mapp g ([x \<mapsto> y]) = [x \<mapsto> g x y]"
  apply (intro ext iffI; clarsimp simp: mapp_def plus_fun_def plus_option_def split: option.splits)
  done

lemma aligned_allocations_hd: "aligned_allocations spec ptr (a#list) a =
  Some (alignUp ptr (spec_object_size spec a))"
  apply (clarsimp simp: aligned_allocations_def allocate.simps)
  apply (simp add: plus_fun_def plus_option_def)
  done

lemma mapp_app[simp]: "M x \<noteq> None \<Longrightarrow> (mapp f M) x = Some (f x (the (M x)))"
  by (clarsimp simp: mapp_def)

lemma [simp]: "distinct (x#xs) \<Longrightarrow>
     ([x \<mapsto> v] + allocate y spec xs) x = Some v"
  apply (induct xs; clarsimp simp: plus_fun_def plus_option_def)
  done

lemma [simp]: "distinct (x#xs) \<Longrightarrow>
      ([x \<mapsto> v] + mapp g (allocate y spec xs)) x = Some v"
  apply (induct xs; clarsimp simp: plus_fun_def plus_option_def)
  done

lemma [simp]: "allocate ptr spec (a # list) a = Some ptr"
  apply (clarsimp simp: allocate.simps)
  by (simp add: plus_fun_def plus_option_def)

lemma not_in_previous: "x \<notin> set list \<Longrightarrow>
   previous x list = None"
  apply (induct list arbitrary: x; clarsimp)
  by (metis list.set_intros(1) not_NilE previous.simps(2) previous.simps(3))

lemma not_in_previous':"x \<notin> set list \<Longrightarrow> Some p = previous x (x # list) \<Longrightarrow> False"
  apply (induct list arbitrary: x p; clarsimp)
  by (simp add: not_in_previous)

lemma in_tail_previous: "x \<in> set list \<Longrightarrow> previous x (a # list) \<noteq> None"
  by (induct list arbitrary: a; clarsimp)

lemma previous_in_head: "x \<in> set list \<Longrightarrow> the (previous x (a # list)) \<notin> set list
        \<Longrightarrow> the (previous x (a # list)) = a"
  by (induct list arbitrary: a; clarsimp)

lemma previous_in_tail: "Some p = previous x (a # list) \<Longrightarrow> x \<in> set list"
  by (induct list arbitrary: a; clarsimp split: if_splits)

lemma in_right_map[simp]: "v \<noteq> x \<Longrightarrow> ([x \<mapsto> y] + ys) v = ys v"
 by (clarsimp simp: plus_fun_def plus_option_def)

lemma in_list_allocate: "x \<in> set list \<Longrightarrow> \<exists>z. allocate ptr spec (list) x = Some z"
  apply (induct list arbitrary: ptr x)
   apply (clarsimp)
  apply (case_tac "x=a")
   apply (clarsimp)
  apply (drule meta_spec)
  apply (drule_tac x=x in meta_spec)
  apply (drule meta_mp)
   apply (clarsimp)
  apply (clarsimp)
  apply (rule exI)
  apply (clarsimp simp: allocate.simps(2))
  apply (fastforce simp: in_right_map)
  done

lemma previous_in_list: "previous x list = Some y \<Longrightarrow> y \<in> set list"
  apply (induct list arbitrary: y)
   apply clarsimp+
  apply (metis option.sel previous_in_head previous_in_tail)
  done

lemma distinct_previous_const:
  "\<lbrakk>distinct (a#list); previous x list = Some y\<rbrakk> \<Longrightarrow> Some y = previous x (a # list)"
  apply (induct list arbitrary: x y; clarsimp)
  apply (metis previous_in_tail)
  done

lemma previous_in_allocate: "\<lbrakk>previous x list = Some y; distinct (a#list); x \<in> set list\<rbrakk>
  \<Longrightarrow> \<exists>z. allocate ptr spec (a # list) y = Some z"
  apply (drule (1) distinct_previous_const[rotated])
  apply (drule sym)
  apply (frule previous_in_list)
  apply (erule in_list_allocate)
  done

lemma allocate_alignUp:
  "distinct list \<Longrightarrow>
       x \<in> set list \<Longrightarrow>
       (aligned_allocations spec (ptr :: machine_word) list) x =
   Some (alignUp (the (allocate (ptr :: machine_word) spec list x))
  (obj_bits_cdl (object_type (the (cdl_objects spec x))) (object_size_bits (the (cdl_objects spec x)))))"
  supply allocate.simps[simp]
  apply (induct list arbitrary: ptr; clarsimp)
  apply (clarsimp simp: aligned_allocations_def)
  apply (elim disjE; clarsimp)
   apply (clarsimp simp: spec_object_size_def Let_unfold)
  apply (subst in_right_map; clarsimp)
  apply (subst in_right_map; clarsimp)
  done

lemma some_previous: "\<lbrakk>a \<notin> set list; Some a = previous x (a#list)\<rbrakk> \<Longrightarrow> x = hd list"
  apply (induct list arbitrary: x a; clarsimp)
  apply (metis Some_to_the empty_iff list.exhaust_sel list.set(1)
               not_in_previous option.distinct(1) previous.simps(3) set_ConsD)
  done

lemma previous_cons[simp]: "a \<notin> set list \<Longrightarrow> p \<noteq> a \<Longrightarrow>
     Some p = previous x (a # list) \<Longrightarrow> previous x (a # list) = previous x list"
  by (induct list; clarsimp)

lemma allocate_previous: "\<lbrakk>distinct list; x \<in> set list; Some p = previous x list\<rbrakk> \<Longrightarrow>
       (allocate ptr spec  list) x = Some (next_allocation spec (the (allocate ptr spec list p)) p)"
  apply (subgoal_tac "p \<in> set list")
   supply allocate.simps[simp]
   apply (induct list arbitrary: p ptr)
    apply (clarsimp simp: aligned_allocations_def)
   apply (frule previous_in_tail, clarsimp)
   apply (elim disjE; clarsimp?)
    apply (frule some_previous)
     apply (clarsimp, rule refl)
    apply (subst in_right_map)
     apply clarsimp
    apply (case_tac "list")
     apply fastforce+
   apply (subst in_right_map)
    apply clarsimp
   apply (frule previous_in_tail, clarsimp)
   apply (drule_tac x=p in meta_spec)
   apply (drule_tac x="(next_allocation spec ptr a)" in meta_spec)
   apply clarsimp
   apply (drule meta_mp)
    apply clarsimp
    apply (case_tac list)
     apply clarsimp+
   apply (subst in_right_map; clarsimp)
  apply (induct list arbitrary: p; clarsimp)
  apply (metis previous_cons previous_in_tail)
  done

lemma aligned_allocate_previous:
  "\<lbrakk>distinct list; x \<in> set list; Some p = previous x list \<rbrakk> \<Longrightarrow>
    (aligned_allocations spec  ptr  list) x =
       Some (alignUp ((next_allocation spec (the (allocate (ptr :: machine_word) spec list p)) p))
         (obj_bits_cdl (object_type (the (cdl_objects spec x))) (object_size_bits (the (cdl_objects spec x)))))"
  apply (unfold aligned_allocations_def mapp_def)
  apply (subst arg_cong[OF allocate_previous,
                        where f="map_option (\<lambda>ptr'. alignUp ptr' (spec_object_size spec x))"])
     apply (fastforce)+
  apply (metis option.simps(9) spec_object_size_def)
  done

abbreviation cptr_of ::
  "(cdl_cptr \<times> bi_untyped_desc \<times> cdl_cap) option \<Rightarrow> cdl_cptr"
  where
  "cptr_of \<equiv> \<lambda>x. fst (the x)"

abbreviation cap_of ::
  "(cdl_cptr \<times> bi_untyped_desc \<times> cdl_cap) option \<Rightarrow> cdl_cap"
  where
  "cap_of \<equiv> \<lambda>x. snd (snd (the x))"

definition valid_derivations where
  "valid_derivations spec untyped_derivations untyped_map \<equiv>
    distinct (map fst untyped_derivations) \<and>
    distinct_sets (map (set o snd) untyped_derivations) \<and>
    (\<forall>family\<in>(set untyped_derivations).
      let parent      = fst family;
          parent_cap  = cap_of (untyped_map parent);
          start       = Min (available_range (parent_cap));
          children    = snd family
      in
        distinct children \<and>
        (\<forall>child\<in>(set children).
          let spec_child = the (cdl_objects spec child);
              child_size = spec_object_size spec child
          in
            cdl_objects spec child \<noteq> None \<and>
            object_type spec_child \<noteq> UntypedType \<and>
            object_size_bits spec_child < 2 ^ word_bits \<and>
            start \<le> start + 2 ^ child_size \<and>
            child_size < word_size \<and>
            is_aligned start child_size \<and>
            start \<le> the (aligned_allocations spec start children child) + 2 ^ child_size \<and>
            (previous child children \<noteq> None \<longrightarrow> start < the (allocate start spec children child)) \<and>
            the (allocate start spec children child) \<in> available_range (parent_cap)))"

end