(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* Port of Anthony Fox's HOL4 realisation of John Harrison's paper
   in TPHOLs 2005 on finite cartesian products *)

theory Arrays
imports
  "~~/src/HOL/Main"
  "~~/src/HOL/Library/Numeral_Type"
begin

definition
  has_size :: "'a set => nat => bool" where
   "has_size s n == finite(s) \<and> card(s) = n"

definition
  finite_index :: "nat => 'a::finite" where
  "finite_index ==
     SOME f. ALL x::'a. EX! n. n < CARD('a::finite) & f n = x"

lemma card_image_inj[rule_format]:
  "finite s ==>  (ALL x y. x : s & y : s & f x = f y --> x = y) -->
                 (card (f ` s) = card s)"
apply (erule finite_induct)
apply (simp_all add: card_insert_if)
apply clarsimp
apply blast
done

lemma has_size_image_inj:
  "[| has_size s n ;
      (!!x y. x \<in> s \<and> y \<in> s \<and> f x = f y ==> x = y) |]
   ==>
     has_size (f ` s) n"
apply (simp add: has_size_def card_image_inj)
done

lemma has_size_0[simp]:
  "has_size s 0 = (s = {})"
apply(simp_all add: has_size_def)
apply(rule iffI)
  apply clarsimp
apply simp
done

lemma has_size_suc:
  "has_size s (Suc n) =
     (s ~= {} & (ALL a. a : s --> has_size (s - {a}) n))"
apply (simp add: has_size_def)
apply (case_tac "s = {}", simp_all)
apply (simp add: card_Diff_singleton cong: conj_cong)
apply (case_tac "finite s", simp_all)
apply (subgoal_tac "EX a. a : s")
  apply simp
  apply (subgoal_tac "card s ~= 0")
    apply arith
  apply (erule contrapos_nn)
  apply simp
apply (simp add: ex_in_conv)
done

lemma has_index[rule_format]:
  "ALL s. finite s & card s = n -->
            (EX f. (ALL m. m < n --> f m : s) &
                   (ALL x. x : s --> (EX! m. m < n & f m = x)))"
apply (rule nat.induct)
  apply (simp add: card_eq_0_iff cong: conj_cong)
apply clarsimp
apply (simp add: card_Suc_eq )
apply clarsimp
apply (erule_tac x = "B" in allE)
apply simp
apply clarsimp
apply (rule_tac x = "%n. if n = card B then b else f n" in exI)
apply clarsimp
apply rule
  apply rule
  apply (rule ex_ex1I)
    apply (rule_tac x = "card B" in exI)
    apply simp
  apply (subgoal_tac "m = card B")
    apply (subgoal_tac "y = card B")
      apply simp
    apply (rule ccontr)
    apply (subgoal_tac "y < Suc (card B) & f y = b")
      apply (subgoal_tac "y < card B")
        apply fast
      apply arith
    apply fast
  apply (rule ccontr)
  apply (subgoal_tac "m < Suc (card B) & f m = b")
    apply (subgoal_tac "m < card B")
      apply fast
    apply arith
  apply fast
apply rule
apply (rule ex_ex1I)
  apply (erule_tac x = x in allE)
  apply (erule_tac impE)
    apply simp
  apply (drule ex1_implies_ex)
  apply clarsimp
  apply (rule_tac x = m in exI)
  apply simp
apply (subgoal_tac "b ~= x")
  apply simp
  apply clarsimp
  apply (subgoal_tac "y < card B & m < card B")
    apply clarsimp
    apply blast
  apply arith
apply blast
done

lemma finite_index_works[rule_format]:
  "ALL i :: 'a. EX! n. n < CARD('a::finite) & finite_index n = i"
apply (simp add: finite_index_def)
apply (rule someI_ex[where 'a = "nat => 'a"])
apply (insert has_index[where s = "UNIV :: 'a set"])
apply (simp add: finite)
done

lemma finite_index_inj:
  "[| i < CARD('a::finite); j < CARD('a) |] ==>
   ((finite_index i :: 'a) = finite_index j) = (i = j)"
apply (insert finite_index_works[where i = "finite_index j"])
apply blast
done

lemma forall_finite_index:
  "(ALL k::('a::finite). P k) =
   (ALL i. i < CARD('a) --> P (finite_index i))"
apply rule
  apply simp
apply rule+
apply (insert finite_index_works[where 'a = 'a])
apply (erule_tac x = "k::'a" in meta_allE)
apply blast
done

section {* Finite Cartesian Products *}

typedef ('a,'b) array ("_[_]" [30,0] 31)
  = "UNIV :: ('b::finite => 'a) set"
by simp

lemma array_inject:
  "(Abs_array x = Abs_array y) = (x = y)"
  by (metis Abs_array_inverse UNIV_I)

lemma array_induct:
  "(!!f. P (Abs_array f)) \<Longrightarrow> P x"
apply (drule_tac allI)
apply (drule_tac spec[where ?x = "Rep_array x"])
apply (simp add: Rep_array_inverse)
done

rep_datatype "Abs_array"
  by (auto simp: array_inject intro: array_induct)

(* should add nice syntax for index *)
definition index :: "('a,'b::finite)array => nat => 'a" where
  "index x i == Rep_array x (finite_index i)"

lemma my_ext: "(ALL x. f x = g x) = (f = g)"
apply (rule+, simp+)
done

theorem cart_eq:
  "((x::('a,'b::finite)array) = y) =
      (ALL i. i < CARD('b) --> index x i = index y i)"
apply (rule, simp)
apply (simp add: index_def)
apply (drule forall_finite_index[THEN iffD2])
apply (simp add: my_ext Rep_array_inject)
done

(* should make FCP a binder, and perhaps call it something else.
   Maybe "ARRAY" ? *)
definition FCP :: "(nat => 'a) => ('a,'b::finite) array" where
  "FCP == \<lambda> g.
             SOME f.
               ALL i. i < CARD('b) --> index f i = g i"

definition
  update :: "('a,'b::finite) array \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> ('a,'b) array"
where
  "update f i x \<equiv> FCP ((index f)(i := x))"

definition
  fupdate :: "nat => ('a => 'a) => ('a,'b::finite) array =>
              ('a,'b::finite) array"
where
  "fupdate i f x \<equiv> update x i (f (index x i))"

lemma fcp_beta[rule_format]:
  "ALL i. i < CARD('b::finite) -->
          index (FCP g :: ('a,'b) array) i = g i"
apply (simp add: FCP_def)
apply (rule someI_ex)
apply (rule_tac x =
                "Abs_array (%k. g (SOME i. i < CARD('b) &
                                           finite_index i = k))"
       in exI)
apply (simp add: index_def Abs_array_inverse)
apply rule+
apply (rule arg_cong[where 'a = nat])
apply (rule some_equality)
  apply simp
apply (erule conjE)
apply (rule finite_index_inj[THEN iffD1])
apply simp_all
done

lemma fcp_unique:
  "(ALL i. i < CARD('b::finite) --> (index f i = g i)) =
   (FCP g = (f :: ('a,'b) array))"
  by (fastforce simp: cart_eq fcp_beta)

lemma fcp_eta:
  "FCP (%i. index g i) = g"
  by (simp add: cart_eq fcp_beta)

lemma index_update [simp]:
  "n < CARD('b::finite) \<Longrightarrow> index (update (f::('a,'b) array) n x) n = x"
  by (simp add: update_def fcp_beta)

lemma index_update2 [simp]:
  "\<lbrakk> k < CARD('b::finite); n \<noteq> k \<rbrakk>
   \<Longrightarrow>
    index (update (f::('a,'b) array) n x) k = index f k"
  by (simp add: update_def fcp_beta)

lemma update_update [simp]:
  "update (update f n x) n y = update f n y"
apply(subst cart_eq)
apply clarsimp
apply(case_tac "i=n")
 apply simp+
done

lemma update_comm [simp]:
  "n \<noteq> m \<Longrightarrow> update (update f m v) n v' = update (update f n v') m v"
apply(subst cart_eq)
apply clarsimp
apply(case_tac "i=n")
 apply simp
apply(case_tac "i=m")
 apply simp
apply simp
done

lemma update_index_same [simp]:
  "update v n (index v n) = v"
apply(subst cart_eq)
apply clarsimp
apply(case_tac "i=n")
 apply simp+
done

function
  foldli0 :: "(nat => 'acc => 'a => 'acc) => 'acc => nat => ('a,'index::finite)array => 'acc"
where
  "foldli0 f a i (arr::('a,'index::finite)array) =
     (if CARD('index::finite) <= i then a
      else foldli0 f (f i a (index arr i)) (i+1) arr)"
  by pat_completeness auto

termination
  apply (relation "measure (% (f,a,i,(arr::('b,'c::finite)array)). CARD('c) - i)")
  apply auto
  done

definition
  foldli :: "(nat => 'acc => 'a => 'acc) => 'acc => ('a,'i::finite) array => 'acc"
where
   "foldli f a arr == foldli0 f a 0 arr"

(* for a traditional word presentation, with MSB on the left, you'd
   want a fold that numbered in the reverse direction (with element 0
   on the right rather than the left) *)

end
