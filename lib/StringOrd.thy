(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory StringOrd
imports "~~/src/HOL/Main"
begin

datatype anotherBL =
   BLNon
 | BLZer anotherBL
 | BLOne anotherBL
 | BLTwo anotherBL
 | BLThr anotherBL

lemma twice_bound_meta_all:
  "(\<And>a b. x = a \<and> y = b \<Longrightarrow> PROP Q a b) \<equiv> (PROP Q x y)"
  apply (rule equal_intr_rule)
   apply (erule meta_allE, erule meta_allE, erule meta_mp)
   apply simp
  apply clarsimp
  done

function(sequential) anotherBL_ord :: "anotherBL \<Rightarrow> anotherBL \<Rightarrow> bool"
where
   "anotherBL_ord BLNon x = True"
 | "anotherBL_ord x BLNon = False"
 | "anotherBL_ord (BLZer x) (BLZer y) = anotherBL_ord x y"
 | "anotherBL_ord (BLZer x) y = True"
 | "anotherBL_ord x (BLZer y) = False"
 | "anotherBL_ord (BLOne x) (BLOne y) = anotherBL_ord x y"
 | "anotherBL_ord (BLOne x) y = True"
 | "anotherBL_ord x (BLOne y) = False"
 | "anotherBL_ord (BLTwo x) (BLTwo y) = anotherBL_ord x y"
 | "anotherBL_ord (BLTwo x) y = True"
 | "anotherBL_ord x (BLTwo y) = False"
 | "anotherBL_ord (BLThr x) (BLThr y) = anotherBL_ord x y"
  apply simp_all
  apply (case_tac x, simp_all)
  apply (case_tac a, simp_all)
     apply (case_tac b, simp_all add: twice_bound_meta_all)[1]
    apply (case_tac b, simp_all add: twice_bound_meta_all)[1]
   apply (case_tac b, simp_all add: twice_bound_meta_all)[1]
  apply (case_tac b, simp_all add: twice_bound_meta_all)[1]
  done

termination anotherBL_ord
  apply (rule anotherBL_ord.termination)
      apply (rule wf_measure[where f="size_prod size size"])
     apply simp+
  done

instantiation
  anotherBL :: ord
begin
  definition le_anotherBL: "a \<le> b \<equiv> anotherBL_ord a b"
  definition less_anotherBL: "a < b \<equiv> (anotherBL_ord a b \<and> a \<noteq> b)"

  instance ..
end

lemma anotherBL_to_less_simps:
  "(anotherBL_ord a b = v) \<Longrightarrow> (a < b = (v \<and> a \<noteq> b))"
  by (simp add: less_anotherBL)

lemmas anotherBL_ords[simp] =
  anotherBL_ord.simps[folded le_anotherBL, simplified]
  anotherBL_ord.simps [THEN anotherBL_to_less_simps,
                       simplified, folded less_anotherBL]

lemma anotherBL_trans:
  "\<lbrakk> x \<le> (y :: anotherBL); y \<le> z \<rbrakk> \<Longrightarrow> x \<le> z"
  apply (rule ccontr)
  apply (erule rev_mp)+
  apply (induct y arbitrary: x z)
      apply (case_tac x, simp_all)[1]
     apply (case_tac x, simp_all(no_asm_simp))[1]
     apply (case_tac z, simp_all)[1]
    apply (case_tac x, simp_all(no_asm_simp))[1]
     apply (case_tac z, simp_all)[1]
    apply (case_tac z, simp_all)[1]
   apply (case_tac z, simp_all(no_asm_simp))[1]
    apply (case_tac x, simp_all)[1]
   apply (case_tac x, simp_all)[1]
  apply (case_tac z, simp_all(no_asm_simp))[1]
  apply (case_tac x, simp_all)[1]
  done

lemma anotherBL_antisym:
  "\<lbrakk> x \<le> y; (y :: anotherBL) \<le> x \<rbrakk> \<Longrightarrow> x = y"
  apply (erule rev_mp)+
  apply (induct x arbitrary: y)
      apply (case_tac y, simp_all)[1]
     apply (case_tac y, simp_all)[1]
    apply (case_tac y, simp_all)[1]
   apply (case_tac y, simp_all)[1]
  apply (case_tac y, simp_all)[1]
  done

lemma anotherBL_total_ord:
  "x \<le> y \<or> y \<le> (x :: anotherBL)"
  apply (induct x arbitrary: y)
      apply simp
     apply (case_tac y, simp_all)[1]
    apply (case_tac y, simp_all)[1]
   apply (case_tac y, simp_all)[1]
  apply (case_tac y, simp_all)[1]
  done

lemma less_eq_conj_anotherBL:
  "x < (y :: anotherBL) = (x \<le> y \<and> x \<noteq> y)"
  by (simp add: less_anotherBL le_anotherBL)

instantiation anotherBL :: linorder
begin

instance
  apply intro_classes
      apply (simp add: less_eq_conj_anotherBL)
      apply safe[1]
      apply (drule(1) anotherBL_antisym)
      apply simp
     apply (induct_tac x, simp_all)[1]
    apply (erule(1) anotherBL_trans)
   apply (erule(1) anotherBL_antisym)
  apply (rule anotherBL_total_ord)
  done

end

primrec
  nibble_to_anbl :: "nibble \<Rightarrow> anotherBL \<Rightarrow> anotherBL"
where
  "nibble_to_anbl Nibble0 anbl = BLZer (BLZer anbl)"
| "nibble_to_anbl Nibble1 anbl = BLZer (BLOne anbl)"
| "nibble_to_anbl Nibble2 anbl = BLZer (BLTwo anbl)"
| "nibble_to_anbl Nibble3 anbl = BLZer (BLThr anbl)"
| "nibble_to_anbl Nibble4 anbl = BLOne (BLZer anbl)"
| "nibble_to_anbl Nibble5 anbl = BLOne (BLOne anbl)"
| "nibble_to_anbl Nibble6 anbl = BLOne (BLTwo anbl)"
| "nibble_to_anbl Nibble7 anbl = BLOne (BLThr anbl)"
| "nibble_to_anbl Nibble8 anbl = BLTwo (BLZer anbl)"
| "nibble_to_anbl Nibble9 anbl = BLTwo (BLOne anbl)"
| "nibble_to_anbl NibbleA anbl = BLTwo (BLTwo anbl)"
| "nibble_to_anbl NibbleB anbl = BLTwo (BLThr anbl)"
| "nibble_to_anbl NibbleC anbl = BLThr (BLZer anbl)"
| "nibble_to_anbl NibbleD anbl = BLThr (BLOne anbl)"
| "nibble_to_anbl NibbleE anbl = BLThr (BLTwo anbl)"
| "nibble_to_anbl NibbleF anbl = BLThr (BLThr anbl)"

primrec
  char_to_anbl :: "char \<Rightarrow> anotherBL \<Rightarrow> anotherBL"
where
 "char_to_anbl (Char nib nob) anbl = nibble_to_anbl nib (nibble_to_anbl nob anbl)"

primrec
  string_to_anbl :: "string \<Rightarrow> anotherBL"
where
  "string_to_anbl []          = BLNon"
| "string_to_anbl (chr # str) = char_to_anbl chr (string_to_anbl str)"

lemmas string_ord_simps
  = string_to_anbl.simps char_to_anbl.simps nibble_to_anbl.simps
    anotherBL_ords anotherBL.simps

end
