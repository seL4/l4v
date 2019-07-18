(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* Author: Thomas Sewell

   Library routines etc expected by Haskell code.
*)

theory HaskellLib_H
imports
  Lib
  NatBitwise
  "More_Numeral_Type"
  "Monad_WP/NonDetMonadVCG"
begin

abbreviation (input) "flip \<equiv> swp"

abbreviation(input) bind_drop :: "('a, 'c) nondet_monad \<Rightarrow> ('a, 'b) nondet_monad
                      \<Rightarrow> ('a, 'b) nondet_monad" (infixl ">>'_" 60)
  where "bind_drop \<equiv> (\<lambda>x y. bind x (K_bind y))"

lemma bind_drop_test:
  "foldr bind_drop x (return ()) = sequence_x x"
  by (rule ext, simp add: sequence_x_def)

(* If the given monad is deterministic, this function converts
    the nondet_monad type into a normal deterministic state monad *)
definition
  runState :: "('s, 'a) nondet_monad \<Rightarrow> 's \<Rightarrow> ('a \<times> 's)" where
 "runState f s \<equiv> THE x. x \<in> fst (f s)"

definition
  sassert :: "bool \<Rightarrow> 'a \<Rightarrow> 'a" where
 "sassert P \<equiv> if P then id else (\<lambda>x. undefined)"

lemma sassert_cong[fundef_cong]:
 "\<lbrakk> P = P'; P' \<Longrightarrow> s = s' \<rbrakk> \<Longrightarrow> sassert P s = sassert P' s'"
  apply (simp add: sassert_def)
  done

definition
  haskell_assert :: "bool \<Rightarrow> unit list \<Rightarrow> ('a, unit) nondet_monad" where
 "haskell_assert P L \<equiv> assert P"

definition
  haskell_assertE :: "bool \<Rightarrow> unit list \<Rightarrow> ('a, 'e + unit) nondet_monad" where
 "haskell_assertE P L \<equiv> assertE P"

declare haskell_assert_def [simp] haskell_assertE_def [simp]

definition
  stateAssert :: "('a \<Rightarrow> bool) \<Rightarrow> unit list \<Rightarrow> ('a, unit) nondet_monad" where
 "stateAssert P L \<equiv> get >>= (\<lambda>s. assert (P s))"

definition
  haskell_fail :: "unit list \<Rightarrow> ('a, 'b) nondet_monad" where
  haskell_fail_def[simp]:
 "haskell_fail L \<equiv> fail"

definition
  catchError_def[simp]:
 "catchError \<equiv> handleE"

definition
  "curry1 \<equiv> id"
definition
  "curry2 \<equiv> curry"
definition
  "curry3 f a b c \<equiv> f (a, b, c)"
definition
  "curry4 f a b c d \<equiv> f (a, b, c, d)"
definition
  "curry5 f a b c d e \<equiv> f (a, b, c, d, e)"

declare curry1_def[simp] curry2_def[simp]
        curry3_def[simp] curry4_def[simp] curry5_def[simp]

definition
  "split1 \<equiv> id"
definition
  "split2 \<equiv> case_prod"
definition
  "split3 f \<equiv> \<lambda>(a, b, c). f a b c"
definition
  "split4 f \<equiv> \<lambda>(a, b, c, d). f a b c d"
definition
  "split5 f \<equiv> \<lambda>(a, b, c, d, e). f a b c d e"

declare split1_def[simp] split2_def[simp]

lemma split3_simp[simp]: "split3 f (a, b, c) = f a b c"
  by (simp add: split3_def)

lemma split4_simp[simp]: "split4 f (a, b, c, d) = f a b c d"
  by (simp add: split4_def)

lemma split5_simp[simp]: "split5 f (a, b, c, d, e) = f a b c d e"
  by (simp add: split5_def)

definition
 "Just \<equiv> Some"
definition
 "Nothing \<equiv> None"

definition
 "fromJust \<equiv> the"
definition
 "isJust x \<equiv> x \<noteq> None"

definition
 "tail \<equiv> tl"
definition
 "head \<equiv> hd"

definition
  error :: "unit list \<Rightarrow> 'a" where
 "error \<equiv> \<lambda>x. undefined"

definition
 "reverse \<equiv> rev"

definition
 "isNothing x \<equiv> x = None"

definition
 "maybeApply \<equiv> option_map"

definition
 "maybe \<equiv> case_option"

definition
 "foldR f init L \<equiv> foldr f L init"

definition
 "elem x L \<equiv> x \<in> set L"

definition
 "notElem x L \<equiv> x \<notin> set L"

type_synonym ordering = bool

definition
  compare :: "('a :: ord) \<Rightarrow> 'a \<Rightarrow> ordering" where
  "compare \<equiv> (<)"

primrec
  insertBy :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "insertBy f a [] = [a]"
| "insertBy f a (b # bs) = (if (f a b) then (a # b # bs) else (b # (insertBy f a bs)))"

lemma insertBy_length [simp]:
  "length (insertBy f a as) = (1 + length as)"
  by (induct as) simp_all

primrec
  sortBy :: "('a \<Rightarrow> 'a \<Rightarrow> ordering) \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "sortBy f [] = []"
| "sortBy f (a # as) = insertBy f a (sortBy f as)"

lemma sortBy_length:
  "length (sortBy f as) = length as"
  by (induct as) simp_all

definition
 "sortH \<equiv> sortBy compare"

definition
 "catMaybes \<equiv> (map the) \<circ> (filter isJust)"

definition
 "runExceptT \<equiv> id"

declare Just_def[simp] Nothing_def[simp] fromJust_def[simp]
      isJust_def[simp] tail_def[simp] head_def[simp]
      error_def[simp] reverse_def[simp] isNothing_def[simp]
      maybeApply_def[simp] maybe_def[simp]
      foldR_def[simp] elem_def[simp] notElem_def[simp]
      catMaybes_def[simp] runExceptT_def[simp]

definition
 "headM L \<equiv> (case L of (h # t) \<Rightarrow> return h | _ \<Rightarrow> fail)"

definition
 "tailM L \<equiv> (case L of (h # t) \<Rightarrow> return t | _ \<Rightarrow> fail)"

axiomatization
  typeOf :: "'a \<Rightarrow> unit list"

definition
 "either f1 f2 c \<equiv> case c of Inl r1 \<Rightarrow> f1 r1 | Inr r2 \<Rightarrow> f2 r2"

lemma either_simp[simp]: "either = case_sum"
  apply (rule ext)+
  apply (simp add: either_def)
  done

class HS_bit = bit_operations +
  fixes shiftL :: "'a \<Rightarrow> nat \<Rightarrow> 'a"
  fixes shiftR :: "'a \<Rightarrow> nat \<Rightarrow> 'a"
  fixes bitSize :: "'a \<Rightarrow> nat"

instantiation word :: (len0) HS_bit
begin

definition
  shiftL_word[simp]: "(shiftL :: 'a::len0 word \<Rightarrow> nat \<Rightarrow> 'a word) \<equiv> shiftl"

definition
  shiftR_word[simp]: "(shiftR :: 'a::len0 word \<Rightarrow> nat \<Rightarrow> 'a word) \<equiv> shiftr"

definition
  bitSize_word[simp]: "(bitSize :: 'a::len0 word \<Rightarrow> nat) \<equiv> size"

instance ..

end

instantiation nat ::  HS_bit
begin

definition
  shiftL_nat: "shiftL (x :: nat) n \<equiv> (2 ^ n) * x"

definition
  shiftR_nat: "shiftR (x :: nat) n \<equiv> x div (2 ^ n)"

text \<open>bitSize not defined for nat\<close>

instance ..

end

class finiteBit = bit_operations +
  fixes finiteBitSize :: "'a \<Rightarrow> nat"

instantiation word :: (len0) finiteBit
begin

definition
  finiteBitSize_word[simp]: "(finiteBitSize :: 'a::len0 word \<Rightarrow> nat) \<equiv> size"

instance ..

end

definition
  bit_def[simp]:
 "bit x \<equiv> shiftL 1 x"

definition
"isAligned x n \<equiv> x && mask n = 0"

class integral = ord +
  fixes fromInteger :: "nat \<Rightarrow> 'a"
  fixes toInteger :: "'a \<Rightarrow> nat"
  assumes integral_inv: "fromInteger \<circ> toInteger = id"

instantiation nat :: integral
begin

definition
 fromInteger_nat: "fromInteger \<equiv> id"

definition
 toInteger_nat: "toInteger \<equiv> id"

instance
  apply (intro_classes)
  apply (simp add: toInteger_nat fromInteger_nat)
  done

end


instantiation word :: (len) integral
begin

definition
 fromInteger_word: "fromInteger \<equiv> of_nat :: nat \<Rightarrow> 'a::len word"

definition
 toInteger_word: "toInteger \<equiv> unat"

instance
  apply (intro_classes)
  apply (rule ext)
  apply (simp add: toInteger_word fromInteger_word)
  done

end

definition
  fromIntegral :: "('a :: integral) \<Rightarrow> ('b :: integral)" where
 "fromIntegral \<equiv> fromInteger \<circ> toInteger"

lemma fromIntegral_simp1[simp]: "(fromIntegral :: nat \<Rightarrow> ('a :: len) word) = of_nat"
  by (simp add: fromIntegral_def fromInteger_word toInteger_nat)

lemma fromIntegral_simp2[simp]: "fromIntegral = unat"
  by (simp add: fromIntegral_def fromInteger_nat toInteger_word)

lemma fromIntegral_simp3[simp]: "fromIntegral = ucast"
  apply (simp add: fromIntegral_def fromInteger_word toInteger_word)
  apply (rule ext)
  apply (simp add: ucast_def)
  apply (subst word_of_nat)
  apply (simp add: unat_def)
  done

lemma fromIntegral_simp_nat[simp]: "(fromIntegral :: nat \<Rightarrow> nat) = id"
  by (simp add: fromIntegral_def fromInteger_nat toInteger_nat)

definition
  infix_apply :: "'a \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'c" ("_ `~_~` _" [81, 100, 80] 80) where
  infix_apply_def[simp]:
 "infix_apply a f b \<equiv> f a b"

term "return $ a `~b~` c d"

definition
  zip3 :: "'a list \<Rightarrow> 'b list \<Rightarrow> 'c list \<Rightarrow> ('a \<times> 'b \<times> 'c) list" where
 "zip3 a b c \<equiv> zip a (zip b c)"

(* avoid even attempting haskell's show class *)
definition
 "show" :: "'a \<Rightarrow> unit list" where
 "show x \<equiv> []"

lemma show_simp_away[simp]: "S @ show t = S"
  by (simp add: show_def)

definition
 "andList \<equiv> foldl (\<and>) True"

definition
 "orList \<equiv> foldl (\<or>) False"

primrec
  mapAccumL :: "('a \<Rightarrow> 'b \<Rightarrow> 'a \<times> 'c) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a \<times> ('c list)"
where
  "mapAccumL f s [] = (s, [])"
| "mapAccumL f s (x#xs) = (
     let (s', r) = f s x;
         (s'', rs) = mapAccumL f s' xs
     in (s'', r#rs)
  )"

primrec
  untilM :: "('b \<Rightarrow> ('s, 'a option) nondet_monad) \<Rightarrow> 'b list \<Rightarrow> ('s, 'a option) nondet_monad"
where
  "untilM f [] = return None"
| "untilM f (x#xs) = do
    r \<leftarrow> f x;
    case r of
      None     \<Rightarrow> untilM f xs
    | Some res \<Rightarrow> return (Some res)
  od"

primrec
  untilME :: "('c \<Rightarrow> ('s, ('a + 'b option)) nondet_monad) \<Rightarrow> 'c list \<Rightarrow> ('s, 'a + 'b option) nondet_monad"
where
  "untilME f [] = returnOk None"
| "untilME f (x#xs) = doE
    r \<leftarrow> f x;
    case r of
      None     \<Rightarrow> untilME f xs
    | Some res \<Rightarrow> returnOk (Some res)
  odE"

primrec
  findM :: "('a \<Rightarrow> ('s, bool) nondet_monad) \<Rightarrow> 'a list \<Rightarrow> ('s, 'a option) nondet_monad"
where
  "findM f [] = return None"
| "findM f (x#xs) = do
    r \<leftarrow> f x;
    if r
      then return (Some x)
      else findM f xs
  od"

primrec
  findME :: "('a \<Rightarrow> ('s, ('e + bool)) nondet_monad) \<Rightarrow> 'a list \<Rightarrow> ('s, ('e + 'a option)) nondet_monad"
where
  "findME f [] = returnOk None"
| "findME f (x#xs) = doE
    r \<leftarrow> f x;
    if r
      then returnOk (Some x)
      else findME f xs
  odE"

primrec
  tails :: "'a list \<Rightarrow> 'a list list"
where
  "tails [] = [[]]"
| "tails (x#xs) = (x#xs)#(tails xs)"

lemma finite_surj_type:
  "\<lbrakk> (\<forall>x. \<exists>y. (x :: 'b) = f (y :: 'a)); finite (UNIV :: 'a set) \<rbrakk> \<Longrightarrow> finite (UNIV :: 'b set)"
  apply (erule finite_surj)
  apply safe
  apply (erule allE)
  apply safe
  apply (erule image_eqI)
  apply simp
  done

lemma finite_finite[simp]: "finite (s :: ('a :: finite) set)"
  by simp

lemma finite_inv_card_less':
  "U = (UNIV :: ('a :: finite) set) \<Longrightarrow> (card (U - insert a s) < card (U - s)) = (a \<notin> s)"
  apply (case_tac "a \<in> s")
   apply (simp_all add: insert_absorb)
  apply (subgoal_tac "card s < card U")
   apply (simp add: card_Diff_subset)
  apply (rule psubset_card_mono)
   apply safe
    apply simp_all
  done

lemma finite_inv_card_less:
   "(card (UNIV - insert (a :: ('a :: finite)) s) < card (UNIV - s)) = (a \<notin> s)"
  by (simp add: finite_inv_card_less')

text \<open>Support for defining enumerations on datatypes derived from enumerations\<close>
lemma distinct_map_enum: "\<lbrakk> (\<forall> x y. (F x = F y \<longrightarrow> x = y )) \<rbrakk> \<Longrightarrow> distinct (map F (enum :: 'a :: enum list))"
  apply (simp add: distinct_map)
  apply (rule inj_onI)
  apply simp
  done

definition
  "minimum ls \<equiv> Min (set ls)"
definition
  "maximum ls \<equiv> Max (set ls)"

primrec (nonexhaustive)
  hdCons :: "'a \<Rightarrow> 'a list list \<Rightarrow> 'a list list"
where
 "hdCons x (ys # zs) = (x # ys) # zs"

primrec
  rangesBy :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list list"
where
  "rangesBy f [] = []"
| "rangesBy f (x # xs) =
    (case xs of [] \<Rightarrow> [[x]]
             | (y # ys) \<Rightarrow> if (f x y) then hdCons x (rangesBy f xs)
                                     else [x] # (rangesBy f xs))"

definition
  partition :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<times> 'a list" where
 "partition f xs \<equiv> (filter f xs, filter (\<lambda>x. \<not> f x) xs)"

definition
  listSubtract :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
 "listSubtract xs ys \<equiv> filter (\<lambda>x. x \<in> set ys) xs"

definition
  init :: "'a list \<Rightarrow> 'a list" where
 "init xs \<equiv> case (length xs) of Suc n \<Rightarrow> take n xs | _ \<Rightarrow> undefined"

primrec
  break :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> 'a list)"
where
  "break f []       = ([], [])"
| "break f (x # xs) =
   (if f x
    then ([], x # xs)
    else (\<lambda>(ys, zs). (x # ys, zs)) (break f xs))"

definition
 "uncurry \<equiv> case_prod"

definition
  sum :: "'a list \<Rightarrow> 'a::{plus,zero}" where
 "sum \<equiv> foldl (+) 0"

definition
 "replicateM n m \<equiv> sequence (replicate n m)"

definition
  maybeToMonad_def[simp]:
 "maybeToMonad \<equiv> assert_opt"

definition
  funArray :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"  where
  funArray_def[simp]:
 "funArray \<equiv> id"

definition
  funPartialArray :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a :: enumeration_alt \<times> 'a) \<Rightarrow> ('a \<Rightarrow> 'b)"  where
 "funPartialArray f xrange \<equiv> \<lambda>x. (if x \<in> set [fst xrange .e. snd xrange] then f x else undefined)"

definition
  forM_def[simp]:
 "forM xs f \<equiv> mapM f xs"

definition
  forM_x_def[simp]:
 "forM_x xs f \<equiv> mapM_x f xs"

definition
  forME_x_def[simp]:
 "forME_x xs f \<equiv> mapME_x f xs"

definition
  arrayListUpdate :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<Rightarrow> 'b)" (infixl "aLU" 90)
where
  arrayListUpdate_def[simp]:
  "arrayListUpdate f l  \<equiv> foldl (\<lambda>f p. f(fst p := snd p)) f l"

definition
 "genericTake \<equiv> take \<circ> fromIntegral"

definition
 "genericLength \<equiv> fromIntegral \<circ> length"

abbreviation
  "null == List.null"

syntax (input)
  "_listcompr" :: "'a \<Rightarrow> lc_qual \<Rightarrow> lc_quals \<Rightarrow> 'a list"  ("[_ | __")

lemma "[(x,1) . x \<leftarrow> [0..10]] = [(x,1) | x \<leftarrow> [0..10]]" by (rule refl)

end
