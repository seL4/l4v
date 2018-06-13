(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory DataMap
imports Main
begin

type_synonym ('k, 'a) map = "'k \<rightharpoonup> 'a"

definition
  data_map_empty :: "('k, 'a) map"
where
  data_map_empty_def[simp]: "data_map_empty \<equiv> Map.empty"

definition
  data_map_insert :: "'k \<Rightarrow> 'a \<Rightarrow> ('k, 'a) map \<Rightarrow> ('k, 'a) map"
where
  data_map_insert_def[simp]: "data_map_insert x y m \<equiv> (m (x \<mapsto> y))"

definition
  lookupBefore :: "('k :: {linorder, finite}) \<Rightarrow> ('k, 'a) map \<Rightarrow> ('k \<times> 'a) option"
where
  "lookupBefore x m \<equiv>
     let Ks = {k \<in> dom m. k \<le> x}
     in if Ks = {} then None
            else Some (Max Ks, the (m (Max Ks)))"

definition
  lookupAround :: "('k :: {linorder, finite}) \<Rightarrow> ('k, 'a) map
                       \<Rightarrow> (('k \<times> 'a) option \<times> 'a option \<times> ('k \<times> 'a) option)"
where
  "lookupAround x m \<equiv>
     let Bs = {k \<in> dom m. k < x};
         As = {k \<in> dom m. k > x}
     in (if Bs = {} then None else Some (Max Bs, the (m (Max Bs))),
         m x,
         if As = {} then None else Some (Min As, the (m (Min Bs))))"

definition
  data_map_filterWithKey :: "('k \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('k, 'a) map \<Rightarrow> ('k, 'a) map"
where
  "data_map_filterWithKey f m \<equiv> \<lambda>x. case m x of
       None   \<Rightarrow> None
     | Some y \<Rightarrow> if f x y then Some y else None"

abbreviation(input)
  "data_set_empty \<equiv> {}"

abbreviation(input)
  "data_set_insert \<equiv> insert"

abbreviation(input)
  "data_set_delete x S \<equiv> S - {x}"

end
