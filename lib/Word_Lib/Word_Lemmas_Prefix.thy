(*
 * Copyright 2018, Data61
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

section "Word Lemmas that use List Prefix-Order"

(* The AFP does not includes this theory to avoid polluting the class name
   space with the List prefix order. New lemmas should be proved with
   explicit prefix/strict_prefix in Word_Lemmas and then lifted here *)

theory Word_Lemmas_Prefix
imports
  Word_Lemmas
  Word_Lemmas_Internal
  "HOL-Library.Prefix_Order"
begin

lemmas bl_pad_to_prefix = bl_pad_to_prefix[folded less_eq_list_def]
lemmas sublist_equal_part = sublist_equal_part[folded less_eq_list_def]
lemmas not_prefix_longer = not_prefix_longer[folded less_eq_list_def]
lemmas map_prefixI = map_prefixI[folded less_eq_list_def]
lemmas take_prefix = take_prefix[folded less_eq_list_def]
lemmas take_is_prefix = take_is_prefix[folded less_eq_list_def]

lemmas prefix_length_less = prefix_length_less[folded less_list_def']
lemmas take_less = take_strict_prefix[folded less_list_def']

end
