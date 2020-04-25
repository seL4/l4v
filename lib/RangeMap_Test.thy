(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory RangeMap_Test
imports
  Lib.RangeMap
  Main
begin

section \<open>Examples for RangeMap\<close>

experiment begin

subsection \<open>Basic usage\<close>

local_setup \<open>
RangeMap.define_map
  (* Specification of names to generate. "name_opts_default" generates qualified names
     starting with the given string i.e. "test_map.foo". *)
  (RangeMap.name_opts_default "test_map")

  (* List of ((start key, end key), value).
     Key ranges include the start but not the end points. *)
  [((@{cterm "1::nat"}, @{cterm "2::nat"}), @{cterm "True"}),
   ((@{cterm "2::nat"}, @{cterm "3::nat"}), @{cterm "False"}),
   ((@{cterm "5::nat"}, @{cterm "8::nat"}), @{cterm "True \<and> False"}),
   (* Key ranges are allowed to be empty, such as this one *)
   ((@{cterm "8::nat"}, @{cterm "8::nat"}), @{cterm "True \<or> False"}),
   (* Test for input preservation; see below *)
   ((@{cterm "if True then 8::nat else undefined"}, @{cterm "6 + 7 :: nat"}),
    @{cterm "False \<longrightarrow> True"})
  ]

  (* Key and value types. *)
  @{typ nat} @{typ bool}
  (* Key comparison solver. This should be a conversion that converts
     key comparisons to True or False. *)
  (Simplifier.rewrite @{context})
\<close>
print_theorems

text \<open>
  Generated definitions for lookup tree and list:
\<close>
thm test_map.tree_def test_map.list_def

text \<open>
  Lookup theorems:
\<close>
thm test_map.lookups

text \<open>
  We also get lookup theorems for the start of each range (if nonempty).
  These can be useful simplifier equations in some scenarios.
\<close>
thm test_map.start_lookups

text \<open>
  Test that user-provided key terms are preserved verbatim.
\<close>
ML \<open>
@{assert}
  (Thm.prop_of @{thm test_map.lookups(5)[where x=x]}
   = @{term "Trueprop (((if True then 8 else undefined) \<le> x \<and> x < 6 + 7)
             = (RangeMap.lookup_range_tree test_map.tree x
                = Some ((if True then 8 else undefined, 6 + 7), False \<longrightarrow> True)))"});
\<close>

text \<open>
  The domain is just the union of all key ranges.
  In practice, maps tend to have many contiguous ranges. RangeMap also
  generates a "compact" domain theorem that merges adjacent ranges.
\<close>
thm test_map.domain test_map.domain_compact


subsection \<open>Test that empty maps are supported\<close>

local_setup \<open>
RangeMap.define_map
  (RangeMap.name_opts_default "empty_test")
  []
  @{typ int} @{typ int}
  Thm.reflexive (* unused *)
\<close>
print_theorems


subsection \<open>Stress testing\<close>
ML \<open>
fun range_map_test_legendre n =
  let fun P q x = if q*q > x then true else x mod q <> 0 andalso P (q+1) x;
  in (1 upto n)
     |> map (fn k => ((k*k, (k+1)*(k+1)), hd (filter (P 2) (k*k+1 upto (k+1)*(k+1))))) end;

fun range_map_test_legendre_ct T n =
  let fun cterm_of_num T n = Thm.cterm_of @{context} (HOLogic.mk_number T n);
  in range_map_test_legendre n
     |> map (fn ((ks, ke), v) => ((cterm_of_num T ks, cterm_of_num T ke), cterm_of_num T v)) end;
\<close>

local_setup \<open>
RangeMap.define_map
  (RangeMap.name_opts_default "legendre_10")
  (range_map_test_legendre_ct @{typ nat} 10)
  @{typ nat} @{typ nat}
  (FP_Eval.eval_conv @{context} (FP_Eval.make_rules @{thms rel_simps} []))
\<close>

local_setup \<open>
RangeMap.define_map
  (RangeMap.name_opts_default "legendre_100")
  (range_map_test_legendre_ct @{typ nat} 100)
  @{typ nat} @{typ nat}
  (FP_Eval.eval_conv @{context} (FP_Eval.make_rules @{thms rel_simps} []))
\<close>

local_setup \<open>
RangeMap.define_map
  (RangeMap.name_opts_default "legendre_1000")
  (range_map_test_legendre_ct @{typ nat} 1000)
  @{typ nat} @{typ nat}
  (FP_Eval.eval_conv @{context} (FP_Eval.make_rules @{thms rel_simps} []))
\<close>

(* Example of proof using range map *)
lemma legendre_100_values:
  "RangeMap.lookup_range_tree legendre_100.tree k = Some ((start, end), v)
   \<Longrightarrow> start < v \<and> v < end"
  (* Convert to list and expand *)
  apply (subst (asm) legendre_100.tree_list_lookup_eq)
  apply (drule RangeMap.range_map_of_Some)
  apply (clarsimp simp: legendre_100.list_def)
  apply linarith
  done

end

end
