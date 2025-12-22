(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory FastMap_Test
imports
  Lib.FastMap
  Lib.LexordList
  Lib.NICTATools
  Lib.Qualify
begin

section \<open>Basic usage example\<close>

experiment begin
  local_setup \<open>
    FastMap.define_map
      (* The name of the map constant and names of associated theorems.
       * This function constructs a set of sensible default names, but
       * you can also choose different names manually. *)
      (FastMap.name_opts_default "simple_test_map")

      (* List of the actual mappings. These must be sorted by key
       * and the key type must admit a linear order. *)
      [(@{term "0 :: nat"}, @{term "0 :: nat"}),
       (@{term "1 :: nat"}, @{term "1 :: nat"}),
       (@{term "2 :: nat"}, @{term "1 :: nat"}),
       (@{term "3 :: nat"}, @{term "2 :: nat"}),
       (@{term "4 :: nat"}, @{term "3 :: nat"}),
       (@{term "5 :: nat"}, @{term "5 :: nat"})]

      (* Key transformer. Must be an injective function that maps the
       * key type to a linorder type. This will usually be id, unless
       * the key type isn't naturally linorder. See string_map below
       * for an example of a non-trivial key transform. *)
      @{term "id :: nat \<Rightarrow> nat"}

      (* Extra simp rules to use when verifying the key ordering. *)
      @{thms}

      (* Use the default background simpset for solving goals.
       * Set to true if you want precise control over the simpset. *)
      false
  \<close>
  thm simple_test_map_def

  text \<open>Default theorem names are generated based on the map name\<close>
  thm simple_test_map_to_lookup_list
  thm simple_test_map_lookups
  thm simple_test_map_domain simple_test_map_range simple_test_map_keys_distinct


  subsection \<open>Check the generated theorems\<close>
  lemma "simple_test_map = map_of [(0, 0), (1, 1), (2, 1), (3, 2), (4, 3), (5, 5)]"
    by (rule simple_test_map_to_lookup_list)

  lemma
    "simple_test_map 0 = Some 0"
    "simple_test_map 1 = Some 1"
    "simple_test_map 2 = Some 1"
    "simple_test_map 3 = Some 2"
    "simple_test_map 4 = Some 3"
    "simple_test_map 5 = Some 5"
    by (rule simple_test_map_lookups)+

  lemma
    "dom simple_test_map = set [0, 1, 2, 3, 4, 5]"
    by (rule simple_test_map_domain)

  text \<open>Note that the range is not simplified\<close>
  lemma
    "ran simple_test_map = set [0, 1, 1, 2, 3, 5]"
    by (rule simple_test_map_range)

  lemma
    "distinct ([0, 1, 2, 3, 4, 5] :: nat list)"
    by (rule simple_test_map_keys_distinct[simplified list.map prod.sel])

end


section \<open>Basic tests for the generated theorems\<close>

ML \<open>
fun create_int_map name n typ ctxt =
  FastMap.define_map (FastMap.name_opts_default name)
    (List.tabulate (n, fn i => (HOLogic.mk_number typ i,
                                HOLogic.mk_string (string_of_int i))))
    (Const (@{const_name id}, typ --> typ))
    @{thms}
    false
    ctxt
\<close>

experiment begin
  local_setup \<open>
    create_int_map "simple_test_map_100" 100 @{typ int}
  \<close>
  print_theorems

  text \<open>Direct lookup theorems\<close>
  lemma "simple_test_map_100 42 = Some ''42''"
    by (rule simple_test_map_100_lookups)

  text \<open>We try to configure the default simpset for fast lookups\<close>
  lemma "simple_test_map_100 100 = None"
    by (time_methods
            default:
                \<open>simp add: simple_test_map_100_def\<close>
            minimal:
                \<open>simp only: simple_test_map_100_def FastMap.lookup_tree_simps'
                            id_apply rel_simps if_False
                      cong: if_weak_cong\<close>
            slow_simps:
                \<open>simp add: simple_test_map_100_def FastMap.lookup_tree.simps
                      del: FastMap.lookup_tree_simps'
                      cong: if_weak_cong cong del: if_cong\<close>
            slow_simps_l4v:
                \<open>simp add: simple_test_map_100_def FastMap.lookup_tree.simps
                      del: FastMap.lookup_tree_simps'
                      cong: if_cong cong del: if_weak_cong\<close>
            (* This simulates using a functional map instead of FastMap *)
            fun_map:
                \<open>simp add: simple_test_map_100_to_lookup_list\<close>
            (* Strangely, this is much faster, even though it uses the same rules
               (and even has the same simp trace) *)
            fun_map_minimal:
                \<open>simp only: simple_test_map_100_to_lookup_list
                            map_of.simps fun_upd_apply prod.sel
                            rel_simps simp_thms if_True if_False
                      cong: if_weak_cong\<close>)

  text \<open>Domain and range theorems\<close>
  lemma "dom simple_test_map_100 = {0 .. 99}"
    apply (simp add: upto_rec1 flip: set_upto)
    by (simp only: simple_test_map_100_domain set_simps)

  lemma
    "ran simple_test_map_100 =
     set ([[x] | x \<leftarrow> ''0123456789''] @ [[x, y] | x \<leftarrow> ''123456789'', y \<leftarrow> ''0123456789''])"
    apply simp
    by (simp only: simple_test_map_100_range set_simps)
end



section \<open>Test with larger mapping\<close>

experiment begin
  local_setup \<open>
    create_int_map "simple_test_map_1000" 1000 @{typ int}
  \<close>

  lemma "simple_test_map_1000 42 = Some ''42''"
    by (rule simple_test_map_1000_lookups)

  lemma "simple_test_map_1000 1000 = None"
    by (simp add: simple_test_map_1000_def)

  lemma "dom simple_test_map_1000 = {0 .. 999}"
    apply (simp add: upto_rec1 flip: set_upto)
    by (simp only: simple_test_map_1000_domain set_simps)

  lemma
    "ran simple_test_map_1000 =
     set ([[x] | x \<leftarrow> ''0123456789''] @
          [[x, y] | x \<leftarrow> ''123456789'', y \<leftarrow> ''0123456789''] @
          [[x, y, z] | x \<leftarrow> ''123456789'', y \<leftarrow> ''0123456789'', z \<leftarrow> ''0123456789''])"
    apply simp
    by (simp only: simple_test_map_1000_range set_simps)
end



section \<open>Optimising an existing mapping\<close>

experiment begin
  local_setup \<open>
    let
      val map_def =
          fold (fn i => fn m =>
                @{term "fun_upd :: (int \<Rightarrow> string option) \<Rightarrow> int \<Rightarrow> string option \<Rightarrow> (int \<Rightarrow> string option)"} $
                  m $ HOLogic.mk_number @{typ int} i $
                  (@{term "Some :: string \<Rightarrow> string option"} $ HOLogic.mk_string (string_of_int i)))
               (0 upto 100 - 1) @{term "Map.empty :: int \<Rightarrow> string option"};
      val name = Binding.name "slow_map";
    in
      Local_Theory.define
        ((name, NoSyn), ((Thm.def_binding name, []), map_def))
      #> snd
    end
  \<close>
  thm slow_map_def

  local_setup \<open>
    create_int_map "fast_map" 100 @{typ int}
  \<close>

  lemma slow_map_alt_def:
    "slow_map = fast_map"
    unfolding slow_map_def
    unfolding fast_map_to_lookup_list
    apply (simp only: FastMap.map_of_rev[symmetric] fast_map_keys_distinct)
    apply (simp only: rev.simps append.simps map_of.simps prod.sel)
    done

  lemma "slow_map 42 = Some ''42''"
    by (time_methods
          fast_map:      \<open>simp add: slow_map_alt_def fast_map_def\<close>
          direct_lookup: \<open>simp add: slow_map_alt_def fast_map_lookups\<close>
          slow_map:      \<open>simp add: slow_map_def\<close>)

  lemma "slow_map 100 = None"
    by (time_methods
          fast_map: \<open>simp add: slow_map_alt_def fast_map_def\<close>
          slow_map: \<open>simp add: slow_map_def\<close>)

  lemma "dom slow_map = {0 .. 99}"
    supply upto_rec1[simp]
    apply (simp flip: set_upto)
    (* Domain for slow_map gets generated in reverse order *)
    using set_rev[where xs="[0 .. 99] :: int list", simplified]

    by (time_methods
          fast_map: \<open>simp add: slow_map_alt_def fast_map_domain\<close>
          slow_map: \<open>simp add: slow_map_def\<close>)
end



section \<open>Simpset tests\<close>

definition my_id
  where
  "my_id x \<equiv> x"

lemma my_id_loop:
  "my_id x = my_id (Suc x) - 1"
  by (simp add: my_id_def)

declare my_id_loop[simp]
declare my_id_def[simp]

text \<open>With our faulty simpset, the key ordering solver gets into a loop.\<close>
local_setup \<open> fn ctxt =>
  (Timeout.apply (Time.fromSeconds 5) (
      FastMap.define_map (FastMap.name_opts_default "minimal_test_map")
        (List.tabulate (100, fn i => (HOLogic.mk_number @{typ nat} i,
                                      HOLogic.mk_string (string_of_int i))))
        @{term "my_id :: nat => nat"}
        @{thms}
        false
      ) ctxt;
   error "FastMap timeout test: shouldn't get here"
  )
  handle Timeout.TIMEOUT _ => ctxt
\<close>
declare my_id_loop[simp del]
declare my_id_def[simp del]


text \<open>The solver for injectivity of the key transformer can also loop.\<close>
lemma inj_my_id_loop[simp]:
  fixes x y :: nat
  shows "(my_id x = my_id y) = (my_id (x + x) = my_id (y + y))"
  by (auto simp: my_id_def)

lemma my_id_lessI:
  "(my_id x < my_id y) = (x < y)"
  by (simp add: my_id_def)

local_setup \<open> fn ctxt =>
  (Timeout.apply (Time.fromSeconds 5) (
      FastMap.define_map (FastMap.name_opts_default "minimal_test_map")
        (List.tabulate (100, fn i => (HOLogic.mk_number @{typ nat} i,
                                      HOLogic.mk_string (string_of_int i))))
        @{term "my_id :: nat => nat"}
        @{thms my_id_lessI}
        false
      ) ctxt;
   error "FastMap timeout test: shouldn't get here"
  )
  handle Timeout.TIMEOUT _ => ctxt
\<close>


text \<open>Manual simpset control.\<close>
lemma my_id_inj:
  "inj my_id"
  by (simp add: inj_def my_id_def)

local_setup \<open>
  FastMap.define_map (FastMap.name_opts_default "minimal_test_map")
    (List.tabulate (100, fn i => (HOLogic.mk_number @{typ nat} i,
                                  HOLogic.mk_string (string_of_int i))))
    @{term "my_id :: nat => nat"}
    @{thms my_id_lessI rel_simps my_id_inj[THEN inj_eq]}
    true
\<close>



section \<open>Test preserving user input\<close>

text \<open>
  Even when using the background simpset, FastMap should never simplify
  inside of the supplied keys and values.
\<close>

local_setup \<open>
  FastMap.define_map (FastMap.name_opts_default "preserve_input_test_map")
    (List.tabulate (100, fn i => (@{term "(+) :: nat \<Rightarrow> nat \<Rightarrow> nat"} $
                                    HOLogic.mk_number @{typ nat} i $
                                    @{term "0 :: nat"},
                                  @{term "rev :: string \<Rightarrow> string"} $
                                    HOLogic.mk_string (string_of_int i))))
    @{term "id :: nat => nat"}
    @{thms}
    false
\<close>

lemma "preserve_input_test_map (42 + 0) = Some (rev ''42'')"
  apply (fails \<open>simp; rule preserve_input_test_map_lookups\<close>)
  by (rule preserve_input_test_map_lookups)

lemma "42 + 0 \<in> dom preserve_input_test_map"
  apply (fails \<open>solves \<open>simp; unfold preserve_input_test_map_domain; intro list.set_intros\<close>\<close>)
  by (unfold preserve_input_test_map_domain; intro list.set_intros)

lemma "rev ''42'' \<in> ran preserve_input_test_map"
  apply (fails \<open>solves \<open>simp; unfold preserve_input_test_map_range; intro list.set_intros\<close>\<close>)
  by (unfold preserve_input_test_map_range; intro list.set_intros)



section \<open>Test @{command qualify}\<close>

locale qualified_map_test
qualify qualified_map_test

local_setup \<open>
  create_int_map "qualified_map" 100 @{typ nat}
\<close>

end_qualify

text \<open>Check that unqualified name doesn't exist\<close>
ML \<open>
  @{assert} (not (can dest_Const @{term qualified_map}));
  @{assert} (can dest_Const @{term qualified_map_test.qualified_map});
\<close>



section \<open>Test locales\<close>

context qualified_map_test begin

local_setup \<open>
  create_int_map "locale_map" 100 @{typ nat}
\<close>
thm locale_map_def

end

text \<open>Check that unqualified name doesn't exist\<close>
ML \<open>
  @{assert} (not (can dest_Const @{term locale_map}));
  @{assert} (can dest_Const @{term qualified_map_test.locale_map});
\<close>



section \<open>Test other key types\<close>

subsection \<open>Finite words\<close>

experiment begin
  local_setup \<open>
    create_int_map "word_map" 256 @{typ word32}
  \<close>

  lemma "word_map 42 = Some ''42''"
    by (rule word_map_lookups)

  lemma "word_map 999 = None"
    by (simp add: word_map_def)
end


subsection \<open>Strings\<close>

instantiation char :: ord begin
  definition[simp]: "(c::char) < d \<equiv> (of_char c :: nat) < of_char d"
  definition[simp]: "(c::char) \<le> d \<equiv> (of_char c :: nat) \<le> of_char d"
  instance ..
end

instantiation char :: linorder begin
  instance
    by intro_classes
       (auto simp: preorder_class.less_le_not_le linorder_class.linear)
end

experiment begin
  text \<open>
    Strings are not naturally in the @{class linorder} class.
    However, we can use a key transformer (@{const lexord_list})
    to use strings as @{class linorder} keys.
  \<close>
  local_setup \<open>
    FastMap.define_map (FastMap.name_opts_default "string_map")
      (List.tabulate (100, fn i => (HOLogic.mk_string (StringCvt.padLeft #"0" 3 (string_of_int i)),
                                    HOLogic.mk_number @{typ nat} i)))
      @{term "lexord_list :: string \<Rightarrow> char lexord_list"}
      @{thms}
      false
  \<close>

  lemma "string_map ''042'' = Some 42"
    by (rule string_map_lookups)

  lemma "string_map ''0123'' = None"
    by (simp add: string_map_def)

  text \<open>
    Notice that the domain and map theorems don't include the key
    transformer; it is merely an implementation detail.
  \<close>
  schematic_goal "(dom string_map = (?x :: string set))"
    by (rule string_map_domain)
  schematic_goal "string_map = map_of (?binds :: (string \<times> nat) list)"
    by (rule string_map_to_lookup_list)
end



section \<open>Small inputs\<close>
experiment begin
  text \<open>
    Note that the current interface doesn't support empty mappings,
    because it would have no input values to derive the correct map
    type. This tests 1-to-4-element mappings.
  \<close>

  local_setup \<open>
    create_int_map "small_test_map_1" 1 @{typ nat}
  \<close>
  lemma
    "small_test_map_1 \<equiv> FastMap.lookup_tree id (FastMap.Node 0 ''0'' FastMap.Leaf FastMap.Leaf)"
    by (rule small_test_map_1_def)
  lemma
    "small_test_map_1 = map_of [(0, ''0'')]"
    by (rule small_test_map_1_to_lookup_list)
  lemma
    "small_test_map_1 0 = Some ''0''"
    by (rule small_test_map_1_lookups)

  local_setup \<open>
      create_int_map "small_test_map_2" 2 @{typ nat}
      #>
      create_int_map "small_test_map_3" 3 @{typ nat}
      #>
      create_int_map "small_test_map_4" 4 @{typ nat}
  \<close>
end

end