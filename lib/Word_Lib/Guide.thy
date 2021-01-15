(*
 * Copyright Florian Haftmann
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*<*)
theory Guide
  imports Word_Lib_Sumo
begin

hide_const (open) Generic_set_bit.set_bit

(*>*)
section \<open>A short overview over bit operations and word types\<close>

subsection \<open>Basic theories and key ideas\<close>

text \<open>
  When formalizing bit operations, it is tempting to represent
  bit values as explicit lists over a binary type. This however
  is a bad idea, mainly due to the inherent ambiguities in
  representation concerning repeating leading bits.

  Hence this approach avoids such explicit lists altogether
  following an algebraic path:

    \<^item> Bit values are represented by numeric types: idealized
      unbounded bit values can be represented by type \<^typ>\<open>int\<close>,
      bounded bit values by quotient types over \<^typ>\<open>int\<close>, aka \<^typ>\<open>'a word\<close>.

    \<^item> (A special case are idealized unbounded bit values ending
      in @{term [source] 0} which can be represented by type \<^typ>\<open>nat\<close> but
      only support a restricted set of operations).

  The most fundamental ideas are developed in theory \<^theory>\<open>HOL.Parity\<close>
  (which is part of \<^theory>\<open>Main\<close>):

    \<^item> Multiplication by \<^term>\<open>2 :: int\<close> is a bit shift to the left and

    \<^item> Division by \<^term>\<open>2 :: int\<close> is a bit shift to the right.

    \<^item> Concerning bounded bit values, iterated shifts to the left
    may result in eliminating all bits by shifting them all
    beyond the boundary.  The property \<^prop>\<open>(2 :: int) ^ n \<noteq> 0\<close>
    represents that \<^term>\<open>n\<close> is \<^emph>\<open>not\<close> beyond that boundary.

    \<^item> The projection on a single bit is then @{thm [mode=iff] bit_iff_odd [where ?'a = int, no_vars]}.

    \<^item> This leads to the most fundamental properties of bit values:

      \<^item> Equality rule: @{thm [display, mode=iff] bit_eq_iff [where ?'a = int, no_vars]}

      \<^item> Induction rule: @{thm [display, mode=iff] bits_induct [where ?'a = int, no_vars]}

    \<^item> Characteristic properties \<^prop>\<open>bit (f x) n \<longleftrightarrow> P x n\<close>
      are available in fact collection \<^text>\<open>bit_simps\<close>.

  On top of this, the following generic operations are provided
  after import of theory \<^theory>\<open>HOL-Library.Bit_Operations\<close>:

    \<^item> Singleton \<^term>\<open>n\<close>th bit: \<^term>\<open>(2 :: int) ^ n\<close>

    \<^item> Bit mask upto bit \<^term>\<open>n\<close>: @{thm mask_eq_exp_minus_1 [where ?'a = int, no_vars]}

    \<^item> Left shift: @{thm push_bit_eq_mult [where ?'a = int, no_vars]}

    \<^item> Right shift: @{thm drop_bit_eq_div [where ?'a = int, no_vars]}

    \<^item> Truncation: @{thm take_bit_eq_mod [where ?'a = int, no_vars]}

    \<^item> Negation: @{thm [mode=iff] bit_not_iff [where ?'a = int, no_vars]}

    \<^item> And: @{thm [mode=iff] bit_and_iff [where ?'a = int, no_vars]}

    \<^item> Or: @{thm [mode=iff] bit_or_iff [where ?'a = int, no_vars]}

    \<^item> Xor: @{thm [mode=iff] bit_xor_iff [where ?'a = int, no_vars]}

    \<^item> Set a single bit: @{thm set_bit_def [where ?'a = int, no_vars]}

    \<^item> Unset a single bit: @{thm unset_bit_def [where ?'a = int, no_vars]}

    \<^item> Flip a single bit: @{thm flip_bit_def [where ?'a = int, no_vars]}

    \<^item> Signed truncation, or modulus centered around \<^term>\<open>0::int\<close>:
        @{thm [display] signed_take_bit_def [where ?'a = int, no_vars]}

    \<^item> (Bounded) conversion from and to a list of bits:
        @{thm [display] horner_sum_bit_eq_take_bit [where ?'a = int, no_vars]}

  Proper word types are introduced in theory \<^theory>\<open>HOL-Library.Word\<close>, with
  the following specific operations:

    \<^item> Standard arithmetic:
        @{term \<open>(+) :: 'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>},
        @{term \<open>uminus :: 'a::len word \<Rightarrow> 'a word\<close>},
        @{term \<open>(-) :: 'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>},
        @{term \<open>(*) :: 'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>},
        @{term \<open>0 :: 'a::len word\<close>}, @{term \<open>1 :: 'a::len word\<close>}, numerals etc.

    \<^item> Standard bit operations: see above.

    \<^item> Conversion with unsigned interpretation of words:

        \<^item> @{term [source] \<open>unsigned :: 'a::len word \<Rightarrow> 'b::semiring_1\<close>}

        \<^item> Important special cases as abbreviations:

            \<^item> @{term [source] \<open>unat :: 'a::len word \<Rightarrow> nat\<close>}

            \<^item> @{term [source] \<open>uint :: 'a::len word \<Rightarrow> int\<close>}

            \<^item> @{term [source] \<open>ucast :: 'a::len word \<Rightarrow> 'b::len word\<close>}

    \<^item> Conversion with signed interpretation of words:

        \<^item> @{term [source] \<open>signed :: 'a::len word \<Rightarrow> 'b::ring_1\<close>}

        \<^item> Important special cases as abbreviations:

            \<^item> @{term [source] \<open>sint :: 'a::len word \<Rightarrow> int\<close>}

            \<^item> @{term [source] \<open>scast :: 'a::len word \<Rightarrow> 'b::len word\<close>}

    \<^item> Operations with unsigned interpretation of words:

        \<^item> @{thm [mode=iff] word_le_nat_alt [no_vars]}

        \<^item> @{thm [mode=iff] word_less_nat_alt [no_vars]}

        \<^item> @{thm unat_div_distrib [no_vars]}

        \<^item> @{thm unat_drop_bit_eq [no_vars]}

        \<^item> @{thm unat_mod_distrib [no_vars]}

        \<^item> @{thm [mode=iff] udvd_iff_dvd [no_vars]}

    \<^item> Operations with signed interpretation of words:

        \<^item> @{thm [mode=iff] word_sle_eq [no_vars]}

        \<^item> @{thm [mode=iff] word_sless_alt [no_vars]}

        \<^item> @{thm sint_signed_drop_bit_eq [no_vars]}

    \<^item> Rotation and reversal:

        \<^item> @{term [source] \<open>word_rotl :: nat \<Rightarrow> 'a::len word \<Rightarrow> 'a word\<close>}

        \<^item> @{term [source] \<open>word_rotr :: nat \<Rightarrow> 'a::len word \<Rightarrow> 'a word\<close>}

        \<^item> @{term [source] \<open>word_roti :: int \<Rightarrow> 'a::len word \<Rightarrow> 'a word\<close>}

        \<^item> @{term [source] \<open>word_reverse :: 'a::len word \<Rightarrow> 'a word\<close>}

    \<^item> Concatenation: @{term [source, display] \<open>word_cat :: 'a::len word \<Rightarrow> 'b::len word \<Rightarrow> 'c::len word\<close>}

  For proofs about words the following default strategies are applicable:

    \<^item> Using bit extensionality (facts \<^text>\<open>bit_eq_iff\<close>, \<^text>\<open>bit_eqI\<close>; fact
      collection \<^text>\<open>bit_simps\<close>).

    \<^item> Using the @{method transfer} method.
\<close>

subsection \<open>More library theories\<close>

text \<open>
  Note: currently, the theories listed here are hardly separate
  entities since they import each other in various ways.
  Always inspect them to understand what you pull in if you
  want to import one.

    \<^descr>[Syntax]

      \<^descr>[\<^theory>\<open>Word_Lib.Hex_Words\<close>]
        Printing word numerals as hexadecimal numerals.

      \<^descr>[\<^theory>\<open>Word_Lib.Type_Syntax\<close>]
        Pretty type-sensitive syntax for cast operations.

      \<^descr>[\<^theory>\<open>Word_Lib.Word_Syntax\<close>]
        Specific ASCII syntax for prominent bit operations on word.

    \<^descr>[Proof tools]

      \<^descr>[\<^theory>\<open>Word_Lib.Norm_Words\<close>]
        Rewriting word numerals to normal forms.

      \<^descr>[\<^theory>\<open>Word_Lib.Bitwise\<close>]
        Method @{method word_bitwise} decomposes word equalities and inequalities into bit propositions.

      \<^descr>[\<^theory>\<open>Word_Lib.Word_EqI\<close>]
        Method @{method word_eqI_solve} decomposes word equalities and inequalities into bit propositions.

    \<^descr>[Operations]

      \<^descr>[\<^theory>\<open>Word_Lib.Signed_Division_Word\<close>]

        Signed division on word:

          \<^item> @{term [source] \<open>(sdiv) :: 'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>}

          \<^item> @{term [source] \<open>(smod) :: 'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>}

      \<^descr>[\<^theory>\<open>Word_Lib.Aligned\<close>] \

          \<^item> @{thm [mode=iff] is_aligned_iff_udvd [no_vars]}

      \<^descr>[\<^theory>\<open>Word_Lib.Least_significant_bit\<close>]

        The least significant bit as an alias:
        @{thm [mode=iff] lsb_odd [where ?'a = int, no_vars]}

      \<^descr>[\<^theory>\<open>Word_Lib.Most_significant_bit\<close>]

        The most significant bit:

          \<^item> @{thm [mode=iff] msb_int_def [of k]}

          \<^item> @{thm [mode=iff] word_msb_sint [no_vars]}

          \<^item> @{thm [mode=iff] msb_word_iff_sless_0 [no_vars]}

          \<^item> @{thm [mode=iff] msb_word_iff_bit [no_vars]}

      \<^descr>[\<^theory>\<open>Word_Lib.Traditional_Infix_Syntax\<close>]

        Clones of existing operations decorated with
        traditional syntax:

          \<^item> @{thm test_bit_eq_bit [no_vars]}

          \<^item> @{thm shiftl_eq_push_bit [no_vars]}

          \<^item> @{thm shiftr_eq_drop_bit [no_vars]}

          \<^item> @{thm sshiftr_eq [no_vars]}

      \<^descr>[\<^theory>\<open>Word_Lib.Next_and_Prev\<close>] \

          \<^item> @{thm word_next_unfold [no_vars]}

          \<^item> @{thm word_prev_unfold [no_vars]}

      \<^descr>[\<^theory>\<open>Word_Lib.Enumeration_Word\<close>]

        More on explicit enumeration of word types.

      \<^descr>[\<^theory>\<open>Word_Lib.More_Word_Operations\<close>]

        Even more operations on word.

    \<^descr>[Types]

      \<^descr>[\<^theory>\<open>Word_Lib.Signed_Words\<close>]

          Formal tagging of word types with a \<^text>\<open>signed\<close> marker.

    \<^descr>[Lemmas]

      \<^descr>[\<^theory>\<open>Word_Lib.More_Word\<close>]

          More lemmas on words.

      \<^descr>[\<^theory>\<open>Word_Lib.Word_Lemmas\<close>]

          More lemmas on words, covering many other theories mentioned here.

    \<^descr>[Words of fixed length]

      \<^descr>[\<^theory>\<open>Word_Lib.Word_8\<close>]

          for 8-bit words.

      \<^descr>[\<^theory>\<open>Word_Lib.Word_16\<close>]

          for 16-bit words.

      \<^descr>[\<^theory>\<open>Word_Lib.Word_32\<close>]

          for 32-bit words.

      \<^descr>[\<^theory>\<open>Word_Lib.Word_64\<close>]

          for 64-bit words.
\<close>


subsection \<open>More library sessions\<close>

text \<open>
  \<^descr>[\<^text>\<open>Native_Word\<close>] Makes machine words and machine arithmetic available for code generation.
  It provides a common abstraction that hides the differences between the different target languages.
  The code generator maps these operations to the APIs of the target languages.
\<close>

subsection \<open>Legacy theories\<close>

text \<open>
  The following theories contain material which has been
  factored out since it is not recommended to use it in
  new applications, mostly because matters can be expressed
  succinctly using already existing operations.

  This section gives some indication how to migrate away
  from those theories.  However theorem coverage may still
  be terse in some cases.

  \<^descr>[\<^theory>\<open>Word_Lib.Word_Lib_Sumo\<close>]

    An entry point importing any relevant theory in that session.  Intended
    for backward compatibility: start importing this theory when
    migrating applications to Isabelle2021, and later sort out
    what you really need.

  \<^descr>[\<^theory>\<open>Word_Lib.Generic_set_bit\<close>]

    Kind of an alias: @{thm set_bit_eq [no_vars]}

  \<^descr>[\<^theory>\<open>Word_Lib.Typedef_Morphisms\<close>]

    A low-level extension to HOL typedef providing
    conversions along type morphisms.  The @{method transfer} method
    seems to be sufficient for most applications though.

  \<^descr>[\<^theory>\<open>Word_Lib.Bit_Comprehension\<close>]

    Comprehension syntax for bit values over predicates
    \<^typ>\<open>nat \<Rightarrow> bool\<close>.  For \<^typ>\<open>'a::len word\<close>, straightforward
    alternatives exist; difficult to handle for \<^typ>\<open>int\<close>.

  \<^descr>[\<^theory>\<open>Word_Lib.Reversed_Bit_Lists\<close>]

    Representation of bit values as explicit list in
    \<^emph>\<open>reversed\<close> order.

    This should rarely be necessary: the \<^const>\<open>bit\<close> projection
    should be sufficient in most cases.  In case explicit lists
    are needed, existing operations can be used:

    @{thm [display] horner_sum_bit_eq_take_bit [where ?'a = int, no_vars]}

  \<^descr>[\<^theory>\<open>Word_Lib.Many_More\<close>]

    Collection of operations and theorems which are kept for backward
    compatibility and not used in other theories in session \<^text>\<open>Word_Lib\<close>.
\<close>

(*<*)
end
(*>*)
