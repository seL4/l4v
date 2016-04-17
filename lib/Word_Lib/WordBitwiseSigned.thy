theory WordBitwiseSigned imports
  Aligned
  "~~/src/HOL/Library/Prefix_Order"
begin

ML {* fun bw_tac_signed ctxt = let
  val (ss, sss) = Word_Bitwise_Tac.expand_word_eq_sss
  val sss = nth_map 2 (fn ss => put_simpset ss ctxt addsimps @{thms len_signed} |> simpset_of) sss
in
    foldr1 (op THEN_ALL_NEW)
      ((CHANGED o safe_full_simp_tac (put_simpset ss ctxt)) ::
        map (fn ss => safe_full_simp_tac (put_simpset ss ctxt)) sss)
  end;
*}

method_setup word_bitwise_signed =
  {* Scan.succeed (fn ctxt => Method.SIMPLE_METHOD (bw_tac_signed ctxt 1))  *}
  "decomposer for word equalities and inequalities into bit propositions"

end
