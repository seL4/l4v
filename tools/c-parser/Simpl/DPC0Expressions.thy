(*
    Author:      Norbert Schirmer
    Maintainer:  Norbert Schirmer, norbert.schirmer at web de
    License:     LGPL
*)

section {* SHORTENED! Parallel expressions in DPC/Hoare. *}

theory DPC0Expressions imports Main begin

definition p_not :: "bool list => bool list"  ("\<not>\<^sub>p")
  where "p_not = map Not"

definition elem_wise :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list"
  where "elem_wise f xs ys = map (\<lambda> (x, y). f x y) (zip xs ys)"

definition p_and  :: "bool list => bool list => bool list"  (infixl "\<and>\<^sub>p"  35)
  where "p_and = elem_wise op&"

notation (ASCII)
  p_and  (infixl "pand"  35)

end
