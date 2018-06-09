(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*
   Decompose a meta-conjunction as a proper fact (list of theorems)
*)

theory Conjuncts
imports Main
begin

ML\<open>

structure Conjuncts =
struct

local

  structure Data = Generic_Data
  (
    type T = thm;
    val empty: T = Drule.dummy_thm;
    val extend = I;
    val merge : T * T -> T = (K Drule.dummy_thm);
  );

  fun elim_conjuncts thm =
    case try Conjunction.elim thm of
    SOME (thm', thm'') => elim_conjuncts thm' @ elim_conjuncts thm''
    | NONE => if Thm.prop_of thm = Thm.prop_of (Drule.dummy_thm) then [] else [thm]

  in

  val _ = Context.>> (Context.map_theory (
    (Attrib.setup @{binding "conjuncts"}
      (Scan.lift (Args.mode "accumulate") >> (fn acc =>
        if acc then
        Thm.declaration_attribute (Data.map o (fn x => fn y => Conjunction.intr y x))
        else
        Thm.declaration_attribute Data.put))
      "add meta_conjuncts to \"conjuncts\" named theorem") #>
    Global_Theory.add_thms_dynamic (@{binding "conjuncts"}, elim_conjuncts o Data.get)))

end

end

\<close>

notepad begin

  fix A B C D
  assume ABC[conjuncts]: "(A &&& B) &&& (B &&& C)"
  note ABC' = conjuncts

  have "A" by (rule ABC')
  have "B" by (rule \<open>B\<close>)
  have "C" by (rule ABC'(4))

  (* Disclaimer: only the last declared lemma is stored *)
  assume ABCD[conjuncts]: "A &&& B" "C &&& D"
  note CD = conjuncts

  have "A" by ((rule CD)?,rule ABC')
  have "C" by (rule CD)



  note ABCD(1)[conjuncts]
  note AB = conjuncts

  note ABCD(2)[conjuncts]
  note CD = conjuncts

  (* We can accumulate multi-thms, we just need to clear conjuncts first *)
  note [[conjuncts]]

  note ABCD[conjuncts (accumulate)]
  note ABCD' = conjuncts

end

end
