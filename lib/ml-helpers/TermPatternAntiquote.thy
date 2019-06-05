(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

text \<open>
  term_pat: ML antiquotation for pattern matching on terms.

  See TermPatternAntiquote_Tests for examples and tests.
\<close>
theory TermPatternAntiquote imports
  Pure
begin

ML \<open>
structure Term_Pattern_Antiquote = struct

val quote_string = quote

(* typ matching; doesn't support matching on named TVars.
 * This is because each TVar is likely to appear many times in the pattern. *)
fun gen_typ_pattern (TVar _) = "_"
  | gen_typ_pattern (TFree (v, sort)) =
      "Term.TFree (" ^ quote_string v ^ ", [" ^ commas (map quote_string sort) ^ "])"
  | gen_typ_pattern (Type (typ_head, args)) =
      "Term.Type (" ^ quote_string typ_head ^ ", [" ^ commas (map gen_typ_pattern args) ^ "])"

(* term matching; does support matching on named (non-dummy) Vars.
 * The ML var generated will be identical to the Var name except in
 * indexed names like "?v1.2", which creates the var "v12". *)
fun gen_term_pattern (Var (("_dummy_", _), _)) = "_"
  | gen_term_pattern (Var ((v, 0), _)) = v
  | gen_term_pattern (Var ((v, n), _)) = v ^ string_of_int n
  | gen_term_pattern (Const (n, typ)) =
      "Term.Const (" ^ quote_string n ^ ", " ^ gen_typ_pattern typ ^ ")"
  | gen_term_pattern (Free (n, typ)) =
      "Term.Free (" ^ quote_string n ^ ", " ^ gen_typ_pattern typ ^ ")"
  | gen_term_pattern (t as f $ x) =
      (* (read_term_pattern "_") "helpfully" generates a dummy var that is
       * applied to all bound vars in scope. We go back and remove them. *)
      let fun default () = "(" ^ gen_term_pattern f ^ " $ " ^ gen_term_pattern x ^ ")";
      in case strip_comb t of
             (h as Var (("_dummy_", _), _), bs) =>
               if forall is_Bound bs then gen_term_pattern h else default ()
           | _ => default () end
  | gen_term_pattern (Abs (_, typ, t)) =
      "Term.Abs (_, " ^ gen_typ_pattern typ ^ ", " ^ gen_term_pattern t ^ ")"
  | gen_term_pattern (Bound n) = "Bound " ^ string_of_int n

(* Create term pattern. All Var names must be distinct in order to generate ML variables. *)
fun term_pattern_antiquote ctxt s =
  let val pat = Proof_Context.read_term_pattern ctxt s
      val add_var_names' = fold_aterms (fn Var (v, _) => curry (::) v | _ => I);
      val vars = add_var_names' pat [] |> filter (fn (n, _) => n <> "_dummy_")
      val _ = if vars = distinct (=) vars then () else
                raise TERM ("Pattern contains duplicate vars", [pat])
  in "(" ^ gen_term_pattern pat ^ ")" end

end;
val _ = Context.>> (Context.map_theory (
    ML_Antiquotation.inline @{binding "term_pat"}
      ((Args.context -- Scan.lift Args.embedded_inner_syntax)
         >> uncurry Term_Pattern_Antiquote.term_pattern_antiquote)))
\<close>

end
