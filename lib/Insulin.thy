(*
 * @TAG(NICTA_BSD)
 *
 * Insulin.thy: regulate sugar in terms, thms and proof goals.
 *
 * Usage:
 * This theory provides the improper commands
 *   desugar_term <term> <str> <str>...
 *   desugar_thm <thm> <str> <str>...
 *   desugar_goal [<goal_num>] <str> <str>...
 * which print the term, thm or subgoal(s) with the syntax <str> replaced by the
 * underlying constants.
 *
 * For example:
 *   > thm fun_upd_apply
 *   (?f(?x := ?y)) ?z = (if ?z = ?x then ?y else ?f ?z)
 *
 * But what is this ":="?
 *   > desugar_thm fun_upd_apply ":="
 *   Fun.fun_upd ?f ?x ?y ?z = (if ?z = ?x then ?y else ?f ?z)
 *
 * Remove all sugar:
 *   > desugar_thm fun_upd_apply "=" "if"
 *   HOL.eq (Fun.fun_upd ?f ?x ?y ?z)
 *     (HOL.If (HOL.eq ?z ?x) ?y (?f ?z))
 *
 * Desugar only one subterm:
 *   > desugar_thm fun_upd_apply "?z = ?x"
 *   (?f(?x := ?y)) ?z = (if HOL.eq ?z ?x then ?y else ?f ?z)
 *
 * Another example (l4v libraries):
 *   > desugar_term "\<lbrace> P and Q \<rbrace> f \<lbrace> \<lambda>r _. r \<in> {0..<5} \<rbrace>!" "\<lbrace>"
 *   NonDetMonad.validNF (P and Q) f (\<lambda>r _. r \<in> {0\<Colon>'b..<5\<Colon>'b})
 *
 * Desugar multiple operators:
 *   > desugar_term "\<lbrace> P and Q \<rbrace> f \<lbrace> \<lambda>r _. r \<in> {0..<5} \<rbrace>!" "\<lbrace>" "and" ".."
 *   NonDetMonad.validNF (Lib.pred_conj P Q) f
 *     (\<lambda>r _. r \<in> Set_Interval.ord_class.atLeastLessThan (0\<Colon>'b) (5\<Colon>'b))
 *
 *
 * Known problems:
 * - The output may have bad indentation. This is because the mangled constant
 *   name has a different length compared to the original.
 *
 * - May not work with exotic syntax translations (e.g. ML-defined syntax).
 *
 * - May not work with terms that contain the magic string "dsfjdssdfsd".
 *
 * - Naive algorithm, takes \<approx>quadratic time.
 *)

theory Insulin imports HOL
  keywords "desugar_term" "desugar_thm" "desugar_goal" :: diag
begin

(*
 * Isabelle syntax rules are invoked based on constants appearing in a term.
 * Insulin works by replacing each constant with a free variable, which is
 * displayed without triggering syntax translations.
 * It tries each constant in the term to find the ones that produce a given
 * syntax fragment, then limits the replacement to those constants only.
 *
 * The tricky bit is determining which constants contribute to the proscribed
 * syntax fragment. We do this somewhat naively by trying each constant
 * one-at-a-time, then replacing those which reduce the *number of occurrences*
 * of the proscribed syntax.
 * Since syntax translations are arbitrary, it is possible that the final result
 * still contains unwanted syntax, so we iterate this process.
 *
 * This one-at-a-time approach fails for syntax that can be triggered by any of
 * several constants in a term. I don't know any examples of this, though.
 *)

ML {*
structure Insulin = struct

val desugar_random_tag = "dsfjdssdfsd"
fun fresh_substring s = let
  fun next [] = [#"a"]
    | next (#"z" :: n) = #"a" :: next n
    | next (c :: n) = Char.succ c :: n
  fun fresh n = let
    val ns = String.implode n
    in if String.isSubstring ns s then fresh (next n) else ns end
  in fresh [#"a"] end

(* Encode a (possibly qualified) constant name as an (expected-to-be-)unused name.
 * The encoded name will be treated as a free variable. *)
fun escape_const c = let
  val delim = fresh_substring c
  in desugar_random_tag ^ delim ^ "_" ^
       String.concat (case Long_Name.explode c of
                        (a :: b :: xs) => a :: map (fn x => delim ^ x) (b :: xs)
                      | xs => xs)
  end
(* Decode; if it fails, return input string *)
fun unescape_const s =
  if not (String.isPrefix desugar_random_tag s) then s else
  let val cs = String.extract (s, String.size desugar_random_tag, NONE) |> String.explode
      fun readDelim d (#"_" :: cs) = (d, cs)
        | readDelim d (c :: cs) = readDelim (d @ [c]) cs
      val (delim, cs) = readDelim [] cs
      val delimlen = length delim
      fun splitDelim name cs =
            if take delimlen cs = delim then name :: splitDelim [] (drop delimlen cs)
              else case cs of [] => if null name then [] else [name]
                            | (c::cs) => splitDelim (name @ [c]) cs
      val names = splitDelim [] cs
  in Long_Name.implode (map String.implode names) end
  handle Match => s

fun dropQuotes s = if String.isPrefix "\"" s andalso String.isSuffix "\"" s
                       then String.substring (s, 1, String.size s - 2) else s

(* Translate markup from consts-encoded-as-free-variables to actual consts *)
fun desugar_reconst ctxt (tr as XML.Elem ((tag, attrs), children))
  = if tag = "fixed" orelse tag = "intensify" then
      let val s = XML.content_of [tr]
          val name = unescape_const s
          fun get_entity_attrs (XML.Elem (("entity", attrs), _)) = SOME attrs
            | get_entity_attrs (XML.Elem (_, body)) =
                find_first (K true) (List.mapPartial get_entity_attrs body)
            | get_entity_attrs (XML.Text _) = NONE
      in
        if name = s then tr else
          (* try to look up the const's info *)
          case Syntax.read_term ctxt name
               |> Thm.cterm_of ctxt
               |> Proof_Display.pp_cterm (fn _ => Proof_Context.theory_of ctxt)
               |> Pretty.string_of
               |> dropQuotes
               |> YXML.parse
               |> get_entity_attrs of
              SOME attrs =>
                XML.Elem (("entity", attrs), [XML.Text name])
            | _ =>
                XML.Elem (("entity", [("name", name), ("kind", "constant")]),
                          [XML.Text name]) end
    else XML.Elem ((tag, attrs), map (desugar_reconst ctxt) children)
  | desugar_reconst _ (t as XML.Text _) = t

fun term_to_string ctxt no_markup =
  Syntax.pretty_term ctxt
  #> Pretty.string_of
  #> YXML.parse_body
  #> map (desugar_reconst ctxt)
  #> (if no_markup then XML.content_of else YXML.string_of_body)
  #> dropQuotes

(* Strip constant names from a term.
 * A term is split to a "term_unconst" and a "string list" of the
 * const names in tree preorder. *)
datatype term_unconst =
    UCConst of typ |
    UCAbs of string * typ * term_unconst |
    UCApp of term_unconst * term_unconst |
    UCVar of term

fun is_ident_char c = Char.isAlphaNum c orelse c = #"_" orelse c = #"." orelse c = #"'"

fun term_to_unconst (Const (name, typ)) =
    (* some magical constants have strange names, such as ==>; ignore them *)
      if forall is_ident_char (String.explode name) then (UCConst typ, [name])
        else (UCVar (Const (name, typ)), [])
  | term_to_unconst (Abs (var, typ, body)) = let
      val (body', consts) = term_to_unconst body
      in (UCAbs (var, typ, body'), consts) end
  | term_to_unconst (f $ x) = let
      val (f', consts1) = term_to_unconst f
      val (x', consts2) = term_to_unconst x
      in (UCApp (f', x'), consts1 @ consts2) end
  | term_to_unconst t = (UCVar t, [])

fun term_from_unconst (UCConst typ) (name :: consts) =
      ((if unescape_const name = name then Const else Free) (name, typ), consts)
  | term_from_unconst (UCAbs (var, typ, body)) consts = let
      val (body', consts) = term_from_unconst body consts
      in (Abs (var, typ, body'), consts) end
  | term_from_unconst (UCApp (f, x)) consts = let
      val (f', consts) = term_from_unconst f consts
      val (x', consts) = term_from_unconst x consts
      in (f' $ x', consts) end
  | term_from_unconst (UCVar v) consts = (v, consts)

(* Count occurrences of bad strings.
 * Bad strings are allowed to overlap, but for each string, non-overlapping occurrences are counted.
 * Note that we search on string lists, to deal with symbols correctly. *)
fun count_matches (haystack: ''a list) (needles: ''a list list): int list =
  let (* Naive algorithm. Probably ok, given that we're calling the term printer a lot elsewhere. *)
      fun try_match xs [] = SOME xs
        | try_match (x::xs) (y::ys) = if x = y then try_match xs ys else NONE
        | try_match _ _ = NONE
      fun count [] = 0
        | count needle = let
            fun f [] occs = occs
              | f haystack' occs = case try_match haystack' needle of
                                       NONE => f (tl haystack') occs
                                     | SOME tail => f tail (occs + 1)
            in f haystack 0 end
  in map count needles end

fun focus_list (xs: 'a list): ('a list * 'a * 'a list) list =
  let fun f head x [] = [(head, x, [])]
        | f head x (tail as x'::tail') = (head, x, tail) :: f (head @ [x]) x' tail'
  in case xs of [] => []
              | (x::xs) => f [] x xs end

(* Do one rewrite pass: try every constant in sequence, then collect the ones which
 * reduced the occurrences of bad strings *)
fun rewrite_pass ctxt (t: term) (improved: term -> bool) (escape_const: string -> string): term =
  let val (ucterm, consts) = term_to_unconst t
      fun rewrite_one (prev, const, rest) =
            let val (t', []) = term_from_unconst ucterm (prev @ [escape_const const] @ rest)
            in improved t' end
      val consts_to_rewrite = focus_list consts |> map rewrite_one
      val consts' = map2 (fn rewr => fn const => if rewr then escape_const const else const) consts_to_rewrite consts
      val (t', []) = term_from_unconst ucterm consts'
  in t' end

(* Do rewrite passes until bad strings are gone or no more rewrites are possible *)
fun desugar ctxt (t0: term) (bads: string list): term =
  let fun count t = count_matches (Symbol.explode (term_to_string ctxt true t)) (map Symbol.explode bads)
      val _ = if null bads then error "Nothing to desugar" else ()
      fun rewrite t = let
        val counts0 = count t
        fun improved t' = exists op< (count t' ~~ counts0)
        val t' = rewrite_pass ctxt t improved escape_const
        in if forall (fn c => c = 0) (count t') (* bad strings gone *)
           then t'
           else if t = t' (* no more rewrites *)
             then let
               val bads' = filter (fn (c, _) => c > 0) (counts0 ~~ bads) |> map snd
               val _ = warning ("Sorry, failed to desugar " ^ commas_quote bads')
               in t end
             else rewrite t'
         end
  in rewrite t0 end

fun span _ [] = ([],[])
  | span p (a::s) =
      if p a then let val (y, n) = span p s in (a::y, n) end else ([], a::s)

fun check_desugar s = let
  fun replace [] = []
    | replace xs =
        if take (String.size desugar_random_tag) xs = String.explode desugar_random_tag
          then case span is_ident_char xs of
                   (v, xs) => String.explode (unescape_const (String.implode v)) @ replace xs
          else hd xs :: replace (tl xs)
  val desugar_string = String.implode o replace o String.explode
  in if not (String.isSubstring desugar_random_tag s) then s
       else desugar_string s end

fun desugar_term ctxt t s =
  desugar ctxt t s |> term_to_string ctxt false |> check_desugar

fun desugar_thm ctxt thm s = desugar_term ctxt (Thm.prop_of thm) s

fun desugar_goal ctxt goal n s = let
  val subgoals = goal |> Thm.prems_of
  val subgoals = if n = 0 then subgoals else
                 if n < 1 orelse n > length subgoals then
                      (* trigger error *) [Logic.get_goal (Thm.term_of (Thm.cprop_of goal)) n]
                 else [nth subgoals (n - 1)]
  val results = map (fn t => (NONE, desugar_term ctxt t s)
                             handle ex as TERM _ => (SOME ex, term_to_string ctxt false t))
                    subgoals
  in if null results
        then error "No subgoals to desugar"
     else if forall (Option.isSome o fst) results
        then raise the (fst (hd results))
     else map snd results
  end

end
*}

ML {*
Outer_Syntax.command @{command_keyword "desugar_term"}
  "term str str2... -> desugar str in term"
  (Parse.term -- Scan.repeat1 Parse.string >> (fn (t, s) =>
    Toplevel.keep (fn state => let val ctxt = Toplevel.context_of state in
      Insulin.desugar_term ctxt (Syntax.read_term ctxt t) s
      |> writeln end)))
*}

ML {*
Outer_Syntax.command @{command_keyword "desugar_thm"}
  "thm str str2... -> desugar str in thm"
  (Parse.thm -- Scan.repeat1 Parse.string >> (fn (t, s) =>
    Toplevel.keep (fn state => let val ctxt = Toplevel.context_of state in
      Insulin.desugar_thm ctxt (Attrib.eval_thms ctxt [t] |> hd) s |> writeln end)))
*}

ML {*
fun print_subgoals (x::xs) n = (writeln (Int.toString n ^ ". " ^ x); print_subgoals xs (n+1))
  | print_subgoals [] _ = ();
Outer_Syntax.command @{command_keyword "desugar_goal"}
  "goal_num str str2... -> desugar str in goal"
  (Scan.option Parse.int -- Scan.repeat1 Parse.string >> (fn (n, s) =>
    Toplevel.keep (fn state => let val ctxt = Toplevel.context_of state in
      Insulin.desugar_goal ctxt (Toplevel.proof_of state |> Proof.raw_goal |> #goal) (Option.getOpt (n, 0)) s
      |> (fn xs => case xs of
            [x] => writeln x
            | _ => print_subgoals xs 1) end)))
*}

end