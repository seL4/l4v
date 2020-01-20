(*
 *
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)
theory Match_Abbreviation

imports Main

keywords "match_abbreviation" :: thy_decl
  and "reassoc_thm" :: thy_decl

begin

text \<open>Splicing components of terms and saving as abbreviations.
See the example at the bottom for explanation/documentation.
\<close>

ML \<open>
structure Match_Abbreviation = struct

fun app_cons_dummy cons x y
  = Const (cons, dummyT) $ x $ y

fun lazy_lam x t = if Term.exists_subterm (fn t' => t' aconv x) t
    then lambda x t else t

fun abs_dig_f ctxt lazy f (Abs (nm, T, t))
  = let
    val (nms, ctxt) = Variable.variant_fixes [nm] ctxt
    val x = Free (hd nms, T)
    val t = betapply (Abs (nm, T, t), x)
    val t' = f ctxt t
  in if lazy then lazy_lam x t' else lambda x t' end
  | abs_dig_f _ _ _ t = raise TERM ("abs_dig_f: not abs", [t])

fun find_term1 ctxt get (f $ x)
  = (get ctxt (f $ x) handle Option => (find_term1 ctxt get f
        handle Option => find_term1 ctxt get x))
  | find_term1 ctxt get (a as Abs _)
  = abs_dig_f ctxt true (fn ctxt => find_term1 ctxt get) a
  | find_term1 ctxt get t = get ctxt t

fun not_found pat t = raise TERM ("pattern not found", [pat, t])

fun find_term ctxt get pat t = find_term1 ctxt get t
  handle Option => not_found pat t

fun lambda_frees_vars ctxt ord_t t = let
    fun is_free t = is_Free t andalso not (Variable.is_fixed ctxt (Term.term_name t))
    fun is_it t = is_free t orelse is_Var t
    val get = fold_aterms (fn t => if is_it t then insert (=) t else I)
    val all_vars = get ord_t []
    val vars = get t []
    val ord_vars = filter (member (=) vars) all_vars
  in fold lambda ord_vars t end

fun parse_pat_fixes ctxt fixes pats = let
    val (_, ctxt') = Variable.add_fixes
            (map (fn (b, _, _) => Binding.name_of b) fixes) ctxt
    val read_pats = Syntax.read_terms ctxt' pats
  in Variable.export_terms ctxt' ctxt read_pats end

fun add_reassoc name rhs fixes thms_info ctxt = let
    val thms = Attrib.eval_thms ctxt thms_info
    val rhs_pat = singleton (parse_pat_fixes ctxt fixes) rhs
      |> Thm.cterm_of ctxt
    val rew = Simplifier.rewrite (clear_simpset ctxt addsimps thms) rhs_pat
      |> Thm.symmetric
    val (_, ctxt) = Local_Theory.note ((name, []), [rew]) ctxt
    val pretty_decl = Pretty.block [Pretty.str (Binding.name_of name ^ ":\n"),
        Thm.pretty_thm ctxt rew]
  in Pretty.writeln pretty_decl; ctxt end

fun dig_f ctxt repeat adj (f $ x) = (adj ctxt (f $ x)
    handle Option => (dig_f ctxt repeat adj f
            $ (if repeat then (dig_f ctxt repeat adj x
                handle Option => x) else x)
        handle Option => f $ dig_f ctxt repeat adj x))
  | dig_f ctxt repeat adj (a as Abs _)
    = abs_dig_f ctxt false (fn ctxt => dig_f ctxt repeat adj) a
  | dig_f ctxt _ adj t = adj ctxt t

fun do_rewrite ctxt repeat rew_pair t = let
    val thy = Proof_Context.theory_of ctxt
    fun adj _ t = case Pattern.match_rew thy t rew_pair
      of NONE => raise Option | SOME (t', _) => t'
  in dig_f ctxt repeat adj t
    handle Option => not_found (fst rew_pair) t end

fun select_dig ctxt [] f t = f ctxt t
  | select_dig ctxt (p :: ps) f t = let
    val thy = Proof_Context.theory_of ctxt
    fun do_rec ctxt t = if Pattern.matches thy (p, t)
      then select_dig ctxt ps f t else raise Option
  in dig_f ctxt false do_rec t handle Option => not_found p t end

fun ext_dig_lazy ctxt f (a as Abs _)
  = abs_dig_f ctxt true (fn ctxt => ext_dig_lazy ctxt f) a
  | ext_dig_lazy ctxt f t = f ctxt t

fun report_adjust ctxt nm t = let
    val pretty_decl = Pretty.block [Pretty.str (nm ^ ", have:\n"),
        Syntax.pretty_term ctxt t]
  in Pretty.writeln pretty_decl; t end

fun do_adjust ctxt ((("select", []), [p]), fixes) t = let
    val p = singleton (parse_pat_fixes ctxt fixes) p
    val thy = Proof_Context.theory_of ctxt
    fun get _ t = if Pattern.matches thy (p, t) then t else raise Option
    val t = find_term ctxt get p t
  in report_adjust ctxt "Selected" t end
  | do_adjust ctxt ((("retype_consts", []), consts), []) t = let
    fun get_constname (Const (s, _)) = s
      | get_constname (Abs (_, _, t)) = get_constname t
      | get_constname (f $ _) = get_constname f
      | get_constname _ = raise Option
    fun get_constname2 t = get_constname t
      handle Option => raise TERM ("do_adjust: no constant", [t])
    val cnames = map (get_constname2 o Syntax.read_term ctxt) consts
      |> Symtab.make_set
    fun adj (Const (cn, T)) = if Symtab.defined cnames cn
        then Const (cn, dummyT) else Const (cn, T)
      | adj t = t
    val t = Syntax.check_term ctxt (Term.map_aterms adj t)
  in report_adjust ctxt "Adjusted types" t end
  | do_adjust ctxt (((r, in_selects), [from, to]), fixes) t = if
        r = "rewrite1" orelse r = "rewrite" then let
    val repeat = r <> "rewrite1"
    val sel_pats = map (fn (p, fixes) => singleton (parse_pat_fixes ctxt fixes) p)
        in_selects
    val rewrite_pair = case parse_pat_fixes ctxt fixes [from, to]
      of [f, t] => (f, t) | _ => error ("do_adjust: unexpected length")
    val t = ext_dig_lazy ctxt (fn ctxt => select_dig ctxt sel_pats
        (fn ctxt => do_rewrite ctxt repeat rewrite_pair)) t
  in report_adjust ctxt (if repeat then "Rewrote" else "Rewrote (repeated)") t end
  else error ("do_adjust: unexpected: " ^ r)
  | do_adjust _ args _ = error ("do_adjust: unexpected: " ^ @{make_string} args)

fun unvarify_types_same ty = ty
  |> Term_Subst.map_atypsT_same
    (fn TVar ((a, i), S) => TFree (a ^ "_var_" ^ string_of_int i, S)
      | _ => raise Same.SAME)

fun unvarify_types tm = tm
  |> Same.commit (Term_Subst.map_types_same unvarify_types_same)

fun match_abbreviation mode name init adjusts int ctxt = let
    val init_term = init ctxt
    val init_lambda = lambda_frees_vars ctxt init_term init_term
      |> unvarify_types
      |> Syntax.check_term ctxt
    val decl = (name, NONE, Mixfix.NoSyn)
    val result = fold (do_adjust ctxt) adjusts init_lambda
    val lhs = Free (Binding.name_of name, fastype_of result)
    val eq = Logic.mk_equals (lhs, result)
    val ctxt = Specification.abbreviation mode (SOME decl) [] eq int ctxt
    val pretty_eq = Syntax.pretty_term ctxt eq
  in Pretty.writeln pretty_eq; ctxt end

fun from_thm f thm_info ctxt = let
    val thm = singleton (Attrib.eval_thms ctxt) thm_info
  in f thm end

fun from_term term_str ctxt = Syntax.parse_term ctxt term_str

val init_term_parse = Parse.$$$ "in" |--
    ((Parse.reserved "concl" |-- Parse.thm >> from_thm Thm.concl_of)
        || (Parse.reserved "thm_prop" |-- Parse.thm >> from_thm Thm.prop_of)
        || (Parse.term >> from_term)
    )

val term_to_term = (Parse.term -- (Parse.reserved "to" |-- Parse.term))
    >> (fn (a, b) => [a, b])

val p_for_fixes = Scan.optional
    (Parse.$$$ "(" |-- Parse.for_fixes --| Parse.$$$ ")") []

val adjust_parser = Parse.and_list1
    ((Parse.reserved "select" -- Scan.succeed [] -- (Parse.term >> single) -- p_for_fixes)
        || (Parse.reserved "retype_consts" -- Scan.succeed []
            -- Scan.repeat Parse.term -- Scan.succeed [])
        || ((Parse.reserved "rewrite1" || Parse.reserved "rewrite")
            -- Scan.repeat (Parse.$$$ "in" |-- Parse.term -- p_for_fixes)
            -- term_to_term -- p_for_fixes)
    )

(* install match_abbreviation. see below for examples/docs *)
val _ =
  Outer_Syntax.local_theory' @{command_keyword match_abbreviation}
    "setup abbreviation for subterm of theorem"
    (Parse.syntax_mode -- Parse.binding
        -- init_term_parse -- adjust_parser
      >> (fn (((mode, name), init), adjusts)
            => match_abbreviation mode name init adjusts));

val _ =
  Outer_Syntax.local_theory @{command_keyword reassoc_thm}
    "store a reassociate-theorem"
    (Parse.binding -- Parse.term -- p_for_fixes -- Scan.repeat Parse.thm
      >> (fn (((name, rhs), fixes), thms)
            => add_reassoc name rhs fixes thms));
end
\<close>

text \<open>
The match/abbreviate command. There are examples of all elements below,
and an example involving monadic syntax in the theory Match-Abbreviation-Test.

Each invocation is match abbreviation, a syntax mode (e.g. (input)), an
abbreviation name, a term specifier, and a list of adjustment specifiers.

A term specifier can be term syntax or the conclusion or proposition of
some theorem. Examples below.

Each adjustment is a select, a rewrite, or a constant retype.

The select adjustment picks out the part of the term matching the
pattern (examples below). It picks the first match point, ordered in
term order with compound terms before their subterms and functions
before their arguments.

The rewrite adjustment uses a pattern pair, and rewrites instances
of the first pattern into the second. The match points are found in
the same order as select. The "in" specifiers (examples below)
limit the rewriting to within some matching subterm, specified with
pattern in the same way as select. The rewrite1 variant only
rewrites once, at the first matching site.

The rewrite mechanism can be used to replace terms with terms
of different types. The retype adjustment can then be used
to repair the term by resetting the types of all instances of
the named constants. This is used below with list constructors,
to assemble a new list with a different element type.
\<close>

experiment begin

text \<open>Fetching part of the statement of a theorem.\<close>
match_abbreviation (input) fixp_thm_bit
  in thm_prop fixp_induct_tailrec
  select "X \<equiv> Y" (for X Y)

text \<open>Ditto conclusion.\<close>
match_abbreviation (input) rev_simps_bit
  in concl rev.simps(2)
  select "X" (for X)

text \<open>Selecting some conjuncts and reorienting an equality.\<close>
match_abbreviation (input) conjunct_test
  in "(P \<and> Q \<and> P \<and> P \<and> P \<and> ((1 :: nat) = 2) \<and> Q \<and> Q, [Suc 0, 0])"
  select "Q \<and> Z" (for Z)
  and rewrite "x = y" to "y = x" (for x y)
  and rewrite in "x = y & Z" (for x y Z)
    "A \<and> B" to "A" (for A B)

text \<open>The relevant reassociate theorem, that rearranges a
conjunction like the above to group the elements selected.\<close>
reassoc_thm conjunct_test_reassoc
  "conjunct_test P Q \<and> Z" (for P Q Z)
  conj_assoc

text \<open>Selecting some elements of a list, and then replacing
tuples with equalities, and adjusting the type of the list constructors
so the new term is type correct.\<close>
match_abbreviation (input) list_test
  in "[(Suc 1, Suc 2), (4, 5), (6, 7), (8, 9), (10, 11), (x, y), (6, 7),
    (18, 19), a, a, a, a, a, a, a]"
  select "(4, V) # xs" (for V xs)
  and rewrite "(x, y)" to "(y, x)" (for x y)
  and rewrite1 in "(9, V) # xs" (for V xs) in "(7, V) # xs" (for V xs)
    "x # xs" to "[x]" (for x xs)
  and rewrite "(x, y)" to "x = y" (for x y)
  and retype_consts Cons Nil

end

end
