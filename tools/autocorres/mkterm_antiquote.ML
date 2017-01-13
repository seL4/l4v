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
 * Term generation.
 *
 * Construct a term-generator at compile time.
 *
 *    @{mk_term "foo"} ()
 *      ==> @{term "foo"}
 *
 *    @{mk_term "?f a b c" (f)}
 *      ==> (fn t1 => t1 $ @{term a} $ @{term b} $ @{term c}
 *
 *    @{mk_term "a::(?'a::plus) + b" ('a)}
 *      ==> (fn t1 => Const (@{const_name plus}, t1 --> t1 --> t1) $ Free ("a", t1) $ Free ("b", t1))
 *)
structure MkTermAntiquote =
struct

local
  open ML_Syntax

  (*
   * Find the name and type of all schematic variables in the given term.
   *
   *   @{term "?x ?y"} ==> [("x", 'a => 'b), ("y", 'b)]
   *)
  fun get_schematic_types (a $ b) = get_schematic_types a @ get_schematic_types b
    | get_schematic_types (t as (Abs _)) = get_schematic_types (snd (Term.strip_abs_eta (~1) t))
    | get_schematic_types (Var ((name, _), T)) = [(name, T)]
    | get_schematic_types _ = []

  (*
   * Generate ML code to perform variable capture of the given type.
   *
   * In particular, all type variables will be captured into ML variables. The
   * returned dictionary indicates the mapping from type variables to ML variable
   * names.
   *)
  fun capture_type prefix (Type (_, Ts)) dict =
      let
        val (strings, new_dict) = fold_map (capture_type prefix) Ts dict
      in
        if length (Symtab.dest dict) = length (Symtab.dest new_dict) then
          ("_", dict)
        else
          ("Type (_,  " ^ (ML_Syntax.print_list I strings) ^ ")", new_dict)
      end
    | capture_type prefix (T as (TVar ((var_name, _), _))) dict =
      let
        val name = prefix ^ "_" ^ string_of_int (length (Symtab.dest dict))
      in
        case Symtab.lookup dict var_name of
          SOME _ => ("_", dict)
        | NONE => (name, Symtab.update_new (var_name, (name, T)) dict)
      end
    | capture_type _ (TFree _) dict = ("_", dict)

    (* Parse a list of the form "(x, y, z)". "inner" parses each of the indivdual items. *)
    fun comma_list inner =
      (inner >> (fn a => [a])) ||
          (Args.parens (inner -- (Scan.repeat (Args.$$$ "," -- inner >> snd)) >> (fn (a, b) => a :: b)))

  (* Write ML code for generating the given term, replacing schematic variables
   * with the ML code in the "replacements" dictionary. *)
  fun write_term_constructor replacements term =
  let
    fun print_typ (Type arg) = "Type " ^ print_pair print_string (print_list print_typ) arg
      | print_typ (TFree arg) = "TFree " ^ print_pair print_string print_sort arg
      | print_typ (TVar (arg as ((name, _), _))) =
          (case Symtab.lookup replacements name of
             NONE => "TVar " ^ print_pair print_indexname print_sort arg
           | SOME ml => atomic ml)

    fun print_term (Const arg) = "Const " ^ print_pair print_string print_typ arg
      | print_term (Free arg) = "Free " ^ print_pair print_string print_typ arg
      | print_term (Var (arg as ((name, _), _))) =
          (case Symtab.lookup replacements name of
             NONE => "Var " ^ print_pair print_indexname print_typ arg
           | SOME ml => atomic ml)
      | print_term (Bound i) = "Bound " ^ print_int i
      | print_term (Abs (s, T, t)) =
          "Abs (" ^ print_string s ^ ", " ^ print_typ T ^ ", " ^ print_term t ^ ")"
      | print_term (t1 $ t2) = atomic (print_term t1) ^ " $ " ^ atomic (print_term t2);
  in
    print_term term
  end

  (* Print ML code for rendering a tuple. *)
  val print_tuple = enclose "(" ")" o commas

  (*
   * Generate ML code for a lambda function that replaces variables and types
   * in a term with parameters.
   *
   *   print_lambda ["a", "'b"] "xxx"
   *     ==> ("(fn (t1, t2) => (xxx))", {"t1 => a", "t2 => 'b"})
   *)
  fun print_lambda vars =
  let
    val temps = 1 upto (length vars)
      |> map (fn x => "t" ^ (string_of_int x))
    val lambda_term = (fn x => atomic ("fn " ^ print_tuple temps ^ " => " ^ (atomic x)))
    val dict = Symtab.make (vars ~~ temps)
  in
    (lambda_term,  dict)
  end

  (* Generate ML code for constructing the given pattern with the given
   * template variables. *)
  fun gen_constructor ((ctxt, pattern), params : string list ) =
  let
    (* Parse user term. *)
    val term = Proof_Context.read_term_pattern ctxt pattern

    (*
     * Generate the outer shell of our final result:
     *
     *    (fn (t1, t2, t3) => ...)
     *)
    val (outer_fn, var_dict) = print_lambda params

    (*
     * For each parameter passed in by the user, generate ML code
     * to extract relevant parts of its type.
     *
     * For example, if the user wants to replace "?X" (having type "?'a =>
     * ?'b"), then when the user finally fills us in with a concrete term, we
     * want to substitute "?'a" and "?'b" with their concrete values.
     *)
    val schematic_types =
    let
      val typ_table =
        get_schematic_types term
        |> distinct (op =)
        |> Symtab.make
    in
      (params ~~ map (Symtab.lookup typ_table) params)
      |> filter (fn (_, b) => b <> NONE)
      |> map (fn (a, b) => (a, the b))
    end
    val (type_patterns, typ_dict) =
        fold_map (fn (v, T) => capture_type ("T__" ^ v) T) schematic_types Symtab.empty

    (* Merge the dictionary generated above (designed to capture types from
     * the input term) with the user-provided definitions (which may also
     * attempt to define types). *)
    val replacement_dict = Symtab.join
        (fn k => fn _ => error ("Key " ^ k ^ " used twice. Did you specify a type "
            ^ "twice in the parameter list (possibly implicity)?"))
        (Symtab.map (K fst) typ_dict, var_dict)

    (* Generate code to determine types of variables. *)
    val typ_match =
      outer_fn (
        "(let "
        ^ (cat_lines (map (fn (pattern, param) =>
            "val " ^ pattern ^ " = fastype_of " ^ param ^ "; ")
            (type_patterns ~~ map (the o Symtab.lookup var_dict o fst) schematic_types)))
        ^ " in "
          ^ (write_term_constructor replacement_dict term)
        ^ " end)"
      )
  in
    typ_match
  end
in
  val _ = Context.>> (Context.map_theory (
    ML_Antiquotation.inline @{binding "mk_term"}
      ((Args.context -- Scan.lift Args.embedded_inner_syntax -- (Scan.optional (Scan.lift ((comma_list Args.name))) []))
         >>  gen_constructor)))
end

end
