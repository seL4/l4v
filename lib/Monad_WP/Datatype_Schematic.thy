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
theory Datatype_Schematic

imports
  "../ml-helpers/MLUtils"
  "../ml-helpers/TermPatternAntiquote"
begin

text \<open>
  Introduces a method for improving unification outcomes for schematics with
  datatype expressions as parameters.

  There are two variants:
    1. In cases where a schematic is applied to a constant like @{term True},
       we wrap the constant to avoid some undesirable unification candidates.

    2. In cases where a schematic is applied to a constructor expression like
       @{term "Some x"} or @{term "(x, y)"}, we supply selector expressions
       like @{term "the"} or @{term "fst"} to provide more unification
       candidates.  This is only done if parameter that would be selected (e.g.
       @{term x} in @{term "Some x"}) contains bound variables which the
       schematic does not have as parameters.

  In the "constructor expression" case, we let users supply additional
  constructor handlers via the `datatype_schematic` attribute. The method uses
  rules of the following form:

    @{term "\<And>x1 x2 x3. getter (constructor x1 x2 x3) = x2"}

  These are essentially simp rules for simple "accessor" primrec functions,
  which are used to turn schematics like

    @{text "?P (constructor x1 x2 x3)"}

  into

    @{text "?P' x2 (constructor x1 x2 x3)"}.
\<close>

ML \<open>
  \<comment> \<open>
    Anchor used to link error messages back to the documentation above.
  \<close>
  val usage_pos = @{here};
\<close>

definition
  ds_id :: "'a \<Rightarrow> 'a"
where
  "ds_id = (\<lambda>x. x)"

lemma wrap_ds_id:
  "x = ds_id x"
  by (simp add: ds_id_def)

ML \<open>
structure Datatype_Schematic = struct

fun eq ((idx1, name1, thm1), (idx2, name2, thm2)) =
  idx1 = idx2 andalso
  name1 = name2 andalso
  (Thm.full_prop_of thm1) aconv (Thm.full_prop_of thm2);

structure Datatype_Schematic_Data = Generic_Data
(
  \<comment> \<open>
    Keys are names of datatype constructors (like @{const Cons}), values are
    `(index, function_name, thm)`.

    - `function_name` is the name of an "accessor" function that accesses part
      of the constructor specified by the key (so the accessor @{const hd} is
      related to the constructor/key @{const Cons}).

    - `thm` is a theorem showing that the function accesses one of the
      arguments to the constructor (like @{thm list.sel(1)}).

    - `idx` is the index of the constructor argument that the accessor
      accesses.  (eg. since `hd` accesses the first argument, `idx = 0`; since
      `tl` accesses the second argument, `idx = 1`).
  \<close>
  type T = ((int * string * thm) list) Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge_list eq;
);

fun gen_att m =
  Thm.declaration_attribute (fn thm => fn context =>
    Datatype_Schematic_Data.map (m (Context.proof_of context) thm) context);

(* gathers schematic applications from the goal. no effort is made
   to normalise bound variables here, since we'll always be comparing
   elements within a compound application which will be at the same
   level as regards lambdas. *)
fun gather_schem_apps (f $ x) insts = let
    val (f, xs) = strip_comb (f $ x)
    val insts = fold (gather_schem_apps) (f :: xs) insts
  in if is_Var f then (f, xs) :: insts else insts end
  | gather_schem_apps (Abs (_, _, t)) insts
    = gather_schem_apps t insts
  | gather_schem_apps _ insts = insts

fun sfirst xs f = get_first f xs

fun get_action ctxt prop = let
    val schem_insts = gather_schem_apps prop [];
    val actions = Datatype_Schematic_Data.get (Context.Proof ctxt);
    fun mk_sel selname T i = let
        val (argTs, resT) = strip_type T
      in Const (selname, resT --> nth argTs i) end
  in
    sfirst schem_insts
    (fn (var, xs) => sfirst (Library.tag_list 0 xs)
        (try (fn (idx, x) => let
            val (c, ys) = strip_comb x
            val (fname, T) = dest_Const c
            val acts = Symtab.lookup_list actions fname
            fun interesting arg = not (member Term.aconv_untyped xs arg)
                andalso exists (fn i => not (member (=) xs (Bound i)))
                    (Term.loose_bnos arg)
          in the (sfirst acts (fn (i, selname, thms) => if interesting (nth ys i)
            then SOME (var, idx, mk_sel selname T i, thms) else NONE))
          end)))
  end

fun get_bound_tac ctxt = SUBGOAL (fn (t, i) => case get_action ctxt t of
  SOME (Var ((nm, ix), T), idx, sel, thm) => (fn t => let
    val (argTs, _) = strip_type T
    val ix2 = Thm.maxidx_of t + 1
    val xs = map (fn (i, T) => Free ("x" ^ string_of_int i, T))
        (Library.tag_list 1 argTs)
    val nx = sel $ nth xs idx
    val v' = Var ((nm, ix2), fastype_of nx --> T)
    val inst_v = fold lambda (rev xs) (betapplys (v' $ nx, xs))
    val t' = Drule.infer_instantiate ctxt
        [((nm, ix), Thm.cterm_of ctxt inst_v)] t
    val t'' = Conv.fconv_rule (Thm.beta_conversion true) t'
  in safe_full_simp_tac (clear_simpset ctxt addsimps [thm]) i t'' end)
  | _ => no_tac)

fun id_applicable (f $ x) = let
    val (f, xs) = strip_comb (f $ x)
    val here = is_Var f andalso exists is_Const xs
  in here orelse exists id_applicable (f :: xs) end
  | id_applicable (Abs (_, _, t)) = id_applicable t
  | id_applicable _ = false

fun combination_conv cv1 cv2 ct =
  let
    val (ct1, ct2) = Thm.dest_comb ct
    val r1 = SOME (cv1 ct1) handle Option => NONE
    val r2 = SOME (cv2 ct2) handle Option => NONE
    fun mk _ (SOME res) = res
      | mk ct NONE = Thm.reflexive ct
  in case (r1, r2) of
      (NONE, NONE) => raise Option
    | _ => Thm.combination (mk ct1 r1) (mk ct2 r2)
  end

val wrap = mk_meta_eq @{thm wrap_ds_id}

fun wrap_const_conv _ ct = if is_Const (Thm.term_of ct)
        andalso fastype_of (Thm.term_of ct) <> @{typ unit}
    then Conv.rewr_conv wrap ct
    else raise Option

fun combs_conv conv ctxt ct = case Thm.term_of ct of
    _ $ _ => combination_conv (combs_conv conv ctxt) (conv ctxt) ct
  | _ => conv ctxt ct

fun wrap_conv ctxt ct = case Thm.term_of ct of
    Abs _ => Conv.sub_conv wrap_conv ctxt ct
  | f $ x => if is_Var (head_of f) then combs_conv wrap_const_conv ctxt ct
    else if not (id_applicable (f $ x)) then raise Option
    else combs_conv wrap_conv ctxt ct
  | _ => raise Option

fun CONVERSION_opt conv i t = CONVERSION conv i t
    handle Option => no_tac t

exception Datatype_Schematic_Error of Pretty.T;

fun apply_pos_markup pos text =
  let
    val props = Position.def_properties_of pos;
    val markup = Markup.properties props (Markup.entity "" "");
  in Pretty.mark_str (markup, text) end;

fun invalid_accessor ctxt thm : exn =
  Datatype_Schematic_Error ([
    Pretty.str "Bad input theorem '",
    Syntax.pretty_term ctxt (Thm.full_prop_of thm),
    Pretty.str "'. Click ",
    apply_pos_markup usage_pos "*here*",
    Pretty.str " for info on the required rule format." ] |> Pretty.paragraph);

local
  fun dest_accessor' thm =
    case (thm |> Thm.full_prop_of |> HOLogic.dest_Trueprop) of
      @{term_pat "?fun_name ?data_pat = ?rhs"} =>
        let
          val fun_name = Term.dest_Const fun_name |> fst;
          val (data_const, data_args) = Term.strip_comb data_pat;
          val data_vars = data_args |> map (Term.dest_Var #> fst);
          val rhs_var = rhs |> Term.dest_Var |> fst;
          val data_name = Term.dest_Const data_const |> fst;
          val rhs_idx = ListExtras.find_index (curry op = rhs_var) data_vars |> the;
        in (fun_name, data_name, rhs_idx) end;
in
  fun dest_accessor ctxt thm =
    case try dest_accessor' thm of
      SOME x => x
    | NONE => raise invalid_accessor ctxt thm;
end

fun add_rule ctxt thm data =
  let
    val (fun_name, data_name, idx) = dest_accessor ctxt thm;
    val entry = (data_name, (idx, fun_name, thm));
  in Symtab.insert_list eq entry data end;

fun del_rule ctxt thm data =
  let
    val (fun_name, data_name, idx) = dest_accessor ctxt thm;
    val entry = (data_name, (idx, fun_name, thm));
  in Symtab.remove_list eq entry data end;

val add = gen_att add_rule;
val del = gen_att del_rule;

fun wrap_tac ctxt = CONVERSION_opt (wrap_conv ctxt)

fun tac1 ctxt = REPEAT_ALL_NEW (get_bound_tac ctxt) THEN' (TRY o wrap_tac ctxt)

fun tac ctxt = tac1 ctxt ORELSE' wrap_tac ctxt

val add_section =
  Args.add -- Args.colon >> K (Method.modifier add @{here});

val method =
  Method.sections [add_section] >> (fn _ => fn ctxt => Method.SIMPLE_METHOD' (tac ctxt));

end
\<close>

setup \<open>
  Attrib.setup
    @{binding "datatype_schematic"}
    (Attrib.add_del Datatype_Schematic.add Datatype_Schematic.del)
    "Accessor rules to fix datatypes in schematics"
\<close>

method_setup datatype_schem = \<open>
  Datatype_Schematic.method
\<close>

declare prod.sel[datatype_schematic]
declare option.sel[datatype_schematic]
declare list.sel(1,3)[datatype_schematic]

locale datatype_schem_demo begin

lemma handles_nested_constructors:
  "\<exists>f. \<forall>y. f True (Some [x, (y, z)]) = y"
  apply (rule exI, rule allI)
  apply datatype_schem
  apply (rule refl)
  done

datatype foo =
    basic nat int
  | another nat

primrec get_basic_0 where
  "get_basic_0 (basic x0 x1) = x0"

primrec get_nat where
    "get_nat (basic x _) = x"
  | "get_nat (another z) = z"

lemma selectively_exposing_datatype_arugments:
  notes get_basic_0.simps[datatype_schematic]
  shows "\<exists>x. \<forall>a b. x (basic a b) = a"
  apply (rule exI, (rule allI)+)
  apply datatype_schem \<comment> \<open>Only exposes `a` to the schematic.\<close>
  by (rule refl)

lemma method_handles_primrecs_with_two_constructors:
  shows "\<exists>x. \<forall>a b. x (basic a b) = a"
  apply (rule exI, (rule allI)+)
  apply (datatype_schem add: get_nat.simps)
  by (rule refl)

end

end
