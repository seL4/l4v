(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* Theory data which records which attributes should be saved,
 * and how to do so. *)
structure Attrib_Fetchers = Theory_Data(
  type T = (Proof.context -> (string * string) list) Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge (K true)
)

(*** Encoding / Decoding into XML ***)

(*
 * Convert attribute data into XML.
 *
 * <attrib_trace name="MyTheory">
 *   <ancestors>
 *     <ancestor>Foo</ancestor>
 *     <ancestor>Bar</ancestor>
 *     <ancestor>Cow</ancestor>
 *   </ancestors>
 *   <sets>
 *     <set name="simp">
 *       <rule name="Foo.my_rule1">(?a = ?b) = (?b = ?a)</rule>
 *       <rule name="Foo.my_rule2">2 + 2 = 4</rule>
 *     </set>
 *   </sets>
 * </attrib_trace>
 *)
fun attrib_data_to_xml (name, ancestors, attribs) =
  xml_list "attrib_trace" [("name", name)] [
      (* Ancestor list. *)
      xml_list "ancestors" [] (
          map (xml_node "ancestor") ancestors
      ),

     (* Set of rules. *)
      xml_list "sets" [] (
          map (fn (name, vals) =>
            xml_list "set" [("name", name)] (
              map (fn (name, rule) =>
                  xml_attrib_node "rule" [("name", name)] rule)
                vals)) (Symtab.dest attribs)
      )
    ]

(* Convert XML into attrib data. *)
fun xml_to_attrib_data root =
let
  val name =
    xml_get_attrib "name" root

  val ancestors =
    xml_get_child "ancestors" root
    |> hd
    |> xml_get_child "ancestor"
    |> map xml_get_text

  val attrib_sets =
    xml_get_child "sets" root
    |> hd
    |> xml_get_child "set"
    |> map (fn n =>
         (xml_get_attrib "name" n,
            xml_get_child "rule" n
            |> map (fn n =>
                (xml_get_attrib "name" n, xml_get_text n))
         ))
    |> Symtab.make
in
  (name, ancestors, attrib_sets)
end

(*** Fetching theory data. ***)

(* Ugly print (i.e., not pretty-print) a type. *)
fun ugly_print_type T =
  case T of
    Type (s, Ts) =>
      "[" ^ commas (s :: map ugly_print_type Ts) ^ "]"
  | TFree (n, S) =>
       n ^ "::{" ^ commas S ^ "}"
  | TVar ((n,i),S) =>
       "?" ^ n ^ "/" ^ string_of_int i ^ "::{" ^ commas S ^ "}"

(* Ugly print (i.e., not pretty-print) a term. *)
fun ugly_print_term t =
  case t of
    Free (n, T) =>
     "(F " ^ n ^ " :: " ^ (ugly_print_type T) ^ ")"
  | Var ((n, i), T) =>
     "(V " ^ n ^ "/" ^ string_of_int i ^ " :: " ^ (ugly_print_type T) ^ ")"
  | Const (n, T) =>
     "(C " ^ n ^ " :: " ^ (ugly_print_type T) ^ ")"
  | Abs (_, T, t') =>
     "(%x :: " ^ (ugly_print_type T) ^ ". " ^ (ugly_print_term t') ^ ")"
  | Bound n =>
     "(B " ^ (string_of_int n) ^ ")"
  | a $ b =>
     "(" ^ ugly_print_term a ^ " $ " ^ ugly_print_term b ^ ")"

(* Render a thm to a string. *)
fun render_thm _ thm =
  Thm.prop_of thm
  |> ugly_print_term
  |> SHA1.digest
  |> SHA1.rep

(*
 * Guess the name of a list of thms.
 *
 * The "filter" is a set of theorem names which we ignore when trying
 * to come up with a name. For instance, the simplifier often munges
 * theorems together before placing them into the simpset; the filter
 * should be a list of theorems that the simplifier uses (and hence,
 * we should ignore).
 *)
fun guess_thm_names filter thms =
let
  (* Attempt to introspect the thm to find a name. *)
  val filter = Symtab.make_set filter
  fun guess_name_from_introspection filter thm =
  let
    fun thms_of (PBody {thms,...}) = thms
    fun proof_body_descend' (_,("",_,body)) =
          fold (append o proof_body_descend') (thms_of (Future.join body)) []
      | proof_body_descend' (_,(nm,t,_)) = [(nm,t)]
    fun used_facts thm =
        fold (append o proof_body_descend')
          (thms_of (Thm.proof_body_of thm)) []
  in
    used_facts thm
    |> map fst
    |> filter_out (Symtab.defined filter)
  end

  (* Get a single thm's name *)
  fun guess_thm_name thm =
    (* Attempt to get a name hint directly. Failing that, introspect the thm. *)
    if Thm.has_name_hint thm then
      SOME (Thm.get_name_hint thm)
    else case (guess_name_from_introspection filter thm) of
      [x] => SOME x
    | _ => NONE
in
  map guess_thm_name thms
end

(* Convert the list of theorems into an attribute set. *)
fun get_attrib_set ctxt filter_thms thms =
  (guess_thm_names filter_thms thms ~~ thms)
  |> filter (fn (name, thm) => name <> NONE)
  |> map (fn (name, thm) => (the name, render_thm ctxt thm))
  |> sort (fn ((nameA, _), (nameB, _)) => string_ord (nameA, nameB))

(* Get the data for attribute sets. *)
fun get_attrib_data ctxt =
let
  val thy = Proof_Context.theory_of ctxt

  (* Get theory name. *)
  val my_name = Context.theory_name thy

  (* Get ancestor names. *)
  val ancestors =
      Context.ancestors_of thy
      |> map Context.theory_name
      |> sort string_ord

  (* Fetch attributes. *)
  val attrib_sets =
    Attrib_Fetchers.get (Proof_Context.theory_of ctxt)
    |> Symtab.dest
    |> map (apsnd (fn f => f ctxt))
    |> Symtab.make
in
  (my_name, ancestors, attrib_sets)
end

(* Convert a path into one relative to the given theory. *)
fun mk_thy_relative thy filename =
  if OS.Path.isRelative filename then
    OS.Path.concat(Path.implode (Resources.master_directory thy), filename)
  else
    filename;

(* Write all attribute information to a file. *)
fun save_attribs_xml ctxt filename =
let
  val thy = Proof_Context.theory_of ctxt
  val target_file = Path.explode (mk_thy_relative thy filename)
in
  get_attrib_data ctxt
  |> attrib_data_to_xml
  |> XML.string_of
  |> File.write target_file
end

(* Load attribute information from a file. *)
fun load_attribs_xml ctxt filename =
let
  val thy = Proof_Context.theory_of ctxt
  val target_file = Path.explode (mk_thy_relative thy filename)
in
  File.read target_file
  |> XML.parse
  |> xml_to_attrib_data
end

(* Get default trace filename for given theory. *)
fun get_theory_trace_filename thy =
  "." ^ Context.theory_name thy ^ ".attrib_trace"

(*** Diffing Old and New ***)

(*
 * Get all facts currently defined.
 *
 * Clagged from "Find_Theorems.all_facts_of".
 *)
fun all_facts_of ctxt =
  let
    val local_facts = Proof_Context.facts_of ctxt;
    val global_facts = Global_Theory.facts_of (Proof_Context.theory_of ctxt);
  in
    maps Facts.selections
     (Facts.dest_static false [global_facts] local_facts @
      Facts.dest_static false [] global_facts)
  end

(* Diff attrib data, showing what commands will convert "new" into "old". *)
fun diff_attrib_data ctxt (_, old_ancestors, old_sets) (_, new_ancestors, new_sets) =
let
  (* Discard attribute sets which are not common to both old and new. *)
  val common_sets =
    Symset.inter
      (Symset.make (Symtab.keys new_sets))
      (Symset.make (Symtab.keys old_sets))
  fun filter_common_sets set =
    Symtab.dest set
    |> filter (fn (n, _) => Symset.contains common_sets n)
    |> sort (prod_ord string_ord (fn _ => EQUAL))
  val new_sets = filter_common_sets new_sets
  val old_sets = filter_common_sets old_sets

  (* Simpset filter *)
  fun filter_simp_rule ctxt thm =
    try (Simplifier.mksimps ctxt #> hd) thm

  (* Congset filter *)
  fun filter_cong_rule thm =
    try (fn rl =>
      zero_var_indexes
      (let val rl' = Seq.hd (TRYALL (fn i => fn st =>
         rtac (lift_meta_eq_to_obj_eq i st) i st) rl)
       in mk_meta_eq rl' handle THM _ =>
         if can Logic.dest_equals (concl_of rl') then rl'
         else error "Conclusion of congruence rules must be =-equality"
     end)) thm

  (* Fetch all facts, and create simp-mangled and cong-mangled versions of them. *)
  val all_facts =
    all_facts_of ctxt
    |> map (apfst Facts.string_of_ref)

  fun filter_snd_none xs =
    map_filter (fn (a, b) => case b of NONE => NONE | SOME x => SOME (a, x)) xs

  val all_facts_variants =
    (Par_List.map (apsnd filter_cong_rule) all_facts |> filter_snd_none)
    @ (Par_List.map (apsnd (filter_simp_rule ctxt)) all_facts |> filter_snd_none)
    @ all_facts

  (* Create a table for looking up theorem names from their ugly-printted
   * version. *)
  val all_facts_table = all_facts_variants
      |> Par_List.map (apsnd (render_thm ctxt))
      |> map swap
      |> (fn xs => fold Symtab.update xs Symtab.empty)

  (* Diff a paritcular set of attributes. *)
  fun diff_sets ((old_name, old), (_, new)) =
  let
    (* Convert ugly thm's into theorem names. *)
    fun pretty_thm_names thms = thms
      |> map (Symtab.lookup all_facts_table)
      |> map_filter I
      |> sort string_ord

    val old = Symset.make (map snd old)
    val new = Symset.make (map snd new)
  in
    (old_name,
        Symset.subtract old new |> Symset.dest |> pretty_thm_names,
        Symset.subtract new old |> Symset.dest |> pretty_thm_names)
  end
in
  map diff_sets (new_sets ~~ old_sets)
end

fun render_diffs diffs =
let
  fun render_diff (name, needed_adds, needed_dels) =
  let
    val adds =
      if length needed_adds > 0 then
        ["lemmas [" ^ name ^ "] = "]
        @ (map (fn x => "    " ^ x) needed_adds)
        @ [""]
      else
        []
    val dels =
      if length needed_dels > 0 then
        ["lemmas [" ^ name ^ " del] = "]
        @ (map (fn x => "    " ^ x) needed_dels)
        @ [""]
      else
        []
  in
    adds @ dels
  end
in
  map render_diff diffs
  |> List.concat
  |> (fn x => ["(* Approximate commands to restore old attrib sets. *)", ""] @ x @ [""])
  |> cat_lines
end

