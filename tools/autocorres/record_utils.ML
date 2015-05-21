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
 * Utiltites for working with HOL records.
 *)
structure RecordUtils =
struct

(* Fetch information about a record from the record package. *)
fun get_record_info thy T =
  Record.dest_recTs T
  |> hd
  |> fst
  |> Long_Name.explode
  |> split_last
  |> fst
  |> Long_Name.implode
  |> Record.the_info thy

(*
 * Get the constructor for the given record type; i.e., the constant
 * which is used to construct records of this type.
 *
 * We instantiate the "more" component of the record type to unit.
 *
 * HACK: This doesn't seem to be the best way of doing this, because we
 * rely on the ordering of the "#defs" field of the record_info
 * structure.
 *)
fun get_record_constructor thy T =
  get_record_info thy T |> #ext_def |> Thm.prop_of |> Utils.lhs_of |> head_of
  |> Term_Subst.instantiate ([((("'z", 0), @{sort "type"}), @{typ unit})], [])

(*
 * Given a record "bar" (assumed to have fields "a", "b", "c" and a
 * definition of the form:
 *
 *   foo x y s == bar_ext (f x y s) (f' x y s) (f'' x y s)
 *
 * generate simps of the form:
 *
 *   a (foo x y s) = f x y s
 *   b (foo x y s) = f' x y s
 *   c (foo x y s) = f'' x y s
 *
 * This allows certain simplifications to occur on the definition
 * "foo" without having to expand it.
 *)
fun generate_ext_simps name def_thm ctxt =
let
  val thy = Proof_Context.theory_of ctxt

  (* Determine record type. *)
  val T = Thm.prop_of def_thm |> Utils.rhs_of |> head_of |> fastype_of |> body_type

  (* Fetch components that make up the new record. *)
  val components = Thm.prop_of def_thm |> Utils.rhs_of |> strip_comb |> snd

  (* Fetch fields of the record type T. *)
  val fields = let
    val (a, b) = Record.get_recT_fields thy T
  in
    a @ [b]
  end

  (* Generate theorems. *)
  fun gen_simp_proof ((field_name, field_type), defn) =
      HOLogic.mk_Trueprop (
        HOLogic.mk_eq (
          Const (field_name, T --> field_type) $ (Thm.prop_of def_thm |> Utils.lhs_of), defn))
      |> Thm.cterm_of ctxt
      |> Goal.init
      |> Utils.apply_tac "solve simple record proof"
          (simp_tac (ctxt addsimps [def_thm]) 1)
      |> Goal.finish ctxt
  val thms = map gen_simp_proof (fields ~~ components)

  (* Define the theorem. *)
  val lthy = Utils.define_lemmas name thms ctxt |> snd

  (* Add new rules to the simpset. *)
  val lthy = Local_Theory.map_contexts
    (fn _ => Context.proof_map (Simplifier.map_ss (fn x => x addsimps thms))) lthy
in
  (thms, lthy)
end

(* Get a record setter from its getter name and type. *)
fun get_record_getter recT (name, T) =
  Const (name, recT --> T)
fun get_record_setter recT (name, T) =
  Const (name ^ "_update", (T --> T) --> recT --> recT)

(* Get the simpset including all record-based theorems, including simprocs. *)
fun get_record_simpset ctxt =
let
  val thy = Proof_Context.theory_of ctxt
  val record_ss_1 = Record.get_simpset thy
  val record_ss_2 = RecursiveRecordPackage.get_simpset thy
  val record_ss = merge_ss (record_ss_1, record_ss_2)
in
  (put_simpset record_ss ctxt)
      addsimprocs ([
          Record.simproc,
          Record.upd_simproc,
          Record.eq_simproc,
          Record.ex_sel_eq_simproc,
          Record.split_simproc (K ~1)
      ])
      addsimps (Record.get_extinjects thy)
  |> simpset_of
end

end
