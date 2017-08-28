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
 * Construct necessary infrastructure to allow heap lifting to take place.
 * This creates the new globals record; the proofs relating it with the old
 * globals will be performed in HeapLift.
 *)

structure HeapLiftBase =
struct

type field_info = {
  name : string,
  field_type : typ,
  getter : term,
  setter : term
};

type struct_info = {
  name : string,
  struct_type : typ,
  field_info : field_info list
};

type heap_info =
{
  globals_type : typ,
  old_globals_type : typ,
  heap_getters : (string * typ) Typtab.table,
  heap_setters : (string * typ) Typtab.table,
  heap_valid_getters : (string * typ) Typtab.table,
  heap_valid_setters : (string * typ) Typtab.table,
  global_fields : (string * string * typ) list,
  global_field_getters : (term * term) Symtab.table,
  global_field_setters : (term * term) Symtab.table,
  lift_fn_name : string,
  lift_fn_thm : thm,
  lift_fn_full : term,
  dummy_state : term,
  lift_fn_simp_thms : thm list,
  structs : struct_info Symtab.table,
  struct_types : struct_info Typtab.table
};

type heap_lift_setup =
{
  heap_info : heap_info,
  (* Thms that depend only on heap types and can be pre-generated. *)
  (* Groups of instantiation lemmas. FIXME: does cross_instantiate really need grouping? *)
  lifted_heap_lemmas : thm list list,
  (* Empty if no syntax consts have been defined yet *)
  heap_syntax_rewrs : thm list
};

(*
 * Attempt to generate a pleasant name for the record
 * field name for the given heap.
 *
 *   word32        => heap_w32
 *   signed word32 => heap_w32
 *   word32 ptr    => heap_w32_ptr
 *   node_C ptr    => heap_node_ptr
 *)
fun name_from_type (T : typ) =
let
  (* Convert a numerical type back into an integer. *)
  fun get_num_type x =
    case (dest_Type x) of
        (@{type_name "Numeral_Type.num0"}, _) => 0
      | (@{type_name "Numeral_Type.num1"}, _) => 1
      | (@{type_name "Numeral_Type.bit0"}, [T])
          => 2 * get_num_type T
      | (@{type_name "Numeral_Type.bit1"}, [T])
          => 2 * get_num_type T + 1
      | _ => raise TYPE ("name_from_type/get_num_type", [x], [])

  fun get_name x =
    case (dest_Type x) of
         (@{type_name "Word.word"}, [x])
           => "w" ^ (@{make_string} (get_num_type x))
       | (@{type_name "ptr"}, [x])
           => (get_name x) ^ "'ptr"
       | (@{type_name "array"}, [x,y])
           => (get_name x) ^ "'array_" ^ (@{make_string} (get_num_type y))
       | (x, _) => (Long_Name.base_name x)
in
  (get_name T)
end
fun heap_name_from_type T = "heap_" ^ (name_from_type T)
fun heap_valid_name_from_type T = "is_valid_" ^ (name_from_type T)

(*
 * Determine what types we will need for the split heap to support the given
 * term.
 *)
fun get_term_heap_types ctxt t =
let
  fun is_ptr_type T =
    case T of
        Type (@{type_name "ptr"}, [_]) => true
      | _ => false
in
  case t of
      (t as Abs _) => Utils.concrete_abs' ctxt t |> #1 |> get_term_heap_types ctxt
    | a $ b => get_term_heap_types ctxt a @ get_term_heap_types ctxt b
    | a => (body_type (fastype_of a) :: binder_types (fastype_of a))
           |> filter is_ptr_type
           |> map (dest_Type #> snd #> hd)
end

(* Determine what heap types the given program accesses. *)
fun get_program_heap_types prog_info fn_infos gen_word_heaps lthy =
let
  (* Map the type "T" into a (possibly different) type that should appear in
   * our new heap. *)
  fun map_heap_type T =
    case T of
      (* Signed words are converted to standard words on the heap. *)
        Type (@{type_name "Word.word"},
          [Type (@{type_name "Signed_Words.signed"}, x)]) =>
            Type (@{type_name "Word.word"}, x)

      (* Pointers are valid if their inner type is valid. *)
      | Type (@{type_name "ptr"}, [x])
          => Type (@{type_name "ptr"}, [map_heap_type x])

      (* Arrays are valid if their inner type is valid. *)
      | Type (@{type_name "array"}, [x,y])
          => map_heap_type x

      | _ => T

  (* Process a function. *)
  fun process fn_name =
      (* Fetch body of "fn_name". *)
      the (Symtab.lookup fn_infos fn_name)
      |> #definition
      |> Thm.prop_of
      |> Utils.rhs_of_eq

      (* Fetch types from function body. *)
      |> get_term_heap_types lthy

      (* Fiddle with types if necessary. *)
      |> map map_heap_type
      |> Typset.make

      (* Remove the "void" heap if it exists. *)
      |> Typset.subtract (Typset.make [@{typ "unit"}])

  (* Generate all word heaps if desired. *)
  val word_typs = if not gen_word_heaps then Typset.empty else
                      Typset.make [@{typ word8}, @{typ word16}, @{typ word32}, @{typ word64}]
in
  Typset.union_sets (word_typs :: map process (Symtab.keys fn_infos))
end

(* Get fields from the globals type that should be copied from the
 * old globals type to the new globals type. *)
fun get_real_global_vars globalsT thy =
  (* Get all existing globals, filtering out "t_hrs_'". *)
   Record.get_recT_fields thy globalsT
   |> fst
   |> filter (fn (a, _) => Long_Name.base_name a <> "t_hrs_'")

(* Get the "t_hrs_'" accessor from the given globals record type. *)
fun get_globals_t_hrs globalsT thy =
   Record.get_recT_fields thy globalsT
   |> fst
   |> filter (fn (a, _) => Long_Name.base_name a = "t_hrs_'")
   |> hd


(*
 * Define a new heap record using the record package.
 *
 * "globalsT" is the type of the existing globals record, while "heapTs" is a
 * list of the different types the new heap will need to support.
 *)
fun gen_new_heap make_lifted_globals_field_name globalsT heapTs thy =
let
  val existing_fields = get_real_global_vars globalsT thy
  val new_heap_rec_name = "lifted_globals"

  (* Generate new fields. *)
  val new_names =
     map (fn (name, _) => make_lifted_globals_field_name
                            (unsuffix "_'" (Long_Name.base_name name))) existing_fields
  val copied_fields =
     map (fn ((name, ty), new_name) => (Binding.name new_name, ty, NoSyn))
         (existing_fields ~~ new_names)
  val heap_fields =
     map (fn a => (Binding.name (heap_name_from_type a), Utils.mk_ptrT a --> a, NoSyn)) heapTs
  val heap_valid_fields =
     map (fn a => (Binding.name (heap_valid_name_from_type a), Utils.mk_ptrT a --> @{typ bool}, NoSyn)) heapTs

  (* Define the record. *)
  val thy = Record.add_record {overloaded = false} ([], Binding.name new_heap_rec_name)
    NONE (copied_fields @ heap_fields @ heap_valid_fields) thy

  (* The record package doesn't tell us what we just defined, so we
   * attempt to fetch the type of the record. *)
  val full_rec_name = Sign.full_name thy (Binding.name new_heap_rec_name)
  val lifted_globalsT = Proof_Context.read_typ (Proof_Context.init_global thy) full_rec_name

  (* Create a list of the names of the new fields. *)
  val new_fields = Record.get_extT_fields thy lifted_globalsT
      |> fst |> take (length copied_fields)

  (* Hide the constants of existing fields, if required. *)
  val overlapped_names = filter (fn n => member op= new_names (Long_Name.base_name n)) (map fst existing_fields)
  val thy = fold (Sign.hide_const false) overlapped_names thy

  (* Generate a mapping from heap types to the getter/setter for that heap. *)
  val heap_fields =
      Record.get_recT_fields thy lifted_globalsT |> fst
      |> drop (length copied_fields)
      |> take (length heap_fields)
  val valid_fields =
      Record.get_recT_fields thy lifted_globalsT |> fst
      |> drop ((length copied_fields) + (length heap_fields))
  val getters = map (fn (a,b) => (a, lifted_globalsT --> b)) heap_fields
  val setters = map (fn (a,b) => (a ^ Record.updateN, (b --> b) --> (lifted_globalsT --> lifted_globalsT))) heap_fields
  val valid_getters = map (fn (a,b) => (a, lifted_globalsT --> b)) valid_fields
  val valid_setters = map (fn (a,b) => (a ^ Record.updateN, (b --> b) --> (lifted_globalsT --> lifted_globalsT))) valid_fields
  val type_heap_map = Typtab.make (heapTs ~~ ((getters ~~ setters) ~~ (valid_getters ~~ valid_setters)))
in
  ((lifted_globalsT, type_heap_map,
      map (fn ((a, T), (b, _)) => (a, b, T)) (existing_fields ~~ new_fields)), thy)
end

(*
 * Generate a heap abstraction function.
 *
 * That is, we generate a function that takes a "globals" variable that comes
 * from the C parser and spits out a "lifted_globals" variable which has a split
 * heap format.
 *
 * The "lifted_globals" type should be generated by "gen_new_heap".
 *)
fun gen_heap_abs_fn (prog_info : ProgramInfo.prog_info) old_globalsT lifted_globalsT heapTs lthy =
let
  val thy = Proof_Context.theory_of lthy
  val dummy_old_globals = Free ("g", old_globalsT)

  (* Fetch the fields of the globals record. *)
  val existing_fields = get_real_global_vars old_globalsT thy

  (* Fetch the "t_hrs_'" variable from the old globals, which
   * contains heap data. *)
  val t_hrs = get_globals_t_hrs old_globalsT thy

  (* Generate a term to construct the local variables record. *)
  val head_term = RecordUtils.get_record_constructor thy lifted_globalsT

  (*
   * We assume that the order of the variables in "lifted_globalsT"
   * match those in existing fields, followed by those in
   * heapTs.
   *
   * If this assumption is wrong, the following probably will
   * not type check (and, if it does, will be wrong).
   *
   * Our first step, we copy fields from the old globals type.
   *)
  val copy_term = fold (fn (name, t) => fn rest =>
    (rest $ (Const (name, old_globalsT --> t) $ dummy_old_globals)))
      existing_fields head_term

  (* Next, we generate lifted heaps from the old globals type. *)
  val lift_term =
    fold (fn t => fn rest =>
      (rest $ @{mk_term "%x. (the (simple_lift (?t_hrs ?s) (x::('a::c_type) ptr)))"
        ('a, t_hrs, s)} (t, Const (fst t_hrs, fastype_of dummy_old_globals --> snd t_hrs), dummy_old_globals)))
      (Typset.dest heapTs) copy_term
     |> fold (fn t => fn rest =>
        (rest $ @{mk_term "%x. (? z. (simple_lift (?t_hrs ?s) (x::('a::c_type) ptr)) = Some z)"
          ('a, t_hrs, s)} (t, Const (fst t_hrs, fastype_of dummy_old_globals --> snd t_hrs), dummy_old_globals)))
      (Typset.dest heapTs)
     |> (fn t => t $ @{term "()"})
     |> Syntax.check_term lthy

  (* Generate a body of a definition, and define it. *)
  val (Const (lift_name, _), def_thm, lthy) =
    Utils.define_const_args "lift_global_heap" false
       lift_term [("g", old_globalsT)] lthy

  (* Generate some simp rules to make life easier. *)
  val (simp_thms, lthy) = RecordUtils.generate_ext_simps "lifted_globals_ext_simps" def_thm lthy
in
  (lift_name, def_thm, simp_thms, lthy)
end

(*
 * Fetch information about structures in the program, such as
 * the fields of each structure and their types.
 *
 * We return a tuple containing (
 *     <mapping from struct names to field information>,
 *     <mapping from struct typs to field information>
 * ).
 *)
fun get_prog_struct_info thy prog_info =
let
  (* Fetch the namespace we are working in. *)
  val namespace =
    Long_Name.explode (dest_Type (#globals_type prog_info) |> fst)
    |> hd |> Long_Name.explode |> hd

  (* Fetch information about structures defined in the program. *)
  val struct_data = ProgramAnalysis.get_senv (#csenv prog_info)
        @ ProgramAnalysis.get_globals_rcd (#csenv prog_info)

  (* Given the name of a struct ("struct foo" would be "foo_C"), return
   * the type of that structure. *)
  fun get_struct_type name =
    CalculateState.ctype_to_typ (thy, CTypeDatatype.StructTy name)

  (* Generate information relating to a field of a single struct. *)
  fun get_field_info struct_name struct_type (field_name, field_type) = let
    val hol_field_type = CalculateState.ctype_to_typ (thy, field_type)
  in
    {
      name = field_name,
      field_type = hol_field_type,
      getter =
        Const (Long_Name.implode [namespace, struct_name, field_name],
            struct_type --> hol_field_type),
      setter =
        Const (Long_Name.implode [namespace, struct_name, field_name ^ "_update"],
            (hol_field_type --> hol_field_type) --> struct_type --> struct_type)
    }
  end

  (* Generate info relating to a single struct. *)
  fun get_struct_info (struct_name, struct_fields) =
  let
    val struct_type = get_struct_type struct_name
  in
    (struct_name, {
      name = struct_name,
      struct_type = struct_type,
      field_info = map (get_field_info struct_name struct_type) struct_fields
    })
  end

  val struct_info = map get_struct_info struct_data
in
  (Symtab.make struct_info,
      Typtab.make (map (fn (a,b) => (get_struct_type a, b)) struct_info))
end

fun mk_heap_info
  (thy : theory)
  (prog_info : ProgramInfo.prog_info)
  (lifted_globalsT : typ)
  (heap_getters_setters : (((string * typ) * (string * typ)) * ((string * typ) * (string * typ))) Typtab.table)
  (lift_fn : string * thm)
  (simp_thms : thm list)
  (global_fields : (string * string * typ) list) =
let
  val old_globalsT = #globals_type prog_info
  val (structs, struct_types) = get_prog_struct_info thy prog_info
  fun get_getter_const name globalsT destT
      = Const (name, globalsT --> destT)
  fun get_setter_const name globalsT destT
      = Const (name ^ Record.updateN, (destT --> destT) --> globalsT --> globalsT)
in
  {
    (* Type of the new globals state. *)
    globals_type = lifted_globalsT,
    old_globals_type = old_globalsT,

    (* Heap getters / setters. *)
    heap_getters = Typtab.map (K (fst o fst)) heap_getters_setters,
    heap_setters = Typtab.map (K (snd o fst)) heap_getters_setters,
    heap_valid_getters = Typtab.map (K (fst o snd)) heap_getters_setters,
    heap_valid_setters = Typtab.map (K (snd o snd)) heap_getters_setters,

    (* List of mappings between the old and new global fields. *)
    global_fields = global_fields,
    global_field_getters =
        map (fn (old_name, new_name, T) =>
          (old_name, (get_getter_const old_name old_globalsT T,
            get_getter_const new_name lifted_globalsT T)))
          global_fields
        |> Symtab.make,
    global_field_setters=
        map (fn (old_name, new_name, T) =>
          (old_name, (get_setter_const old_name old_globalsT T,
            get_setter_const new_name lifted_globalsT T)))
          global_fields
        |> Symtab.make,

    (* Function to lift the old globals type into the new globals type. *)
    lift_fn_name = fst lift_fn,
    lift_fn_thm = snd lift_fn,

    (* Function to lift old globals into new globals. *)
    lift_fn_full = Const (fst lift_fn, old_globalsT --> lifted_globalsT),

    (* Dummy state variable, used as a placeholder during translation. *)
    dummy_state = Free ("_dummy_state", lifted_globalsT),

    (* Simplification theorems for the lifting function. *)
    lift_fn_simp_thms = simp_thms,

    (* Structure information. *)
    structs = structs,
    struct_types = struct_types
  } : heap_info
end

fun setup
      prog_info
      (fn_infos: FunctionInfo.function_info Symtab.table)
      make_lifted_globals_field_name gen_word_heaps lthy =
let
  val old_globalsT = #globals_type prog_info

  (* Generate a new globals structure. *)
  val heapTs = get_program_heap_types prog_info fn_infos gen_word_heaps lthy
  val ((lifted_globalsT, heap_getters_setters, global_fields), lthy)
      = Local_Theory.raw_theory_result (
          gen_new_heap make_lifted_globals_field_name old_globalsT (Typset.dest heapTs)) lthy

  (*
   * HACK: Exit and enter the context again, so the simpset created by the new
   * record gets imported in. No idea what the "correct" way of doing this is.
   *)
  val lthy = Local_Theory.exit_global lthy |> Named_Target.init (the (Named_Target.locale_of lthy))

  (* Generate a function mapping old globals to the new globals. *)
  val (lift_name, lift_def, simp_thms, lthy) = gen_heap_abs_fn
      prog_info old_globalsT lifted_globalsT heapTs lthy

  (* Generate data structure encoding all relevant information. *)
  val heap_info = mk_heap_info (Proof_Context.theory_of lthy) prog_info lifted_globalsT
        heap_getters_setters (lift_name, lift_def) simp_thms
        global_fields
in
  (heap_info, lthy)
end

end

(* Save heap information into the theory. *)
structure HeapInfo = Theory_Data(
  type T = HeapLiftBase.heap_lift_setup Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge (l, r) =
    Symtab.merge (fn _ => true) (l, r);
)
