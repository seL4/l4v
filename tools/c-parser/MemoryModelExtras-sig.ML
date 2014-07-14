(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

signature USER_TYPE_DECL_CHECKING =
sig

  type t
  type csenv = ProgramAnalysis.csenv
  val initial_state : t
  val finalise : t -> theory -> theory

  val struct_type :
      csenv ->
      { struct_type : string * (string * typ * int Absyn.ctype) list,
        state : t } ->
      theory -> t * theory
  val array_type : csenv ->
                   {element_type : typ, array_size : int, state : t} ->
                   theory -> t * theory
end



signature MEMORY_MODEL_EXTRAS =
sig

  val extended_heap_ty : typ

  val check_safety : {heap: term, ptrval:term} -> term * term
  val dereference_ptr : {heap:term, ptrval:term} -> term
  val mk_heap_update_extended : term -> term

  val mk_aux_guard : term -> term
  val mk_aux_update : term -> term
  val mk_aux_type : typ -> typ

  val check_global_record_type : string -> theory -> theory

  val mk_lookup_proc_pair : term -> term -> term -> term * term

  structure UserTypeDeclChecking : USER_TYPE_DECL_CHECKING
end (* sig *)
(*
  [extended_heap_ty] is the Isabelle type of heaps that are to be manipulated
  by the StrictC programs.  It will include (some way or another) the underlying
  heap (mapping addresses to bytes), but may also include other stuff.

  [check_safety{heap,ptrval}] generates a pair of terms that will be
  used to guard an assignment if the ms ("memory safety") flag is set.
  (By default it is not set.)  The ptrval is a term of pointer type
  pointing to the address that is about to be written to; the heap is
  the term of the current (extended) heap.  A result (t1,t2) should
  have t1 of type state-predicate (i.e., state -> bool), and t2 of type
  error.  That is, t1 will be the guard of the checked assignment, and t2 will
  be the error a failing guard would cause.

  If you don't ever intend to use the 'ms' flag, this function could
  just raise an exception.

  [dereference_ptr{heap,ptrval}] returns the value stored in (extended)
  heap at address ptrval.  The value ptrval will be of type Ptr sometype, the
  result should be a term of type sometype.

  [mk_heap_update_extended t] lifts t, an update on an underlying
  primitive heap (a term of type `primheap -> primheap`), returning an
  update on the extended_heap_ty (extended_heap_ty -> extended_heap_ty`)

  [mk_aux_guard t] The term t is of the form (predicate $ var), where var is
  of type `state`.  The predicate has come from text entered as part of an
  "aux update".  This is a statement form such as

     /** AUXUPD: "some term" */

  The string "some term" is actually mangled to become
    "antiquoteParseTranslation (some term)" and it is this that is
  parsed.  My understanding of apt is that makes a normal term
  implicit on a state.

  This term should have type   mk_aux_type statetype, which has to be a
  function type because it is applied to a var (corresponding to the current
  state).

  mk_aux_guard is applied to the value to generate a boolean that corresponds
  to a guard.

  [mk_aux_update t] is applied to the same sort of term as mk_aux_guard, and
  returns an updator for the extended heap.

  [mk_aux_type ty] turns the type corresponding to machine states into the type
  used to implement auxiliary guards and updators.

  [check_global_record_type s thy] takes the current theory and the
  name of the global variable record (containing the heap, the c_exn
  variable, the global variable struct and the phantom state).  It
  then does whatever proving is necessary to confirm the global
  variable record is OK.

  [UserTypeDeclChecking]
  This structure implements additional checks on new C types that arise in the
  analysed program.  The model allows for additional data to be passed through
  all successive calls using the type UserTypeDeclChecking.t.  Once the
  initial value of this is to hand, calls will be made to
    struct_type     with details of new struct types
                     - the Isabelle record type that corresponds to
                       the struct type will already have been defined,
                       along with appropriate accessor and updator
                       functions.
    array_type      with details of new array types
                     - there is already a binary array type operator
                       in the background theory, so the array type
                       already exists.  However, the particular
                       combination required by the user may still need
                       things proved of it.
    arraysize_type  to establish properties of number types
  The calls are made in appropriate topological order.  Calls for the same
  type may be repeated.

*)
