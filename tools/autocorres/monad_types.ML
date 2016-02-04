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
 * Basic definitions for monad types.
 *
 * This file is loaded before type strengthening so that its
 * attributes can be used.
 *
 * The basic set of attributes is defined in TypeStrengthen.thy.
 *)

structure Monad_Types = struct

(*
 * The monad_type and ts_rule attribute setup.
 *)
type monad_type = {

  (* A short name used to refer to this monad. *)
  name : string,

  (* A longer description. AutoCorres does not use this, so write whatever you want. *)
  description : string,

  (*
   * Type conversion rules.
   * While we store full contexts, we are really only interested in their simpsets.
   * The rest of the context data is unused.
   *)

  (* Rules for converting L2_monad to your monad. *)
  lift_rules : unit Thmtab.table,

  (* Rules for converting your monad back to L2_monad.
     You need these rules if you want to use monad_convert. *)
  unlift_rules : unit Thmtab.table,

  (* Any extra simplifications that are applied after conversion. *)
  polish_rules : unit Thmtab.table,

  (* Decide whether a term is written in your monad.
     A usual way is to check that the term starts with <L2_call_lift> (see below). *)
  valid_term : Proof.context -> term -> bool,

  (*
   * TypeStrengthen internal usage
   *)

  (* Rule precedence; higher-numbered rules are tried first. *)
  precedence : int,

  (* If TypeStrengthen cannot finish a proof, throw simp rules here until it can *)
  L2_simp_rules : thm list,

  (* Function whose type is "your monad type => (...) L2_monad".
     This term also needs to appear in the following thm. *)
  L2_call_lift : term,

  (* Thm of the form
       L2_call ?l2_func = <L2_call_lift> ?new_func
         ==> L2_call ?l2_func = <L2_call_lift> ?new_func
     where the LHS and RHS have different polymorphic exception types. *)
  polymorphic_thm : thm,

  (* Construct your monad type, given (state, result, exception). *)
  typ_from_L2 : (typ * typ * typ) -> typ,

  (* Transfer monad_mono property to the new monad.
   * Input thms: "L2_call l2_func = lift new_func", "monad_mono l2_func"
   * This is not needed if the new monad will not contain recursive functions. *)
  prove_mono : thm -> thm -> thm
}

fun update_mt_rules update_lifts update_unlifts update_polish (mt : monad_type) = {
  name = #name mt,
  description = #description mt,
  lift_rules = update_lifts (#lift_rules mt),
  unlift_rules = update_unlifts (#unlift_rules mt),
  polish_rules = update_polish (#polish_rules mt),
  valid_term = #valid_term mt,
  precedence = #precedence mt,
  L2_simp_rules = #L2_simp_rules mt,
  L2_call_lift = #L2_call_lift mt,
  polymorphic_thm = #polymorphic_thm mt,
  typ_from_L2 = #typ_from_L2 mt,
  prove_mono = #prove_mono mt
}
fun update_mt_lift_rules f = update_mt_rules f I I
fun update_mt_unlift_rules f = update_mt_rules I f I
fun update_mt_polish_rules f = update_mt_rules I I f

fun merge_mt (mt1 : monad_type, mt2 : monad_type) =
  mt1 |> update_mt_rules (fn ss => Thmtab.merge op= (ss, #lift_rules mt2))
                         (fn ss => Thmtab.merge op= (ss, #unlift_rules mt2))
                         (fn ss => Thmtab.merge op= (ss, #polish_rules mt2))

(* TODO: figure out how to do this with Theory_Data *)
structure TSRules = Generic_Data
(
  type T = monad_type Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.join (K merge_mt)
  val extend = I
)

fun error_no_such_mt name = error ("autocorres: no such monad type " ^ quote name)

fun update_the_mt (name : Symtab.key) (f : monad_type -> monad_type) (t : TSRules.T) =
  case Symtab.lookup t name of
      NONE => error_no_such_mt name
    | SOME mt => Symtab.update (name, f mt) t

fun change_TSRules update_rules update_simps name thms =
  TSRules.map (update_the_mt name (update_rules
    (fn thmset => update_simps thmset thms)))

fun thmset_adds set thms = fold Thmtab.update (map (fn thm => (thm, ())) thms) set
fun thmset_dels set thms = fold Thmtab.delete thms set

val add_lift_rules = change_TSRules update_mt_lift_rules thmset_adds
val del_lift_rules = change_TSRules update_mt_lift_rules thmset_dels
val add_unlift_rules = change_TSRules update_mt_unlift_rules thmset_adds
val del_unlift_rules = change_TSRules update_mt_unlift_rules thmset_dels
val add_polish_rules = change_TSRules update_mt_polish_rules thmset_adds
val del_polish_rules = change_TSRules update_mt_polish_rules thmset_dels

val ts_attrib : attribute context_parser =
  Scan.lift (Parse.name --
    (Args.$$$ "add" >> K add_lift_rules ||
     Args.$$$ "del" >> K del_lift_rules ||

     (* TODO: use Scan.optional *)
     (Args.$$$ "unlift" |-- Args.$$$ "add") >> K add_unlift_rules ||
     Args.$$$ "unlift" >> K add_unlift_rules ||
     (Args.$$$ "unlift" |-- Args.$$$ "del") >> K del_unlift_rules ||

     (Args.$$$ "polish" |-- Args.$$$ "add") >> K add_polish_rules ||
     Args.$$$ "polish" >> K add_polish_rules ||
     (Args.$$$ "polish" |-- Args.$$$ "del") >> K del_polish_rules ||
     Scan.succeed add_lift_rules
    )) >>
  (fn (name, update_f) =>
    (Thm.declaration_attribute (fn thm => update_f name [thm])))



(*
 * Extra monad_type utilities.
 *)

(* Lazy check_lifting, which only checks the head term. *)
fun check_lifting_head (heads : term list) : (Proof.context -> term -> bool) =
  let val head_names = map (fn Const (name, _) => name) heads
      fun check _ t = case head_of t of
                          Const (name, _) => member (op =) head_names name
                        | _ => false
  in check end

fun new_monad_type
      (name : string)
      (description : string)
      (valid_term : Proof.context -> term -> bool)
      (precedence : int)
      (L2_simp_rules : thm list)
      (L2_call_lift : term)
      (polymorphic_thm : thm)
      (typ_from_L2 : (typ * typ * typ) -> typ)
      (prove_mono : thm -> thm -> thm)
      : Context.generic -> Context.generic =
  TSRules.map (fn t =>
    let
      val mt = {
        name = name,
        description = description,
        (* TODO: it seems that we could use empty_ss instead of HOL_basic_ss,
                 but then Isabelle throws all the rules away when we cross
                 theory boundaries or merge theories. Investigate. *)
        lift_rules = Thmtab.empty,
        unlift_rules = Thmtab.empty,
        polish_rules = Thmtab.empty,
        valid_term = valid_term,
        precedence = precedence,
        L2_simp_rules = L2_simp_rules,
        L2_call_lift = L2_call_lift,
        polymorphic_thm = polymorphic_thm,
        typ_from_L2 = typ_from_L2,
        prove_mono = prove_mono
      }
    in
      Symtab.update_new (name, mt) t
      handle Symtab.DUP _ =>
        error ("autocorres: cannot define the monad type " ^ quote name ^
               " because it has already been defined.")
    end)

fun get_monad_type (name : string) (ctxt : Context.generic) : monad_type option =
  Symtab.lookup (TSRules.get ctxt) name

fun monad_type_rules (rules : monad_type) =
  { lift_rules = #lift_rules rules |> Thmtab.dest |> map fst,
    unlift_rules = #unlift_rules rules |> Thmtab.dest |> map fst,
    polish_rules = #polish_rules rules |> Thmtab.dest |> map fst }

fun get_monad_type_rules (name : string) (ctxt : Context.generic) =
  get_monad_type name ctxt
  |> Option.map monad_type_rules


(* Get rules ordered by precedence. If only_use is empty, return all rules. *)
fun get_ordered_rules (only_use : string list)
                      (ctxt : Context.generic) : monad_type list =
let
  val mts = TSRules.get ctxt
  val needed_mts =
      if null only_use then Symtab.dest mts |> map snd
      else only_use |> map (fn name => case Symtab.lookup mts name of
                                           SOME x => x
                                         | NONE => error_no_such_mt name)
in
  (* Order by highest precedence first. *)
  map (fn mt => (#precedence mt, mt)) needed_mts
  |> sort (rev_order o int_ord o apply2 fst)
  |> map snd
end


end
