(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* this is an -*- sml -*- file *)

signature RECURSIVE_RECORD_PACKAGE =
sig

  (* no type variables allowed! *)
  val define_record_type :
       {record_name : string,
        fields : {fldname : string, fldty : typ} list} list ->
      theory -> theory

  val get_simpset : theory -> simpset;

end;

structure RecursiveRecordPackage : RECURSIVE_RECORD_PACKAGE =
struct

structure RecursiveRecordData = Theory_Data
(
  type T = simpset;
  val empty = HOL_basic_ss;
  val extend = I;
  val merge = merge_ss;
);

val get_simpset = RecursiveRecordData.get;

fun add_recursive_record_thms simps congs thy
    = RecursiveRecordData.map (fn ss =>
        Proof_Context.init_global thy
        |> put_simpset ss
        |> (fn ctxt => ctxt addsimps simps)
        |> fold Raw_Simplifier.add_cong congs
        |> simpset_of) thy

val updateN = Record.updateN

fun gen_vars tys = List.tabulate(length tys,
                                 (fn n => Free("x" ^ Int.toString n,
                                               List.nth(tys, n))))

fun define_accessor arg (({fldname, fldty}, result), thy) = let
  val acc_ty = type_of arg --> fldty
  val bnm = Binding.name
  val acc_t = Free(fldname, acc_ty)
  val defn = TermsTypes.mk_prop (TermsTypes.mk_eqt(acc_t $ arg, result))
  val (_, thy) =
    BNF_LFP_Compat.primrec_global
         [(bnm fldname, NONE, NoSyn)]
         [(((bnm (fldname ^ "_def"), []), defn), [], [])] thy
in
  thy
end

fun define_updator arg (i, {fldname, fldty}) thy = let
  val bnm = Binding.name
  val arg_ty = type_of arg
  val (con, args) = strip_comb arg
  val upd_ty = (fldty --> fldty) --> (arg_ty --> arg_ty)
  val upd_name = suffix updateN fldname
  val upd_t = Free(upd_name, upd_ty)
  val f = Free("f", fldty --> fldty)
  val lhs_t = upd_t $ f $ arg
  val modified_args = Library.nth_map i (fn t => f $ t) args
  val rhs_t = foldl (fn (a,t) => t $ a) con modified_args
  val defn = TermsTypes.mk_prop(TermsTypes.mk_eqt(lhs_t, rhs_t))
  val (_, thy) =
    BNF_LFP_Compat.primrec_global
         [(bnm upd_name, NONE, NoSyn)]
         [(((bnm (upd_name ^ "_def"), []), defn), [], [])] thy
in
  thy
end

fun define_functions (r as {record_name, fields}) thy = let
  val recordnameb = Binding.name record_name
  val domty = Type(Sign.full_name thy recordnameb, [])
  val constructor_ty = List.foldr op--> domty (map #fldty fields)
  val constructor_t =
      Const(Sign.intern_const thy record_name, constructor_ty)
  val args = gen_vars (map #fldty fields)
  val record_value_t = List.foldl (fn (a,t) => t $ a) constructor_t args
  val field_args = ListPair.zip(fields, args)
  fun define_accessors thy =
      List.foldl (define_accessor record_value_t) thy field_args
in
  (thy |> Sign.add_path record_name
       |> define_accessors
       |> Library.fold_index (define_updator record_value_t) fields
       |> RecursiveRecordPP.install_translations r
       |> Sign.parent_path)
  before
  tracing("Defined accessor and update functions for record "^record_name)
end

fun cprod_less_diag list = let
  fun recurse acc l =
      case l of
        [] => acc
      | h::t => let
          val acc' = List.foldl (fn (e,acc) => (h,e) :: (e,h) :: acc) acc t
        in
          recurse acc' t
        end
in
  recurse [] list
end

fun lower_triangle list = let
  fun recurse acc l =
      case l of
        [] => acc
      | h :: t => let
          val acc' = List.foldl (fn (e,acc) => (e,h) :: acc) acc t
        in
          recurse acc' t
        end
in
  recurse [] list
end

val updcong_foldE = @{thm "idupdate_compupdate_fold_congE"};

(* copied from src/Pure/old_term.ML -r 6a973bd43949 and then
   s/OrdList/Ord_List/
   s/TermOrd/Term_Ord/
*)
local
(*Accumulates the Vars in the term, suppressing duplicates.*)
fun add_term_vars (t, vars: term list) = case t of
    Var   _ => Ord_List.insert Term_Ord.term_ord t vars
  | Abs (_,_,body) => add_term_vars(body,vars)
  | f$t =>  add_term_vars (f, add_term_vars(t, vars))
  | _ => vars;

fun term_vars t = add_term_vars(t,[]);
in
val [updvar] = term_vars (nth (Thm.prems_of updcong_foldE) 1)
end

fun prove_record_rewrites ({record_name, fields}, thy) = let
  val _ = tracing("Proving rewrites for struct "^record_name)
  val rty = Type(Sign.intern_type thy record_name, [])
  val r_var = Free("r", rty)
  val r_var' = Free("r'", rty)
  val domty = Type(Sign.full_name thy (Binding.name record_name), [])
  val constructor_ty = List.foldr op--> domty (map #fldty fields)
  val constructor_t =
      Const(Sign.intern_const thy record_name, constructor_ty)
  open TermsTypes
  val case_tac = Induct_Tacs.case_tac
  fun prove g =
      Goal.prove_global_future thy [] [] (mk_prop g)
                        (fn {prems=_,context} =>
                            case_tac context "r" [] NONE 1 THEN
                            asm_full_simp_tac context 1)
  fun mk_upd_t {fldname,fldty} =
      Const(Sign.intern_const thy (suffix updateN fldname),
            (fldty --> fldty) --> (rty --> rty))

  fun prove_accupd_same (fld as {fldname, fldty}) = let
    val f = Free("f", fldty --> fldty)
    val acc = Const(Sign.intern_const thy fldname, rty --> fldty)
    val upd = mk_upd_t fld
    val lhs_t = acc $ (upd $ f $ r_var)
    val rhs_t = f $ (acc $ r_var)
  in
    prove (mk_eqt(lhs_t, rhs_t))
  end
  val accupd_sames = map prove_accupd_same fields

  fun prove_accupd_diff (acc, upd) = let
    val {fldname = accname, fldty = accty} = acc
    val {fldname = _, fldty = updty} = upd
    val acc_t = Const(Sign.intern_const thy accname, rty --> accty)
    val upd_t = mk_upd_t upd
    val f = Free("f", updty --> updty)
    val lhs_t = acc_t $ (upd_t $ f $ r_var)
    val rhs_t = acc_t $ r_var
  in
    prove(mk_eqt(lhs_t, rhs_t))
  end
  val accupd_diffs = map prove_accupd_diff (cprod_less_diag fields)

  fun prove_updupd_same (fld as {fldname=_, fldty}) = let
    val ffty = fldty --> fldty
    val upd_t = mk_upd_t fld
    val f = Free("f", ffty)
    val g = Free("g", ffty)
    val lhs_t = upd_t $ f $ (upd_t $ g $ r_var)
    val comp = Const("Fun.comp", ffty --> (ffty --> ffty))
    val rhs_t = upd_t $ (comp $ f $ g) $ r_var
  in
    prove(mk_eqt(lhs_t, rhs_t))
  end
  val updupd_sames = map prove_updupd_same fields

  fun prove_updupd_diff (upd1, upd2) = let
    val {fldname = _, fldty = updty1} = upd1
    val {fldname = _, fldty = updty2} = upd2
    val upd1_t = mk_upd_t upd1
    val upd2_t = mk_upd_t upd2
    val f = Free("f", updty1 --> updty1)
    val g = Free("g", updty2 --> updty2)
    val lhs_t = upd1_t $ f $ (upd2_t $ g $ r_var)
    val rhs_t = upd2_t $ g $ (upd1_t $ f $ r_var)
  in
    prove(mk_eqt(rhs_t, lhs_t))
  end
  val updupd_diffs = map prove_updupd_diff (lower_triangle fields)

  fun prove_idupdates (fld as {fldname, fldty}) = let
    val upd_t = mk_upd_t fld
    val acc_t = Const(Sign.intern_const thy fldname, rty --> fldty)
    val K = K_rec fldty
  in
    prove(mk_eqt(upd_t $ (K $ (acc_t $ r_var)) $ r_var, r_var))
  end
  val idupdates = map prove_idupdates fields

  (* proves that (| fld1 = fld1 v, fld2 = fld2 v, fld3 = fld3 v,..|) = v *)
  val idupd_value1 = let
    fun mk_arg ({fldname, fldty}, acc) = let
      val acc_t = Const(Sign.intern_const thy fldname, rty --> fldty)
    in
      acc $ (acc_t $ r_var)
    end
  in
    prove(mk_eqt(List.foldl mk_arg constructor_t fields, r_var))
  end

  (* proves that u (| fld1 := fld1 v, fld2 := fld2 v, ... |) = v *)
  val idupd_value2 = let
    fun mk_arg (fld as {fldname, fldty}, t) = let
      val acc_t = Const(Sign.intern_const thy fldname, rty --> fldty)
      val upd_t = mk_upd_t fld
      val K = K_rec fldty
    in
      upd_t $ (K $ (acc_t $ r_var)) $ t
    end
  in
    Goal.prove_global_future
      thy [] []
      (mk_prop (mk_eqt(List.foldl mk_arg r_var' fields, r_var)))
      (fn {context,...} => case_tac context "r" [] NONE 1 THEN
                         case_tac context "r'" [] NONE 1 THEN
                         asm_full_simp_tac context 1)
  end

  (* proves a fold congruence, used for eliminating the accessor
     within the body of the updator more generally than the idupdate
     case. *)
  fun prove_fold_cong (idupdate, updupd_same) = let
    val upd = (head_of o fst o HOLogic.dest_eq
                 o HOLogic.dest_Trueprop o Thm.concl_of) idupdate;
    val ctxt = Proof_Context.init_global thy;
    val ct  = Thm.cterm_of ctxt;
    val cgE = infer_instantiate ctxt [(#1(dest_Var updvar), ct upd)] updcong_foldE;
  in [idupdate, updupd_same] MRS cgE end;

  val fold_congs = map prove_fold_cong (idupdates ~~ updupd_sames);

  fun add_thms (_, []) thy = thy
    | add_thms (sfx, thms) thy =
        (Global_Theory.add_thmss [
          ((Binding.name (record_name ^ sfx), thms), [Simplifier.simp_add])] thy)
        |> #2
        |> add_recursive_record_thms thms []

  fun add_fold_thms (_, []) thy = thy
    | add_fold_thms (sfx, thms) thy =
    let
      val (thms', thy') = thy
         |> Global_Theory.add_thmss [((Binding.name(record_name ^ sfx), thms), [])];
    in
      HoarePackage.add_foldcongs (flat thms') thy'
      |> add_recursive_record_thms [] thms
    end;
in
  thy |> add_thms ("_accupd_same", accupd_sames)
      |> add_thms ("_accupd_diff", accupd_diffs)
      |> add_thms ("_updupd_same", updupd_sames)
      |> add_thms ("_updupd_diff", updupd_diffs)
      |> add_thms ("_idupdates",   idupd_value1 :: idupd_value2 :: idupdates)
      |> add_fold_thms ("_fold_congs", fold_congs)
end



fun define_record_type records thy = let
  (* define algebraic types *)
  fun mk_one_type {record_name, fields} =
      ((Binding.name record_name, [], NoSyn),
       [(Binding.name record_name, map (fn f => #fldty f) fields, NoSyn)])
  val (_, thy) =
      BNF_LFP_Compat.add_datatype
          []
          (map mk_one_type records)
          thy
  val _ = tracing("Defined struct types: "^
                  String.concat (map (fn x => #record_name x ^ " ") records))
  val thy =
      List.foldl (fn (r, thy) => define_functions r thy) thy records

  val thy = List.foldl prove_record_rewrites thy records
in
  thy
end;

(*
add_datatype_i
  true     (* whether to check for some error condition *)
  false    (* use top-level declaration or not,
                with false, constructors will get called Thy.foo.zero etc *)
  ["foo", "bar"]  (* names for theorems *)
  [([], "foo", NoSyn,                     (* type-name, list for arguments *)
    [("zero", [], NoSyn),                 (* constructors for given type *)
     ("suc", [Type(Sign.full_name thy "bar", [])], NoSyn)]),
   ([], "bar", NoSyn,
    [("b1", [TermsTypes.nat], NoSyn),
     ("b2", [TermsTypes.bool, Type(Sign.full_name thy "foo", [])], NoSyn)])]
  thy;

use "recursive_records/recursive_record_package.ML";
val thy0 = the_context();
val thy = RecursiveRecordPackage.define_record_type
  [{record_name = "lnode",
    fields = [{fldname = "data1", fldty = TermsTypes.nat},
              {fldname = "data2", fldty = TermsTypes.nat},
              {fldname = "next",
               fldty = TermsTypes.mk_ptr_ty
                         (Type(Sign.full_name thy0 "lnode", []))}]}]
  thy0;
print_theorems thy;

*)
end;
