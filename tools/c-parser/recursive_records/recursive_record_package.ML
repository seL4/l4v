(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* this is an -*- sml -*- file *)

(*
 * This file builds the Isabelle translations of C structures and unions.
 * These are implemented with Isabelle's datatypes package, and then functions which provide
 * record update syntax are added on top of these.
 *)

signature RECURSIVE_RECORD_PACKAGE =
sig
  (* Constructs the translated type of C struct *)
  (* no type variables allowed! *)
  val define_record_type :
    {record_name : string, members : {name : string, typ : typ} list} list -> theory -> theory

  (* Constructs the translated type of C struct *)
  val define_union_type :
    {union_name : string, members : {name : string, typ : typ} list} list -> theory -> theory

  val get_simpset : theory -> simpset
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
    = RecursiveRecordData.map
        (fn ss =>
          Proof_Context.init_global thy
          |> put_simpset ss
          |> (fn ctxt => ctxt addsimps simps)
          |> fold Raw_Simplifier.add_cong congs
          |> simpset_of)
        thy

val updateN = Record.updateN

fun gen_vars tys = Library.map_index (fn (i,ty) => Free ("x" ^ Int.toString i, ty)) tys

fun make_casename nm =
  case String.explode nm of
    c :: cs => String.implode (Char.toUpper c :: cs)
  | _ => raise Fail "empty member name in union!"

fun make_extractor_name nm =
  "get_" ^ make_casename nm


fun define_record_updator arg (i, {name, typ}) thy =
  let
    val bnm = Binding.name
    val arg_ty = type_of arg
    val (con, args) = strip_comb arg
    val upd_ty = (typ --> typ) --> (arg_ty --> arg_ty)
    val upd_name = suffix updateN name
    val upd_t = Free (upd_name, upd_ty)
    val f = Free ("f", typ --> typ)
    val lhs_t = upd_t $ f $ arg
    val modified_args = Library.nth_map i (curry op$ f) args
    val rhs_t = List.foldl (op$ o swap) con modified_args
    val defn = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs_t, rhs_t))
  in
    thy
    |> BNF_LFP_Compat.primrec_global
           [(bnm upd_name, NONE, NoSyn)]
           [(((bnm (upd_name ^ "_def"), []), defn), [], [])]
    |> snd
  end

fun define_record_functions (r as {record_name, members}) thy =
  let
    val recordnameb = Binding.name record_name
    val domty = Type (Sign.full_name thy recordnameb, [])
    val constructor_ty = List.foldr op--> domty (map #typ members)
    val constructor_t = Const (Sign.intern_const thy record_name, constructor_ty)
    val args = gen_vars (map #typ members)
    val record_value_t = List.foldl (fn (a,t) => t $ a) constructor_t args
  in
    (thy
      |> Sign.add_path record_name
      |> Library.fold_index (define_record_updator record_value_t) members
      |> RecursiveRecordPP.install_translations r
      |> Sign.parent_path)
    before
    tracing("Defined accessor and update functions for record " ^ record_name)
  end


fun define_union_accessor arg (({name,typ}, result), thy) =
  let
    val acc_ty = type_of arg --> typ
    val acc_t = Free (name, acc_ty)
    val defn = HOLogic.mk_Trueprop (HOLogic.mk_eq (acc_t $ arg, result))      
  in
    thy
    |> BNF_LFP_Compat.primrec_global
         [(Binding.name name, NONE, NoSyn)]
         [(((Binding.name (name ^ "_def"), []), defn), [], [])]
    |> snd
  end

fun define_union_updator arg (i, {name,typ}) thy =
  let
    val arg_ty = type_of arg
    val (con, args) = strip_comb arg
    val upd_ty = (typ --> typ) --> (arg_ty --> arg_ty)
    val upd_name = suffix updateN name
    val upd_t = Free (upd_name, upd_ty)
    val f = Free ("f", typ --> typ)
    val lhs_t = upd_t $ f $ arg
    val modified_args = Library.nth_map i (curry op$ f) args
    val rhs_t = List.foldl (op$ o swap) con modified_args
    val defn = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs_t, rhs_t))
  in
    thy
    |> BNF_LFP_Compat.primrec_global
           [(Binding.name upd_name, NONE, NoSyn)]
           [(((Binding.name (upd_name ^ "_def"), []), defn), [], [])]
    |> snd
  end

fun define_union_functions (u as {union_name, members}) thy =
  let
  val ctxt = Context.proof_of (Context.Theory thy)
  val union_typ = Type (Sign.full_name thy (Binding.name union_name), [])
  (* define the extractor functions *)
  fun const_undef_t T U = Term.absdummy T (Const (@{const_name "undefined"}, U))
  fun const_id_t T = Abs ("x", T, Bound 0)
  val case_union_t = Syntax.parse_term ctxt ("case_"^union_name)
  fun mk_defn (i,{name,typ=lhstyp}) thy =
    let
      val extractor_name = make_extractor_name name
      val bname = Binding.name (extractor_name ^ "_def")
      val lhs = Free (extractor_name, union_typ --> lhstyp)
      val rhs =
        Library.fold_index
        (fn (j, {typ,...}) => fn acc_t =>
          acc_t $ (if i = j then const_id_t typ else const_undef_t typ lhstyp))
        members
        case_union_t
      val (_,ctxt) =
        Specification.definition
          NONE
          []
          []
          ((bname,[]), Logic.mk_equals (lhs, rhs))
          (Named_Target.theory_init thy)
    in
      Local_Theory.exit_global ctxt
    end
in
  (thy |> Sign.add_path union_name
       |> Library.fold_index mk_defn members
(*
       |> Library.fold_index (define_union_updator union_value_t) members
*)
       |> Sign.parent_path)
  before
  tracing("Defined accessor and update functions for union "^union_name)
end


fun cprod_less_diag list =
  let
    fun recurse (l,acc) =
      case l of
        []   => acc
      | h::t =>
          let
            val acc' = List.foldl (fn (e,acc) => (h,e) :: (e,h) :: acc) acc t
          in
            recurse (t,acc')
          end
  in
    recurse (list,[])
  end

fun lower_triangle list =
  let
    fun recurse acc l =
      case l of
        []     => acc
      | h :: t =>
          let
            val acc' = List.foldl (fn (e,acc) => (e,h) :: acc) acc t
          in
            recurse acc' t
          end
  in
    recurse [] list
  end

val updcong_foldE = @{thm "idupdate_compupdate_fold_congE"}

val [updvar] =
  let
    (*Accumulates the Vars in the term, suppressing duplicates.*)
    val get_vars =
      fold_aterms (fn t as Var _ => Ord_List.insert Term_Ord.term_ord t | _ => fn a => a)
  in
    get_vars (nth (Thm.prems_of updcong_foldE) 1) []
  end

fun prove_record_rewrites ({record_name, members}, thy) =
  let
    val _ = tracing("Proving rewrites for struct "^record_name)
    val rty = Type (Sign.intern_type thy record_name, [])
    val r_var = Free ("r", rty)
    val r_var' = Free ("r'", rty)
    val domty = Type (Sign.full_name thy (Binding.name record_name), [])
    val constructor_ty = List.foldr op--> domty (map #typ members)
    val constructor_t =
        Const (Sign.intern_const thy record_name, constructor_ty)
    val case_tac = Induct_Tacs.case_tac
    fun prove g =
        Goal.prove_global_future thy [] [] (HOLogic.mk_Trueprop g)
                          (fn {context,...} =>
                              case_tac context "r" [] NONE 1 THEN
                              asm_full_simp_tac context 1)
    fun mk_upd_t {name,typ} =
        Const (Sign.intern_const thy (suffix updateN name),
              (typ --> typ) --> (rty --> rty))
  
    fun prove_accupd_same (fld as {name, typ}) =
      let
        val f = Free ("f", typ --> typ)
        val acc = Const (Sign.intern_const thy name, rty --> typ)
        val upd = mk_upd_t fld
        val lhs_t = acc $ (upd $ f $ r_var)
        val rhs_t = f $ (acc $ r_var)
      in
        prove (HOLogic.mk_eq (lhs_t, rhs_t))
      end
    val accupd_sames = map prove_accupd_same members
  
    fun prove_accupd_diff (acc, upd) =
      let
        val {name = accname, typ = accty} = acc
        val {name = _, typ = updty} = upd
        val acc_t = Const (Sign.intern_const thy accname, rty --> accty)
        val upd_t = mk_upd_t upd
        val f = Free ("f", updty --> updty)
        val lhs_t = acc_t $ (upd_t $ f $ r_var)
        val rhs_t = acc_t $ r_var
      in
        prove (HOLogic.mk_eq (lhs_t, rhs_t))
      end
    val accupd_diffs = map prove_accupd_diff (cprod_less_diag members)

    fun prove_updupd_same (fld as {typ,...}) =
      let
        val ffty = typ --> typ
        val upd_t = mk_upd_t fld
        val f = Free ("f", ffty)
        val g = Free ("g", ffty)
        val lhs_t = upd_t $ f $ (upd_t $ g $ r_var)
        val comp = Const ("Fun.comp", ffty --> (ffty --> ffty))
        val rhs_t = upd_t $ (comp $ f $ g) $ r_var
      in
        prove (HOLogic.mk_eq (lhs_t, rhs_t))
      end
    val updupd_sames = map prove_updupd_same members
  
    fun prove_updupd_diff (upd1, upd2) =
      let
        val {name = _, typ = updty1} = upd1
        val {name = _, typ = updty2} = upd2
        val upd1_t = mk_upd_t upd1
        val upd2_t = mk_upd_t upd2
        val f = Free ("f", updty1 --> updty1)
        val g = Free ("g", updty2 --> updty2)
        val lhs_t = upd1_t $ f $ (upd2_t $ g $ r_var)
        val rhs_t = upd2_t $ g $ (upd1_t $ f $ r_var)
      in
        prove (HOLogic.mk_eq (rhs_t, lhs_t))
      end
    val updupd_diffs = map prove_updupd_diff (lower_triangle members)
  
    fun prove_idupdates (fld as {name, typ}) =
    let
      val upd_t = mk_upd_t fld
      val acc_t = Const (Sign.intern_const thy name, rty --> typ)
    in
      prove (HOLogic.mk_eq (upd_t $ (Term.abs ("_",typ) (acc_t $ r_var)) $ r_var, r_var))
    end
    val idupdates = map prove_idupdates members
  
    (* proves that (| fld1 = fld1 v, fld2 = fld2 v, fld3 = fld3 v,..|) = v *)
    val idupd_value1 =
      let
        fun mk_arg ({name, typ}, acc) =
          let
            val acc_t = Const (Sign.intern_const thy name, rty --> typ)
          in
            acc $ (acc_t $ r_var)
          end
      in
        prove (HOLogic.mk_eq (List.foldl mk_arg constructor_t members, r_var))
      end

  (* proves that u (| fld1 := fld1 v, fld2 := fld2 v, ... |) = v *)
  val idupd_value2 =
    let
      fun mk_arg (fld as {name, typ}, t) =
        let
          val acc_t = Const (Sign.intern_const thy name, rty --> typ)
          val upd_t = mk_upd_t fld
        in
          upd_t $ (Term.abs ("_",typ) (acc_t $ r_var)) $ t
        end
    in
      Goal.prove_global_future
        thy [] []
        (HOLogic.mk_Trueprop (HOLogic.mk_eq (List.foldl mk_arg r_var' members, r_var)))
        (fn {context,...} => case_tac context "r" [] NONE 1 THEN
                           case_tac context "r'" [] NONE 1 THEN
                           asm_full_simp_tac context 1)
    end

  (* proves a fold congruence, used for eliminating the accessor
     within the body of the updator more generally than the idupdate
     case. *)
  fun prove_fold_cong idupdate updupd_same =
    let
      val upd = (head_of o fst o HOLogic.dest_eq
                   o HOLogic.dest_Trueprop o Thm.concl_of) idupdate;
      val ctxt = Proof_Context.init_global thy;
      val ct_upd = Thm.cterm_of ctxt upd;
      val cgE = infer_instantiate ctxt [(#1(dest_Var updvar), ct_upd)] updcong_foldE;
    in
      [idupdate, updupd_same] MRS cgE
    end

  val fold_congs = map2 prove_fold_cong idupdates updupd_sames;

  fun add_thms (_, []) thy = thy
    | add_thms (sfx, thms) thy =
        thy
        |> Global_Theory.add_thmss
            [((Binding.name (record_name ^ sfx), thms), [Simplifier.simp_add])]
        |> #2
        |> add_recursive_record_thms thms []

  fun add_fold_thms (_, []) thy = thy
    | add_fold_thms (sfx, thms) thy =
      thy
      |> Global_Theory.add_thmss [((Binding.name (record_name ^ sfx), thms), [])]
      |>> flat
      |-> Hoare.add_foldcongs
      |> add_recursive_record_thms [] thms
  in
    thy
    (* the accupd_diffs theorems are simplifications of the following shapes:
     *   x_update f (y_update g r) = y_update f (x_update g r)    (where x occurs before y)
     *)
    |> add_thms ("_accupd_same", accupd_sames)
    (* the accupd_diffs theorems are simplifications of the following shapes:
     *   rec0.x (rec0.y_update f r) = rec0.x r    (where x is not y)
     *)
    |> add_thms ("_accupd_diff", accupd_diffs)
    (* the updupd_sames theorems are simplifications of the following shape:
     *   x_update f (x_update g r) = x_update (f \<circ> g) r
     *)
    |> add_thms ("_updupd_same", updupd_sames)
    (* the updupd_diffs theorems are simplifications of the following shape:
     *   rec0.x (rec0.x_update f r) = f (rec0.x r)
     *)
    |> add_thms ("_updupd_diff", updupd_diffs)
    (* the idupd theorems are simplifications of the following shapes:
     *   rec (rec.x r.x) (rec.y r) ... (rec.z r)) = r
     *   r'\<lparr> x := rec.x r, y := rec.y r, ... , z := rec.z r \<rparr> = r
     *   r\<lparr> x := rec.x r \<rparr> = r
     *)
    |> add_thms ("_idupdates",   idupd_value1 :: idupd_value2 :: idupdates)
    (* the record fold congs are simplification rules of the following shape:
     *   \<lbrakk> r = r'; rec0.x r' = v'; \<And>v. v' = v \<Longrightarrow> f v = f' v \<rbrakk>
     *   \<Longrightarrow> rec0.x_update f r = rec0.x_update f' r'
     *      (for every field x)
     *)
    |> add_fold_thms ("_fold_congs", fold_congs)
  end

(*
 * Proves helpful rewrites on the union setter and accessor functions
 *)
fun prove_union_rewrites ({union_name, members}, thy) =
  let
    val _ = tracing("Proving rewrites for union "^union_name)

    fun add_thms (_, []) thy = thy
      | add_thms (sfx, thms) thy =
          thy
          |> Global_Theory.add_thmss
              [((Binding.name (union_name ^ sfx), thms), [Simplifier.simp_add])]
          |> #2
          |> add_recursive_record_thms thms []

    fun prove g =
      Goal.prove_global_future thy [] [] (HOLogic.mk_Trueprop g)
        (fn {context = ctxt,...} =>
          let
            val extractor_defns =
              map
                (Proof_Context.get_thm ctxt o (fn n => make_extractor_name n ^ "_def") o #name)
                members
          in
            asm_full_simp_tac (ctxt addsimps extractor_defns) 1
          end)

    (* lemmas of the forms:
         x (X a) = a
         y (X a) = undefined
    *)
    (* TODO: the second won't be globally true in future *)
    fun prove_extractor_reduce (i,{name,typ = T}) =
      let
        val unty = Type (Sign.intern_type thy union_name, [])
        val constructor = Const (Sign.intern_const thy (make_casename name), T --> unty)
        val val_var = Free ("x", T) (* has to be same as in the case_tac above *)
        fun mk_undef T = Const (@{const_name undefined}, T)
      in
        Library.map_index
          (fn (j,{name = j_name, typ = U}) =>
            let
              val extractor_name = make_extractor_name j_name
              val extractor = Const (Sign.intern_const thy extractor_name, unty --> U)
              val lhs = extractor $ (constructor $ val_var)
            in
              if i = j then
                prove (HOLogic.mk_eq (lhs, val_var))
              else
                prove (HOLogic.mk_eq (lhs, mk_undef U))
            end)
          members
      end
    val extractor_reduce_thms = List.concat (Library.map_index prove_extractor_reduce members)
  in
    thy
    |> add_thms ("_extractor_reduce", extractor_reduce_thms)
  end
(*
  let
    val _ = tracing("Proving rewrites for union "^union_name)
    val rty = Type (Sign.intern_type thy union_name, [])
    val r_var = Free ("r", rty)
    val r_var' = Free ("r'", rty)
    val domty = Type (Sign.full_name thy (Binding.name union_name), [])
    val constructor_ty = List.foldr op--> domty (map #typ members)
    val constructor_t =
        Const (Sign.intern_const thy union_name, constructor_ty)
    val case_tac = Induct_Tacs.case_tac
    fun prove g =
        Goal.prove_global_future thy [] [] (HOLogic.mk_Trueprop g)
                          (fn {context,...} =>
                              case_tac context "r" [] NONE 1 THEN
                              asm_full_simp_tac context 1)
    fun mk_upd_t {name,typ} =
        Const (Sign.intern_const thy (suffix updateN name),
              (typ --> typ) --> (rty --> rty))
  
    fun prove_accupd_same (memb as {name, typ}) =
      let
        val f = Free ("f", typ --> typ)
        val acc = Const (Sign.intern_const thy name, rty --> typ)
        val upd = mk_upd_t memb
        val lhs_t = acc $ (upd $ f $ r_var)
        val rhs_t = f $ (acc $ r_var)
      in
        prove (HOLogic.mk_eq (lhs_t, rhs_t))
      end
    val accupd_sames = map prove_accupd_same members

    fun prove_accupd_diff (acc, upd) = let
      val {name = accname, typ = accty} = acc
      val {name = _, typ = updty} = upd
      val acc_t = Const (Sign.intern_const thy accname, rty --> accty)
      val upd_t = mk_upd_t upd
      val f = Free ("f", updty --> updty)
      val lhs_t = acc_t $ (upd_t $ f $ r_var)
      val rhs_t = acc_t $ r_var
    in
      prove (HOLogic.mk_eq (lhs_t, rhs_t))
    end
    val accupd_diffs = map prove_accupd_diff (cprod_less_diag members)

    fun prove_updupd_same (fld as {typ,...}) =
      let
        val ffty = typ --> typ
        val upd_t = mk_upd_t fld
        val f = Free ("f", ffty)
        val g = Free ("g", ffty)
        val lhs_t = upd_t $ f $ (upd_t $ g $ r_var)
        val comp = Const ("Fun.comp", ffty --> (ffty --> ffty))
        val rhs_t = upd_t $ (comp $ f $ g) $ r_var
      in
        prove (HOLogic.mk_eq (lhs_t, rhs_t))
      end
    val updupd_sames = map prove_updupd_same members

    fun prove_updupd_diff (upd1, upd2) =
      let
        val {typ = updty1, ...} = upd1
        val {typ = updty2, ...} = upd2
        val upd1_t = mk_upd_t upd1
        val upd2_t = mk_upd_t upd2
        val f = Free ("f", updty1 --> updty1)
        val g = Free ("g", updty2 --> updty2)
        val lhs_t = upd1_t $ f $ (upd2_t $ g $ r_var)
        val rhs_t = upd2_t $ g $ (upd1_t $ f $ r_var)
      in
        prove (HOLogic.mk_eq (rhs_t, lhs_t))
      end
    val updupd_diffs = map prove_updupd_diff (lower_triangle members)

    fun prove_idupdates (fld as {name, typ}) =
      let
        val upd_t = mk_upd_t fld
        val acc_t = Const (Sign.intern_const thy name, rty --> typ)
      in
        prove (HOLogic.mk_eq (upd_t $ (Term.abs ("_",typ) (acc_t $ r_var)) $ r_var, r_var))
      end
    val idupdates = map prove_idupdates members

    (* proves that (| fld1 = fld1 v, fld2 = fld2 v, fld3 = fld3 v,..|) = v *)
    val idupd_value1 =
      let
        fun mk_arg ({name, typ}, acc) =
          acc $ (Const (Sign.intern_const thy name, rty --> typ) $ r_var)
      in
        prove (HOLogic.mk_eq (List.foldl mk_arg constructor_t members, r_var))
      end

    (* proves that u (| fld1 := fld1 v, fld2 := fld2 v, ... |) = v *)
    val idupd_value2 =
      let
        fun mk_arg (fld as {name, typ}, t) =
          let
            val acc_t = Const (Sign.intern_const thy name, rty --> typ)
            val upd_t = mk_upd_t fld
          in
            upd_t $ (Term.abs ("_",typ) (acc_t $ r_var)) $ t
          end
      in
        Goal.prove_global_future
          thy [] []
          (HOLogic.mk_Trueprop (HOLogic.mk_eq (List.foldl mk_arg r_var' members, r_var)))
          (fn {context,...} => case_tac context "r" [] NONE 1 THEN
                             case_tac context "r'" [] NONE 1 THEN
                             asm_full_simp_tac context 1)
      end

    (* proves a fold congruence, used for eliminating the accessor
       within the body of the updator more generally than the idupdate
       case. *)
    fun prove_fold_cong idupdate updupd_same =
      let
        val upd = (head_of o fst o HOLogic.dest_eq
                     o HOLogic.dest_Trueprop o Thm.concl_of) idupdate;
        val ctxt = Proof_Context.init_global thy;
        val ct_upd = Thm.cterm_of ctxt upd;
        val cgE = infer_instantiate ctxt [(#1(dest_Var updvar), ct_upd)] updcong_foldE;
      in
        [idupdate, updupd_same] MRS cgE
      end
  
    val fold_congs = map2 prove_fold_cong idupdates updupd_sames

    fun add_thms (_, []) thy = thy
      | add_thms (sfx, thms) thy =
          thy
          |> Global_Theory.add_thmss
              [((Binding.name (union_name ^ sfx), thms), [Simplifier.simp_add])]
          |> #2
          |> add_recursive_record_thms thms []
  
    fun add_fold_thms (_, []) thy = thy
      | add_fold_thms (sfx, thms) thy =
        thy
        |> Global_Theory.add_thmss [((Binding.name (union_name ^ sfx), thms), [])]
        |>> flat
        |-> Hoare.add_foldcongs
        |> add_recursive_record_thms [] thms
  in
    thy
    (* the accupd_diffs theorems are simplifications of the following shapes:
     *   x_update f (y_update g r) = y_update f (x_update g r)    (where x occurs before y)
     *)
    |> add_thms ("_accupd_same", accupd_sames)
    (* the accupd_diffs theorems are simplifications of the following shapes:
     *   rec0.x (rec0.y_update f r) = rec0.x r    (where x is not y)
     *)
    |> add_thms ("_accupd_diff", accupd_diffs)
    (* the updupd_sames theorems are simplifications of the following shape:
     *   x_update f (x_update g r) = x_update (f \<circ> g) r
     *)
    |> add_thms ("_updupd_same", updupd_sames)
    (* the updupd_diffs theorems are simplifications of the following shape:
     *   rec0.x (rec0.x_update f r) = f (rec0.x r)
     *)
    |> add_thms ("_updupd_diff", updupd_diffs)
    (* the idupd theorems are simplifications of the following shapes:
     *   rec (rec.x r.x) (rec.y r) ... (rec.z r)) = r
     *   r'\<lparr> x := rec.x r, y := rec.y r, ... , z := rec.z r \<rparr> = r
     *   r\<lparr> x := rec.x r \<rparr> = r
     *)
    |> add_thms ("_idupdates",   idupd_value1 :: idupd_value2 :: idupdates)
    (* the record fold congs are simplification rules of the following shape:
     *   \<lbrakk> r = r'; rec0.x r' = v'; \<And>v. v' = v \<Longrightarrow> f v = f' v \<rbrakk>
     *   \<Longrightarrow> rec0.x_update f r = rec0.x_update f' r'
     *      (for every field x)
     *)
    |> add_fold_thms ("_fold_congs", fold_congs)
  end
*)


fun define_record_type records thy =
  let
    (* define algebraic types *)
    val fpT_names = map (Sign.full_name thy o Binding.name o #record_name) records

    fun spec_of {record_name, members} =
      let
        val b = Binding.name record_name
        val field_bindings = map (fn {name,typ} => (Binding.name name, typ)) members
        val case_bindings = [(( (Binding.empty, b), field_bindings), NoSyn)]
      in
        ((((([], b), NoSyn), case_bindings), (Binding.empty, Binding.empty, Binding.empty)), [])
      end
    val specs = map spec_of records
  in
    thy
    |> Named_Target.theory_map
       (BNF_FP_Def_Sugar.co_datatypes
          BNF_FP_Rec_Sugar_Util.Least_FP
          BNF_LFP.construct_lfp
          (Ctr_Sugar.default_ctr_options, specs))
    |> perhaps (try (BNF_LFP_Compat.datatype_compat_global fpT_names))
    |> tap (fn _ => tracing("Defined struct types: "^
                      String.concat (map (fn x => #record_name x ^ " ") records)))
    |> (fn thy => List.foldl (uncurry define_record_functions) thy records)
    |> (fn thy => List.foldl prove_record_rewrites thy records)
  end

fun define_union_type unions thy =
  let
    (* define algebraic types *)
    val fpT_names = map (Sign.full_name thy o Binding.name o #union_name) unions;
  
    fun spec_of {union_name, members} =
      let
        val constructor = Binding.name union_name
        fun member_to_binding {name,typ} =
          (((Binding.empty, Binding.name (make_casename name)), [(Binding.empty, typ)]), NoSyn)
        val case_bindings = map member_to_binding members
      in
        ((((([], constructor), NoSyn), case_bindings),
          (Binding.empty, Binding.empty, Binding.empty)), [])
      end
    val specs = map spec_of unions;
  in
    thy
    |> Named_Target.theory_map
       (BNF_FP_Def_Sugar.co_datatypes
          BNF_FP_Rec_Sugar_Util.Least_FP
          BNF_LFP.construct_lfp
          (Ctr_Sugar.default_ctr_options, specs))
    |> perhaps (try (BNF_LFP_Compat.datatype_compat_global fpT_names))
    |> tap (fn _ => tracing("Defined union types: "^
                      String.concat (map (fn x => #union_name x ^ " ") unions)))
    |> (fn thy => List.foldl (uncurry define_union_functions) thy unions)
    |> (fn thy => List.foldl prove_union_rewrites thy unions)
  end

(* Example use:

use "recursive_records/recursive_record_package.ML";

val thy0 = the_context ();
val thy = RecursiveRecordPackage.define_record_type
  [{record_name = "lnode",
    members = [{name = "data1", typ = TermsTypes.nat},
              {name = "data2", typ = TermsTypes.nat},
              {name = "next",
               typ = TermsTypes.mk_ptr_ty
                         (Type (Sign.full_name thy0 "lnode", []))}]}]
  thy0;

print_theorems thy;
*)
end;
