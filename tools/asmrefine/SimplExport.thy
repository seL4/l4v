(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory SimplExport

imports GraphLang CommonOps GlobalsSwap

begin

lemma field_lvalue_offset_eq:
  "field_lookup (typ_info_t TYPE('a :: c_type)) f 0 = Some v
        \<Longrightarrow> field_lvalue (ptr :: 'a ptr) f = ptr_val ptr + of_nat (snd v)"
  apply (cases v, simp, drule field_lookup_offset_eq)
  apply (simp add: field_lvalue_def)
  done

ML {*
fun dest_binT (Type (@{type_name signed}, [t])) = Word_Lib.dest_binT t
  | dest_binT t = Word_Lib.dest_binT t

fun dest_array_type (Type (@{type_name array}, [T, n])) = let
    val (s, _) = dest_Type n
    val s = Long_Name.base_name s
  in if String.isPrefix "tyCopy" s
    then (T, fst (read_int (raw_explode (unprefix "tyCopy" s))))
    else (T, dest_binT n)
  end
  | dest_array_type typ = raise TYPE ("dest_array_type", [typ], [])

fun dest_array_init (Const (@{const_name fupdate}, _) $ n $ f $ arr) = let
    val xs = dest_array_init arr
    val n = HOLogic.dest_number n |> snd
  in nth_map n (curry betapply f) xs end
  | dest_array_init (Const (@{const_name FCP}, T) $ f) = let
    val (_, width) = dest_array_type (range_type T)
  in map (curry betapply f) (map (HOLogic.mk_number @{typ nat})
    (0 upto width - 1))
  end
  | dest_array_init t = raise TERM ("dest_array_init", [t])

val ops = Symtab.make [
    (@{const_name "plus"}, ("Plus", true)),
    (@{const_name "minus"}, ("Minus", true)),
    (@{const_name "times"}, ("Times", true)),
    (@{const_name "div_class.mod"}, ("Modulus", true)),
    (@{const_name "div_class.div"}, ("DividedBy", true)),
    (@{const_name "bitAND"}, ("BWAnd", true)),
    (@{const_name "bitOR"}, ("BWOr", true)),
    (@{const_name "bitXOR"}, ("BWXOR", true)),
    (@{const_name "conj"}, ("And", true)),
    (@{const_name "disj"}, ("Or", true)),
    (@{const_name "implies"}, ("Implies", true)),
    (@{const_name "HOL.eq"}, ("Equals", false)),
    (@{const_name "less"}, ("Less", false)),
    (@{const_name "less_eq"}, ("LessEquals", false)),
    (@{const_name "word_sless"}, ("SignedLess", false)),
    (@{const_name "word_sle"}, ("SignedLessEquals", false)),
    (@{const_name "Not"}, ("Not", true)),
    (@{const_name "bitNOT"}, ("BWNot", true)),
    (@{const_name "ucast"}, ("WordCast", false)),
    (@{const_name "scast"}, ("WordCastSigned", false)),
    (@{const_name "True"}, ("True", true)),
    (@{const_name "False"}, ("False", true)),
    (@{const_name "If"}, ("IfThenElse", false)),
    (@{const_name "Set.member"}, ("MemDom", false)),
    (@{const_name "shiftl"}, ("ShiftLeft", false)),
    (@{const_name "shiftr"}, ("ShiftRight", false)),
    (@{const_name "sshiftr"}, ("SignedShiftRight", false)),
    (@{const_name "all_htd_updates"}, ("HTDUpdate", false))
  ] |> Symtab.lookup

fun locals ctxt = Syntax.read_typ ctxt "'a myvars"
  |> Record.get_recT_fields (Proof_Context.theory_of ctxt)
  |> fst
  |> filter_out (fn (s, _) => s = @{const_name "globals"})
  |> Symtab.make |> Symtab.defined

fun local_upds ctxt = Syntax.read_typ ctxt "'a myvars"
  |> Record.get_recT_fields (Proof_Context.theory_of ctxt)
  |> fst
  |> filter_out (fn (s, _) => s = @{const_name "globals"})
  |> map (apfst (suffix Record.updateN))
  |> Symtab.make |> Symtab.defined

fun get_field ctxt s = let
    val xs = space_explode "." s
    val fld = List.last xs
    val tp = rev xs |> tl |> rev |> space_implode "."
    val is_upd = String.isSuffix "_update" fld
    val fld = if is_upd then unsuffix "_update" fld else fld
    val _ = Proof_Context.get_thm ctxt
        (tp ^ "_" ^ fld ^ "_fl_Some")
  in SOME (tp, fld, is_upd) end
    handle ERROR _ => NONE
       | Bind => NONE

val read_const = Proof_Context.read_const {proper = true, strict = true}

fun process_struct ctxt csenv (nm, flds) = let
    val offs = map (ProgramAnalysis.offset csenv (map snd flds))
        (0 upto (length flds - 1))
    val cons = read_const ctxt (nm ^ "." ^ nm)
    val typ = dest_Const cons |> snd |> strip_type |> snd
    val sz = ProgramAnalysis.sizeof csenv (Absyn.StructTy nm)
    val algn = ProgramAnalysis.alignof csenv (Absyn.StructTy nm)
    val accs = map (fst #> prefix (nm ^ ".")
        #> read_const ctxt) flds
  in (nm, (cons, typ, sz, algn, map fst flds ~~ (accs ~~ offs))) end

fun structs ctxt csenv = ProgramAnalysis.get_senv csenv
  |> map (process_struct ctxt csenv)
  |> Symtab.make

fun structs_by_typ ctxt csenv = Symtab.dest (structs ctxt csenv)
  |> map (fn (nm, (cons, typ, sz, algn, flds)) => (fst (dest_Type typ), (nm, cons, sz, algn, flds)))
  |> Symtab.make |> Symtab.lookup

fun cons_fields ctxt csenv = structs ctxt csenv |> Symtab.dest
  |> map (fn (_, (cons, typ, _, _, flds))
    => (fst (dest_Const cons), (fst (dest_Type typ),
           map (snd #> fst #> dest_Const #> fst) flds)))
  |> Symtab.make |> Symtab.lookup

fun enums ctxt csenv = let
    val Absyn.CE ecenv = ProgramAnalysis.cse2ecenv csenv
  in
    #enumenv ecenv |> Symtab.dest
    |> map (fn (s, (n, _)) =>
        (read_const ctxt s
            |> dest_Const |> fst, n))
    |> Symtab.make |> Symtab.lookup
  end

fun cons_field_upds ctxt csenv = let
  val simps = ProgramAnalysis.get_senv csenv
    |> maps (fn (tp, vs) => map (pair tp o fst) vs)
    |> maps (fn (tp, fld) => [Proof_Context.get_thm ctxt
          (tp ^ "." ^ fld ^ ".simps"),
        Proof_Context.get_thm ctxt
          (tp ^ "." ^ fld ^ Record.updateN ^ ".simps")])
  val accups = ProgramAnalysis.get_senv csenv
    |> map (fn (tp, _) => (tp, Proof_Context.get_thms ctxt
          (tp ^ "_accupd_same")))
    |> maps (fn (_, [t]) => [t]
              | (tp, ts) => ts @ Proof_Context.get_thms ctxt
          (tp ^ "_accupd_diff"))
  val rews = map (Thm.concl_of #> HOLogic.dest_Trueprop #> HOLogic.dest_eq) (simps @ accups)
  in Pattern.rewrite_term (Proof_Context.theory_of ctxt) rews [] end

type export_params = {cons_field_upds: term -> term,
         cons_fields: string -> (string * string list) option,
         const_globals: Termtab.key -> string option,
         enums: string -> int option,
         local_upds: string -> bool,
         locals: string -> bool,
         rw_global_accs: string -> string option,
         rw_global_upds: string -> string option,
         rw_globals_tab: (term * term) Symtab.table,
         structs_by_typ:
         string -> (string * term * int * int * (string * (term * int)) list) option}

fun get_all_export_params ctxt csenv : export_params = let
    (* assuming DefineGlobalsList has already run *)
    val defs = Proof_Context.get_thms ctxt "global_data_defs"
    val rhss = map (Thm.concl_of #> Logic.dest_equals #> snd) defs
    val const_globals = map_filter
      (fn (Const (@{const_name const_global_data}, _) $ nm $ v)
            => SOME (HOLogic.dest_string nm, v)
        | _ => NONE) rhss |> map swap |> Termtab.make |> Termtab.lookup
    val rw_globals = map_filter (fn (Const (@{const_name global_data}, _) $ nm $ get $ set)
        => SOME (HOLogic.dest_string nm, get, set) | _ => NONE) rhss
    val rw_globals_tab = Symtab.make (map (fn x => (#1 x, (#2 x, #3 x))) rw_globals)
    val rw_global_accs = map (fn (nm, c, _) => (fst (dest_Const c), nm)) rw_globals
        |> Symtab.make |> Symtab.lookup
    val rw_global_upds = map (fn (nm, _, c) => (fst (dest_Const c), nm)) rw_globals
        |> Symtab.make |> Symtab.lookup
  in {const_globals = const_globals, rw_globals_tab = rw_globals_tab,
    rw_global_accs = rw_global_accs,
    rw_global_upds = rw_global_upds,
    cons_field_upds = cons_field_upds ctxt csenv,
    enums = enums ctxt csenv,
    cons_fields = cons_fields ctxt csenv,
    structs_by_typ = structs_by_typ ctxt csenv,
    locals = locals ctxt,
    local_upds = local_upds ctxt} end
*}

ML {*

fun convert_type _ _ @{typ bool} = "Bool"
  | convert_type _ _ (Type (@{type_name word}, [n]))
    = "Word " ^ signed_string_of_int (dest_binT n)
  | convert_type abs ctxt (Type (@{type_name array}, [t, n]))
    = "Array " ^ convert_type abs ctxt t ^ " " ^ (string_of_int (dest_binT n)
        handle TYPE _ => (case n of Type (s, []) => (unprefix "tyCopy" (Long_Name.base_name s)
            handle Fail _ => raise TYPE ("convert_type", [t, n], []))
         | _ => raise TYPE ("convert_type", [t, n], [])))
  | convert_type true ctxt (Type (@{type_name ptr}, [T])) = "Ptr " ^ convert_type true ctxt T
  | convert_type false _ (Type (@{type_name ptr}, _)) = "Word 32"
  | convert_type _ _ @{typ "word32 \<Rightarrow> word8"} = "Mem"
  | convert_type _ _ @{typ "word32 \<Rightarrow> bool"} = "Dom"
  | convert_type _ _ @{typ "word32 set"} = "Dom"
  | convert_type _ _ @{typ heap_typ_desc} = "HTD"
  | convert_type _ _ @{typ nat} = "Word 32"
  | convert_type _ _ @{typ unit} = "UNIT"
  | convert_type _ _ (Type (@{type_name itself}, _)) = "Type"
  | convert_type _ _ @{typ int} = raise TYPE ("convert_type: int", [], [])
  | convert_type _ ctxt (Type (s, [])) = if Long_Name.base_name s = "machine_state" then "PMS"
    else (Proof_Context.get_thm ctxt
        (Long_Name.base_name s ^ "_td_names"); "Struct " ^ s)
  | convert_type _ _ T = raise TYPE ("convert_type", [T], [])
*}

consts
  pseudo_acc :: "'a \<Rightarrow> 'a"

text {*

Phase 1 of the conversion, converts accs and upds on SIMPL
state (a record) to accs of named vars, using the pseudo_acc
constant above to guard the accesses and lists of upds with strings.
*}

ML {*

fun naming localname = Long_Name.base_name localname
    |> unsuffix "_'" |> suffix "#v"

fun mk_pseudo_acc s T = Const (@{const_name pseudo_acc}, T --> T)
    $ Free (s, T)

fun dest_global_mem_acc_addr (params : export_params) t = let
    val acc = case head_of t of Const (c, _) => #rw_global_accs params c
        | _ => NONE
    val const = #const_globals params t
    val T = fastype_of t
  in case (const, acc) of
      (SOME nm, _) => SOME (TermsTypes.mk_global_addr_ptr (nm, T))
    | (NONE, SOME nm) => SOME (TermsTypes.mk_global_addr_ptr (nm, T))
    | (NONE, NONE) => NONE
  end

fun dest_ptr_type (Type (@{type_name ptr}, [a])) = a
  | dest_ptr_type T = raise TYPE ("dest_ptr_type", [T], [])

fun mk_memacc p = let
    val T = fastype_of p
  in Const (@{const_name h_val}, @{typ heap_mem} --> T --> dest_ptr_type T)
    $ mk_pseudo_acc "Mem" @{typ heap_mem} $ p end

fun convert_fetch_phase1 _ (@{term hrs_mem} $ _) = mk_pseudo_acc "Mem" @{typ heap_mem}
  | convert_fetch_phase1 _ (@{term hrs_htd} $ _) = mk_pseudo_acc "HTD" @{typ heap_typ_desc}
  | convert_fetch_phase1 params (Abs (s, T, t))
    = Abs (s, T, convert_fetch_phase1 params t)
  | convert_fetch_phase1 params t = if not (is_Const (head_of t)) then t
  else let
    val (f, xs) = strip_comb t
    val (c, _) = dest_Const f
    val T = fastype_of t
  in case (#locals params c, dest_global_mem_acc_addr params t, #enums params c) of
    (true, _, _) => (case xs of [Free ("s", _)] => mk_pseudo_acc (naming c) T
        | [Free ("rv", _)] => mk_pseudo_acc ("rv#space#" ^ naming c) T
        | _ => raise TERM ("convert_fetch_phase1: acc?", [t])
    )
  | (_, SOME p, _) => mk_memacc p
  | (_, _, SOME n) => HOLogic.mk_number T n
  | _ => list_comb (f, map (convert_fetch_phase1 params) xs)
  end

fun mk_memupd1 ptr v m = if dest_ptr_type (fastype_of ptr) = fastype_of v
    then Const (@{const_name heap_update}, fastype_of ptr --> fastype_of v
            --> @{typ "heap_mem \<Rightarrow> heap_mem"})
        $ ptr $ v $ m
    else raise TERM ("mk_memupd1: types disagree", [ptr, v])

fun mk_memupd2 ptr v = mk_memupd1 ptr v (mk_pseudo_acc "Mem" @{typ heap_mem})

fun convert_upd_phase1 params (t as (Const (@{const_name globals_update}, _)
    $ (Const (c, _) $ f) $ s)) = (case (f, String.isPrefix NameGeneration.ghost_state_name
            (Long_Name.base_name c), #rw_global_upds params c) of
        (Const (@{const_name hrs_mem_update}, _)
            $ (Const (@{const_name heap_update}, _) $ p $ v), _, _)
        => [("Mem", convert_fetch_phase1 params (mk_memupd2 p v))]
        | (Const (@{const_name hrs_htd_update}, _) $ g, _, _)
        => [("HTD", (convert_fetch_phase1 params
            (betapply (g, mk_pseudo_acc "HTD" @{typ heap_typ_desc}))))]
        | (_, true, _) => []
        | (_, _, SOME nm) => let
    val acc = the (Symtab.lookup (#rw_globals_tab params) nm) |> fst
    val v = convert_fetch_phase1 params (betapply (f, acc $ s))
    val ptr = TermsTypes.mk_global_addr_ptr (nm, fastype_of v)
  in [("Mem", mk_memupd2 ptr v)] end
    | _ => raise TERM ("convert_upd", [t]))
  | convert_upd_phase1 params (t as (Const (c, _) $ f $ s)) = let
    val c' = unsuffix Record.updateN c
    val cT' = fastype_of s --> fastype_of (f $ s)
    val _ = (#local_upds params c) orelse raise TERM ("convert_upd_phase1: nonlocal", [t])
    val v = betapply (f, Const (c', cT') $ s)
  in [(naming c', convert_fetch_phase1 params v)] end
  | convert_upd_phase1 _ t = raise TERM ("convert_upd_phase1", [t])
*}

text {* Phase 2 eliminates compound types, so we access and
update only words from memory and local values. *} 

ML {*
fun ptr_simp ctxt = ctxt addsimps @{thms CTypesDefs.ptr_add_def size_of_def size_td_array
        field_lvalue_offset_eq align_td_array' word_of_int scast_def[symmetric]
        sint_sbintrunc' sdiv_word_def sdiv_int_def}
  |> Simplifier.rewrite

val trace_ptr_simp = false

fun ptr_simp_term ctxt s pat t = let
    val rew_thm = pat |> Thm.cterm_of ctxt |> ptr_simp ctxt
    val rew = rew_thm |> Thm.concl_of |> Logic.varify_global |> Logic.dest_equals
    val _ = (not (fst rew aconv snd rew))
        orelse raise TERM ("ptr_simp_term: " ^ s, [fst rew])
    val _ = if not trace_ptr_simp then () else
        (Display.pretty_thm ctxt rew_thm |> Pretty.writeln;
         Syntax.pretty_term ctxt t |> Pretty.writeln)
  in Pattern.rewrite_term (Proof_Context.theory_of ctxt) [rew] [] t end

fun dest_arrayT (Type (@{type_name array}, [elT, nT])) = let
  in (elT, dest_binT nT) end
  | dest_arrayT T = raise TYPE ("dest_arrayT", [T], [])

fun dest_nat (@{term Suc} $ n) = dest_nat n + 1
  | dest_nat (@{term "0 :: nat"}) = 0
  | dest_nat n = HOLogic.dest_number n |> snd

fun get_c_type_size ctxt T = let
    val TT = Logic.mk_type T
    val size_of = Const (@{const_name size_of}, type_of TT --> @{typ nat}) $ TT
  in (ptr_simp_term ctxt "c_type_size" size_of size_of |> dest_nat) end

val ptr_to_typ = Logic.mk_type o dest_ptr_type o fastype_of

fun mk_arr_idx arr i = let
    val arrT = fastype_of arr
    val elT = case arrT of Type (@{type_name "array"}, [elT, _])
        => elT | _ => raise TYPE ("mk_arr_idx", [arrT], [arr])
  in Const (@{const_name "Arrays.index"}, arrT --> @{typ nat} --> elT)
    $ arr $ i
  end

fun get_ptr_val (Const (@{const_name "Ptr"}, _) $ x) = x
  | get_ptr_val p = Const (@{const_name ptr_val},
        fastype_of p --> @{typ word32}) $ p

fun mk_ptr_offs opt_T p offs = let
    val pT = fastype_of p
    val T = case opt_T of NONE => pT
      | SOME T => Type (@{type_name ptr}, [T])
  in Const (@{const_name Ptr}, @{typ word32} --> T)
       $ (@{term "op + :: word32 \<Rightarrow> _"}
            $ get_ptr_val p $ offs)
  end

fun get_acc_type [] T = T
  | get_acc_type accs _ = (List.last accs $ @{term x})
      |> fastype_of 

val normalise_ring_ops = let
    fun gather_plus (Const (@{const_name "plus"}, _) $ a $ b)
        = gather_plus a @ gather_plus b
      | gather_plus x = [x]
    fun gather_times (Const (@{const_name "times"}, _) $ a $ b)
        = gather_times a @ gather_times b
      | gather_times x = [x]
    fun fold_op _ [x] = x
      | fold_op oper (x :: xs) = oper $ x $ (fold_op oper xs)
      | fold_op _ [] = error "fold_op: shouldn't get empty list"
    fun inner (x as (Const (@{const_name "plus"}, _) $ _ $ _))
      = gather_plus x |> map inner
          |> sort Term_Ord.fast_term_ord
          |> fold_op (head_of x)
      | inner (x as (Const (@{const_name "times"}, _) $ _ $ _))
      = gather_times x |> map inner
          |> sort Term_Ord.fast_term_ord
          |> fold_op (head_of x)
      | inner (f $ x) = inner f $ inner x
      | inner x = x
  in inner end

fun dest_mem_acc_addr (Const (@{const_name h_val}, _) $ _ $ p)
        = SOME p
  | dest_mem_acc_addr _ = NONE

fun narrow_mem_upd ctxt (params : export_params) p v = let
    val T = fastype_of v
    fun mk_offs T = mk_ptr_offs (SOME T) p
    fun mk_offs2 T = mk_offs T o HOLogic.mk_number @{typ word32}
    val sterm = Syntax.pretty_term ctxt #> Pretty.string_of
    val styp = Syntax.pretty_typ ctxt #> Pretty.string_of
  in if (dest_mem_acc_addr v = SOME p) then []
    else if #structs_by_typ params (fst (dest_Type T)) <> NONE
    then let
      val (_, _, _, _, flds) = the (#structs_by_typ params (fst (dest_Type T)))
      val fld_writes = map (fn (_, (acc, offs))
          => (mk_offs2 (fastype_of (acc $ v)) offs,
              #cons_field_upds params (acc $ v))) flds
    in maps (uncurry (narrow_mem_upd ctxt params)) fld_writes end
    else if fst (dest_Type T) = @{type_name array}
    then let
        val (elT, n) = dest_arrayT T
        val elT_size = get_c_type_size ctxt elT
      in case v of (Const (@{const_name Arrays.update}, _) $ arr $ i $ x)
          => narrow_mem_upd ctxt params (mk_offs elT (@{term "op * :: word32 => _"}
                  $ HOLogic.mk_number @{typ word32} elT_size
                      $ (@{term "of_nat :: nat \<Rightarrow> word32"} $ i)))
              x @ narrow_mem_upd ctxt params p arr
      | _ => let
          val addrs = map (fn i => (mk_offs2 elT (i * elT_size)))
              (0 upto (n - 1))
          val elems = dest_array_init v
              handle TERM _ => map
                    (fn i => mk_arr_idx v (HOLogic.mk_number @{typ nat} i))
                    (0 upto (n - 1))
          val _ = (if n < 16 then () else
            warning ("expanding " ^ string_of_int n ^ ": "
                ^ sterm p ^ styp (fastype_of p) ^ ": " ^ sterm v))
      in maps (uncurry (narrow_mem_upd ctxt params)) (addrs ~~ elems) end
    end
    else if fst (dest_Type T) <> @{type_name word}
        andalso fst (dest_Type T) <> @{type_name ptr}
    then raise TERM ("narrow_mem_upd failed to narrow:", [p, v])
    else [(p, v)]
  end

fun triv_mem_upd ctxt p v = case dest_mem_acc_addr v of
      NONE => false
    | SOME p' => p aconv p' orelse let
      val t = @{term "op - :: word32 \<Rightarrow> _"} $ get_ptr_val p $ get_ptr_val p'
      val thm = ptr_simp ctxt (Thm.cterm_of ctxt t)
      val t' = Thm.rhs_of thm |> Thm.term_of
    in t' = @{term "0 :: word32"} 
        orelse (Display.pretty_thm ctxt thm |> Pretty.writeln; false)
    end

fun narrow_mem_acc _ _ [] p = p
  | narrow_mem_acc ctxt params accs p = let
    fun get_offs (Const (@{const_name Arrays.index}, idxT) $ i) = let
        val (elT, _) = dest_arrayT (domain_type idxT)
        val elT_size = get_c_type_size ctxt elT
      in @{term "op * :: word32 \<Rightarrow> _"} $ HOLogic.mk_number @{typ word32} elT_size
              $ (@{term "of_nat :: nat \<Rightarrow> word32"} $ i) end
      | get_offs (Const (s, T)) = let
        val struct_typ = domain_type T |> dest_Type |> fst
        val (_, _, _, _, flds) = the (#structs_by_typ params struct_typ)
        val matches = filter (fn (_, (c, _)) => c = Const (s, T)) flds
        val _ = (length matches = 1)
            orelse raise TERM ("narrow_mem_acc: get_offs: ", [Const (s, T)])
        val offs = snd (snd (hd matches))
      in HOLogic.mk_number @{typ word32} offs end
      | get_offs t = raise TERM ("narrow_mem_acc: get_offs: ", [t])
    val T' = get_acc_type accs (@{typ nat} (* doesn't matter *))
    val offs = foldr1 (fn (x, y) => @{term "op + :: word32 \<Rightarrow> _"} $ x $ y)
        (map get_offs accs)
    in mk_ptr_offs (SOME T') p offs end

fun try_norm_index ctxt i = let
    val i' = ptr_simp_term ctxt "idx_simp" i i
  in dest_nat i'; i' end handle TERM _ => i

fun mk_acc_array i xs = let
    val n = length xs
    val _ = warning ("expanding acc array, width " ^ string_of_int n)
    val i = @{term "of_nat :: nat \<Rightarrow> word32"} $ i
    fun inner [(x, _)] = x
      | inner ((x, j) :: xs) = let
        val y = inner xs
        val T = fastype_of x
      in Const (@{const_name "If"}, HOLogic.boolT --> T --> T --> T)
        $ HOLogic.mk_eq (i, HOLogic.mk_number @{typ word32} j) $ x $ y end
      | inner [] = error "mk_acc_array: empty"
  in inner (xs ~~ (0 upto (n - 1))) end

fun convert_fetch_ph2 ctxt params [] (t as (Const (@{const_name CTypesDefs.ptr_add}, T) $ _ $ _))
    = convert_fetch_ph2 ctxt params [] (ptr_simp_term ctxt "ptr_add"
        (head_of t $ Free ("p", domain_type T) $ Free ("n", @{typ int})) t)
  | convert_fetch_ph2 ctxt params [] (t as (Const (@{const_name field_lvalue}, T) $ _ $ s))
    = convert_fetch_ph2 ctxt params [] (ptr_simp_term ctxt "field_lvalue"
        (head_of t $ Free ("p", domain_type T) $ s) t)
  | convert_fetch_ph2 ctxt params ((Const (@{const_name Arrays.index}, _) $ i) :: accs)
            (t as (Const (@{const_name fupdate}, _) $ _ $ _ $ _)) = let
        val xs = dest_array_init (#cons_field_upds (params : export_params) t)
      in case (try dest_nat (try_norm_index ctxt i)) of
        SOME i => convert_fetch_ph2 ctxt params accs (nth xs i)
      | NONE => mk_acc_array (convert_fetch_ph2 ctxt params [] i)
            (map (convert_fetch_ph2 ctxt params accs) xs)
      end
  | convert_fetch_ph2 ctxt params ((Const (@{const_name Arrays.index}, _) $ i) :: accs)
            (t as (Const (@{const_name FCP}, _) $ _)) = let
        val xs = dest_array_init (#cons_field_upds params t)
      in case (try dest_nat (try_norm_index ctxt i)) of
        SOME i => convert_fetch_ph2 ctxt params accs (nth xs i)
      | NONE => mk_acc_array (convert_fetch_ph2 ctxt params [] i)
            (map (convert_fetch_ph2 ctxt params accs) xs)
      end
  | convert_fetch_ph2 ctxt params accs ((idx as Const (@{const_name Arrays.index}, _)) $ arr $ i) = let
        val i' = try_norm_index ctxt i
      in convert_fetch_ph2 ctxt params (idx $ i' :: accs) arr end
  | convert_fetch_ph2 ctxt params ((idx as Const (@{const_name Arrays.index}, _)) $ i :: accs)
        (Const (@{const_name Arrays.update}, _) $ arr' $ i' $ v)
     = let
         val eq = HOLogic.mk_eq (i, i')
         val eq = ptr_simp_term ctxt "idx_eq_simp" eq eq handle TERM _ => eq
         val x = convert_fetch_ph2 ctxt params accs v
         val y = convert_fetch_ph2 ctxt params (idx $ try_norm_index ctxt i :: accs) arr'
         val T = fastype_of x
      in case eq of @{term True} => x | @{term False} => y
        | _ => Const (@{const_name If}, HOLogic.boolT --> T --> T --> T)
            $ convert_fetch_ph2 ctxt params [] eq $ x $ y end
  | convert_fetch_ph2 ctxt params accs (Const (@{const_name h_val}, _) $ _ $ p)
    = let
      val p = convert_fetch_ph2 ctxt params [] p
      val p = narrow_mem_acc ctxt params accs p
    in mk_memacc p end
  | convert_fetch_ph2 ctxt params [] (Const (@{const_name heap_update}, _) $ p $ v $ m)
    = let
      val xs = narrow_mem_upd ctxt params p v
        |> map (apply2 (convert_fetch_ph2 ctxt params []))
        |> filter_out (uncurry (triv_mem_upd ctxt))
      val m = convert_fetch_ph2 ctxt params [] m
    in fold (uncurry mk_memupd1) xs m end
  | convert_fetch_ph2 _ _ [] (t as (Const (@{const_name pseudo_acc}, _) $ _)) = t
  | convert_fetch_ph2 ctxt params accs (Const (@{const_name pseudo_acc}, _) $ Free (s, T)) = let
    val T = get_acc_type accs T
    fun canon s [] = mk_pseudo_acc s T
      | canon s (Const (@{const_name Arrays.index}, idxT) $ i :: accs) = (case
            (try dest_nat (try_norm_index ctxt i))
        of SOME i => canon (s ^ "." ^ string_of_int i) accs
          | NONE => let val (_, n) = dest_arrayT (domain_type idxT)
          in mk_acc_array (convert_fetch_ph2 ctxt params [] i)
            (map (fn j => canon (s ^ "." ^ string_of_int j) accs)
              (0 upto (n - 1))) end)
      | canon s (Const (acc_nm, _) :: accs)
        = canon (s ^ "." ^ Long_Name.base_name acc_nm) accs
      | canon _ (t :: _) = raise TERM ("convert_fetch_ph2: canon: ", [t])
  in canon s accs end
  | convert_fetch_ph2 _ _ [] (t as (Free ("symbol_table", _) $ _))
      = t
  | convert_fetch_ph2 _ _ [] (t as Free ("domain", _))
      = t
  | convert_fetch_ph2 ctxt params accs t = let
    val (f, xs) = strip_comb t
    val (c, _) = dest_Const f
  in if (get_field ctxt c |> Option.map #3) = SOME false
    then case xs of [x] => convert_fetch_ph2 ctxt params (f :: accs) x
        | _ => raise TERM ("convert_fetch_ph2: expected single", f :: xs)
  else if (get_field ctxt c <> NONE orelse #cons_fields params c <> NONE)
  then let
    val _ = (accs <> []) orelse raise TERM ("convert_fetch_ph2: no accs", [t])
    val t' = hd accs $ t
    val t'' = #cons_field_upds params t'
  in if t'' aconv t' then raise TERM ("convert_fetch_ph2: irreducible upd:", [t'])
    else convert_fetch_ph2 ctxt params (tl accs) t'' end
  else list_comb (f, map (convert_fetch_ph2 ctxt params []) xs) end

fun convert_upd_ph2_worker ctxt params s v T accs =
  if #structs_by_typ params (fst (dest_Type T)) <> NONE
  then let
    val (_, _, _, _, flds) = the (#structs_by_typ params (fst (dest_Type T)))
  in maps (fn (fld_nm, (acc, _)) => convert_upd_ph2_worker ctxt params (s ^ "." ^ fld_nm)
    v (range_type (fastype_of acc)) (accs @ [acc])) flds end
  else if fst (dest_Type T) = @{type_name array}
  then let
    val (elT, n) = dest_arrayT T
  in maps (fn i => convert_upd_ph2_worker ctxt params (s ^ "." ^ string_of_int i)
    v elT (accs @ [Const (@{const_name Arrays.index}, T --> @{typ nat} --> elT)
        $ HOLogic.mk_number @{typ nat} i])) (0 upto (n - 1))
  end
  else [(s, convert_fetch_ph2 ctxt params accs v)]

fun convert_upd_ph2 ctxt params (s, v)
    = convert_upd_ph2_worker ctxt params s v (fastype_of v) []
(*      |> tap (map (snd #> Syntax.pretty_term ctxt #> Pretty.writeln)) *)
*}

text {* The final conversion reduces Isabelle terms to strings *}

ML {*
val space_pad = space_implode " "

fun space_pad_list xs = space_pad (string_of_int (length xs) :: xs)

fun s_st ctxt = Syntax.read_term ctxt "s :: globals myvars"
fun rv_st ctxt = Syntax.read_term ctxt "rv :: globals myvars"

fun convert_op ctxt params nm tp xs = "Op " ^ nm ^ " " ^ tp
    ^ " " ^ space_pad_list (map (convert_ph3 ctxt params) xs)

and convert_ph3 ctxt params (Const (@{const_name Collect}, _) $ S $ x)
    = convert_ph3 ctxt params (betapply (S, x))
  | convert_ph3 ctxt params (Const (@{const_name Lattices.inf}, _) $ S $ T $ x)
    = convert_op ctxt params "And" "Bool" [betapply (S, x), betapply (T, x)]
  | convert_ph3 ctxt params (Const (@{const_name Ptr}, _) $ p) = convert_ph3 ctxt params p
  | convert_ph3 ctxt params (Const (@{const_name ptr_val}, _) $ p) = convert_ph3 ctxt params p
  | convert_ph3 ctxt params (Const (@{const_name store_word32}, _) $ p $ w $ m)
        = convert_op ctxt params "MemUpdate" "Mem" [m, p, w]
  | convert_ph3 ctxt params (Const (@{const_name store_word8}, _) $ p $ w $ m)
        = convert_op ctxt params "MemUpdate" "Mem" [m, p, w]
  | convert_ph3 ctxt params (Const (@{const_name heap_update}, _) $ p $ v $ m)
        = convert_op ctxt params "MemUpdate" "Mem" [m, p, v]
  | convert_ph3 ctxt params (t as (Const (@{const_name h_val}, _) $ m $ p))
        = convert_op ctxt params "MemAcc" (convert_type false ctxt (fastype_of t)) [m, p]
  | convert_ph3 ctxt params (Const (@{const_name load_word32}, _) $ p $ m)
        = convert_op ctxt params "MemAcc" "Word 32" [m, p]
  | convert_ph3 ctxt params (Const (@{const_name load_word8}, _) $ p $ m)
        = convert_op ctxt params "MemAcc" "Word 8" [m, p]
  | convert_ph3 ctxt params ((le as Const (@{const_name less_eq}, _))
        $ (Const (@{const_name insert}, _) $ p $ S) $ D)
        = convert_op ctxt params "And" "Bool" [HOLogic.mk_mem (p, D), le $ S $ D]
  | convert_ph3 ctxt params (Const (@{const_name less_eq}, _)
        $ Const (@{const_name bot_class.bot}, _) $ _) = convert_ph3 ctxt params @{term True}
  | convert_ph3 ctxt params (Const (@{const_name htd_safe}, _) $ _ $ _)
        = convert_ph3 ctxt params @{term True}
  | convert_ph3 ctxt params (Const (@{const_name uminus}, T) $ v)
        = let val T = domain_type T
          in convert_ph3 ctxt params (Const (@{const_name minus}, T --> T --> T)
                $ Const (@{const_name zero_class.zero}, T) $ v) end
  | convert_ph3 ctxt params (Const (@{const_name h_t_valid}, _) $ htd
            $ Const (@{const_name c_guard}, _) $ p)
        = convert_op ctxt params "PValid" "Bool" [htd, ptr_to_typ p, p]
  | convert_ph3 ctxt params (Const (@{const_name ptr_inverse_safe}, _) $ p $ htd)
        = convert_op ctxt params "PGlobalValid" "Bool" [htd, ptr_to_typ p, p]
  | convert_ph3 ctxt params (Const (@{const_name ptr_safe}, _) $ p $ htd)
        = convert_op ctxt params "PWeakValid" "Bool" [htd, ptr_to_typ p, p]
  | convert_ph3 ctxt params (Const (@{const_name globals_list_distinct}, _) $
        (Const (@{const_name image}, _) $ Const (@{const_name fst}, _)
            $ (Const (@{const_name s_footprint}, _) $ _)) $ _ $ _)
        = convert_ph3 ctxt params @{term True}
  | convert_ph3 ctxt params (Const (@{const_name c_guard}, _) $ p)
        = convert_op ctxt params "PAlignValid" "Bool" [ptr_to_typ p, p]
  | convert_ph3 ctxt params (Const (@{const_name bot}, _) $ _)
        = convert_ph3 ctxt params @{term False}
  | convert_ph3 ctxt params (Const (@{const_name top_class.top}, _) $ _)
        = convert_ph3 ctxt params @{term True}
  | convert_ph3 ctxt params (Const (@{const_name insert}, _) $ v $ S $ x)
        = convert_op ctxt params "Or" "Bool" [HOLogic.mk_eq (v, x), betapply (S, x)]
  | convert_ph3 _ _ (Free ("symbol_table", _) $ s)
        = "Symbol " ^ HOLogic.dest_string s ^ " Word 32"
  | convert_ph3 ctxt params (Const (@{const_name of_nat}, T) $ (Const (@{const_name unat}, _) $ x))
        = let
            val t1 = fastype_of x
            val t2 = range_type T
          in if t1 = t2 then convert_ph3 ctxt params x
            else convert_ph3 ctxt params (Const (@{const_name ucast}, t1 --> t2) $ x)
          end
  | convert_ph3 ctxt params (t as (Const (@{const_name of_nat}, _) $
            (Const (@{const_name count_leading_zeroes}, _) $ x)))
        = convert_op ctxt params "CountLeadingZeroes" (convert_type false ctxt (fastype_of t)) [x]
(*  | convert_ph3 ctxt params (t as (Const (@{const_name unat}, _) $ _))
        = convert_ph3 ctxt params (@{term "of_nat :: nat \<Rightarrow> word32"} $ t) *)
  | convert_ph3 ctxt params (t as (Const (@{const_name of_nat}, _) $ _))
        = convert_ph3 ctxt params (ptr_simp_term ctxt "of_nat" t t)
  | convert_ph3 ctxt params (t as (Const (@{const_name power}, _) $ _ $ _))
        = convert_ph3 ctxt params (ptr_simp_term ctxt "power" t t)
  | convert_ph3 ctxt params (Const (@{const_name ptr_coerce}, _) $ p)
        = convert_ph3 ctxt params p
  | convert_ph3 ctxt params (t as (Const (@{const_name word_of_int}, _) $ _))
    = let
        val thy = Proof_Context.theory_of ctxt
        val t' = Pattern.rewrite_term thy (map (Thm.concl_of #> HOLogic.dest_Trueprop
            #> HOLogic.dest_eq) @{thms word_uint.Rep_inverse word_sint.Rep_inverse}) [] t
      in if t' aconv t then convert_ph3 ctxt params (ptr_simp_term ctxt "word_of_int" t t)
        else convert_ph3 ctxt params t' end
  | convert_ph3 ctxt params (t as (Const (@{const_name sdiv}, _) $ _ $ _))
    = convert_ph3 ctxt params (ptr_simp_term ctxt "sdiv" t t)
  | convert_ph3 ctxt _ (t as (Const (@{const_name numeral}, _) $ _))
    = let
    val n = HOLogic.dest_number t |> snd
        handle TERM _ => raise TERM ("convert_ph3", [t])
    val _ = (fastype_of t <> @{typ int}) orelse raise TERM ("convert_ph3: int", [t])
  in "Num " ^ signed_string_of_int n ^ " " ^ convert_type false ctxt (fastype_of t) end
  | convert_ph3 ctxt _ (Const (@{const_name Pure.type}, Type (_, [T])))
    = "Type " ^ convert_type true ctxt T
  | convert_ph3 ctxt _ (Const (@{const_name pseudo_acc}, _) $ Free (s, T))
    = "Var " ^ s ^ " " ^ convert_type false ctxt T
  | convert_ph3 ctxt params t = let
    val (f, xs) = strip_comb t
    val (c, _) = dest_Const f
    val xs = if member (op =) [@{const_name shiftl},
        @{const_name shiftr}, @{const_name sshiftr}] c
      then case xs of
        [x, y] => [x, Const (@{const_name of_nat}, @{typ nat} --> fastype_of x) $ y]
        | _ => raise TERM ("convert_ph3: shift", [t])
      else xs
  in case ops c of
    (SOME (nm, _)) => convert_op ctxt params nm (convert_type false ctxt (fastype_of t)) xs
  | NONE => ("Num " ^ signed_string_of_int (snd (HOLogic.dest_number t))
        ^ " " ^ convert_type false ctxt (fastype_of t)
    handle TERM _ => raise TERM ("convert_ph3", [t]))
  end

fun htd_simp ctxt = ctxt addsimps @{thms fold_all_htd_updates
        unat_lt2p[where 'a=32, simplified]}
  |> Simplifier.add_cong @{thm if_cong} |> Simplifier.rewrite

fun simp_htd ctxt t = let
    val rew_thm = Thm.cterm_of ctxt t |> htd_simp ctxt
  in Thm.term_of (Thm.rhs_of rew_thm) end

fun convert_upd_ph3 ctxt params (s, v) =
  let
    val nm = if s = "HTD" then "HTD HTD"
        else s ^ " " ^ convert_type false ctxt (fastype_of v)
    val v = if s = "HTD" then simp_htd ctxt v else v
    val v = convert_ph3 ctxt params v
  in (nm, v) end
    handle TERM (s, ts) => raise TERM ("convert_upd_ph3: " ^ s, v :: ts)
*}

ML {*
fun convert_fetch ctxt params t =
    Envir.beta_eta_contract t
    |> convert_fetch_phase1 params
    |> convert_fetch_ph2 ctxt params []
    |> convert_ph3 ctxt params

fun tracet (s, t) = ((Syntax.pretty_term @{context} t |> Pretty.writeln); (s, t))

fun convert_param_upds ctxt params (t as (Const (c, _) $ _ $ s))
    = if #local_upds params c orelse c = @{const_name globals_update}
      then convert_param_upds ctxt params s
        @ (Envir.beta_eta_contract t
(*        |> tap (Syntax.pretty_term ctxt #> Pretty.writeln) *)
        |> convert_upd_phase1 params
(*        |> map tracet *)
(*        |> map (apsnd (Syntax.check_term ctxt)) *)
        |> maps (convert_upd_ph2 ctxt params)
(*        |> map (apsnd (Syntax.check_term ctxt)) *)
        |> map (convert_upd_ph3 ctxt params)
        )
      else raise TERM ("convert_param_upds", [t])
  | convert_param_upds ctxt _ t = (if t = s_st ctxt then []
    else raise TERM ("convert_param_upds", [t]))

*}

lemmas sdiv_word32_max_ineq = sdiv_word32_max[folded zle_diff1_eq, simplified]

ML {*

val outfile = ref (NONE: TextIO.outstream option)

fun emit s = case ! outfile of
    SOME stream => TextIO.output (stream, s ^ "\n")
  | NONE => tracing s

val all_c_params = ["Mem Mem", "HTD HTD", "PMS PMS"]
val all_c_in_params = map (prefix "Var ") all_c_params

fun mk_safe f ctxt params s = (
    Proof_Context.get_thm ctxt (s ^ "_body_def");
    Proof_Context.get_thm ctxt (s ^ "_impl");
  f ctxt params s) handle ERROR _ => false

fun mk_set_int s t = let
    val T = fastype_of s
  in Const (@{const_name Lattices.inf}, T --> T --> T) $ s $ t end

val reduce_set_mem_eqs = @{thms mem_Collect_eq Int_iff Un_iff empty_iff iffI[OF TrueI UNIV_I]}
      |> map (mk_meta_eq #> Thm.concl_of #> Logic.dest_equals)

fun reduce_set_mem ctxt x S = let
    val t = HOLogic.mk_mem (x, S)
    val t' = Pattern.rewrite_term (Proof_Context.theory_of ctxt)
    reduce_set_mem_eqs [] t
  in if t aconv t' then Pretty.writeln (Syntax.pretty_term ctxt (HOLogic.mk_prod (t, t')))
     else (); t'
  end

fun has_reads body = exists_Const (fn (s, T) =>
    snd (strip_type T) = @{typ heap_raw_state}
        orelse s = @{const_name Spec}) body

fun has_reads_globals (params : export_params) body = exists_Const (fn (s, T) =>
    snd (strip_type T) = @{typ heap_raw_state}
  orelse s = @{const_name Spec}
  orelse #rw_global_accs params s <> NONE
  orelse #const_globals params (Const (s, T)) <> NONE
  ) body

fun get_reads_calls ctxt params globals name = let
    val thm = Proof_Context.get_thm ctxt (name ^ "_body_def")
        |> simplify (put_simpset HOL_basic_ss ctxt addsimps @{thms call_def block_def})
    fun calls (Const (@{const_name com.Call}, _) $ proc) = [proc]
      | calls (f $ x) = calls f @ calls x
      | calls (Abs (_, _, t)) = calls t
      | calls _ = []
    val reads = (if globals then has_reads_globals params else has_reads)
        (Thm.concl_of thm)
    val call_to_name = dest_Const #> fst #> Long_Name.base_name
        #> unsuffix "_'proc"
  in (reads, calls (Thm.concl_of thm) |> map call_to_name) end

fun is_no_read ctxt params globals s = let
    fun inner stack s = if member (op =) stack s then true else let
        val (reads, calls) = get_reads_calls ctxt params globals s
      in not reads andalso forall I (map (inner (s :: stack)) calls) end
  in inner [] s end

fun is_no_write ctxt s = let
    val thm = Proof_Context.get_thm ctxt (s ^ "_modifies")
    val mex = exists_Const (fn (s, _) => s = @{const_name mex}) (Thm.concl_of thm)
  in not mex end

fun synthetic_updates ctxt params pref (Const (c, T)) = let
    val s = s_st ctxt
    val sT = fastype_of s
    val xT = range_type T
    val upd = Const (suffix Record.updateN c, (xT --> xT) --> sT --> sT)
        $ Abs ("v", xT, Bound 0) $ s
      |> Syntax.check_term ctxt
    val upds = convert_param_upds ctxt params upd
  in map (apfst (prefix pref)) upds end
  | synthetic_updates _ _ _ t = raise TERM ("synthetic_updates", [t])

fun is_no_read_globals ctxt params = is_no_read ctxt params true

fun get_global_valid_assertion ctxt (params : export_params) t = let
    val tnames = Term.add_const_names t []
    val globs = map_filter (#rw_global_accs params) tnames
        @ map_filter (#rw_global_upds params) tnames
    fun assert nm = let
        val T = Symtab.lookup (#rw_globals_tab params) nm
            |> the |> fst |> fastype_of |> range_type
        val p = TermsTypes.mk_global_addr_ptr (nm, T)
      in convert_op ctxt params "PGlobalValid" "Bool"
          [mk_pseudo_acc "HTD" @{typ heap_typ_desc}, ptr_to_typ p, p]
      end
    val globs = sort_distinct fast_string_ord globs
      |> map assert
    fun conj (x, y) = "Op And Bool 2 " ^ x ^ " " ^ y
  in case globs of [] => NONE
    | _ => SOME (foldr1 conj globs)
  end

fun emit_body ctxt params (Const (@{const_name Seq}, _) $ a $ b) n c e = let
    val (n, nm) = emit_body ctxt params b n c e
        handle TERM (s, ts) => raise TERM (s, b :: ts)
            | Empty => raise TERM ("emit_body: got Empty", [b])
    val (n, nm) = emit_body ctxt params a n nm e
        handle TERM (s, ts) => raise TERM (s, a :: ts)
            | Empty => raise TERM ("emit_body: got Empty", [a])
  in (n, nm) end
  | emit_body ctxt params (Const (@{const_name Catch}, _) $ a $ b) n c e = (case b of
    Const (@{const_name com.Skip}, _) => emit_body ctxt params a n c (c, c)
  | Const (@{const_name ccatchbrk}, _) $ _ => emit_body ctxt params a n c (fst e, c)
  | t => raise TERM ("emit_body ctxt params (Catch)", [t])
  )
  | emit_body ctxt params (Const (@{const_name creturn}, _) $ _ $ upd $ f) n _ (r, b) =
    emit_body ctxt params (@{term com.Basic} $ Abs ("s", dummyT, betapplys (upd,
        [Abs ("_", dummyT, betapply (f, Bound 1)), Bound 0]))) n r (r, b)
  | emit_body _ _ (Const (@{const_name creturn_void}, _) $ _) n _ (r, _) = (n, r)
  | emit_body _ _ (Const (@{const_name cbreak}, _) $ _) n _ (_, b) = (n, b)
  | emit_body _ _ (Const (@{const_name com.Skip}, _)) n c _ = (n, c)
  | emit_body ctxt params (Const (@{const_name com.Cond}, _) $ S $ a $ b) n c e = let
    val (n, nm_a) = emit_body ctxt params a n c e
    val (n, nm_b) = emit_body ctxt params b n c e
    val s = convert_fetch ctxt params (reduce_set_mem ctxt (s_st ctxt) S)
  in
    emit (string_of_int n ^ " Cond " ^ nm_a ^ " " ^ nm_b ^ " " ^ s);
    (n + 1, string_of_int n)
  end
  | emit_body ctxt params (Const (@{const_name Guard}, T) $ F $ G $
            (Const (@{const_name Guard}, _) $ _ $ G' $ a)) n c e
        = emit_body ctxt params (Const (@{const_name Guard}, T) $ F
            $ (mk_set_int G G') $ a) n c e
  | emit_body ctxt params (Const (@{const_name Guard}, _) $ _ $ G $ a) n c e = let
    val (n, nm) = emit_body ctxt params a n c e
    val thy = Proof_Context.theory_of ctxt
    val G = Pattern.rewrite_term thy
      (@{thms WordLemmaBucket.signed_arith_ineq_checks_to_eq_word32
              signed_arith_eq_checks_to_ord
              signed_mult_eq_checks32_to_64
              sdiv_word32_min[THEN eqTrueI] sdiv_word32_max_ineq
              signed_shift_guard_to_word_32}
        |> map (Thm.concl_of #> HOLogic.dest_Trueprop #> HOLogic.dest_eq)) [] G
    val s = convert_fetch ctxt params (reduce_set_mem ctxt (s_st ctxt) G)
  in
    emit (string_of_int n ^ " Cond " ^ nm ^ " Err " ^ s);
    (n + 1, string_of_int n)
  end
  | emit_body _ _ (Const (@{const_name com.Basic}, _) $ Abs (_, _, Bound 0)) n c _
    = (n, c)
  | emit_body ctxt params (Const (@{const_name com.Basic}, _) $ f) n c _ = let
    val upds = convert_param_upds ctxt params (betapply (f, s_st ctxt))
      |> filter_out (fn (s, v) => v = "Var " ^ s)
      |> map (fn (s, v) => s ^ " " ^ v)

  in
    emit (string_of_int n ^ " Basic " ^ c ^ " " ^ space_pad_list upds);
    case get_global_valid_assertion ctxt params f of NONE =>
        (n + 1, string_of_int n)
      | SOME ass => (emit (string_of_int (n + 1) ^ " Cond " ^ string_of_int n ^ " Err " ^ ass);
        (n + 2, string_of_int (n + 1)))
  end
  | emit_body ctxt params (Const (@{const_name call}, _) $ f $ Const (p, _)
        $ _ $ r2) n c e = let
    val proc_info = Hoare.get_data ctxt |> #proc_info
    val ret_vals = Symtab.lookup proc_info (Long_Name.base_name p)
        |> the |> #params
        |> filter (fn (v, _) => v = HoarePackage.Out)
        |> maps (snd #> read_const ctxt
         #> synthetic_updates ctxt params "rv#space#")
        |> map fst

    val p_short = unsuffix "_'proc" (Long_Name.base_name p)
    val no_read = mk_safe is_no_read_globals ctxt params p_short
    val no_write = mk_safe (K o is_no_write) ctxt params p_short
    (* writes implicitly require reads, really *)
    val no_read = no_read andalso no_write

    val args = ((convert_param_upds ctxt params (betapply (f, s_st ctxt))
            |> map snd (* discard the local names of the updated variables *))
        @ (if no_read then [] else all_c_in_params))
      handle TERM (s, ts) => raise TERM ("emit_body call: " ^ s, f :: ts)

    val out = ret_vals @ (if no_write then [] else all_c_params)

    val (n, nm_save) = emit_body ctxt params (betapplys (r2, [@{term i}, rv_st ctxt])) n c e

  in emit (string_of_int n ^ " Call " ^ nm_save ^ " " ^ (unsuffix "_'proc" p)
    ^ " " ^ space_pad_list args ^ " " ^ space_pad_list out);
    (n + 1, string_of_int n)
  end
  | emit_body _ _ (Const (@{const_name lvar_nondet_init}, _) $ _ $ _) n c _
    = (n, c)
  | emit_body ctxt params (Const (@{const_name whileAnno}, _) $ C $ _ $ _ $ a) n c e = let
    fun sn i = string_of_int (n + i)
    val lc = "loop#" ^ sn 0 ^ "#count" ^ " Word 32"
    val (n', nm) = emit_body ctxt params a (n + 3) (sn 0) e
    val cond = convert_fetch ctxt params (reduce_set_mem ctxt (s_st ctxt) C)
  in emit (sn 0 ^ " Basic " ^ sn 1 ^ " 1 " ^ lc
      ^ " Op Plus Word 32 2 Var " ^ lc ^ " Num 1 Word 32");
    emit (sn 1 ^ " Cond " ^ nm ^ " " ^ c ^ " " ^ cond);
    emit (sn 2 ^ " Basic " ^ sn 1 ^ " 1 " ^ lc ^ " Num 0 Word 32");
    (n', sn 2)
  end
  | emit_body _ _ t _ _ _ = raise TERM ("emit_body", [t])

fun emit_func_body ctxt eparams name = let
    val proc_info = Hoare.get_data ctxt |> #proc_info
    val params = Symtab.lookup proc_info (name ^ "_'proc")
        |> the |> #params
        |> map (apsnd (read_const ctxt
                #> synthetic_updates ctxt eparams ""
                #> map fst))

    val no_read = mk_safe is_no_read_globals ctxt eparams name
    val no_write = mk_safe (K o is_no_write) ctxt eparams name
    (* writes implicitly require reads, really *)
    val no_read = no_read andalso no_write

    val inputs = (filter (fn p => fst p = HoarePackage.In) params
      |> maps snd) @ (if no_read then [] else all_c_params)

    val outputs = (filter (fn p => fst p = HoarePackage.Out) params
      |> maps snd) @ (if no_write then [] else all_c_params)

    val body = Proof_Context.get_thm ctxt (name ^ "_body_def")
            |> simplify (put_simpset HOL_basic_ss ctxt
                addsimps @{thms switch.simps fst_conv snd_conv
                                insert_iff empty_iff})
            |> Thm.concl_of |> Logic.dest_equals |> snd
        handle ERROR _ => @{term "Spec S"}

    val full_nm = read_const ctxt (name ^ "_'proc")
        |> dest_Const |> fst |> unsuffix "_'proc"
  in emit ("Function " ^ full_nm ^ " " ^ space_pad_list inputs
                ^ " " ^ space_pad_list outputs);
    case body of Const (@{const_name Spec}, _) $ _
        => ()
    | _ => (emit ("1 Basic Ret 0");
          emit_body ctxt eparams body 2 "1" ("ErrExc", "ErrExc")
            |> snd |> prefix "EntryPoint " |> emit
          handle TERM (s, ts) => raise TERM ("emit_func_body: " ^ name ^ ": " ^ s, body :: @{term True} :: ts)
            | TYPE (s, Ts, ts) => raise TYPE ("emit_func_body: " ^ name ^ ": " ^ s, Ts, body :: @{term True} :: ts)
            | Empty => raise TERM ("emit_func_body: Empty", [body]))
  end

fun emit_struct ctxt csenv (nm, flds) = let
    val offs = map (ProgramAnalysis.offset csenv (map snd flds))
        (0 upto (length flds - 1))
    val full_nm = read_const ctxt (nm ^ "." ^ nm)
        |> dest_Const |> snd |> strip_type |> snd |> dest_Type |> fst
    val thy = Proof_Context.theory_of ctxt
    val sz = ProgramAnalysis.sizeof csenv (Absyn.StructTy nm)
    val algn = ProgramAnalysis.alignof csenv (Absyn.StructTy nm)
    fun emit_fld ((fld_nm, fld_ty), offs) = emit (space_pad
        ["StructField", fld_nm, convert_type false ctxt
            (CalculateState.ctype_to_typ (thy, fld_ty)), string_of_int offs])
  in emit (space_pad ["Struct", full_nm, string_of_int sz,
    string_of_int algn]); app emit_fld (flds ~~ offs) end

fun emit_C_everything ctxt csenv = let
    val fs = ProgramAnalysis.get_functions csenv
    val structs = ProgramAnalysis.get_senv csenv
    val params = get_all_export_params ctxt csenv
  in app (emit_struct ctxt csenv) structs;
     app (emit_func_body ctxt params) fs end
*}

ML {*
fun openOut_relative thy = ParseGraph.filename_relative thy #> TextIO.openOut;
*}

end


