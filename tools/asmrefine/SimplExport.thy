(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory SimplExport

imports GraphLang CommonOpsLemmas GlobalsSwap ExtraSpecs

begin

lemma field_lvalue_offset_eq:
  "field_lookup (typ_info_t TYPE('a :: c_type)) f 0 = Some v
        \<Longrightarrow> field_lvalue (ptr :: 'a ptr) f = ptr_val ptr + of_nat (snd v)"
  apply (cases v, simp, drule field_lookup_offset_eq)
  apply (simp add: field_lvalue_def)
  done

ML \<open>
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
    (@{const_name "modulo_class.modulo"}, ("Modulus", true)),
    (@{const_name "divide_class.divide"}, ("DividedBy", true)),
    (@{const_name "and"}, ("BWAnd", true)),
    (@{const_name "or"}, ("BWOr", true)),
    (@{const_name "xor"}, ("BWXOR", true)),
    (@{const_name "conj"}, ("And", true)),
    (@{const_name "disj"}, ("Or", true)),
    (@{const_name "implies"}, ("Implies", true)),
    (@{const_name "HOL.eq"}, ("Equals", false)),
    (@{const_name "less"}, ("Less", false)),
    (@{const_name "less_eq"}, ("LessEquals", false)),
    (@{const_name "ptr_less"}, ("Less", false)),
    (@{const_name "ptr_le"}, ("LessEquals", false)),
    (@{const_name "word_sless"}, ("SignedLess", false)),
    (@{const_name "word_sle"}, ("SignedLessEquals", false)),
    (@{const_name "Not"}, ("Not", true)),
    (@{const_name "not"}, ("BWNot", true)),
    (@{const_name "unsigned"}, ("WordCast", false)),
    (@{const_name "signed"}, ("WordCastSigned", false)),
    (@{const_name "True"}, ("True", true)),
    (@{const_name "False"}, ("False", true)),
    (@{const_name "If"}, ("IfThenElse", false)),
    (@{const_name "Set.member"}, ("MemDom", false)),
    (@{const_name "shiftl"}, ("ShiftLeft", false)),
    (@{const_name "shiftr"}, ("ShiftRight", false)),
    (@{const_name "sshiftr"}, ("SignedShiftRight", false)),
    (@{const_name "bv_clz"}, ("CountLeadingZeroes", true)),
    (@{const_name "bv_ctz"}, ("CountTrailingZeroes", true)),
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

fun read_const ctxt (pfx : string) (name : string) = let
    val nm = if pfx = "" then name else (pfx ^ "." ^ name)
  in Proof_Context.read_const {proper = true, strict = true} ctxt nm end

fun process_struct ctxt csenv pfx (nm, flds) = let
    val offs = map (ProgramAnalysis.offset csenv (map snd flds))
        (0 upto (length flds - 1))
    val cons = read_const ctxt pfx (nm ^ "." ^ nm)
    val typ = dest_Const cons |> snd |> strip_type |> snd
    val sz = ProgramAnalysis.sizeof csenv (Absyn.StructTy nm)
    val algn = ProgramAnalysis.alignof csenv (Absyn.StructTy nm)
    val accs = map (fst #> prefix (nm ^ ".")
        #> read_const ctxt pfx) flds
  in (nm, (cons, typ, sz, algn, map fst flds ~~ (accs ~~ offs))) end

fun structs ctxt csenv pfx = ProgramAnalysis.get_senv csenv
  |> map (process_struct ctxt csenv pfx)
  |> Symtab.make

fun structs_by_typ ctxt csenv pfx = Symtab.dest (structs ctxt csenv pfx)
  |> map (fn (nm, (cons, typ, sz, algn, flds)) => (fst (dest_Type typ), (nm, cons, sz, algn, flds)))
  |> Symtab.make |> Symtab.lookup

fun cons_fields ctxt csenv pfx = structs ctxt csenv pfx |> Symtab.dest
  |> map (fn (_, (cons, typ, _, _, flds))
    => (fst (dest_Const cons), (fst (dest_Type typ),
           map (snd #> fst #> dest_Const #> fst) flds)))
  |> Symtab.make |> Symtab.lookup

fun enums ctxt csenv pfx = let
    val Absyn.CE ecenv = ProgramAnalysis.cse2ecenv csenv
  in
    #enumenv ecenv |> Symtab.dest
    |> map (fn (s, (n, _)) =>
        (read_const ctxt pfx s
            |> dest_Const |> fst, n))
    |> Symtab.make |> Symtab.lookup
  end

fun thm_to_rew thm
    = ((Thm.concl_of thm |> HOLogic.dest_Trueprop |> HOLogic.dest_eq)
        handle TERM _ => (Thm.concl_of thm |> Logic.dest_equals))
    handle TERM _ => (Thm.concl_of thm |> HOLogic.dest_Trueprop |> HOLogic.dest_imp)

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
  val rews = map thm_to_rew (simps @ accups)
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
         string -> (string * term * int * int * (string * (term * int)) list) option,
         pfx: string (* prefix for looking up full names of constants *)}

fun get_all_export_params ctxt csenv pfx : export_params = let
    (* assuming DefineGlobalsList has already run *)
    val defs = if (can (Proof_Context.get_thms ctxt) "no_global_data_defs")
      then [] else Proof_Context.get_thms ctxt "global_data_defs"
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
    enums = enums ctxt csenv pfx,
    cons_fields = cons_fields ctxt csenv pfx,
    structs_by_typ = structs_by_typ ctxt csenv pfx,
    locals = locals ctxt,
    local_upds = local_upds ctxt,
    pfx = pfx} end
\<close>

ML \<open>

val machine_word = case @{typ machine_word} of
    @{typ word32} => "Word 32"
  | @{typ word64} => "Word 64"

fun convert_type _ _ @{typ bool} = "Bool"
  | convert_type _ _ (Type (@{type_name word}, [n]))
    = "Word " ^ signed_string_of_int (dest_binT n)
  | convert_type abs ctxt (Type (@{type_name array}, [t, n]))
    = "Array " ^ convert_type abs ctxt t ^ " " ^ (string_of_int (dest_binT n)
        handle TYPE _ => (case n of Type (s, []) => (unprefix "tyCopy" (Long_Name.base_name s)
            handle Fail _ => raise TYPE ("convert_type", [t, n], []))
         | _ => raise TYPE ("convert_type", [t, n], [])))
  | convert_type true ctxt (Type (@{type_name ptr}, [T])) = "Ptr " ^ convert_type true ctxt T
  | convert_type false _ (Type (@{type_name ptr}, _)) = machine_word
  | convert_type _ _ @{typ "machine_word \<Rightarrow> word8"} = "Mem"
  | convert_type _ _ @{typ "machine_word \<Rightarrow> bool"} = "Dom"
  | convert_type _ _ @{typ "machine_word set"} = "Dom"
  | convert_type _ _ @{typ heap_typ_desc} = "HTD"

  | convert_type _ _ @{typ nat} = raise TYPE ("convert_type: nat", [], [])
  | convert_type _ _ @{typ unit} = "UNIT"
  | convert_type _ _ (Type ("fun", [Type (@{type_name word}, [i]), Type (@{type_name word}, [j])]))
    = "WordArray " ^ signed_string_of_int (dest_binT i) ^ " " ^ signed_string_of_int (dest_binT j)
  | convert_type _ _ (Type (@{type_name itself}, _)) = "Type"
  | convert_type _ _ @{typ int} = raise TYPE ("convert_type: int", [], [])
  | convert_type _ ctxt (Type (s, [])) = if Long_Name.base_name s = "machine_state" then "PMS"
    else (Proof_Context.get_thm ctxt
        (Long_Name.base_name s ^ "_td_names"); "Struct " ^ s)
  | convert_type _ _ T = raise TYPE ("convert_type", [T], [])
\<close>

consts
  pseudo_acc :: "'a \<Rightarrow> 'a"

text \<open>

Phase 1 of the conversion, converts accs and upds on SIMPL
state (a record) to accs of named vars, using the pseudo_acc
constant above to guard the accesses and lists of upds with strings.
\<close>

ML \<open>

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
      (SOME _, _) => NONE
    | (NONE, SOME nm) => SOME (TermsTypes.mk_global_addr_ptr (nm, T))
    | (NONE, NONE) => NONE
  end

fun dest_ptr_type (Type (@{type_name ptr}, [a])) = a
  | dest_ptr_type T = raise TYPE ("dest_ptr_type", [T], [])

fun mk_memacc p = let
    val T = fastype_of p
  in Const (@{const_name h_val}, @{typ heap_mem} --> T --> dest_ptr_type T)
    $ mk_pseudo_acc "Mem" @{typ heap_mem} $ p end

fun mk_fun_app f x = let
    val fT = fastype_of f
  in Const (@{const_name "fun_app"}, fT --> fastype_of x --> range_type fT) $ f $ x end

val ghost_assns = mk_pseudo_acc "GhostAssertions" @{typ "ghost_assertions"}

val int_to_ghost_key = @{term "word_of_int :: int \<Rightarrow> 50 word"}

fun convert_fetch_phase1 _ (@{term hrs_mem} $ _) = mk_pseudo_acc "Mem" @{typ heap_mem}
  | convert_fetch_phase1 _ (@{term hrs_htd} $ _) = mk_pseudo_acc "HTD" @{typ heap_typ_desc}
  | convert_fetch_phase1 _ (Const (@{const_name ghost_assertion_data_get}, _) $ k $ _ $ _)
    = mk_fun_app ghost_assns (int_to_ghost_key $ k)
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

fun mk_fun_upd f x v = Const (@{const_name fun_upd},
    fastype_of f --> fastype_of x --> fastype_of v --> fastype_of f) $ f $ x $ v

fun convert_upd_phase1 ctxt params (t as (Const (@{const_name globals_update}, _)
    $ (Const (c, _) $ f) $ s)) = (case (Envir.beta_eta_contract f,
            String.isPrefix NameGeneration.ghost_state_name
            (Long_Name.base_name c), #rw_global_upds params c) of
        (Const (@{const_name hrs_mem_update}, _)
            $ (Const (@{const_name heap_update}, _) $ p $ v), _, _)
        => [("Mem", convert_fetch_phase1 params (mk_memupd2 p v))]
        | (Const (@{const_name hrs_htd_update}, _) $ g, _, _)
        => [("HTD", (convert_fetch_phase1 params
            (betapply (g, mk_pseudo_acc "HTD" @{typ heap_typ_desc}))))]
        | (Const (@{const_name ghost_assertion_data_set}, _) $ k $ v $ _, _, _)
        => [("GhostAssertions", mk_fun_upd ghost_assns (int_to_ghost_key $ k)
            (convert_fetch_phase1 params v))]
        | (_, true, _) => ((Syntax.pretty_term ctxt f |> Pretty.writeln); [])
        | (_, _, SOME nm) => let
    val acc = the (Symtab.lookup (#rw_globals_tab params) nm) |> fst
    val v = convert_fetch_phase1 params (betapply (f, acc $ s))
    val ptr = TermsTypes.mk_global_addr_ptr (nm, fastype_of v)
  in [("Mem", mk_memupd2 ptr v)] end
    | _ => raise TERM ("convert_upd", [t]))
  | convert_upd_phase1 _ params (t as (Const (c, _) $ f $ s)) = let
    val c' = unsuffix Record.updateN c
    val cT' = fastype_of s --> fastype_of (f $ s)
    val _ = (#local_upds params c) orelse raise TERM ("convert_upd_phase1: nonlocal", [t])
    val v = betapply (f, Const (c', cT') $ s)
  in [(naming c', convert_fetch_phase1 params v)] end
  | convert_upd_phase1 _ _ t = raise TERM ("convert_upd_phase1", [t])
\<close>

text \<open>Phase 2 eliminates compound types, so we access and
update only words from memory and local values.\<close>

ML \<open>
fun ptr_simp ctxt = ctxt addsimps @{thms CTypesDefs.ptr_add_def size_of_def size_td_array
        field_lvalue_offset_eq align_td_array' scast_def[symmetric]
        ucast_def[symmetric]
        sint_sbintrunc' word_smod_numerals word_sdiv_numerals sdiv_int_def smod_int_def}
  |> Simplifier.rewrite

val trace_ptr_simp = false

fun ptr_simp_term ctxt s pat t = let
    val rew_thm = pat |> Thm.cterm_of ctxt |> ptr_simp ctxt
    val rew = rew_thm |> Thm.concl_of |> Logic.varify_global |> Logic.dest_equals
    val _ = (not (fst rew aconv snd rew))
        orelse raise TERM ("ptr_simp_term: " ^ s, [fst rew])
    val _ = if not trace_ptr_simp then () else
        (Thm.pretty_thm ctxt rew_thm |> Pretty.writeln;
         Syntax.pretty_term ctxt t |> Pretty.writeln)
  in Pattern.rewrite_term (Proof_Context.theory_of ctxt) [rew] [] t end

fun convert_ghost_key ctxt k = let
    val procs = Term.add_const_names k []
      |> filter (String.isSuffix HoarePackage.proc_deco)
    val proc_defs = map (suffix "_def" #> Proof_Context.get_thm ctxt) procs
    val conv = Simplifier.rewrite (ctxt addsimps proc_defs)
      (Thm.cterm_of ctxt k)

    val n = Thm.rhs_of conv |> Thm.term_of
    val _ = HOLogic.dest_number n

  in n end

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
        fastype_of p --> @{typ machine_word}) $ p

fun mk_ptr_offs opt_T p offs = let
    val pT = fastype_of p
    val T = case opt_T of NONE => pT
      | SOME T => Type (@{type_name ptr}, [T])
  in Const (@{const_name Ptr}, @{typ machine_word} --> T)
       $ (@{term "(+) :: machine_word \<Rightarrow> _"}
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
    fun mk_offs2 T = mk_offs T o HOLogic.mk_number @{typ machine_word}
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
          => narrow_mem_upd ctxt params (mk_offs elT (@{term "(*) :: machine_word => _"}
                  $ HOLogic.mk_number @{typ machine_word} elT_size
                      $ (@{term "of_nat :: nat \<Rightarrow> machine_word"} $ i)))
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
      val t = @{term "(-) :: machine_word \<Rightarrow> _"} $ get_ptr_val p $ get_ptr_val p'
      val thm = ptr_simp ctxt (Thm.cterm_of ctxt t)
      val t' = Thm.rhs_of thm |> Thm.term_of
    in t' = @{term "0 :: machine_word"}
        orelse (Thm.pretty_thm ctxt thm |> Pretty.writeln; false)
    end

fun narrow_mem_acc _ _ [] p = p
  | narrow_mem_acc ctxt params accs p = let
    fun get_offs (Const (@{const_name Arrays.index}, idxT) $ i) = let
        val (elT, _) = dest_arrayT (domain_type idxT)
        val elT_size = get_c_type_size ctxt elT
      in @{term "(*) :: machine_word \<Rightarrow> _"} $ HOLogic.mk_number @{typ machine_word} elT_size
              $ (@{term "of_nat :: nat \<Rightarrow> machine_word"} $ i) end
      | get_offs (Const (s, T)) = let
        val struct_typ = domain_type T |> dest_Type |> fst
        val (_, _, _, _, flds) = the (#structs_by_typ params struct_typ)
        val matches = filter (fn (_, (c, _)) => c = Const (s, T)) flds
        val _ = (length matches = 1)
            orelse raise TERM ("narrow_mem_acc: get_offs: ", [Const (s, T)])
        val offs = snd (snd (hd matches))
      in HOLogic.mk_number @{typ machine_word} offs end
      | get_offs t = raise TERM ("narrow_mem_acc: get_offs: ", [t])
    val T' = get_acc_type accs (@{typ nat} (* doesn't matter *))
    val offs = foldr1 (fn (x, y) => @{term "(+) :: machine_word \<Rightarrow> _"} $ x $ y)
        (map get_offs accs)
    in mk_ptr_offs (SOME T') p offs end

fun try_norm_index ctxt i = let
    val i' = ptr_simp_term ctxt "idx_simp" i i
  in dest_nat i'; i' end handle TERM _ => i

fun mk_acc_array i xs = let
    val n = length xs
    val _ = warning ("expanding acc array, width " ^ string_of_int n)
    val i = @{term "of_nat :: nat \<Rightarrow> machine_word"} $ i
    fun inner [(x, _)] = x
      | inner ((x, j) :: xs) = let
        val y = inner xs
        val T = fastype_of x
      in Const (@{const_name "If"}, HOLogic.boolT --> T --> T --> T)
        $ HOLogic.mk_eq (i, HOLogic.mk_number @{typ machine_word} j) $ x $ y end
      | inner [] = error "mk_acc_array: empty"
  in inner (xs ~~ (0 upto (n - 1))) end

fun phase2_convert_global ctxt params accs
    ((idx as Const (@{const_name Arrays.index}, _)) $ i $ t)
    = phase2_convert_global ctxt params ((idx $ try_norm_index ctxt i) :: accs) t
  | phase2_convert_global ctxt params accs (Const acc $ t)
    = phase2_convert_global ctxt params (Const acc :: accs) t
  | phase2_convert_global ctxt params accs t = case #const_globals params t
  of SOME nm => let
    val known_offs = forall (fn Const (@{const_name Arrays.index}, _) $ i
          => (try dest_nat i) <> NONE
        | _ => true) accs
    val (c, _) = dest_Const t
    val c_def = Proof_Context.get_thm ctxt (c ^ "_def")
    val def_body = safe_mk_meta_eq c_def |> Thm.rhs_of |> Thm.term_of
        |> Envir.beta_eta_contract
    val p = TermsTypes.mk_global_addr_ptr (nm, fastype_of t)
    val t' = if known_offs then def_body else mk_memacc p
    val t_thm = if known_offs then SOME c_def else NONE
  in SOME (t', t_thm) end
    | _ => NONE

fun convert_fetch_ph2 ctxt params ((Const (@{const_name Arrays.index}, _) $ i) :: accs)
            (t as (Const (@{const_name fupdate}, _) $ _ $ _ $ _)) = let
        val xs = dest_array_init (#cons_field_upds (params : export_params) t)
      in case (try dest_nat i) of
        SOME i => convert_fetch_ph2 ctxt params accs (nth xs i)
      | NONE => mk_acc_array (convert_fetch_ph2 ctxt params [] i)
            (map (convert_fetch_ph2 ctxt params accs) xs)
      end
  | convert_fetch_ph2 ctxt params ((Const (@{const_name Arrays.index}, _) $ i) :: accs)
            (t as (Const (@{const_name FCP}, _) $ _)) = let
        val xs = dest_array_init (#cons_field_upds params t)
      in case (try dest_nat i) of
        SOME i => convert_fetch_ph2 ctxt params accs (nth xs i)
      | NONE => mk_acc_array (convert_fetch_ph2 ctxt params [] i)
            (map (convert_fetch_ph2 ctxt params accs) xs)
      end
  | convert_fetch_ph2 ctxt params accs ((idx as Const (@{const_name Arrays.index}, _)) $ arr $ i) = let
        val i' = convert_fetch_ph2 ctxt params accs i
        val i'' = try_norm_index ctxt i'
      in convert_fetch_ph2 ctxt params (idx $ i'' :: accs) arr end
  | convert_fetch_ph2 ctxt params ((idx as Const (@{const_name Arrays.index}, _)) $ i :: accs)
        (Const (@{const_name Arrays.update}, _) $ arr' $ i' $ v)
     = let
         val eq = HOLogic.mk_eq (i, i')
         val eq = ptr_simp_term ctxt "idx_eq_simp" eq eq handle TERM _ => eq
         val x = convert_fetch_ph2 ctxt params accs v
         val y = convert_fetch_ph2 ctxt params (idx $ i :: accs) arr'
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
            (try dest_nat i)
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
    val cnv = phase2_convert_global ctxt params accs f
        |> Option.map (fst #> convert_fetch_phase1 params)
  in if (get_field ctxt c |> Option.map #3) = SOME false
    then case xs of [x] => convert_fetch_ph2 ctxt params (f :: accs) x
        | _ => raise TERM ("convert_fetch_ph2: expected single", f :: xs)
  else if cnv <> NONE then convert_fetch_ph2 ctxt params accs (the cnv)
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
\<close>

text \<open>The final conversion reduces Isabelle terms to strings\<close>

ML \<open>
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
  | convert_ph3 ctxt params (t as (Const (@{const_name CTypesDefs.ptr_add}, T) $ _ $ _))
    = convert_ph3 ctxt params (ptr_simp_term ctxt "ptr_add"
        (head_of t $ Free ("p", domain_type T) $ Free ("n", @{typ int})) t)
  | convert_ph3 ctxt params (t as (Const (@{const_name field_lvalue}, T) $ _ $ s))
    = convert_ph3 ctxt params (ptr_simp_term ctxt "field_lvalue"
        (head_of t $ Free ("p", domain_type T) $ s) t)
  | convert_ph3 ctxt params (Const (@{const_name store_word64}, _) $ p $ w $ m)
        = convert_op ctxt params "MemUpdate" "Mem" [m, p, w]
  | convert_ph3 ctxt params (Const (@{const_name store_word32}, _) $ p $ w $ m)
        = convert_op ctxt params "MemUpdate" "Mem" [m, p, w]
  | convert_ph3 ctxt params (Const (@{const_name store_word8}, _) $ p $ w $ m)
        = convert_op ctxt params "MemUpdate" "Mem" [m, p, w]
  | convert_ph3 ctxt params (Const (@{const_name heap_update}, _) $ p $ v $ m)
        = convert_op ctxt params "MemUpdate" "Mem" [m, p, v]
  | convert_ph3 ctxt params (t as (Const (@{const_name h_val}, _) $ m $ p))
        = convert_op ctxt params "MemAcc" (convert_type false ctxt (fastype_of t)) [m, p]
  | convert_ph3 ctxt params (Const (@{const_name load_word64}, _) $ p $ m)
        = convert_op ctxt params "MemAcc" "Word 64" [m, p]
  | convert_ph3 ctxt params (Const (@{const_name load_word32}, _) $ p $ m)
        = convert_op ctxt params "MemAcc" "Word 32" [m, p]
  | convert_ph3 ctxt params (Const (@{const_name load_word8}, _) $ p $ m)
        = convert_op ctxt params "MemAcc" "Word 8" [m, p]
  | convert_ph3 ctxt params (Const (@{const_name fun_upd}, _) $ f $ x $ v)
        = convert_op ctxt params "WordArrayUpdate"
            (convert_type false ctxt (fastype_of f)) [f, x, v]
  | convert_ph3 ctxt params (Const (@{const_name fun_app}, _) $ f $ x)
        = convert_op ctxt params "WordArrayAccess"
            (convert_type false ctxt (fastype_of (f $ x))) [f, x]
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
  | convert_ph3 ctxt params (Const (@{const_name array_assertion}, _) $ p $ n $ htd)
        = convert_op ctxt params "PArrayValid" "Bool"
            [htd, ptr_to_typ p, p, @{term "of_nat :: nat => machine_word"} $ n]
  | convert_ph3 ctxt params (Const (@{const_name ptr_add_assertion'}, assT)
            $ p $ n $ str $ htd)
        = convert_ph3 ctxt params let val T = dest_ptr_type (fastype_of p)
            val ass' = (Const (@{const_name ptr_add_assertion}, assT)) $ p $ n $ str $ htd
            val ass'' = Pattern.rewrite_term (Proof_Context.theory_of ctxt)
              (map thm_to_rew @{thms ptr_add_assertion_uintD ptr_add_assertion_sintD
                                     if_True if_False}) [] ass'
          in if T = @{typ unit} orelse T = @{typ word8}
            then @{term True} else ass'' end
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
        = "Symbol " ^ HOLogic.dest_string s ^ " " ^ machine_word
  | convert_ph3 ctxt params (Const (@{const_name of_nat}, T) $ (Const (@{const_name unsigned}, _) $ x))
        = let
            val t1 = fastype_of x
            val t2 = range_type T
          in if t1 = t2 then convert_ph3 ctxt params x
            else convert_ph3 ctxt params (Const (@{const_name unsigned}, t1 --> t2) $ x)
          end
  | convert_ph3 ctxt params (t as (Const (@{const_name of_nat}, _) $ _))
        = convert_ph3 ctxt params (ptr_simp_term ctxt "of_nat" t t)
  | convert_ph3 ctxt params (t as (Const (@{const_name power}, _) $ x $ y))
        = (case try HOLogic.dest_number x of
            SOME ((typ as Type (@{type_name word}, _)), 2) => convert_ph3 ctxt params
                (Const (@{const_name shiftl}, typ --> @{typ nat} --> typ)
                    $ HOLogic.mk_number typ 1 $ y)
        | _ => convert_ph3 ctxt params (ptr_simp_term ctxt "power" t t))
  | convert_ph3 ctxt params (Const (@{const_name ptr_coerce}, _) $ p)
        = convert_ph3 ctxt params p
  | convert_ph3 ctxt params (t as (Const (@{const_name of_int}, _) $ _))
    = if head_of t = int_to_ghost_key then convert_ph3 ctxt params (convert_ghost_key ctxt t)
     else let
        val thy = Proof_Context.theory_of ctxt
        val t' = Pattern.rewrite_term thy (map (Thm.concl_of #> HOLogic.dest_Trueprop
            #> HOLogic.dest_eq) @{thms word_uint.Rep_inverse word_sint.Rep_inverse}) [] t
      in if t' aconv t then convert_ph3 ctxt params (ptr_simp_term ctxt "word_of_int" t t)
        else convert_ph3 ctxt params t' end
  | convert_ph3 ctxt params (t as (Const (@{const_name signed_divide}, _) $ _ $ _))
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
        unat_less_2p_word_bits[simplified word_bits_conv]}
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
\<close>

ML \<open>
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
        |> convert_upd_phase1 ctxt params
(*        |> map tracet *)
(*        |> map (apsnd (Syntax.check_term ctxt)) *)
        |> maps (convert_upd_ph2 ctxt params)
(*        |> map (apsnd (Syntax.check_term ctxt)) *)
        |> map (convert_upd_ph3 ctxt params)
        )
      else raise TERM ("convert_param_upds", [t])
  | convert_param_upds ctxt _ t = (if t = s_st ctxt then []
    else raise TERM ("convert_param_upds", [t]))

\<close>

ML \<open>

val all_c_params = ["Mem Mem", "HTD HTD", "PMS PMS",
                    "GhostAssertions WordArray 50 " ^ ParseGraph.ptr_size_str]
val all_c_in_params = map (prefix "Var ") all_c_params
val all_asm_params = ["Mem Mem", "PMS PMS"]
val all_asm_in_params = map (prefix "Var ") all_asm_params

fun asm_spec_name_to_fn_name _ specname = let
    val name = space_implode "_" (space_explode " " specname)
  in "asm_instruction'" ^ name end

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


fun is_spec_body_const @{const_name Spec} = true
  | is_spec_body_const @{const_name guarded_spec_body} = true
  | is_spec_body_const _ = false

fun has_reads body = exists_Const (fn (s, T) =>
    snd (strip_type T) = @{typ heap_raw_state}
        orelse is_spec_body_const s) body

fun has_reads_globals (params : export_params) body = exists_Const (fn (s, T) =>
    snd (strip_type T) = @{typ heap_raw_state}
  orelse is_spec_body_const s
  orelse #rw_global_accs params s <> NONE
  orelse #const_globals params (Const (s, T)) <> NONE
  ) body

fun get_reads_calls ctxt params globals name = let
    val thm = Proof_Context.get_thm ctxt (name ^ "_body_def")
        |> simplify (put_simpset HOL_basic_ss ctxt addsimps @{thms call_def block_def block_exn_def})
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

fun emit outfile s = TextIO.output (outfile, s ^ "\n")

fun add_global_valid_assertion outfile ctxt params t n =
  case get_global_valid_assertion ctxt params t of NONE =>
        (n + 1, string_of_int n)
      | SOME ass => (emit outfile (string_of_int (n + 1) ^ " Cond " ^ string_of_int n ^ " Err " ^ ass);
        (n + 2, string_of_int (n + 1)))

fun emit_body ctxt outfile params (Const (@{const_name Seq}, _) $ a $ b) n c e = let
    val (n, nm) = emit_body ctxt outfile params b n c e
        handle TERM (s, ts) => raise TERM (s, b :: ts)
            | Empty => raise TERM ("emit_body: got Empty", [b])
    val (n, nm) = emit_body ctxt outfile params a n nm e
        handle TERM (s, ts) => raise TERM (s, a :: ts)
            | Empty => raise TERM ("emit_body: got Empty", [a])
  in (n, nm) end
  | emit_body ctxt outfile params (Const (@{const_name Catch}, _) $ a $ b) n c e = (case b of
    Const (@{const_name com.Skip}, _) => emit_body ctxt outfile params a n c (c, c)
  | Const (@{const_name ccatchbrk}, _) $ _ => emit_body ctxt outfile params a n c (fst e, c)
  | t => raise TERM ("emit_body ctxt params (Catch)", [t])
  )
  | emit_body ctxt outfile params (Const (@{const_name creturn}, _) $ _ $ upd $ f) n _ (r, b) =
    emit_body ctxt outfile params (@{term com.Basic} $ Abs ("s", dummyT, betapplys (upd,
        [Abs ("_", dummyT, betapply (f, Bound 1)), Bound 0]))) n r (r, b)
  | emit_body _ _ _ (Const (@{const_name creturn_void}, _) $ _) n _ (r, _) = (n, r)
  | emit_body _ _ _ (Const (@{const_name cbreak}, _) $ _) n _ (_, b) = (n, b)
  | emit_body _ _ _ (Const (@{const_name com.Skip}, _)) n c _ = (n, c)
  | emit_body ctxt outfile params (Const (@{const_name com.Cond}, _) $ S $ a $ b) n c e = let
    val (n, nm_a) = emit_body ctxt outfile params a n c e
    val (n, nm_b) = emit_body ctxt outfile params b n c e
    val s = convert_fetch ctxt params (reduce_set_mem ctxt (s_st ctxt) S)
  in
    emit outfile (string_of_int n ^ " Cond " ^ nm_a ^ " " ^ nm_b ^ " " ^ s);
    add_global_valid_assertion outfile ctxt params S n
  end
  | emit_body ctxt outfile params (Const (@{const_name Guard}, T) $ F $ G $
            (Const (@{const_name Guard}, _) $ _ $ G' $ a)) n c e
        = emit_body ctxt outfile params (Const (@{const_name Guard}, T) $ F
            $ (mk_set_int G G') $ a) n c e
  | emit_body ctxt outfile params (Const (@{const_name Guard}, _) $ _ $ G $ a) n c e = let
    val (n, nm) = emit_body ctxt outfile params a n c e
    val thy = Proof_Context.theory_of ctxt
    val G = Pattern.rewrite_term thy
      (@{thms guard_arith_simps meta_eq_to_obj_eq[OF ptr_arr_retyps_def]}
        |> map (Thm.concl_of #> HOLogic.dest_Trueprop #> HOLogic.dest_eq)) [] G
    val s = convert_fetch ctxt params (reduce_set_mem ctxt (s_st ctxt) G)
  in
    emit outfile (string_of_int n ^ " Cond " ^ nm ^ " Err " ^ s);
    add_global_valid_assertion outfile ctxt params G n
  end
  | emit_body _ _ _ (Const (@{const_name com.Basic}, _) $ Abs (_, _, Bound 0)) n c _
    = (n, c)
  | emit_body ctxt outfile params (Const (@{const_name com.Basic}, _) $ f) n c _ = let
    val upds = convert_param_upds ctxt params (betapply (f, s_st ctxt))
      |> filter_out (fn (s, v) => v = "Var " ^ s)
      |> map (fn (s, v) => s ^ " " ^ v)

  in
    emit outfile (string_of_int n ^ " Basic " ^ c ^ " " ^ space_pad_list upds);
    add_global_valid_assertion outfile ctxt params f n
  end
  | emit_body ctxt outfile params (Const (@{const_name Spec}, _)
        $ (Const (@{const_name asm_spec}, _) $ _ $ _ $ vol $ spec $ lhs $ vs))
    n c _ = let
    val spec = HOLogic.dest_string spec
    val lhss = convert_param_upds ctxt params
      (betapplys (lhs, [@{term "0 :: machine_word"}, s_st ctxt]))
    val args = HOLogic.dest_list (betapply (vs, s_st ctxt))
      |> map (convert_fetch ctxt params)
    val args = args @ all_asm_in_params
    val outs = map fst lhss @ all_asm_params
    val _ = HOLogic.mk_prod
  in emit outfile (string_of_int n ^ " Call " ^ c ^ " " ^ asm_spec_name_to_fn_name vol spec
    ^ " " ^ space_pad_list args ^ " " ^ space_pad_list outs);
     add_global_valid_assertion outfile ctxt params (HOLogic.mk_prod (lhs, vs)) n
  end
  | emit_body ctxt outfile params (Const (@{const_name call}, _) $ f $ Const (p, _)
        $ _ $ r2) n c e = let
    val proc_info = Hoare.get_data ctxt |> #proc_info
    val ret_vals = Symtab.lookup proc_info (Long_Name.base_name p)
        |> the |> #params
        |> filter (fn (v, _, _) => v = HoarePackage.Out)
        |> maps (#2 #> read_const ctxt (#pfx params)
         #> synthetic_updates ctxt params "rv#space#")
        |> map #1

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

    val (n, nm_save) = emit_body ctxt outfile params (betapplys (r2, [@{term i}, rv_st ctxt])) n c e

  in emit outfile (string_of_int n ^ " Call " ^ nm_save ^ " " ^ (unsuffix "_'proc" p)
    ^ " " ^ space_pad_list args ^ " " ^ space_pad_list out);
     add_global_valid_assertion outfile ctxt params f n
  end
  | emit_body _ _ _ (Const (@{const_name lvar_nondet_init}, _) $ _ $ _) n c _
    = (n, c)
  | emit_body ctxt outfile params (Const (@{const_name whileAnno}, _) $ C $ _ $ _ $ bd) n c e = let
    fun sn i = string_of_int (n + i)
    val lc = "loop#" ^ sn 0 ^ "#count" ^ " " ^ machine_word
    val (n', nm) = emit_body ctxt outfile params bd (n + 4) (sn 0) e
    val cond = convert_fetch ctxt params (reduce_set_mem ctxt (s_st ctxt) C)
    val err_cond = case get_global_valid_assertion ctxt params C
        of NONE => "Op True Bool 0"
        | SOME s => s
  in emit outfile (sn 0 ^ " Basic " ^ sn 1 ^ " 1 " ^ lc
      ^ " Op Plus " ^ machine_word ^ " 2 Var " ^ lc ^ " Num 1 " ^ machine_word);
    emit outfile (sn 1 ^ " Cond " ^ sn 2 ^ " Err " ^ err_cond);
    emit outfile (sn 2 ^ " Cond " ^ nm ^ " " ^ c ^ " " ^ cond);
    emit outfile (sn 3 ^ " Basic " ^ sn 1 ^ " 1 " ^ lc ^ " Num 0 " ^ machine_word);
    (n', sn 3)
  end
  | emit_body _ _ _ t _ _ _ = raise TERM ("emit_body", [t])

fun emit_func_body ctxt outfile eparams name = let
    val proc_info = Hoare.get_data ctxt |> #proc_info
    val params = Symtab.lookup proc_info (name ^ "_'proc")
        |> the |> #params |> map (fn (a, b, _) => (a, b))
        |> map (apsnd (read_const ctxt (#pfx eparams)
                #> synthetic_updates ctxt eparams ""
                #> map #1))

    val no_read = mk_safe is_no_read_globals ctxt eparams name
    val no_write = mk_safe (K o is_no_write) ctxt eparams name
    (* writes implicitly require reads, really *)
    val no_read = no_read andalso no_write

    val inputs = (filter (fn p => fst p = HoarePackage.In) params
      |> maps snd) @ (if no_read then [] else all_c_params)

    val outputs = (filter (fn p => fst p = HoarePackage.Out) params
      |> maps snd) @ (if no_write then [] else all_c_params)

    val body = Get_Body_Refines.get ctxt name
      |> simplify (put_simpset HOL_basic_ss ctxt
                addsimps @{thms switch.simps fst_conv snd_conv
                                insert_iff empty_iff
                                ptr_add_assertion_def if_True if_False
                                bv_clz_def[symmetric] bv_ctz_def[symmetric]
                 })
      |> Thm.concl_of |> HOLogic.dest_Trueprop
      |> (fn t => (case t of Const (@{const_name simple_simpl_refines}, _) $ _ $ lhs $ _ => lhs
            | _ => raise Option))
        handle Option => @{term "Spec S"}
         | THM _ => @{term "Spec S"}

    val full_nm = read_const ctxt (#pfx eparams) (name ^ "_'proc")
        |> dest_Const |> fst |> unsuffix "_'proc"
  in emit outfile "";
    emit outfile ("Function " ^ full_nm ^ " " ^ space_pad_list inputs
                ^ " " ^ space_pad_list outputs);
    if (try (head_of #> dest_Const #> fst #> is_spec_body_const) body)
        = SOME true
    then ()
    else (emit outfile ("1 Basic Ret 0");
          emit_body ctxt outfile eparams body 2 "1" ("ErrExc", "ErrExc")
            |> snd |> prefix "EntryPoint " |> emit outfile
          handle TERM (s, ts) => raise TERM ("emit_func_body: " ^ name ^ ": " ^ s, body :: @{term True} :: ts)
            | TYPE (s, Ts, ts) => raise TYPE ("emit_func_body: " ^ name ^ ": " ^ s, Ts, body :: @{term True} :: ts)
            | Empty => raise TERM ("emit_func_body: Empty", [body]))
  end

fun emit_struct ctxt outfile csenv pfx (nm, flds) = let
    val offs = map (ProgramAnalysis.offset csenv (map snd flds))
        (0 upto (length flds - 1))
    val full_nm = read_const ctxt pfx (nm ^ "." ^ nm)
        |> dest_Const |> snd |> strip_type |> snd |> dest_Type |> fst
    val thy = Proof_Context.theory_of ctxt
    val sz = ProgramAnalysis.sizeof csenv (Absyn.StructTy nm)
    val algn = ProgramAnalysis.alignof csenv (Absyn.StructTy nm)
    fun emit_fld ((fld_nm, fld_ty), offs) = emit outfile (space_pad
        ["StructField", fld_nm, convert_type false ctxt
            (CalculateState.ctype_to_typ (thy, fld_ty)), string_of_int offs])
  in emit outfile (space_pad ["Struct", full_nm, string_of_int sz,
    string_of_int algn]); app emit_fld (flds ~~ offs) end

fun scan_func_body_asm_instructions ctxt name = let
    val body = Proof_Context.get_thm ctxt (name ^ "_body_def")
    fun has_lhs lhs = betapplys (lhs, [Bound 0, Bound 1]) <> Bound 1
    fun nm_args vs = betapply (vs, s_st ctxt) |> HOLogic.dest_list |> length
    fun gather (Const (@{const_name asm_spec}, _) $ _ $ _ $ vol $ nm $ lhs $ vs) xs
        = (asm_spec_name_to_fn_name vol (HOLogic.dest_string nm),
            has_lhs lhs, nm_args vs) :: xs
      | gather (f $ x) xs = gather f (gather x xs)
      | gather _ xs = xs
  in gather (Thm.concl_of body) [] end
        handle ERROR _ => []

fun emit_asm_protoes ctxt outfile fs = let
    val asm_info = maps (scan_func_body_asm_instructions ctxt) fs
      |> sort_distinct (fn ((s, _, _), (t, _, _)) => fast_string_ord (s, t))
    fun mk_args n = (map (fn i => "arg" ^ string_of_int i ^ " " ^ machine_word) (1 upto n))
    fun mk_rets has_lhs = (if has_lhs then ["ret1 " ^ machine_word] else [])
    fun emit_it (nm, has_lhs, nm_args) = emit outfile
      ("Function " ^ nm
              ^ " " ^ space_pad_list (mk_args nm_args @ all_asm_params)
              ^ " " ^ space_pad_list (mk_rets has_lhs @ all_asm_params)
    )
  in app emit_it asm_info end

fun emit_C_everything ctxt csenv outfile pfx = let
    val fs = ProgramAnalysis.get_functions csenv
    val structs = ProgramAnalysis.get_senv csenv
    val params = get_all_export_params ctxt csenv pfx
  in app (emit_struct ctxt outfile csenv pfx) structs;
     app (emit_func_body ctxt outfile params) fs;
     emit_asm_protoes ctxt outfile fs end
\<close>

ML \<open>
fun openOut_relative thy = ParseGraph.filename_relative thy #> TextIO.openOut;

(* pfx: prefix for constant lookups, usually theory where C code was loaded, e.g. "Kernel_C" *)
fun emit_C_everything_relative ctxt csenv fname pfx = let
    val thy = Proof_Context.theory_of ctxt
    val outfile = openOut_relative thy fname
  in emit_C_everything ctxt csenv outfile pfx; TextIO.closeOut outfile end
\<close>

end
