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

imports
    "../../tools/asmrefine/GraphLang"
    "../../tools/asmrefine/CommonOps"
    "Substitute"

begin

(* things to export
 1 types
  2 C constants
  3 C functions
*)

lemma field_lvalue_offset_eq:
  "field_lookup (typ_info_t TYPE('a :: c_type)) f 0 = Some v
        \<Longrightarrow> field_lvalue (ptr :: 'a ptr) f = ptr_val ptr + of_nat (snd v)"
  apply (cases v, simp, drule field_lookup_offset_eq)
  apply (simp add: field_lvalue_def)
  done

ML {*
val csenv = let
    val the_csenv = CalculateState.get_csenv @{theory} "c/kernel_all.c_pp" |> the
  in fn () => the_csenv end
*}

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

val locals = Record.get_recT_fields @{theory} @{typ "'a myvars"}
  |> fst
  |> filter_out (fn (s, _) => s = @{const_name "globals"})
  |> Symtab.make |> Symtab.defined

val local_upds = Record.get_recT_fields @{theory} @{typ "'a myvars"}
  |> fst
  |> filter_out (fn (s, _) => s = @{const_name "globals"})
  |> map (apfst (suffix Record.updateN))
  |> Symtab.make |> Symtab.defined

fun get_field s = let
    val xs = space_explode "." s
    val fld = List.last xs
    val tp = rev xs |> tl |> rev |> space_implode "."
    val fld = unsuffix "_update" fld handle Fail _ => fld
    val _ = Proof_Context.get_thm @{context}
        (tp ^ "_" ^ fld ^ "_fl_Some")
  in SOME (tp, fld) end
    handle ERROR _ => NONE
       | Bind => NONE

fun process_struct ctxt (nm, flds) = let
    val offs = map (ProgramAnalysis.offset (csenv ()) (map snd flds))
        (0 upto (length flds - 1))
    val cons = Proof_Context.read_const_proper ctxt true (nm ^ "." ^ nm)
    val typ = dest_Const cons |> snd |> strip_type |> snd
    val sz = ProgramAnalysis.sizeof (csenv ()) (Absyn.StructTy nm)
    val algn = ProgramAnalysis.alignof (csenv ()) (Absyn.StructTy nm)
    val accs = map (fst #> prefix (nm ^ ".")
        #> Proof_Context.read_const_proper ctxt true) flds
  in (nm, (cons, typ, sz, algn, map fst flds ~~ (accs ~~ offs))) end

val structs = ProgramAnalysis.get_senv (csenv ())
  |> map (process_struct @{context})
  |> Symtab.make

val structs_by_typ = Symtab.dest structs
  |> map (fn (nm, (cons, typ, sz, algn, flds)) => (fst (dest_Type typ), (nm, cons, sz, algn, flds)))
  |> Symtab.make |> Symtab.lookup

val cons_fields = structs |> Symtab.dest
  |> map (fn (_, (cons, typ, _, _, flds))
    => (fst (dest_Const cons), (fst (dest_Type typ),
           map (snd #> fst #> dest_Const #> fst) flds)))
  |> Symtab.make |> Symtab.lookup

val enums = let
    val Absyn.CE ecenv = ProgramAnalysis.cse2ecenv (csenv ());
  in
    #enumenv ecenv |> Symtab.dest
    |> map (fn (s, (n, _)) =>
        (Proof_Context.read_const_proper @{context} true s
            |> dest_Const |> fst, n))
    |> Symtab.make |> Symtab.lookup
  end

val cons_field_upds = let
  val simps = ProgramAnalysis.get_senv (csenv ())
    |> maps (fn (tp, vs) => map (pair tp o fst) vs)
    |> maps (fn (tp, fld) => [Proof_Context.get_thm @{context}
          (tp ^ "." ^ fld ^ ".simps"),
        Proof_Context.get_thm @{context}
          (tp ^ "." ^ fld ^ Record.updateN ^ ".simps")])
  val accups = ProgramAnalysis.get_senv (csenv ())
    |> map (fn (tp, _) => (tp, Proof_Context.get_thms @{context}
          (tp ^ "_accupd_same")))
    |> maps (fn (_, [t]) => [t]
              | (tp, ts) => ts @ Proof_Context.get_thms @{context}
          (tp ^ "_accupd_diff"))
  val rews = map (concl_of #> HOLogic.dest_Trueprop #> HOLogic.dest_eq) (simps @ accups)
  in Pattern.rewrite_term @{theory} rews [] end

val const_global_tab = const_globals |> map swap |> Termtab.make |> Termtab.lookup

val rw_globals = map_filter (fn (Const (@{const_name global_data}, _) $ nm $ get $ set)
    => SOME (HOLogic.dest_string nm, get, set) | _ => NONE) global_datas

val rw_globals_tab = Symtab.make (map (fn x => (#1 x, (#2 x, #3 x))) rw_globals)

val rw_global_acc_table = map (fn (nm, c, _) => (fst (dest_Const c), nm)) rw_globals
    |> Symtab.make |> Symtab.lookup

val rw_global_upd_table = map (fn (nm, _, c) => (fst (dest_Const c), nm)) rw_globals
    |> Symtab.make |> Symtab.lookup

*}

ML {*

fun convert_type _ @{typ bool} = "Bool"
  | convert_type _ (Type (@{type_name word}, [n]))
    = "Word " ^ signed_string_of_int (dest_binT n)
  | convert_type abs (Type (@{type_name array}, [t, n]))
    = "Array " ^ convert_type abs t ^ " " ^ (string_of_int (dest_binT n)
        handle TYPE _ => (case n of Type (s, []) => (unprefix "tyCopy" (Long_Name.base_name s)
            handle Fail _ => raise TYPE ("convert_type", [t, n], []))
         | _ => raise TYPE ("convert_type", [t, n], [])))
  | convert_type true (Type (@{type_name ptr}, [T])) = "Ptr " ^ convert_type true T
  | convert_type false (Type (@{type_name ptr}, _)) = "Word 32"
  | convert_type _ @{typ "word32 \<Rightarrow> word8"} = "Mem"
  | convert_type _ @{typ "word32 \<Rightarrow> bool"} = "Dom"
  | convert_type _ @{typ "word32 set"} = "Dom"
  | convert_type _ @{typ heap_typ_desc} = "HTD"
  | convert_type _ @{typ machine_state} = "PMS"
  | convert_type _ @{typ nat} = "Word 32"
  | convert_type _ @{typ unit} = "UNIT"
  | convert_type _ (Type (@{type_name itself}, _)) = "Type"
  | convert_type _ @{typ int} = raise TYPE ("convert_type: int", [], [])
  | convert_type _ (Type (s, [])) = (Proof_Context.get_thm @{context}
        (Long_Name.base_name s ^ "_td_names"); "Struct " ^ s)
  | convert_type _ T = raise TYPE ("convert_type", [T], [])

fun ptr_simp ctxt = ctxt addsimps @{thms CTypesDefs.ptr_add_def size_of_def size_td_array
        field_lvalue_offset_eq align_td_array' word_of_int scast_def[symmetric]
        sint_sbintrunc' sdiv_word_def sdiv_int_def}
  |> Simplifier.rewrite

val trace_ptr_simp = false

fun ptr_simp_term ctxt s pat t = let
    val rew_thm = pat |> cterm_of @{theory} |> ptr_simp ctxt
    val rew = rew_thm |> concl_of |> Logic.varify_global |> Logic.dest_equals
    val _ = (not (fst rew aconv snd rew))
        orelse raise TERM ("ptr_simp_term: " ^ s, [fst rew])
    val _ = if not trace_ptr_simp then () else
        (Display.pretty_thm ctxt rew_thm |> Pretty.writeln;
         Syntax.pretty_term ctxt t |> Pretty.writeln)
  in Pattern.rewrite_term (Proof_Context.theory_of ctxt) [rew] [] t end

fun dest_ptr_type (Type (@{type_name ptr}, [a])) = a
  | dest_ptr_type T = raise TYPE ("dest_ptr_type", [T], [])

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

val space_pad = space_implode " "

fun space_pad_list xs = space_pad (string_of_int (length xs) :: xs)

val s_st = @{term "s :: globals myvars"}

fun mk_acc_array i T xs = let
  in fold (fn (j, x) => fn s => "Op IfThenElse " ^ T
            ^ " 3 Op Equals Bool 2 " ^ i ^ " Num " ^ string_of_int j ^ " Word 32 "
            ^ x ^ " " ^ s)
            (1 upto (length xs - 1) ~~ tl xs) (hd xs)
  end

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
  | get_acc_type accs T = head_of (List.last accs)
        |> type_of |> strip_type |> snd

fun dest_mem_acc_addr (Const (@{const_name h_val}, _) $ m $ p)
        = SOME p
  | dest_mem_acc_addr t = let
    val acc = case head_of t of Const (c, _) => rw_global_acc_table c
        | _ => NONE
    val const = const_global_tab t
    val T = fastype_of t
  in case (const, acc) of
      (SOME nm, _) => SOME (TermsTypes.mk_global_addr_ptr (nm, T))
    | (NONE, SOME nm) => SOME (TermsTypes.mk_global_addr_ptr (nm, T))
    | (NONE, NONE) => NONE
  end

fun narrow_mem_upd ctxt p v = let
    val T = fastype_of v
    val mk_offs = mk_ptr_offs NONE p
    val mk_offs2 = mk_offs o HOLogic.mk_number @{typ word32}
    val sterm = Syntax.pretty_term ctxt #> Pretty.string_of
    val styp = Syntax.pretty_typ ctxt #> Pretty.string_of
  in if (dest_mem_acc_addr v = SOME p) then []
    else if structs_by_typ (fst (dest_Type T)) <> NONE
    then let
      val (_, _, _, _, flds) = the (structs_by_typ (fst (dest_Type T)))
      val fld_writes = map (fn (_, (acc, offs)) => (mk_offs2 offs,
          cons_field_upds (acc $ v))) flds
    in maps (uncurry (narrow_mem_upd ctxt)) fld_writes end
    else if fst (dest_Type T) = @{type_name array}
    then let
        val (elT, n) = dest_arrayT T
        val elT_size = get_c_type_size ctxt elT
      in case v of (Const (@{const_name Arrays.update}, _) $ arr $ i $ x)
          => narrow_mem_upd ctxt (mk_offs (@{term "op * :: word32 => _"}
                  $ HOLogic.mk_number @{typ word32} elT_size
                      $ (@{term "of_nat :: nat \<Rightarrow> word32"} $ i)))
              x @ narrow_mem_upd ctxt p arr
      | _ => let
          val addrs = map (fn i => (mk_offs2 (i * elT_size)))
              (0 upto (n - 1))
          val elems = dest_array_init v
              handle TERM _ => map
                    (fn i => mk_arr_idx v (HOLogic.mk_number @{typ nat} i))
                    (0 upto (n - 1))
          val _ = (if n < 16 then () else
            warning ("expanding " ^ string_of_int n ^ ": "
                ^ sterm p ^ styp (fastype_of p) ^ ": " ^ sterm v))
      in maps (uncurry (narrow_mem_upd ctxt)) (addrs ~~ elems) end
    end
    else if fst (dest_Type T) <> @{type_name word}
        andalso fst (dest_Type T) <> @{type_name ptr}
    then raise TERM ("narrow_mem_upd failed to narrow:", [p, v])
    else [(p, v)]
  end

fun narrow_mem_acc _ [] p = p
  | narrow_mem_acc ctxt accs p = let
    fun get_offs (Const (@{const_name Arrays.index}, idxT) $ i) = let
        val (elT, _) = dest_arrayT (domain_type idxT)
        val elT_size = get_c_type_size ctxt elT
      in @{term "op * :: word32 \<Rightarrow> _"} $ HOLogic.mk_number @{typ word32} elT_size
              $ (@{term "of_nat :: nat \<Rightarrow> word32"} $ i) end
      | get_offs (Const (s, T)) = let
        val struct_typ = domain_type T |> dest_Type |> fst
        val (_, _, _, _, flds) = the (structs_by_typ struct_typ)
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

fun convert_mem_acc ctxt accs p m = let
    val p' = narrow_mem_acc ctxt accs p
    val T = dest_ptr_type (fastype_of p')
        handle TYPE _ => raise TERM ("convert_mem_acc", p :: p' :: accs)
  in "Op MemAcc " ^ (convert_type false T) ^ " 2 " ^ m ^ " " ^ convert_fetch ctxt [] p' end

and convert_op_accs ctxt accs nm tp xs = "Op " ^ nm ^ " " ^ tp
    ^ " " ^ space_pad_list (map (convert_fetch ctxt accs) xs)

and convert_op ctxt nm tp xs = convert_op_accs ctxt [] nm tp xs

and convert_fetch ctxt [] (Const (@{const_name Collect}, _) $ S $ x)
    = convert_fetch ctxt [] (betapply (S, x))
  | convert_fetch ctxt [] (Const (@{const_name Lattices.inf}, _) $ S $ T $ x)
    = convert_op ctxt "And" "Bool" [betapply (S, x), betapply (T, x)]
  | convert_fetch ctxt [] (t as (Const (@{const_name CTypesDefs.ptr_add}, T) $ _ $ _))
    = convert_fetch ctxt [] (ptr_simp_term ctxt "ptr_add"
        (head_of t $ Free ("p", domain_type T) $ Free ("n", @{typ int})) t)
  | convert_fetch ctxt [] (t as (Const (@{const_name field_lvalue}, T) $ _ $ s))
    = convert_fetch ctxt [] (ptr_simp_term ctxt "field_lvalue"
        (head_of t $ Free ("p", domain_type T) $ s) t)
  | convert_fetch ctxt [] (Const (@{const_name Ptr}, _) $ p) = convert_fetch ctxt [] p
  | convert_fetch ctxt [] (Const (@{const_name ptr_val}, _) $ p) = convert_fetch ctxt [] p
  | convert_fetch ctxt ((Const (@{const_name Arrays.index}, _) $ i) :: accs)
            (t as (Const (@{const_name fupdate}, _) $ _ $ _ $ _)) = let
        val xs = dest_array_init (cons_field_upds t)
      in case (try dest_nat i) of
        SOME i => convert_fetch ctxt accs (nth xs i)
      | NONE => mk_acc_array (convert_fetch ctxt [] i)
            (convert_type false (get_acc_type accs (fastype_of (hd xs))))
            (map (convert_fetch ctxt accs) xs)
      end
  | convert_fetch ctxt ((Const (@{const_name Arrays.index}, _) $ i) :: accs)
            (t as (Const (@{const_name FCP}, _) $ _)) = let
        val xs = dest_array_init (cons_field_upds t)
      in case (try dest_nat i) of
        SOME i => convert_fetch ctxt accs (nth xs i)
      | NONE => mk_acc_array (convert_fetch ctxt [] i) (convert_type false (fastype_of (hd xs)))
            (map (convert_fetch ctxt accs) xs)
      end
  | convert_fetch ctxt accs ((idx as Const (@{const_name Arrays.index}, _)) $ arr $ i) = let
        val i' = ptr_simp_term ctxt "idx_simp" i i handle TERM _ => i
      in case try dest_nat i' of SOME _ => convert_fetch ctxt (idx $ i' :: accs) arr
        | NONE => convert_fetch ctxt (idx $ i :: accs) arr end
  | convert_fetch ctxt ((idx as Const (@{const_name Arrays.index}, _)) $ i :: accs)
        (Const (@{const_name Arrays.update}, _) $ arr' $ i' $ v)
     = let
         val eq = HOLogic.mk_eq (i, i')
         val eq = ptr_simp_term ctxt "idx_eq_simp" eq eq handle TERM _ => eq
         val x = convert_fetch ctxt accs v
         val y = convert_fetch ctxt (idx $ i :: accs) arr'
      in case eq of @{term True} => x | @{term False} => y
                  | eq => "Op IfThenElse " ^ (convert_type false (fastype_of v))
            ^ " " ^ space_pad_list [convert_fetch ctxt [] eq, x, y] end
  | convert_fetch ctxt [] (Const (@{const_name store_word32}, _) $ p $ w $ m)
        = convert_op ctxt "MemUpdate" "Mem" [m, p, w]
  | convert_fetch ctxt [] (Const (@{const_name store_word8}, _) $ p $ w $ m)
        = convert_op ctxt "MemUpdate" "Mem" [m, p, w]
  | convert_fetch ctxt accs (Const (@{const_name h_val}, _) $ m $ p)
        = convert_mem_acc ctxt accs p (convert_fetch ctxt [] m)
  | convert_fetch ctxt [] (Const (@{const_name load_word32}, _) $ p $ m)
        = convert_op ctxt "MemAcc" "Word 32" [m, p]
  | convert_fetch ctxt [] (Const (@{const_name load_word8}, _) $ p $ m)
        = convert_op ctxt "MemAcc" "Word 8" [m, p]
  | convert_fetch ctxt [] ((m as Free (_, @{typ "word32 \<Rightarrow> word8"})) $ p)
        = convert_op ctxt "MemAcc" "Word 8" [m, p]
  | convert_fetch ctxt [] (Const (@{const_name fun_upd}, _)
        $ (m as Free (_, @{typ "word32 \<Rightarrow> word8"})) $ p $ v)
        = convert_op ctxt "MemUpdate" "Mem" [m, p, v]
  | convert_fetch ctxt [] ((le as Const (@{const_name less_eq}, _))
        $ (Const (@{const_name insert}, _) $ p $ S) $ D)
        = convert_op ctxt "And" "Bool" [HOLogic.mk_mem (p, D), le $ S $ D]
  | convert_fetch ctxt [] (Const (@{const_name less_eq}, _)
        $ Const (@{const_name bot_class.bot}, _) $ _) = convert_fetch ctxt [] @{term True}
  | convert_fetch ctxt [] (Const (@{const_name htd_safe}, _) $ _ $ _) = convert_fetch ctxt [] @{term True}
  | convert_fetch ctxt [] (Const (@{const_name uminus}, T) $ v)
        = let val T = domain_type T
          in convert_fetch ctxt [] (Const (@{const_name minus}, T --> T --> T)
                $ Const (@{const_name zero_class.zero}, T) $ v) end
  | convert_fetch ctxt [] (Const (@{const_name h_t_valid}, _) $ htd
            $ Const (@{const_name c_guard}, _) $ p)
        = convert_op ctxt "PValid" "Bool" [htd, ptr_to_typ p, p]
  | convert_fetch ctxt [] (Const (@{const_name ptr_inverse_safe}, _) $ p $ htd)
        = convert_op ctxt "PGlobalValid" "Bool" [htd, ptr_to_typ p, p]
  | convert_fetch ctxt [] (Const (@{const_name ptr_safe}, _) $ p $ htd)
        = convert_op ctxt "PWeakValid" "Bool" [htd, ptr_to_typ p, p]
  | convert_fetch ctxt [] (Const (@{const_name globals_list_distinct}, _) $
        (Const (@{const_name image}, _) $ Const (@{const_name fst}, _)
            $ (Const (@{const_name s_footprint}, _) $ _)) $ _ $ _)
        = convert_fetch ctxt [] @{term True}
  | convert_fetch ctxt [] (Const (@{const_name c_guard}, _) $ p)
        = convert_op ctxt "PAlignValid" "Bool" [ptr_to_typ p, p]
  | convert_fetch ctxt [] (Const (@{const_name hrs_htd}, _)
            $ (Const (@{const_name t_hrs_'}, _) $ _))
        = "Var HTD HTD"
  | convert_fetch ctxt [] (Const (@{const_name hrs_mem}, _)
            $ (Const (@{const_name t_hrs_'}, _) $ _))
        = "Var Mem Mem"
  | convert_fetch ctxt [] (Const (@{const_name bot}, _) $ _) = convert_fetch ctxt [] @{term False}
  | convert_fetch ctxt [] (Const (@{const_name top_class.top}, _) $ _) = convert_fetch ctxt [] @{term True}
  | convert_fetch ctxt [] (Const (@{const_name insert}, _) $ v $ S $ x)
        = convert_op ctxt "Or" "Bool" [HOLogic.mk_eq (v, x), betapply (S, x)]
  | convert_fetch ctxt [] (Free ("symbol_table", _) $ s)
        = "Symbol " ^ HOLogic.dest_string s ^ " Word 32"
  | convert_fetch ctxt [] (Const (@{const_name of_nat}, T) $ (Const (@{const_name unat}, _) $ x))
        = let
            val t1 = fastype_of x
            val t2 = range_type T
          in if t1 = t2 then convert_fetch ctxt [] x
            else convert_fetch ctxt [] (Const (@{const_name ucast}, t1 --> t2) $ x)
          end
  | convert_fetch ctxt [] (t as (Const (@{const_name of_nat}, _) $
            (Const (@{const_name count_leading_zeroes}, _) $ x)))
        = convert_op ctxt "CountLeadingZeroes" (convert_type false (fastype_of t)) [x]
  | convert_fetch ctxt [] (t as (Const (@{const_name unat}, _) $ _))
        = convert_fetch ctxt [] (@{term "of_nat :: nat \<Rightarrow> word32"} $ t)
  | convert_fetch ctxt [] (t as (Const (@{const_name of_nat}, _) $ _))
        = convert_fetch ctxt [] (ptr_simp_term ctxt "of_nat" t t)
  | convert_fetch ctxt [] (t as (Const (@{const_name power}, _) $ _ $ x))
        = convert_fetch ctxt [] (ptr_simp_term ctxt "power" t t)
  | convert_fetch ctxt [] (Const (@{const_name ptr_coerce}, _) $ p) = convert_fetch ctxt [] p
  | convert_fetch ctxt [] (Const (@{const_name fst}, _) $ tp)
    = convert_fetch ctxt [] (fst (HOLogic.dest_prod tp))
  | convert_fetch ctxt [] (Const (@{const_name snd}, _) $ tp)
    = convert_fetch ctxt [] (snd (HOLogic.dest_prod tp))
  | convert_fetch ctxt [] (t as (Const (@{const_name word_of_int}, _) $ _))
    = let
        val t' = Pattern.rewrite_term @{theory} (map (concl_of #> HOLogic.dest_Trueprop
            #> HOLogic.dest_eq) @{thms word_uint.Rep_inverse word_sint.Rep_inverse}) [] t
      in if t' aconv t then convert_fetch ctxt [] (ptr_simp_term ctxt "word_of_int" t t)
        else convert_fetch ctxt [] t' end
  | convert_fetch ctxt [] (t as (Const (@{const_name sdiv}, _) $ _ $ _))
    = convert_fetch ctxt [] (ptr_simp_term ctxt "sdiv" t t)
  | convert_fetch ctxt [] (t as (Const (@{const_name numeral}, _) $ _))
    = let
    val n = HOLogic.dest_number t |> snd
        handle TERM _ => raise TERM ("convert_fetch", [t])
    val _ = (fastype_of t <> @{typ int}) orelse raise TERM ("convert_fetch: int", [t])
  in "Num " ^ signed_string_of_int n ^ " " ^ convert_type false (fastype_of t) end
  | convert_fetch ctxt [] (Const (@{const_name TYPE}, Type (_, [T])))
    = "Type " ^ convert_type true T
  | convert_fetch ctxt accs t = let
    val (f, xs) = strip_comb t
    val (c, _) = dest_Const f
    val T = convert_type false (get_acc_type accs (fastype_of t))
  in case (locals c, (get_field c <> NONE) orelse (cons_fields c <> NONE), ops c) of
    (true, _, _) => let
        fun canon s [] = "Var " ^ s ^ " " ^ T
          | canon s (Const (@{const_name Arrays.index}, idxT) $ i :: accs) = (case
                (try dest_nat i)
            of SOME i => canon (s ^ "." ^ string_of_int i) accs
              | NONE => let val (_, n) = dest_arrayT (domain_type idxT)
              in mk_acc_array (convert_fetch ctxt [] i) T
                (map (fn j => canon (s ^ "." ^ string_of_int j) accs)
                  (0 upto (n - 1))) end)
          | canon s (Const (acc_nm, _) :: accs)
            = canon (s ^ "." ^ Long_Name.base_name acc_nm) accs
          | canon _ (t :: _) = raise TERM ("convert_fetch: canon: ", [t])
      in if xs = [s_st] then canon c accs
        else if xs = [@{term t}] then canon ("rv#space#" ^ c) accs
        else raise TERM ("convert_fetch: state", [t] @ xs) end
  | (false, true, _) => (case xs of
        [x] => convert_fetch ctxt (f :: accs) x
        | [_, _] => let
            val _ = (accs <> []) orelse raise TERM ("convert_fetch: no accs", [t])
            val t' = hd accs $ t
            val t'' = cons_field_upds t'
          in if t'' aconv t' then raise TERM ("convert_fetch: irreducible upd:", [t'])
            else convert_fetch ctxt (tl accs) t'' end
        | _ => raise TERM ("convert_fetch", [t]))
  | (false, false, SOME (nm, _)) => if accs = []
        then convert_op ctxt nm (convert_type false (fastype_of t)) xs
        else raise TERM ("convert_fetch:", t :: accs)
  | (false, false, NONE) => (case (dest_mem_acc_addr t, enums c) of
    (SOME p, _) => convert_mem_acc ctxt accs p "Var Mem Mem"
  | (NONE, SOME n) => "Num " ^ signed_string_of_int n ^ " " ^ convert_type false (fastype_of t)
  | (NONE, NONE) => "Num " ^ signed_string_of_int (snd (HOLogic.dest_number t))
        ^ " " ^ convert_type false (fastype_of t)
    handle TERM _ => raise TERM ("convert_fetch", [t]))
  end

*}

ML {*
fun htd_simp ctxt = ctxt addsimps @{thms fold_all_htd_updates
        unat_lt2p[where 'a=32, simplified]}
  |> Simplifier.add_cong @{thm if_cong} |> Simplifier.rewrite

fun simp_htd ctxt t = let
    val rew_thm = cterm_of (Proof_Context.theory_of ctxt) t |> htd_simp ctxt
  in term_of (Thm.rhs_of rew_thm) end
*}

ML {*
fun convert_mem_upd ctxt p v hp = let
    val upds = narrow_mem_upd ctxt p v
  in fold_rev (fn (p, v) => fn hp => "Op MemUpdate Mem "
    ^ space_pad_list [hp, convert_fetch ctxt [] p, convert_fetch ctxt [] v]) upds hp
  end

fun get_local_var_upds ctxt nm T v accs =
  if structs_by_typ (fst (dest_Type T)) <> NONE
  then let
    val (_, _, _, _, flds) = the (structs_by_typ (fst (dest_Type T)))
  in maps (fn (fld_nm, (acc, _)) => get_local_var_upds ctxt (nm ^ "." ^ fld_nm)
    (range_type (fastype_of acc)) v (accs @ [acc])) flds end
  else if fst (dest_Type T) = @{type_name array}
  then let
    val (elT, n) = dest_arrayT T
  in maps (fn i => get_local_var_upds ctxt (nm ^ "." ^ string_of_int i)
    elT v (accs @ [Const (@{const_name Arrays.index}, T --> @{typ nat} --> elT)
        $ HOLogic.mk_number @{typ nat} i])) (0 upto (n - 1))
  end
  else [(nm ^ " " ^ convert_type false T, convert_fetch ctxt accs v)]

fun convert_upd ctxt (t as (Const (@{const_name globals_update}, _)
    $ (Const (@{const_name t_hrs_'_update}, _) $ f) $ _)) = (case f of
        Const (@{const_name hrs_mem_update}, _)
            $ (Const (@{const_name heap_update}, _) $ p $ v)
        => ["Mem Mem " ^ convert_mem_upd ctxt p v "Var Mem Mem"]
        | Const (@{const_name hrs_htd_update}, _) $ g
        => ["HTD HTD " ^ convert_fetch ctxt [] (simp_htd ctxt (betapply (g,
                @{term "hrs_htd (t_hrs_' (globals (s :: globals myvars)))"})))]
        | _ => raise TERM ("convert_upd", [t]))
  | convert_upd ctxt (Const (@{const_name globals_update}, _)
    $ (Const (@{const_name ghost'state_'_update}, _) $ _) $ _)
        = ["PMS PMS Var PMS PMS"] (* ghost update: ignore it *)
  | convert_upd ctxt (t as (Const (@{const_name globals_update}, _)
    $ (Const (c, cT) $ f) $ s)) = let
    val nm = case rw_global_upd_table c of SOME nm => nm
      | NONE => raise TERM ("convert_upd", [t])
    val acc = the (Symtab.lookup rw_globals_tab nm) |> fst
    val v = betapply (f, acc $ s)
    val ptr = TermsTypes.mk_global_addr_ptr (nm, fastype_of v)
  in ["Mem Mem " ^ convert_mem_upd ctxt ptr v "Var Mem Mem"] end
  | convert_upd ctxt (t as (Const (c, cT) $ f $ s)) = let
    val v = betapply (f, Const (c, cT) $ s)
    val T = fastype_of v
  in case (local_upds c) of
    true => get_local_var_upds ctxt (unsuffix Record.updateN c) T v []
        |> map (fn (a, b) => a ^ " " ^ b)
    | false => raise TERM ("convert_upd", [t])
  end
  | convert_upd ctxt t = raise TERM ("convert_upd", [t])

fun convert_param_upds ctxt (t as (Const (c, cT) $ f $ s)) = (case local_upds c
  of true => convert_param_upds ctxt s @ let
    val c' = unsuffix Record.updateN c
    val v = betapply (f, Const (c', cT) $ s)
    val T = fastype_of v
  in get_local_var_upds ctxt c' T v [] |> map snd end
  | false => raise TERM ("convert_param_upds", [t]))
  | convert_param_upds _ t = (if t = s_st then []
    else raise TERM ("convert_param_upds", [t]))

*}

lemmas sdiv_word32_max_ineq = sdiv_word32_max[folded zle_diff1_eq, simplified]
term h_val
context kernel_all_substitute begin

ML {*

val proc_info = Hoare.get_data @{context} |> #proc_info

val outfile = ref (NONE: TextIO.outstream option)

fun emit s = case ! outfile of
    SOME stream => TextIO.output (stream, s ^ "\n")
  | NONE => tracing s

val all_c_params = ["Mem Mem", "HTD HTD", "PMS PMS"]
val all_c_in_params = map (prefix "Var ") all_c_params

fun mk_safe f ctxt s = (
    Proof_Context.get_thm ctxt (s ^ "_body_def");
    Proof_Context.get_thm ctxt (s ^ "_impl");
  f ctxt s) handle ERROR _ => false

fun mk_set_int s t = let
    val T = fastype_of s
  in Const (@{const_name Lattices.inf}, T --> T --> T) $ s $ t end

fun has_reads body = exists_Const (fn (s, _) => s = @{const_name "t_hrs_'"}
        orelse s = @{const_name Spec}) body

fun has_reads_globals body = exists_Const (fst #> member (op =)
  ([@{const_name "t_hrs_'"}, @{const_name Spec}]
    @ map (snd #> head_of #> dest_Const #> fst) const_globals
    @ map (#2 #> head_of #> dest_Const #> fst) rw_globals)) body

fun get_reads_calls ctxt globals name = let
    val thm = Proof_Context.get_thm ctxt (name ^ "_body_def")
        |> simplify (put_simpset HOL_basic_ss ctxt addsimps @{thms call_def block_def})
    fun calls (Const (@{const_name com.Call}, _) $ proc) = [proc]
      | calls (f $ x) = calls f @ calls x
      | calls (Abs (_, _, t)) = calls t
      | calls _ = []
    val reads = (if globals then has_reads_globals else has_reads)
        (concl_of thm)
    val call_to_name = dest_Const #> fst #> Long_Name.base_name
        #> unsuffix "_'proc"
  in (reads, calls (concl_of thm) |> map call_to_name) end

fun is_no_read ctxt globals s = let
    fun inner stack s = if member (op =) stack s then true else let
        val (reads, calls) = get_reads_calls ctxt globals s
      in not reads andalso forall I (map (inner (s :: stack)) calls) end
  in inner [] s end

fun is_no_write ctxt s = let
    val thm = Proof_Context.get_thm ctxt (s ^ "_modifies")
  in not (exists_Const (fn (s, _) => s = @{const_name t_hrs_'_update}
        orelse s = @{const_name phantom_machine_state_'_update}
        orelse rw_global_upd_table s <> NONE)
    (concl_of thm)) end
    handle ERROR _ => false

fun is_no_read_globals ctxt = is_no_read ctxt true

fun emit_body ctxt (Const (@{const_name Seq}, _) $ a $ b) n c e = let
    val (n, nm) = emit_body ctxt b n c e
        handle TERM (s, ts) => raise TERM (s, b :: ts)
    val (n, nm) = emit_body ctxt a n nm e
        handle TERM (s, ts) => raise TERM (s, a :: ts)
  in (n, nm) end
  | emit_body ctxt (Const (@{const_name Catch}, _) $ a $ b) n c e = (case b of
    Const (@{const_name com.Skip}, _) => emit_body ctxt a n c (c, c)
  | Const (@{const_name ccatchbrk}, _) $ _ => emit_body ctxt a n c (fst e, c)
  | t => raise TERM ("emit_body ctxt (Catch)", [t])
  )
  | emit_body ctxt (Const (@{const_name creturn}, _) $ _ $ upd $ f) n _ (r, b) =
    emit_body ctxt (@{term com.Basic} $ Abs ("s", dummyT, betapplys (upd,
        [Abs ("_", dummyT, betapply (f, Bound 1)), Bound 0]))) n r (r, b)
  | emit_body ctxt (Const (@{const_name creturn_void}, _) $ _) n _ (r, _) = (n, r)
  | emit_body ctxt (Const (@{const_name cbreak}, _) $ _) n _ (_, b) = (n, b)
  | emit_body ctxt (Const (@{const_name com.Skip}, _)) n c _ = (n, c)
  | emit_body ctxt (Const (@{const_name com.Cond}, _) $ S $ a $ b) n c e = let
    val (n, nm_a) = emit_body ctxt a n c e
    val (n, nm_b) = emit_body ctxt b n c e
    val s = convert_fetch ctxt [] (betapply (S, s_st))
  in
    emit (string_of_int n ^ " Cond " ^ nm_a ^ " " ^ nm_b ^ " " ^ s);
    (n + 1, string_of_int n)
  end
  | emit_body ctxt (Const (@{const_name Guard}, T) $ F $ G $
            (Const (@{const_name Guard}, _) $ _ $ G' $ a)) n c e
        = emit_body ctxt (Const (@{const_name Guard}, T) $ F
            $ (mk_set_int G G') $ a) n c e
  | emit_body ctxt (Const (@{const_name Guard}, _) $ _ $ G $ a) n c e = let
    val (n, nm) = emit_body ctxt a n c e
    val G = Pattern.rewrite_term @{theory}
      (@{thms WordLemmaBucket.signed_arith_ineq_checks_to_eq_word32
              signed_arith_eq_checks_to_ord
              signed_mult_eq_checks32_to_64
              sdiv_word32_min[THEN eqTrueI] sdiv_word32_max_ineq
              signed_shift_guard_to_word_32}
        |> map (concl_of #> HOLogic.dest_Trueprop #> HOLogic.dest_eq)) [] G
    val s = convert_fetch ctxt [] (betapply (G, s_st))
  in
    emit (string_of_int n ^ " Cond " ^ nm ^ " Err " ^ s);
    (n + 1, string_of_int n)
  end
  | emit_body ctxt (Const (@{const_name com.Basic}, _) $ Abs (_, _, Bound 0)) n c e
    = (n, c)
  | emit_body ctxt (Const (@{const_name com.Basic}, _) $ f) n c _ = let
    val upds = convert_upd ctxt (betapply (f, s_st))
  in
    emit (string_of_int n ^ " Basic " ^ c ^ " " ^ space_pad_list upds);
    (n + 1, string_of_int n)
  end
  | emit_body ctxt (Const (@{const_name call}, _) $ f $ Const (p, _)
        $ r1 $ r2) n c e = let
    val ret_val = Symtab.lookup proc_info (Long_Name.base_name p)
        |> the |> #params
        |> filter (fn (v, _) => v = HoarePackage.Out)
        |> maps (snd #> Proof_Context.read_const_proper ctxt true
         #> dest_Const
         #> (fn (s, T) => get_local_var_upds ctxt ("rv#space#" ^ s) (range_type T)
             (Const (s, T) $ s_st) []))
        |> map fst

    val p_short = unsuffix "_'proc" (Long_Name.base_name p)
    val no_read = mk_safe is_no_read_globals @{context} p_short
    val no_write = mk_safe is_no_write @{context} p_short
    (* writes implicitly require reads, really *)
    val no_read = no_read andalso no_write

    val args = (convert_param_upds ctxt (betapply (f, s_st))
        @ (if no_read then [] else all_c_in_params))
      handle TERM (s, ts) => raise TERM ("emit_body call: " ^ s, f :: ts)

    val out = ret_val @ (if no_write then [] else all_c_params)

    val (n, nm_save) = emit_body ctxt (betapplys (r2, [@{term i}, @{term t}])) n c e

  in emit (string_of_int n ^ " Call " ^ nm_save ^ " " ^ (unsuffix "_'proc" p)
    ^ " " ^ space_pad_list args ^ " " ^ space_pad_list out);
    (n + 1, string_of_int n)
  end
  | emit_body ctxt (Const (@{const_name lvar_nondet_init}, _) $ _ $ _) n c _
    = (n, c)
  | emit_body ctxt (Const (@{const_name whileAnno}, _) $ C $ _ $ _ $ a) n c e = let
    fun sn i = string_of_int (n + i)
    val lc = "loop#count" ^ sn 0 ^ " Word 32"
    val (n', nm) = emit_body ctxt a (n + 3) (sn 0) e
    val cond = convert_fetch ctxt [] (betapply (C, s_st))
  in emit (sn 0 ^ " Basic " ^ sn 1 ^ " 1 " ^ lc
      ^ " Op Plus Word 32 2 Var " ^ lc ^ " Num 1 Word 32");
    emit (sn 1 ^ " Cond " ^ nm ^ " " ^ c ^ " " ^ cond);
    emit (sn 2 ^ " Basic " ^ sn 1 ^ " 1 " ^ lc ^ " Num 0 Word 32");
    (n', sn 2)
  end
  | emit_body ctxt ((sw as Const (@{const_name switch}, _)) $ f
        $ ((Const (@{const_name Cons}, _))
            $ (Const (@{const_name Pair}, _) $ C $ a) $ xs)) n c e = let
    val (n, nm_xs) = emit_body ctxt (sw $ f $ xs) n c e
    val (n, nm_a) = emit_body ctxt a n c e
    val s = convert_fetch ctxt [] (betapply (C, betapply (f, s_st)))
  in emit (string_of_int n ^ " Cond " ^ nm_a ^ " " ^ nm_xs ^ " " ^ s);
    (n + 1, string_of_int n) end
  | emit_body ctxt (Const (@{const_name switch}, _)
        $ _ $ Const (@{const_name Nil}, _)) n c _
    = (n, c)
  | emit_body _ t _ _ _ = raise TERM ("emit_body", [t])

fun emit_func_body ctxt name = let
    val params = Symtab.lookup proc_info (name ^ "_'proc")
         |> the |> #params
         |> map (apsnd (fn c => Proof_Context.read_const_proper ctxt true c
                |> dest_Const
                |> (fn (s, T) => get_local_var_upds ctxt s (range_type T)
                     (Const (s, T) $ s_st) [])
                |> map fst))

    val no_read = mk_safe is_no_read_globals ctxt name
    val no_write = mk_safe is_no_write ctxt name
    (* writes implicitly require reads, really *)
    val no_read = no_read andalso no_write

    val inputs = (filter (fn p => fst p = HoarePackage.In) params
      |> maps snd) @ (if no_read then [] else all_c_params)

    val outputs = (filter (fn p => fst p = HoarePackage.Out) params
      |> maps snd) @ (if no_write then [] else all_c_params)

    val body = Proof_Context.get_thm ctxt (name ^ "_body_def")
            |> concl_of |> Logic.dest_equals |> snd
        handle ERROR _ => @{term "Spec S"}

    val full_nm = Proof_Context.read_const_proper ctxt true (name ^ "_'proc")
        |> dest_Const |> fst |> unsuffix "_'proc"
  in emit ("Function " ^ full_nm ^ " " ^ space_pad_list inputs
                ^ " " ^ space_pad_list outputs);
    case body of Const (@{const_name Spec}, _) $ _
        => ()
    | _ => (emit ("1 Basic Ret 0");
          emit_body ctxt body 2 "1" ("ErrExc", "ErrExc")
            |> snd |> prefix "EntryPoint " |> emit
          handle TERM (s, ts) => raise TERM ("emit_func_body: " ^ name ^ ": " ^ s, body :: @{term True} :: ts)
            | TYPE (s, Ts, ts) => raise TYPE ("emit_func_body: " ^ name ^ ": " ^ s, Ts, body :: @{term True} :: ts)
            | Empty => raise TERM ("emit_func_body: Empty", [body]))
  end

fun emit_struct ctxt (nm, flds) = let
    val offs = map (ProgramAnalysis.offset (csenv ()) (map snd flds))
        (0 upto (length flds - 1))
    val full_nm = Proof_Context.read_const_proper ctxt true (nm ^ "." ^ nm)
        |> dest_Const |> snd |> strip_type |> snd |> dest_Type |> fst
    val thy = Proof_Context.theory_of ctxt
    val sz = ProgramAnalysis.sizeof (csenv ()) (Absyn.StructTy nm)
    val algn = ProgramAnalysis.alignof (csenv ()) (Absyn.StructTy nm)
    fun emit_fld ((fld_nm, fld_ty), offs) = emit (space_pad
        ["StructField", fld_nm, convert_type false
            (CalculateState.ctype_to_typ (thy, fld_ty)), string_of_int offs])
  in emit (space_pad ["Struct", full_nm, string_of_int sz,
    string_of_int algn]); app emit_fld (flds ~~ offs) end

fun emit_C_everything ctxt = let
    val fs = ProgramAnalysis.get_functions (csenv ())
    val structs = ProgramAnalysis.get_senv (csenv ())
  in app (emit_struct ctxt) structs;
     app (emit_func_body ctxt) fs end
*}

declare [[show_types = true, show_consts = true]]

ML {*
fun openOut_relative thy = ParseGraph.filename_relative thy #> TextIO.openOut;
*}

ML {* outfile := SOME (openOut_relative @{theory} "CFunDump.txt");
  emit_C_everything @{context};
  TextIO.closeOut (the (! outfile))
*}

end

end


