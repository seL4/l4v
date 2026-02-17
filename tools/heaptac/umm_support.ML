(* Optimisation ideas:
   - Faster string matching (or don't use HOL strings for names)
*)

structure Umm_Support =
struct

(* Tracing *)

val trace_umm_strg = Attrib.setup_config_bool @{binding trace_umm_strg} (K false);

val trace_depth = Unsynchronized.ref 0


fun trace ctxt strf = if Config.get ctxt trace_umm_strg then tracing (strf ()) else ()
fun trace_ct ctxt str ct = trace ctxt (fn () => str ^ Syntax.string_of_term ctxt (Thm.term_of ct))
fun trace_thm ctxt str thm = trace ctxt (fn () => str ^ Thm.string_of_thm ctxt thm)


fun trace_tac ctxt strf st = (trace ctxt strf; all_tac st);
fun trace_tac' ctxt strf _ st = (trace ctxt strf; all_tac st);

(* fun trace_ct_tac ctxt str ct st = (trace_ct ctxt str ct; all_tac st); *)
(* fun trace_ct_tac' ctxt str ct _ st = trace_ct_tac ctxt str ct st *)

fun tracing_enter ctxt str =
  if Config.get ctxt trace_umm_strg
  then let
    val depth  = Unsynchronized.change_result trace_depth (fn x => (x, x + 1))
    val pfx    = (replicate_string depth " ") ^ "[>" ^ string_of_int depth ^ "] "
  in (tracing (pfx ^ str); depth) end
  else 0

fun tracing_leave ctxt depth str =
  if Config.get ctxt trace_umm_strg
  then let
    val depth' = Unsynchronized.change_result trace_depth (fn x => (x - 1, x - 1))
    val pfx    = (replicate_string depth " ") ^ "[<" ^ string_of_int depth ^ "] "
  in if depth <> depth'
     then (tracing (pfx ^  "Depth mismatch in tracing_leave (" ^ str ^ "): expected " ^ string_of_int depth ^ ", saw " ^ string_of_int depth'); depth)
     else (tracing (pfx ^ str); depth)
  end
  else depth

fun tracing_wrap ctxt str f = let
  val depth = tracing_enter ctxt str
  val r      = f ()
in tracing_leave ctxt depth str; r
end

fun traced_tac ctxt str tac st = let
  val depth          = tracing_enter ctxt str
  fun finish str' st = (tracing_leave ctxt depth (str ^ " " ^ str'); all_tac st)
in (tac THEN_ELSE (finish "DONE", finish "FAIL" THEN no_tac)) st
end

fun traced_tac' ctxt str tac i st =
    traced_tac ctxt str (tac i) st

fun traced_ct_tac ctxt str ct tac st =
    traced_tac ctxt (str ^ Syntax.string_of_term ctxt (Thm.term_of ct)) tac st

fun traced_ct_tac' ctxt str ct tac i st = traced_ct_tac ctxt str ct (tac i) st

(* Timing *)

val zero_timing = let
  open Time;
  open Timing;
  val n = now ();
  val z = n - n;
in
  { elapsed = z, cpu = z, gc = z }
end;

fun clear_cost_center (_, r) = let
  open Unsynchronized;
in
  r := zero_timing
end;

fun mk_cost_center name = (name, Unsynchronized.ref zero_timing)
fun pretty_cost_center (name, time) = name ^ ": " ^ Timing.message (Unsynchronized.! time)

fun use_cost_center cc f x = let
  open Time;
  open Timing;
  val ({ elapsed, cpu, gc }, v) = Timing.timing f x
  fun upd_timing { elapsed = elapsed', cpu = cpu', gc = gc' } = { elapsed = elapsed + elapsed', cpu = cpu + cpu', gc = gc + gc' }
  val _ = Unsynchronized.change (snd cc) upd_timing
in
  v
end;

(* Stuff that ML should have but doesn't because it is bad *)
fun minBy ord (x, y) =
    if ord (x, y) = GREATER then y else x

fun maxBy ord (x, y) =
    if ord (x, y) = LESS then y else x

val app_Trueprop = Thm.apply @{cterm Trueprop}
fun dest_Trueprop ct =
    case Thm.term_of ct of
        Const (@{const_name Trueprop}, _) $ _ => Thm.dest_arg ct
      | _ => raise CTERM ("dest_Trueprop", [ct])

(* Theory data, mainly to allow stuff to be defined in a locale and used later *)

structure Typreltab = Table(type key = typ * typ val ord = prod_ord Term_Ord.typ_ord Term_Ord.typ_ord)

(*
val typrel_memo_cache : (((typ * typ -> 'a) -> typ * typ -> 'a) -> typ * typ -> 'a)
    = MemoCache.create Typreltab.empty Typreltab.lookup Typreltab.update;
*)

(* The (int * thm) Net.net is because of resolve_from_nets_tac *)
type thm_info = { fg_fl_net     : (int * thm) Net.net,
                  (* Basically typ -> typ -> string option s.t.

                          typ_map parent child = Some field_name

                          Non transitive.
                   *)
                  (* FIXME: may be slow to compute, do it lazily? *)
                  (* struct_map : (string * typ) list Typtab.table, *)
                  tag_disj_cache : typ * typ -> thm,
                  (* Sometimes it is enough to know the rel
                       without the thm.  Arguably more efficient than
                       a bfs? *)
                  sub_typ_cache : typ * typ -> thm lazy option
                };

structure UMM_Thm_Info = Theory_Data (
  type T = thm_info Symtab.table
  val empty = Symtab.empty;
  val extend = I;
  fun merge data = Symtab.merge (K true) data;
)

fun umm_thm_info_for ctxt = let
  val get_tinfo =
      Symtab.lookup (UMM_Thm_Info.get (Proof_Context.theory_of ctxt))
in
  case Option.mapPartial get_tinfo (Named_Target.locale_of ctxt) of
      NONE       => raise (Fail "Not in a C locale")
    | SOME tinfo => tinfo
end

(* Destructuring rules *)
structure Congs = Generic_Data
(struct
    type T = thm list
    val empty = []
    val extend = I
    val merge = Thm.merge_thms;
end);

val cong_add = Thm.declaration_attribute (Congs.map o Thm.add_thm);
val cong_del = Thm.declaration_attribute (Congs.map o Thm.del_thm);

val _ =
    Theory.setup (
      Attrib.setup @{binding "umm_cong"} (Attrib.add_del cong_add cong_del)
                                     "UMM Strengthen congruence rules"
     );

(* cleanup rules *)
structure Cleanup = Generic_Data
(struct
    type T = thm list
    val empty = []
    val extend = I
    val merge = Thm.merge_thms;
end);

val cleanup_add = Thm.declaration_attribute (Cleanup.map o Thm.add_thm);
val cleanup_del = Thm.declaration_attribute (Cleanup.map o Thm.del_thm);

val _ =
    Theory.setup (
      Attrib.setup @{binding "umm_cleanup"} (Attrib.add_del cleanup_add cleanup_del)
                                     "UMM Strengthen cleanup rules"
     );


(* Helper conversions *)

fun repeat_conv_n 0 _ = Conv.all_conv
  | repeat_conv_n n c = c then_conv (repeat_conv_n (n - 1) c)

fun eq_rewr_conv thm = Conv.rewr_conv (thm RS @{thm eq_reflection})
fun eq_rewrs_conv thms = Conv.rewrs_conv (map (fn thm => thm RS @{thm eq_reflection}) thms)

fun cond_rewr_conv tac ctxt thm ct =
  (* c.f. congc in raw_simplifier.ML *)
  (* FIXME: In a bunch of places they do adjust_maxidx_cterm ~1, not sure why? *)
  let val rthm   = Thm.incr_indexes (Thm.maxidx_of_cterm ct + 1) thm;
      val rlhs   = fst (Thm.dest_equals (Drule.strip_imp_concl (Thm.cprop_of rthm)));
      val insts  =
          Thm.match (rlhs, ct) handle Pattern.MATCH => raise CTERM("cond_rewr_conv", [rlhs, ct]);
      val inst_thm =
        Thm.instantiate insts (Thm.rename_boundvars (Thm.term_of rlhs) (Thm.term_of ct) rthm);
      val thm_no_prems =
        if Thm.nprems_of inst_thm = 0
        then inst_thm
        else case SINGLE (tac ctxt) inst_thm of
                 NONE => raise THM ("conditional_conv: tactic failed" , 0, [inst_thm])
               | SOME thm' => thm'
  in
    Conv.rewr_conv thm_no_prems ct
  end;

fun cond_eq_rewr_conv tac ctxt thm = cond_rewr_conv tac ctxt (thm RS @{thm "eq_reflection"})

fun eq_net_rewr_conv net ct = let
  val typ = Thm.typ_of_cterm ct
  val tm =
      @{term Trueprop}
         $ (Const (@{const_name "HOL.eq"}, typ --> typ --> @{typ bool})
                  $ Thm.term_of ct $ Var (("x", Thm.maxidx_of_cterm ct + 1), typ))
  val thms = map snd (Net.unify_term net tm)
in
  eq_rewrs_conv thms ct
end;

(* Tactics *)

fun assume_as_hyp_tac ctxt i thm = resolve_tac ctxt [ Thm.assume (Thm.cprem_of thm i) ] i thm

fun h_t_valid_simp_then_assume_tac tinfo ctxt i =
    (resolve_tac ctxt @{thms "match_h_t_valid"} THEN'
     FIRST' [ resolve_tac ctxt @{thms "heaptac_h_t_valid_intros"} THEN_ALL_NEW umm_subgoal_tac tinfo ctxt
            , assume_as_hyp_tac ctxt
            ]) i

and umm_subgoal_tac tinfo ctxt i =
    FIRST' [ h_t_valid_simp_then_assume_tac tinfo ctxt
           , resolve_from_net_tac ctxt (#fg_fl_net tinfo)
           ] i

(* rewrite map_option export_uinfo (field_ti TYPE('a) [f]) \<equiv> Some (export_uinfo (typ_info_t TYPE('b)))
   FIXME: probably overkill, use simp instead? *)
fun map_option_export_uinfo_field_ti_conv fg_fl_net ctxt =
    Conv.every_conv [ Conv.arg_conv (eq_net_rewr_conv fg_fl_net)
                    , eq_rewrs_conv @{thms "option.map"}
                    , Conv.arg_conv (cond_eq_rewr_conv (fn ctxt => resolve_from_net_tac ctxt fg_fl_net 1) ctxt
                                     @{thm "heaptac_export_tag_adjust_ti"})
                    ]
(*
fun sub_typ_tac tinfo []        ctxt i = resolve_tac ctxt @{thms "sub_typ_refl"} i
  | sub_typ_tac tinfo ((f, typ) :: fs) ctxt i =
    EVERY' [ resolve_tac ctxt [Thm.instantiate' [NONE, SOME (Thm.ctyp_of ctxt typ)] [] @{thm sub_typ_trans}]
           , resolve_tac ctxt [Thm.instantiate' [] [SOME (Thm.cterm_of ctxt (HOLogic.mk_string f))] @{thm field_ti_into_sub_typ_one}]
           , CONVERSION (HOLogic.Trueprop_conv (Conv.arg1_conv (map_option_export_uinfo_field_ti_conv tinfo ctxt)))
           , resolve_tac ctxt @{thms "refl"}
           , sub_typ_tac fs ctxt
           ] i
*)

(* Turns CLIFT('a) (hrs_mem_update (heap_update (PTR('b) &(p->[f])) v) hp) into something more reasonable *)
(* FIXME: focus on heap_update value to avoid so much matching in _eq2? *)
fun move_heap_field_upd_conv tinfo ctxt =
  let fun tac ctxt = ALLGOALS (umm_subgoal_tac tinfo ctxt)
  in  Conv.every_conv [ cond_eq_rewr_conv tac ctxt @{thm  "heaptac_lift_t_move_field_lookup"}
                      (* , Conv.repeat_conv (cond_eq_rewr_conv tac ctxt @{thm  "heaptac_lift_t_move_field_lookup2"}) *)
                      , eq_rewr_conv @{thm "heaptac_lift_t_move_field_lookup3"}
                      ]
  end;


(* Functions on type graphs *)


(* Turns
   - PTR(t2) &(PTR(t1) &((p :: t0) -> [f1]) -> [f2])
   into
   - [(p, t0), (PTR(t1) &((p :: t0) -> [f1]), t1) (PTR(t2) &(PTR(t1) &((p :: t0) -> [f1]) -> [f2]), t2)]
*)
val dest_pointer_path =
  let fun strip_ptr (Type (@{type_name "ptr"}, [t])) = t
        | strip_ptr t = raise TYPE("strip_ptr", [t], [])

      fun go acc (tm as @{term_pat "Ptr &(?p \<rightarrow> [_])"}) =
             go ((tm, strip_ptr (Term.type_of tm)) :: acc) p
        | go acc tm = (tm, strip_ptr (Term.type_of tm)) :: acc
  in go []
  end

(* This encodes the relationship between two C types. *)
datatype struct_path_type = Equal of int (* Thm is either update_at_type or update_at_word_same_size, intantiated *)
                          | SameWord of int
                          | Disjoint of thm list * int
                          | Super of thm list  * int
                          | Sub   of thm list
                          | Triangle of thm list * int

(* This function determines whether one type is a child of another.  If so,
   it returns a REVERSED list of field names, and the type they operate ont
   s.t. p\<rightarrow>f1\<rightarrow>f2\<rightarrow>...\<rightarrow>fn has the child type
   when p is the parent type.  Note that there may be multiple, we return the shortest.
*)
(* FIXME: fix comment e.g.

   Returns the path components, and the type relationship between lift_typ and the path.
   For example, if we are lifting at foo_C, and we have the pointer bar\<rightarrow>foov we should
   return

   Equal 0

   whereas if we have just the pointer bar, we will get

   Sub

   and if we are lifting at bar_C and we have bar\<rightarrow>foov then

   (Equal, (bar, [("foov_C", foo_C)]))

   The types here can either be C structs, arrays, or primitive types (incl. pointers to types, and enums).
   In the case that the lift_typ is not a struct, we can only really look at the type of the whole
   pointer term.

   In the case that no type in the path matches lift_typ, we can split the path into

   super-to-lift @ disj-to-lift @ sub-to-lift

   1. if disj-to-lift is non-empty, we return (Disjoint, and take the lowest element).
   2. Otherwise, if sub-to-lift is empty, we return (Sub, the last pointer)
   3. Otherwise, if super-to-lift is empty, we return (Super, the root pointer)
   4. Finally, we have the triangle case, so we return (Super, head of sub-to-lift)

   Note the last 2 cases can be merged by taking head of sub-to-lift

   Typically path is very short here (0, 1, maybe 2) so we don't have to worry too much about
   performance of operations which scan it.  We don't want to do type_is_child as that may be
   expensive, so disj should be done last.

   Note that in the case that p isn't a field_lvalue, this does the right thing.
*)

(* FIXME: triangle case:

  struct baz { int baz_x; };

  struct bar {
    struct baz bar_baz;
  };

  struct foo {
    struct baz foo_baz;
    struct bar foo_bar;
  };

  CLIFT(bar_C) (hrs_heap_update (heap_update (PTR(foo_C) &(p \<rightarrow> [''foo_baz_C''])) v) hp)

  should be

  CLIFT(bar_C) hp
*)

fun determine_type_relationship tinfo lift_typ ptr = let
  val path = dest_pointer_path ptr
  val path_len = length path
  fun type_is_child c p = #sub_typ_cache tinfo (c, p)
  val find_fld_path = get_index (fn (_, typ) => type_is_child typ lift_typ)

  fun dest_word_typ (Type (@{type_name "word"}, [ws]))
      = (case ws of
            Type (@{type_name "signed"}, [sz]) => SOME (true, sz)
          | _                                  => SOME (false, ws))
    | dest_word_typ _ = NONE

  fun typ_eq_modulo_sign t t' =
      if t = t' then SOME Equal
      else case (dest_word_typ t, dest_word_typ t') of
               (SOME (_, sz), SOME (_, sz')) => if sz = sz' then SOME SameWord else NONE
             | _ => NONE (* probably not equal *)

  (* We know that at least one element is not a child of the lift_typ *)
  fun non_child_case idx mk =
      let val (_, typ') = List.nth (path, idx - 1)
      in case type_is_child lift_typ typ' of
             NONE       => Disjoint ([#tag_disj_cache tinfo (lift_typ, typ')], path_len - idx)
           | SOME l_thm => mk l_thm
      end;

  fun mktriangle idx t_sub_lift_thm lift_sub_t_thm =
      Triangle ([Lazy.force t_sub_lift_thm, Lazy.force lift_sub_t_thm], path_len - (idx + 1))

in case get_index (typ_eq_modulo_sign lift_typ o snd) path of
       NONE => (case find_fld_path path of
                  NONE              => non_child_case path_len (Sub o single o Lazy.force)
                | SOME (0, l_thm)   => Super ([Lazy.force l_thm], path_len - 1)
                | SOME (idx, t_sub_lift_thm) => non_child_case idx (mktriangle idx t_sub_lift_thm))
     | SOME (idx, f) => f (path_len - (idx + 1))
end

(* The general idea here is to get to the pointer we want by removing fields, then doing
   the appropriate rule
*)

fun lift_t_heap_update_conv ctxt = let
  (* binds ts, p, and v *)
  val tinfo = umm_thm_info_for ctxt

  fun move_fields_conv n = repeat_conv_n n (move_heap_field_upd_conv tinfo ctxt)

  (* Sort of rare *)
  fun word_eq_tac ctxt =
      ALLGOALS (FIRST' [ h_t_valid_simp_then_assume_tac tinfo ctxt
                       , full_simp_tac (put_simpset HOL_ss ctxt addsimps @{thms len_of_signed_unsigned})
                       ])

  fun tac thm ctxt =
      ALLGOALS (FIRST' [ umm_subgoal_tac tinfo ctxt
                       , resolve_tac ctxt thm
                       ])

  fun mkconv rl (thm, n) =
      Conv.every_conv
        [ move_fields_conv n
        , cond_eq_rewr_conv (tac thm) ctxt rl
        ]

  fun conv p (Type (@{type_name "option"}, [lift_typ])) =
      case determine_type_relationship tinfo lift_typ p of
          Equal n => Conv.every_conv
                       [ move_fields_conv n
                       , cond_eq_rewr_conv (fn ctxt => h_t_valid_simp_then_assume_tac tinfo ctxt 1) ctxt
                         @{thm "heaptac_lift_t_heap_update_at_type"}
                       ]

        | SameWord n => Conv.every_conv
                          [ move_fields_conv n
                          , cond_eq_rewr_conv word_eq_tac ctxt
                            @{thm "heaptac_lift_t_heap_update_at_word_same_size"}
                          ]
        | Disjoint r => mkconv @{thm "heaptac_lift_t_heap_update_at_other"} r
        | Super    r => mkconv @{thm "heaptac_lift_t_heap_update_at_super"} r
        | Sub    thm => mkconv @{thm "heaptac_lift_t_heap_update_at_sub"} (thm, 0)
        | Triangle r => mkconv @{thm "heaptac_lift_t_heap_update_at_triangle"} r
in
  fn ct => case Thm.term_of ct of
               Const (@{const_name "lift_t"}, ts) $ _ $ @{term_pat "hrs_mem_update (heap_update ?p _) _"} => conv p (Term.body_type ts) ct
             | _ => Conv.no_conv ct
end

(*
val lift_t_simproc = Simplifier.make_simproc @{context} "lift_t_heap_update"
      {lhss = [@{term "lift_t c_guard (hrs_mem_update (heap_update p v) hp)"}],
       proc = K lift_t_simproc_fun,
       identifier = []}
*)

fun h_val_into_lift_t_conv ctxt = let
  val tinfo = umm_thm_info_for ctxt
in
  cond_eq_rewr_conv (fn ctxt => h_t_valid_simp_then_assume_tac tinfo ctxt 1) ctxt @{thm h_val_is_the_lift_t}
end

fun lift_t_field_access_conv ctxt = let
  val tinfo = umm_thm_info_for ctxt
  fun tac ctxt = ALLGOALS (umm_subgoal_tac tinfo ctxt)
in
  cond_eq_rewr_conv tac ctxt @{thm heaptac_lift_t_access_at_field}
end

(*
val h_val_into_lift_t_simproc = Simplifier.make_simproc @{context} "h_val_into_lift_t"
      {lhss = [@{term "h_val (hrs_mem hp) p"}],
       proc = K h_val_into_lift_t_simproc_fun,
       identifier = []}
*)


(******************************* strengthening *******************************)

val umm_strengthen_prover_cc = mk_cost_center "umm_strengthen_prover"
val strengthen_via_rewr_cc = mk_cost_center "strengthen_via_rewr"
val destructure_tac_cc = mk_cost_center "destructure_tac"
val post_destructure_tac_cc = mk_cost_center "post_destructure_tac"
val prove_and_flush_cc = mk_cost_center "prove_and_flush"
val hyps_to_prems_cc = mk_cost_center "hyps_to_prems"

val cost_centers = [ mk_cost_center "dummy"
                   , umm_strengthen_prover_cc
                   , strengthen_via_rewr_cc
                   , destructure_tac_cc
                   , post_destructure_tac_cc
                   , prove_and_flush_cc
                   , hyps_to_prems_cc
                   ]

(* Turns H |- A into |- /\H --> A *)
fun hyps_to_prems m_var top_thm = let
  val all_hyps = Thm.chyps_of top_thm
  val hyps =
      case m_var of
          NONE => all_hyps
        | SOME x => let
          val vs = HOLogic.strip_tuple x
          val occs = exists_subterm (fn tm => exists (fn x => x aconv tm) vs)
        in filter (fn ct => occs (Thm.term_of ct)) all_hyps end
  fun go []        thm = thm
   | go (h :: hs) thm =
     go hs ((Thm.implies_intr h thm) COMP @{thm conj_under_implies} )
in go hyps (top_thm RS @{thm x_implies_true_implies_x}) COMP @{thm impI}
end


(* fun strip_all_imp ct = let *)
(*   fun dest_all ct' = *)
(*       (case Thm.term_of ct' of *)
(*            Const ("Pure.all", _) $ Abs (a, _, _) => *)
(*            let val (x, ct') = Thm.dest_abs NONE (Thm.dest_arg ct) *)
(*            in SOME ((a, Thm.ctyp_of_cterm x), ct') end *)
(*          | _ => NONE); *)
(*   fun go acc ct' = *)
(*       case dest_all ct' of *)
(*           NONE           => Drule.strip_imp_concl ct' *)
(*         | SOME (v, ct'') => go (v :: acc) ct'' *)
(* in *)
(*   rev (go [] ct) *)
(* end *)

(*
  This expects something like flush_hyps P Q.  Anything else will probably result in odd behaviour
  *)


fun print_clear_cost_centers () =
    tracing (cat_lines
                (map (fn cc => let val msg = pretty_cost_center cc in (clear_cost_center cc; msg) end) cost_centers))

fun strengthen_via_rewr imp_prover_tac eq_prover_tac ctxt = let
  val congs = Congs.get (Context.Proof ctxt)
  fun destructure_tac ctxt i =
      use_cost_center destructure_tac_cc (
        traced_tac' ctxt "destructure_tac"
                    (FIRST' [ resolve_tac ctxt congs
                                          THEN_ALL_NEW
                                          post_destructure_tac ctxt
                            , resolve_tac ctxt @{thms match_eqI} THEN' (eq_prover_tac ctxt)
                            , imp_prover_tac ctxt (* Should at least return P --> P *)
                            ]) i)

  and post_destructure_tac ctxt i =
      use_cost_center post_destructure_tac_cc (
        traced_tac' ctxt "post_destructure_tac"
                    (FIRST' [ resolve_tac ctxt @{thms flush_hypsI}
                                                  THEN' (Subgoal.FOCUS_PREMS (focus_tac NONE) ctxt)
                            , resolve_tac ctxt @{thms match_flush_hyps_for}
                                                  THEN' (Subgoal.FOCUS_PREMS focus_for_tac ctxt)
                            , destructure_tac ctxt
                            ]) i)

  and focus_for_tac (arg as {context = ctxt, concl, ...}) = let
    val v = case HOLogic.dest_Trueprop (Thm.term_of concl) of
                 @{term_pat "flush_hyps_for ?x _ _"} => x
               | _ => raise CTERM ("flush_for_tac", [concl])
  in
    resolve_tac ctxt @{thms flush_hyps_forI} 1 THEN focus_tac (SOME v) arg
  end

  and focus_tac m_var {context = ctxt, concl, ...} = let
    val thm = prove_and_flush ctxt m_var (Thm.dest_arg (dest_Trueprop concl))
  in
    traced_tac ctxt "focus_tac"
               (* (fn st => (EVERY [ trace_tac ctxt "resolving" *)
               (*                  , resolve_tac ctxt [ prove_and_flush ctxt (Thm.dest_arg (dest_Trueprop concl)) ] 1 *)
               (*                  (* , trace_tac ctxt "resolved" *)] st)) *)
               (fn st => (trace_tac ctxt (fn () => "resolving: " ^ Thm.string_of_thm ctxt thm ^ " against " ^ @{make_string} concl) THEN
                                    resolve_tac ctxt [ thm ] 1
                                    THEN trace_tac ctxt (K "resolved"))
                           st)
  end


  (* The goal should be ?H --> P. *)
  (* FIXME: prove_internal ? *)
  and prove_and_flush ctxt m_var ct' = let
    fun doit () = let
      val _         = trace_ct ctxt "" ct'
      val goal      = app_Trueprop ct'
      val thm       = Goal.prove_internal ctxt [] goal (K (destructure_tac ctxt 1))
    in
      use_cost_center hyps_to_prems_cc (fn () => tracing_wrap ctxt "hyps_to_prems" (fn () => hyps_to_prems m_var thm)) ()
    end
  in use_cost_center prove_and_flush_cc (fn () => tracing_wrap ctxt "prove_and_flush" doit) ()
  end
in
  fn i => fn st => let val r = use_cost_center strengthen_via_rewr_cc (destructure_tac ctxt i) st in (print_clear_cost_centers () ; r) end
end

(******************************* Setup *******************************)

fun mk_tag_disj_cache lthy = let
  (* There is no addsimps on simpsets, only contexts *)
  (* This is gross: the cparser creates a structure called UMM_Proof_Theories which contains a symtab. *)
(*  val extra_typ_name_simp_rules = (Proof_Context.get_thms lthy "typ_name_simps") @ (Proof_Context.get_thms lthy "td_names_simps")
 *)
  fun get_umm_thms name =
      case Symtab.lookup (UMM_Proof_Theorems.get (Proof_Context.theory_of lthy)) name of
          SOME thm => thm
        | NONE => raise (Fail ("get_umm_thms: " ^ name))

  val extra_typ_name_simp_rules =
      get_umm_thms "typ_name_simps" @ get_umm_thms "td_names_simps" @ get_umm_thms "typ_name_itself"

  val lthy_with_ss = put_simpset HOL_ss lthy addsimps (@{thms "heaptac_tag_disj_simps"} @ @{thms "char.inject"} @ extra_typ_name_simp_rules) (* addsimprocs [@{simproc char_eq}] *)
  val tag_disj_com = @{thm tag_disj_com [THEN iffD1]}
  val tac =
      resolve_tac lthy_with_ss @{thms tag_disj_via_td_name [unfolded pad_typ_name_def]}  THEN_ALL_NEW simp_tac lthy_with_ss
  fun mk_typ_uinfo t =
      Thm.cterm_of lthy_with_ss (Const (@{const_name "typ_uinfo_t"}, Term.itselfT t --> @{typ typ_uinfo})
                                       $ Logic.mk_type t)
  fun prove _ (* no memoing needed *)  (t1, t2) =
      Goal.prove_internal lthy_with_ss []
                          (app_Trueprop
                             (Thm.mk_binop @{cterm "tag_disj :: typ_uinfo \<Rightarrow> typ_uinfo \<Rightarrow> bool"}
                                              (mk_typ_uinfo t1) (mk_typ_uinfo t2)))
                          (K (tac 1))
      |> Thm.solve_constraints 
  val cache = MemoCache.create Typreltab.empty Typreltab.lookup Typreltab.update prove
in
  fn ts => case Term_Ord.typ_ord ts of
               GREATER => cache (swap ts) RS tag_disj_com
             | _       => cache ts (* EQUAL doesn't make sense here ... *)
end;

structure T = Typtab;
fun mk_sub_typ_cache fg_fl_net struct_info lthy = let
  (* Typtab.make disallows duplicates, whereas we want to just squash dups. *)
  fun flds_to_tbl flds = fold (fn (fldname, typ, _) => T.update (typ, fldname)) flds T.empty
  val struct_map   = T.make (map (fn (_, typ, flds) => (typ, flds_to_tbl flds)) struct_info)

  (* l_thm is c < q, and &(p -> fld_name) : q *)
  fun mkthm p q fld_name () =
      (* We need to prove p' <= p (via fld_name) and then use sub_typ_trans to join them together *)
      let
        val q_p_thm_with_prems =
            Thm.instantiate' [SOME (Thm.ctyp_of lthy p), SOME (Thm.ctyp_of lthy q) ]
                             [SOME (Thm.cterm_of lthy (HOLogic.mk_string fld_name))]
                             @{thm field_ti_into_sub_typ_one}
        val q_p_thm =
            (* Trueprop (map_option export_uinfo X = ...), want to rewrite X *)
            let val tac = CONVERSION (HOLogic.Trueprop_conv (Conv.arg1_conv (map_option_export_uinfo_field_ti_conv fg_fl_net lthy)))
                          THEN' resolve_tac lthy @{thms "refl"}
            in Tactic.rule_by_tactic lthy (tac 1) q_p_thm_with_prems
            end
      in
	  (* Not sure why this is needed, but we get theory mismatch errors otherwise *)
          Thm.solve_constraints q_p_thm
      end

  fun rec_case f (c, p) =
      let fun go (typ, fld_name) =
          if c = typ
          then SOME (Lazy.lazy (mkthm p typ fld_name))
          else Option.map (Lazy.map (fn c_q_thm => @{thm sub_typ_proper_trans} OF [c_q_thm, mkthm p typ fld_name ()])) (f (c, typ))
      in T.get_first go end

  fun prove f (ts as (c, p)) =
      if c = p   (* FIXME: '=' here? *)
      then NONE
      else T.lookup struct_map p |> Option.mapPartial (rec_case f ts)
in
  MemoCache.create Typreltab.empty Typreltab.lookup Typreltab.update prove
end;

fun local_setup lthy = let
  (* fail early with a more useful error than THM *)
  val locale_name =
      case Named_Target.locale_of lthy of
          SOME l => l
        | NONE => raise Fail "Not in a locale"
  val struct_info =
      case List.find (List.exists (fn l => l = locale_name) o #locale_names) (IsarInstall.installed_C_files (Proof_Context.theory_of lthy)) of
          SOME info => #struct_information info
        | NONE      => raise Fail ("Not a C locale: " ^ locale_name)
  val fg_fl_net = Tactic.build_net (Proof_Context.get_thms lthy "fg_cons_simps" @ Proof_Context.get_thms lthy "fl_ti_simps")
  val thm_info = {fg_fl_net = fg_fl_net,
                  tag_disj_cache = mk_tag_disj_cache lthy,
                  sub_typ_cache  = mk_sub_typ_cache fg_fl_net struct_info lthy
                 }
in
  Local_Theory.background_theory (UMM_Thm_Info.map (Symtab.insert (fn _ => false) (* insert once per key *) (locale_name, thm_info))) lthy
end;


(* FIXME: (opt) don't use ctxt passed to convs? *)
fun umm_strengthen_prover ctxt = let
  open Conv;

  (* order is important here *)
  fun convs ctxt = [ h_val_into_lift_t_conv ctxt
                   , lift_t_field_access_conv ctxt
                   , lift_t_heap_update_conv ctxt
                   ]
in
    use_cost_center umm_strengthen_prover_cc
                    (try_conv (top_conv (repeat_conv o first_conv o convs) ctxt))
end

(* Proves ?P --> Q *)
fun imp_prover_tac {context = ctxt, concl = ct, ...} = let
  val _       = trace_ct ctxt "imp_prover_tac: " ct
  val thm     = umm_strengthen_prover ctxt (Thm.dest_arg (dest_Trueprop ct))
  val _       = trace_thm ctxt "imp_prover_tac.after: " thm
  val imp_thm = @{thm eq_into_imp} OF [thm]
  val _       = trace_thm ctxt "imp_prover_tac.imp_thm: " imp_thm				   
in
  traced_tac ctxt "imp_prover_tac: " (resolve_tac ctxt [imp_thm] 1)
end

(* Proves A = ?B *)
fun eq_prover_tac { context = ctxt, concl = ct, ... } = let
  val _       = trace_ct ctxt "eq_prover_tac: " ct
  val thm     = umm_strengthen_prover ctxt (Thm.dest_arg1 (dest_Trueprop ct))
  val _       = trace_thm ctxt "eq_prover_tac.thm: " thm
  val imp_thm = @{thm meta_eq_to_obj_eq} OF [thm]
in
  traced_tac ctxt "eq_prover_tac: " (resolve_tac ctxt [imp_thm] 1)
end

val umm_strengthen_tac =
  strengthen_via_rewr (Subgoal.FOCUS_PREMS imp_prover_tac) (Subgoal.FOCUS_PREMS eq_prover_tac)

fun umm_cleanup_tac ctxt = let
  val tinfo = umm_thm_info_for ctxt
  val rules = Cleanup.get (Context.Proof ctxt)

  fun cleanup_imp_prover_tac ctxt =
      FIRST' [ resolve_tac ctxt rules THEN_ALL_NEW umm_subgoal_tac tinfo ctxt
             , resolve_tac ctxt @{thms imp_refl}
             ]

  (* Don't do anything fancy here, just refl *)
  fun trivial_eq_prover_tac ctxt = resolve_tac ctxt @{thms refl}
in
  strengthen_via_rewr cleanup_imp_prover_tac trivial_eq_prover_tac ctxt
end

(* FIXME: Do this in 1 pass *)
fun umm_strengthen_top_tac ctxt = let
  val _ = Unsynchronized.change trace_depth (K 0)
in
  EVERY' [ resolve_tac ctxt @{thms strengthen_via_rewr_start}
         , umm_strengthen_tac ctxt
         , resolve_tac ctxt @{thms strengthen_via_rewr_start}
         , umm_cleanup_tac ctxt
         ]
end

fun umm_strengthen_first_asm_tac ctxt = let
  val _ = Unsynchronized.change trace_depth (K 0)
in
  EVERY' [ eresolve_tac ctxt @{thms strengthen_via_rewr_asm_start}
         , umm_strengthen_tac ctxt
         ] THEN_ALL_NEW (fn i => TRY (resolve_tac ctxt @{thms TrueI} i))
end

(*Count premises -- quicker than (length o strip_prems)
  FIXME: the Logic version doesn't include Pure.all
 *)
fun count_prems (Const ("Pure.imp", _) $ _ $ B) = 1 + count_prems B
  | count_prems (Const ("Pure.all", _) $ Abs (_, _, B)) = 1 + count_prems B
  | count_prems _ = 0;

fun umm_strengthen_asm_tac ctxt =
    SUBGOAL (fn (tm, i) =>
                REPEAT_DETERM_N (count_prems tm) (umm_strengthen_first_asm_tac ctxt i ORELSE rotate_tac 1 i))

fun umm_strengthen_full_tac ctxt =
    EVERY' [ umm_strengthen_top_tac ctxt
           , umm_strengthen_asm_tac ctxt
           ]

fun umm_strengthen_imp_lhs_tac ctxt = let
  val _ = Unsynchronized.change trace_depth (K 0)
  (* Proves ?P --> Q *)
  fun trivial_imp_prover_tac ctxt = resolve_tac ctxt @{thms imp_refl}
in
  EVERY' [ resolve_tac ctxt @{thms strengthen_via_rewr_imp_lhs_start}
         , strengthen_via_rewr trivial_imp_prover_tac (Subgoal.FOCUS_PREMS eq_prover_tac) ctxt
         ]
end

val congN = "cong"
val postN = "post"

(* via simplifier.ML *)
val cong_modifiers =
 [Args.$$$ congN -- Args.colon >> K (Method.modifier cong_add \<^here>),
  Args.$$$ congN -- Args.add -- Args.colon >> K (Method.modifier cong_add \<^here>),
  Args.$$$ congN -- Args.del -- Args.colon >> K (Method.modifier cong_del \<^here>)];

val post_modifiers =
 [Args.$$$ postN -- Args.colon >> K (Method.modifier cleanup_add \<^here>),
  Args.$$$ postN -- Args.add -- Args.colon >> K (Method.modifier cleanup_add \<^here>),
  Args.$$$ postN -- Args.del -- Args.colon >> K (Method.modifier cleanup_del \<^here>)];

fun mkmethod tac =
    Method.sections (cong_modifiers @ post_modifiers) >> (fn _ => fn ctxt => Method.SIMPLE_METHOD' (tac ctxt))

val method = mkmethod umm_strengthen_top_tac
val method_imp_lhs = mkmethod umm_strengthen_imp_lhs_tac
val method_asm = mkmethod umm_strengthen_asm_tac
val method_full = mkmethod umm_strengthen_full_tac

end
