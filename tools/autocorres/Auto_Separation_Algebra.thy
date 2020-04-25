(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Automatic instantiation of an AutoCorres C state space as a separation algebra.
   FIXME: this is not quite finished. There are some proof tactics missing (see getter_rewrite etc)
*)
theory Auto_Separation_Algebra
imports "AutoCorres" "Sep_Algebra.Separation_Algebra"
keywords "sep_instance" :: thy_goal
begin


lemmas sep_conj_def = Separation_Algebra.sep_algebra_class.sep_conj_def

instantiation "unit" ::  stronger_sep_algebra
   begin
       definition "zero_unit \<equiv> ()"
       definition "plus_unit  \<equiv> (\<lambda>h2 h2.  ()) :: unit \<Rightarrow> unit \<Rightarrow> unit"
       definition "sep_disj_unit \<equiv>(\<lambda>h1 h2. True) :: unit \<Rightarrow> unit \<Rightarrow> bool"
     instance
 apply (standard)
   apply (clarsimp simp: zero_unit_def plus_unit_def sep_disj_unit_def)+
 done
end

instantiation "bool" ::  stronger_sep_algebra
   begin
       definition "zero_bool \<equiv> False"
       definition "plus_bool  \<equiv> (\<or>)"
       definition "sep_disj_bool \<equiv> \<lambda>p q. p \<longrightarrow> \<not>q"
     instance
 apply (standard)
   apply (auto simp: zero_bool_def plus_bool_def sep_disj_bool_def)+
 done
end

 instantiation "fun" :: (type,stronger_sep_algebra) stronger_sep_algebra
 begin
  definition "zero_fun   \<equiv> (\<lambda>x. 0)"
  definition "plus_fun f f'  \<equiv> (\<lambda>x. if f x = 0 then f' x else f x)"
  definition "sep_disj_fun   \<equiv> (\<lambda>f f'.  \<forall>x. (f x = 0 \<or> f' x = 0)) :: ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool "
 instance
  apply standard
       apply (fastforce simp: zero_fun_def sep_disj_fun_def plus_fun_def)+
  apply (clarsimp simp: zero_fun_def sep_disj_fun_def plus_fun_def, safe)
     apply (fastforce)+
  done
end


ML \<open>
type sep_info =
{
  plus_thm : thm option,
  disj_thm : thm option,
  zero_thm : thm option,
  sep_thms : thm list,
  sep_heap_arrows : (term * thm) Typtab.table,
  sep_heap_getters : (term * thm) Typtab.table,
  sep_heap_setters : (term * thm) Typtab.table
}

fun mk_sep_info (plus_thm : thm option) (disj_thm : thm option) (zero_thm : thm option)
  (sep_heap_arrows : (term * thm) Typtab.table) (sep_heap_getters :  (term * thm) Typtab.table)
  ( sep_heap_setters : (term * thm) Typtab.table) (sep_thms : thm list) =
  {plus_thm = plus_thm,
   disj_thm = disj_thm,
   zero_thm = zero_thm,
   sep_thms = sep_thms,
   sep_heap_arrows = sep_heap_arrows,
   sep_heap_getters = sep_heap_getters,
   sep_heap_setters = sep_heap_setters}
\<close>

ML \<open>

fun upd_plus_thm (sep_info : sep_info) plus =
  {plus_thm = plus,
   disj_thm = #disj_thm sep_info,
   zero_thm = #zero_thm sep_info,
   sep_thms = #sep_thms sep_info,
   sep_heap_arrows = #sep_heap_arrows sep_info,
   sep_heap_getters = #sep_heap_getters sep_info,
   sep_heap_setters = #sep_heap_setters sep_info}

fun upd_disj_thm (sep_info : sep_info) disj =
  {plus_thm = #plus_thm sep_info,
   disj_thm = disj,
   zero_thm = #zero_thm sep_info,
   sep_thms = #sep_thms sep_info,
   sep_heap_arrows = #sep_heap_arrows sep_info,
   sep_heap_getters = #sep_heap_getters sep_info,
   sep_heap_setters = #sep_heap_setters sep_info}

fun upd_zero_thm (sep_info : sep_info) zero =
  {plus_thm = #plus_thm sep_info,
   disj_thm = #disj_thm sep_info,
   zero_thm = zero,
   sep_thms = #sep_thms sep_info,
   sep_heap_arrows = #sep_heap_arrows sep_info,
   sep_heap_getters = #sep_heap_getters sep_info,
   sep_heap_setters = #sep_heap_setters sep_info}

fun upd_heap_arrows (sep_info : sep_info) arr =
  {plus_thm = #plus_thm sep_info,
   disj_thm = #disj_thm sep_info,
   zero_thm = #zero_thm sep_info,
   sep_heap_arrows = arr,
   sep_thms = #sep_thms sep_info,
   sep_heap_getters = #sep_heap_getters sep_info,
   sep_heap_setters = #sep_heap_setters sep_info}

fun upd_heap_getters (sep_info : sep_info) getters =
  {plus_thm = #plus_thm sep_info,
   disj_thm = #disj_thm sep_info,
   zero_thm = #zero_thm sep_info,
   sep_heap_arrows = #sep_heap_arrows sep_info,
   sep_heap_getters = getters,
   sep_thms = #sep_thms sep_info,
   sep_heap_setters = #sep_heap_setters sep_info}

fun upd_heap_setters (sep_info : sep_info) setters =
  {plus_thm = #plus_thm sep_info,
   disj_thm = #disj_thm sep_info,
   zero_thm = #zero_thm sep_info,
   sep_thms = #sep_thms sep_info,
   sep_heap_arrows = #sep_heap_arrows sep_info,
   sep_heap_getters = #sep_heap_getters sep_info,
   sep_heap_setters = setters}

fun upd_thms (sep_info : sep_info) thms =
  {plus_thm = #plus_thm sep_info,
   disj_thm = #disj_thm sep_info,
   zero_thm = #zero_thm sep_info,
   sep_thms = thms,
   sep_heap_arrows = #sep_heap_arrows sep_info,
   sep_heap_getters = #sep_heap_getters sep_info,
   sep_heap_setters = #sep_heap_setters sep_info
  }

\<close>

ML \<open>val print_type = dest_Type #> fst\<close>

ML \<open>fun mk_lifted_globals_record stateT rvals ctxt =
  let
      val xs =  rvals
      val state_t = "lifted_globals_ext" |> Syntax.read_term ctxt
  in
  betapplys (state_t, xs)
  |> Syntax.check_term ctxt
end;
\<close>

ML \<open>
val get_data = HeapInfo.get #> Symtab.lookup;

\<close>


ML\<open>
fun zero_lifted_globals subT global_types heap_types  =
  let fun make_zero_heap heap_type = (@{mk_term "(\<lambda>(_ :: ?'T ptr). arbitrary_zero :: (?'T))" ('T)} heap_type)
      fun make_zero_valid_heap heap_type = (@{mk_term "(\<lambda>_. False) ::  ?'T ptr \<Rightarrow> bool" ('T)} heap_type)
      fun make_zero global_type = @{mk_term "arbitrary_zero :: ?'T" ('T)} global_type
  in
  map make_zero global_types @
  map make_zero_heap heap_types @
  map make_zero_valid_heap heap_types @
  [@{term "0\<^sub>? :: 'b"}] |>
  mk_lifted_globals_record subT
end;

val make_conj = @{mk_term "?P \<and> ?Q" (P, Q)}

val make_conj_list = foldr1 make_conj;

fun get_more ctxt t = "lifted_globals.more" |> Syntax.read_term ctxt
\<close>


declare [[ML_print_depth=1000]]

ML \<open>
fun promote subT (Const (str, typ))  =   Const (str, subT --> (typ |> range_type));
\<close>

ML \<open>

fun sep_disj_lifted_globals ctxt subT heap_types heap_valid_getters h1 h2 =
let
  fun make_valid_disjoint heap_type  =
     let val heap_valid_getter = Typtab.lookup heap_valid_getters heap_type |> the |> Const |> promote subT
         (* val heap_valid_getter' = Const (fst heap_valid_getter, subT  --> (heap_valid_getter |> snd |> range_type)) *)
     in
      @{mk_term "(\<lambda> l r. ?f l  ## (?f r)) " (f)} (heap_valid_getter) $ h1 $ h2
     end;
  val typ =  subT |> dest_Type |> snd |> hd;
  val more = get_more ctxt subT
  (* val more_disjoint = @{mk_term "\<lambda>(f :: ?'T => ?'M :: stronger_sep_algebra) (l:: ?'T) (r :: ?'T ).
               (f l) ## (f r)" ('T, 'M)} (subT, typ) $ more $ h1 $ h2 *)
  val is_valid_disjoint = map make_valid_disjoint heap_types
in
  make_conj_list is_valid_disjoint
end;
\<close>


ML \<open>fun setup_heap_zero stateT heap_type global_types sep_info ctxt  =
let
  val (_, thm, ctxt) = Utils.define_const_args "zero_lifted_globals_ext" false (zero_lifted_globals stateT global_types heap_type ctxt) [] ctxt
in
  (upd_zero_thm sep_info (SOME thm), ctxt)
end\<close>

ML \<open>fun setup_heap_disj stateT heap_types heap_valid_getters sep_info ctxt  =
let
  val term = sep_disj_lifted_globals ctxt stateT heap_types heap_valid_getters (Free ("s0", stateT)) (Free ("s1", stateT))
  val (_, thm, ctxt') = Utils.define_const_args "sep_disj_lifted_globals_ext" false (term) [("s0", stateT), ("s1", stateT)] ctxt
in
  (upd_disj_thm sep_info (SOME thm), ctxt')
end\<close>



ML\<open>
fun plus_lifted_globals ctxt subT global_names global_getters heap_types heap_getters heap_valid_getters h1 h2 =
let

 fun make_global_plus global_name =
  let val global_getter = global_name |> Symtab.lookup global_getters |> the |> snd |> promote subT

       in @{mk_term "\<lambda>l r. arbitrary_add (?f l) (?f r)"(f)} global_getter $ h1 $ h2 end;

 fun make_heap_plus heap_type  =
  let val heap_getter = heap_type |> Typtab.lookup heap_getters |> the |> Const |> promote subT
      val heap_valid_getter = heap_type |> Typtab.lookup heap_valid_getters |> the |> Const |> promote subT
   in
   (@{mk_term
       "\<lambda>l r.
        \<lambda>x.  if ?valid l x then ?heap l x else if ?valid r x then ?heap r x else
             arbitrary_add ( ?heap l x) ( ?heap r x) " (heap, valid)}
              (heap_getter, heap_valid_getter) $ h1 $ h2)
  end;

 fun make_heap_valid_plus heap_type =
    let val heap_valid_getter = heap_type |> Typtab.lookup heap_valid_getters |> the |> Const |> promote subT
    in
    (@{mk_term "\<lambda>l r.
      (?valid l) + (?valid r)" (valid)} heap_valid_getter $ h1 $ h2)
    end;
 val typ =  subT |> dest_Type |> snd |> hd;
 val more = get_more ctxt subT

in
   map make_global_plus global_names @
   map make_heap_plus heap_types @
   map make_heap_valid_plus heap_types  @
  [(@{mk_term "\<lambda>l r.
               arbitrary_add (?f l) (?f r)" (f)} (more) $ h1 $ h2)]  |>
   mk_lifted_globals_record subT
end;

\<close>

ML \<open>
fun setup_heap_plus stateT global_names global_getters heap_types heap_getters heap_valid_getters sep_info ctxt =
let
  val term = (plus_lifted_globals ctxt stateT global_names global_getters heap_types
              heap_getters heap_valid_getters (Free ("s0", stateT)) (Free ("s1", stateT)) ctxt)
  val (_, thm, ctxt') = Utils.define_const_args "plus_lifted_globals_ext" false term
                          [("s0", stateT), ("s1", stateT)] ctxt
in
  (upd_plus_thm sep_info (SOME thm), ctxt')
end;


\<close>

ML \<open>

   fun make_arrow stateT heap_type heap_getters heap_valid_getters p v=
      let
          val heap_getter = heap_type |> Typtab.lookup heap_getters |> the |> Const
          val heap_valid  = heap_type |> Typtab.lookup heap_valid_getters |> the |> Const
        in
           @{mk_term "\<lambda>p v s. ?h s p = v \<and> ?v' s p" (h, v')}
             (heap_getter, heap_valid) $ p $ v
    end;

    fun split_on _ [] = [] |
        split_on f (x::xs) = if f x then xs else split_on f xs ;

    filter;

  fun hds s = String.substring (s,0,1)

   fun setup_arrows stateT heap_types heap_getters heap_valid_getters sep_info ctxt =
    let
         val (arrowt, _, ctxt') =  Utils.define_const_args "sep_generic_arrow" true
                               (@{mk_term "undefined :: (?'h ptr => ?'h => ?'T \<Rightarrow> bool)" ('T, 'h) } (stateT, @{typ 'h})) [] ctxt
         val ctxt'' = Local_Theory.notation true Syntax.mode_default
               [(arrowt, Infixl (Input.string "\<mapsto>s", 50, Position.no_range))] ctxt'
        fun setup_arrow (heap_type,(sep_info,ctxt)) =
         let
          val pointer = (Free ("p", Utils.gen_typ @{typ "'a ptr"} [heap_type]))
          val value = (Free ("v", heap_type))
          val term = (make_arrow stateT heap_type heap_getters heap_valid_getters pointer value)
          val arr_name = "sep_map_" ^  HeapLiftBase.name_from_type heap_type
          val arrow = "\<mapsto>"  ^ (HeapLiftBase.name_from_type heap_type |> hds)
          val fix = Infixl (Input.string arrow, 50, Position.no_range)
          val (t , thm, ctxt') = Utils.define_const_args arr_name false term
               [("p", Utils.gen_typ @{typ "'a ptr"} [heap_type]) ,  ("v", heap_type) ] ctxt
          val ctxt'' = Local_Theory.notation true Syntax.mode_default [(t , fix)] ctxt'
          val genarrowstr = arrowt |> dest_Const |> fst
          val sep_info = sep_info |> #sep_heap_arrows |> Typtab.update (heap_type, (t,thm)) |> upd_heap_arrows sep_info
          in
           (sep_info, ctxt'' |>
           Local_Theory.declaration {syntax = true, pervasive = false} (K (Adhoc_Overloading.generic_add_overloaded genarrowstr )) |>
           Local_Theory.declaration {syntax = true, pervasive = false} (K (Adhoc_Overloading.generic_add_variant genarrowstr t)))
         end;
      in foldr setup_arrow (sep_info,ctxt'') heap_types
   end;

\<close>

ML \<open>Utils.expand_type_abbrevs; @{theory}; Proof_Context.theory_of;\<close>

ML \<open>fun liberalise_type _ (Type (s,[])) = (s,[]) |> Type |
          liberalise_type t (Type (s,(xs))) = if (Long_Name.base_name s) = "lifted_globals_ext" then
                                               (Type (s, t :: (tl xs))) else
                                               (Type (s, map (liberalise_type t) (xs)));
\<close>

ML \<open>

fun make_rewrite heap_getters heap_setters heap_type sep_info ctxt =
     let
         val heap_getter  = heap_type |> Typtab.lookup heap_getters |> the |> Const
         val heap_setter  = heap_type |> Typtab.lookup heap_setters |> the |> Const
         val get_heap_term = @{mk_term "gets (\<lambda>s. ?f s p) " (f)} (heap_getter)
         val set_heap_term = @{mk_term "modify (?f (\<lambda>a. a(p := v)))" (f)} heap_setter
         val (t, thy, ctxt) = Utils.define_const_args ("get_" ^ (HeapLiftBase.name_from_type heap_type)) false get_heap_term [("p", Utils.gen_typ @{typ "'a ptr"} [heap_type])] ctxt
         val (t', thy', ctxt) = Utils.define_const_args ("set_" ^ (HeapLiftBase.name_from_type heap_type)) false set_heap_term [("p", Utils.gen_typ @{typ "'a ptr"} [heap_type]), ("v", heap_type)] ctxt
         val localise_term =  @{mk_term "modify (\<lambda>s. ?f (\<lambda>a. a(p:= f s)) (s)) \<equiv> do v <- gets f; ?g p v od" (f,g)} (heap_setter, t')
         val localise_simps = @{thms modify_def gets_def put_def fun_upd_def get_def return_def bind_def }
         val localise_term' = @{mk_term "Trueprop (modify (\<lambda>s. ?f (\<lambda>a. a(p:= f a s)) s) = do a <- gets (\<lambda>s. f (?h s) s); ?g p a od)" (f,h,g)} (heap_setter, heap_getter, t')
         val prove_localise = force_tac
                          (ctxt addsimps localise_simps addsimps [thy'])
         val localise_thm = Goal.prove ctxt ["f", "p"] [] localise_term (fn _ => prove_localise 1)
         val localise'_thm = Goal.prove ctxt ["f", "p"] [] localise_term' (fn _ => prove_localise 1)
         val sep_info =  sep_info |> #sep_thms |> (fn x => x @ [localise_thm, localise'_thm, Thm.symmetric thy,Thm.symmetric thy']) |> upd_thms sep_info
         val sep_info =  sep_info |> #sep_heap_getters |> Typtab.update (heap_type, (t,thy)) |> upd_heap_getters sep_info
         val sep_info =  sep_info |> #sep_heap_setters |> Typtab.update (heap_type, (t',thy')) |> upd_heap_setters sep_info
    in
        (sep_info, ctxt)
end;


\<close>

ML \<open>
Utils.named_cterm_instantiate;

fun make_struct_rewrite (structs : HeapLiftBase.struct_info list) sep_info ctxt =
   let
       val structs = structs |> map #field_info |> List.concat
       fun make_struct_rewrite_inner strct =
       let val getter = strct |> #getter
           val setter = strct |> #setter
           val getter_rewrite_term = @{mk_term "Trueprop (gets (\<lambda>s. ?P (f s) ) =
                                                          do c <- gets f;
                                                             return (?P c )
                                                          od )" (P)} getter
           val getter_rewrite_term' = @{mk_term "Trueprop (gets (\<lambda>s a. ?P (f s) ) =
                                                           do c <- gets f;
                                                           return (\<lambda>a. ?P c ) od )" (P)} getter
           val setter_rewrite_term = @{mk_term "Trueprop (gets (\<lambda>s . ?P (f s) (g s)) =
                                                          do c <- gets f;
                                                             d <- gets g;
                                                             return ( ?P c d )
                                                          od )" (P)} setter
          val setter_rewrite_term' = @{mk_term "Trueprop (gets (\<lambda>s a . ?P (f s) (g s)) =
                                               do c <- gets f;
                                                  d <- gets g;
                                                  return (\<lambda>a. ?P c d )
                                               od )" (P)} setter
           val getter_rewrite = Goal.prove ctxt ["f"] [] getter_rewrite_term (fn _ => Skip_Proof.cheat_tac ctxt 1) (* FIXME: unfinished *)
           val getter_rewrite' = Goal.prove ctxt ["f"] [] getter_rewrite_term' (fn _ => Skip_Proof.cheat_tac ctxt 1) (* FIXME: unfinished *)
           val setter_rewrite = Goal.prove ctxt ["f", "g"] [] setter_rewrite_term (fn _ => Skip_Proof.cheat_tac ctxt 1) (* FIXME: unfinished *)
           val setter_rewrite' = Goal.prove ctxt ["f", "g"] [] setter_rewrite_term' (fn _ => Skip_Proof.cheat_tac ctxt 1) (* FIXME: unfinished *)
       in [setter_rewrite,setter_rewrite', getter_rewrite, getter_rewrite'] end;
     fun upd_sep_info_list info xs = info |> #sep_thms |> (fn x => x @ xs) |> upd_thms info
   in map make_struct_rewrite_inner structs |> List.concat |> upd_sep_info_list sep_info
end;

fun make_rewrites heap_types heap_getters heap_setters structs sep_info ctxt =
  let
    val (sep_info, ctxt) = foldr (fn (htype, (info, ctxt)) => (make_rewrite heap_getters heap_setters htype info ctxt) ) (sep_info,ctxt) heap_types
    val sep_info = (make_struct_rewrite structs sep_info ctxt)
    val thms= sep_info |> #sep_thms
  in
     (sep_info, Utils.define_lemmas "sep_thms" thms ctxt |> snd )
end;
\<close>

ML \<open>val myss = ref HOL_basic_ss\<close>
ML \<open>val mythm = ref @{thms iffI}\<close>

ML \<open>fun prove_get_leaf_lemma heap_type ((sep_info : sep_info),  ctxt) =
          let
              val (heap_getter, heap_getter_def) = heap_type |> Typtab.lookup (#sep_heap_getters sep_info) |> the
              val (heap_arrow, heap_arrow_def) = heap_type |> Typtab.lookup (#sep_heap_arrows sep_info) |> the
              val plus_thm = sep_info |> #plus_thm |> the
              val proof_term = @{mk_term
                                 " Trueprop (
                                 \<lbrace>\<lambda>s. (?arr p x \<and>* R) s\<rbrace>
                                              ?getter p
                                 \<lbrace>\<lambda>rv. pred_conj (?arr p x \<and>* R) ( K (rv = x))\<rbrace> )" (arr,getter)}
                                (heap_arrow, heap_getter)
               val thms =  [@{thm sep_conj_def},
                            @{thm pred_conj_def},
                            heap_getter_def, heap_arrow_def, plus_thm]
               val name = heap_getter |> dest_Const |> fst |> Long_Name.base_name
               fun proof_tac ctxt = fast_force_tac (ctxt addsimps thms)
               val get_wp = Goal.prove ctxt ["x", "p","R"] [] proof_term (fn _ => proof_tac ctxt 1)
       in (sep_info, Utils.define_lemma (name ^ "_wp") get_wp ctxt |> snd) end;\<close>


ML \<open>
      fun prove_update_heap_lemma (heap_arrow, heap_arrow_def) heap_update  ctxt =
         let val proof_term = @{mk_term "((?arr p x) s \<Longrightarrow> (?arr p v) (?heap_update (\<lambda>s. fun_upd s p v) s))" (arr,heap_update)} (heap_arrow, heap_update)
             val proof = clarsimp_tac (ctxt addsimps [heap_arrow_def])
             in   Goal.prove ctxt ["x", "p", "v","s"] [] proof_term (fn x => proof 1)
      end;

      fun prove_set_leaf_lemma (heap_type, heap_updater) ((sep_info : sep_info),  ctxt) =
          let
              val (heap_setter, heap_setter_def) = heap_type |> Typtab.lookup (#sep_heap_setters sep_info) |> the
              val (heap_arrow, heap_arrow_def) = heap_type |> Typtab.lookup (#sep_heap_arrows sep_info) |> the
              val disj_thm = sep_info |> #disj_thm |> the
              val plus_thm = sep_info |> #plus_thm |> the
              val proof_term = @{mk_term
                                 " Trueprop (
                                 \<lbrace>\<lambda>s. (?arr p x \<and>* R) s\<rbrace>
                                              ?setter p v
                                 \<lbrace>\<lambda>rv. (?arr p v \<and>* R)\<rbrace> )" (arr,setter)}
                                (heap_arrow, heap_setter)
               val thms = @{thms fun_upd_def} @ [ heap_arrow_def, disj_thm, plus_thm]
               val name = heap_setter |> dest_Const |> fst |> Long_Name.base_name
               val heap_update_lemma = prove_update_heap_lemma (heap_arrow, heap_arrow_def) (heap_updater) ctxt
               fun proof_tac ctxt = clarsimp_tac (ctxt addsimps [heap_setter_def]) THEN'
                                    eresolve0_tac [@{thm sep_conjE}] THEN'
                                    resolve0_tac [@{thm sep_conjI}] THEN'
                                    eresolve0_tac [heap_update_lemma] THEN'
                                    fast_force_tac (ctxt) THEN_ALL_NEW
                                    fast_force_tac (ctxt addsimps thms)
               val set_wp = Goal.prove ctxt ["x", "p","R", "v"] [] proof_term (fn x =>  proof_tac (#context x) 1 )
       in (sep_info, Utils.define_lemma (name ^ "_wp") set_wp ctxt |> snd) end;\<close>

ML \<open>

fun prove_get_leaf_lemmas heap_types sep_info ctxt =
    foldr (uncurry prove_get_leaf_lemma) (sep_info, ctxt) heap_types


fun prove_set_leaf_lemmas heap_types sep_info ctxt =
   foldr (uncurry prove_set_leaf_lemma) (sep_info, ctxt) heap_types

\<close>

ML \<open>
   fun force_tac ctxt =
      SELECT_GOAL
     (Classical.clarify_tac ctxt 1 THEN
      IF_UNSOLVED (Simplifier.asm_full_simp_tac ctxt 1) THEN
      ALLGOALS (Classical.first_best_tac ctxt))
   fun zipWith (x::xs) (y::ys) f = f x y :: zipWith xs ys f |
       zipWith _ _ _ = []

    fun tester str thy =
         let val data = get_data thy str |> the |> #heap_info
             val typ = data |> #globals_type |> print_type
             val stateT = data |> #globals_type |> dest_Type ||> (K [@{typ 'b}]) |> Type
             val heap_types = data |> #heap_getters |> Typtab.dest |> map fst
             val heap_valid_getters = data |> #heap_valid_getters
             val heap_getters = data |> #heap_getters
             val heap_setters = data |> #heap_setters
             val global_types =  data |> #global_fields |> map (fn (_,_,z) => z)
             val global_names =  data |> #global_fields |> map (fn (x,_,_) => x)
             val global_getters = data |> #global_field_getters
             val structs = data |> #structs |> Symtab.dest |> map snd
             val sep_info = mk_sep_info NONE NONE NONE Typtab.empty Typtab.empty Typtab.empty []
             fun tup_list (x : sep_info)
                            = [x |> #plus_thm |> the,
                               x |> #zero_thm |> the,
                               x |> #disj_thm |> the]
             fun proof_tac thms ctxt =
                 let
                     val equality =  Proof_Context.get_thm ctxt "lifted_globals.equality" ;
                     val simpset = ctxt addsimps @{thms sep_add_left_commute sep_disj_commute sep_add_assoc sep_add_commute
                                                       left_commute zero_fun_def plus_fun_def sep_disj_fun_def zero_bool_def
                                                       commute} addsimps thms
                     val intros = [equality, @{thm ext}]
                  in
                         Class.standard_intro_classes_tac ctxt [] THEN
                         ((resolve_tac ctxt intros  ORELSE'
                           force_tac simpset ) |> REPEAT_ALL_NEW |> TRYALL)
                end;
      in thy
      |>  Class.instantiation ([typ], [("'a", @{sort type})], @{sort stronger_sep_algebra})
      |>  setup_heap_zero stateT heap_types global_types sep_info
      |-> setup_heap_disj stateT heap_types heap_valid_getters
      |-> setup_heap_plus stateT global_names global_getters heap_types heap_getters heap_valid_getters
      |-> setup_arrows stateT heap_types heap_getters heap_valid_getters
      |-> make_rewrites heap_types heap_getters heap_setters structs
      |> (fn (info, ctxt) => (info, (info,ctxt) |> (apfst (tup_list #> proof_tac) #-> Class.prove_instantiation_instance)))
      |-> prove_get_leaf_lemmas heap_types
      |-> prove_set_leaf_lemmas (heap_setters |> Typtab.dest |> map (fn x => x ||> Const)) |> snd
      end;

Adhoc_Overloading.is_overloaded @{context} "\<mapsto>"
\<close>

ML \<open>
val _ =
  Outer_Syntax.command @{command_keyword "sep_instance"} "instantiate and prove type arity"
  (Parse.path >>
   (fn str =>  tester str |> Toplevel.begin_local_theory true #> Toplevel.end_local_theory));

(* get_data @{theory} "swap.c" |> the |> #structs *)
\<close>




end
