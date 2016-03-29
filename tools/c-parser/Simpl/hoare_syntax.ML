(*  Title:      hoare_syntax.ML
    Author:     Norbert Schirmer, TU Muenchen

Copyright (C) 2004-2007 Norbert Schirmer

This library is free software; you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as
published by the Free Software Foundation; either version 2.1 of the
License, or (at your option) any later version.

This library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
USA
*)

(* FIXME: Adapt guard generation to new syntax of op + etc. *)

signature HOARE_SYNTAX =
sig
  val antiquoteCur: string
  val antiquoteOld: string
  val antiquoteOld_tr: Proof.context -> term list -> term
  val antiquote_applied_only_to: (term -> bool) -> term -> bool
  val antiquote_varname_tr: string -> term list -> term
  val app_quote_tr': Proof.context -> term -> term list -> term
  val assert_tr': Proof.context -> term list -> term
  val assign_tr': Proof.context -> term list -> term
  val assign_tr: Proof.context -> term list -> term
  val basic_assigns_tr: Proof.context -> term list -> term
  val basic_tr': Proof.context -> term list -> term
  val basic_tr: Proof.context -> term list -> term
  val bexp_tr': string -> Proof.context -> term list -> term
  val bind_tr': Proof.context -> term list -> term
  val call_ass_tr: bool -> bool -> Proof.context -> term list -> term
  val call_tr': Proof.context -> term list -> term
  val call_tr: bool -> bool -> Proof.context -> term list -> term
  val dyn_call_tr': Proof.context -> term list -> term
  val fcall_tr': Proof.context -> term list -> term
  val fcall_tr: Proof.context -> term list -> term
  val guarded_Assign_tr: Proof.context -> term list -> term
  val guarded_Cond_tr: Proof.context -> term list -> term
  val guarded_NNew_tr: Proof.context -> term list -> term
  val guarded_New_tr: Proof.context -> term list -> term
  val guarded_WhileFix_tr: Proof.context -> term list -> term
  val guarded_While_tr: Proof.context -> term list -> term
  val guards_tr': Proof.context -> term list -> term
  val hide_guards: bool Config.T
  val init_tr': Proof.context -> term list -> term
  val init_tr: Proof.context -> term list -> term
  val loc_tr': Proof.context -> term list -> term
  val loc_tr: Proof.context -> term list -> term
  val new_tr : Proof.context -> term list -> term
  val new_tr': Proof.context -> term list -> term
  val nnew_tr : Proof.context -> term list -> term
  val nnew_tr': Proof.context -> term list -> term
  val proc_ass_tr: Proof.context -> term list -> term
  val proc_tr': Proof.context -> term list -> term
  val proc_tr: Proof.context -> term list -> term
  val quote_mult_tr': Proof.context -> (term -> bool) -> string -> string -> term -> term
  val quote_tr': Proof.context -> string -> term -> term
  val quote_tr: Proof.context -> string -> term -> term
  val raise_tr': Proof.context -> term list -> term
  val raise_tr: Proof.context -> term list -> term
  val switch_tr': Proof.context -> term list -> term
  val update_comp: Proof.context -> string list -> bool -> bool -> xstring -> term -> term -> term
  val use_call_tr': bool Config.T
  val whileAnnoGFix_tr': Proof.context -> term list -> term
  val whileAnnoG_tr': Proof.context -> term list -> term
end;

structure Hoare_Syntax: HOARE_SYNTAX =
struct

val use_call_tr' = Attrib.setup_config_bool @{binding hoare_use_call_tr'} (K true);
val hide_guards = Attrib.setup_config_bool @{binding hoare_hide_guards} (K false);

val globalsN = "globals";
val localsN = "locals";
val globals_updateN = suffix Record.updateN globalsN;
val locals_updateN = suffix Record.updateN localsN;
val upd_globalsN = "upd_globals";   (* FIXME authentic syntax !? *)
val allocN = "alloc_'";
val freeN = "free_'";

val Null = Syntax.free "Simpl_Heap.Null";   (* FIXME ?? *)


(** utils **)

(* transpose [[a,b],[c,d],[e,f]] = [[a,c,d],[b,d,f]] *)
fun transpose [[]] = [[]]
  | transpose ([]::xs) = []
  | transpose ((y::ys)::xs) = (y::map hd xs)::transpose (ys::map tl xs)

fun maxprefix eq ([], ys) = []
  | maxprefix eq (xs, []) = []
  | maxprefix eq ((x::xs),(y::ys)) = if eq (x,y)
                                     then x::maxprefix eq (xs,ys)
                                     else []

fun maxprefixs eq [] = []
  | maxprefixs eq [[]] = []
  | maxprefixs eq xss = foldr1 (maxprefix eq) xss;

fun mk_list [] = Syntax.const @{const_syntax Nil}
  | mk_list (x::xs) = Syntax.const @{const_syntax Cons} $ x $ mk_list xs;

(* convert Fail to Match, useful for print translations *)
fun unsuffix' sfx a = unsuffix sfx a handle Fail _ => raise Match;
fun unsuffixI sfx a = unsuffix sfx a handle Fail _ => a;

fun mk_nib n = "Nibble" ^ chr (n + (if n <= 9 then ord "0" else ord "A" - 10));

fun mk_char c =
  if Char.isAscii c andalso Char.isPrint c then
    Syntax.const @{const_syntax Char} $
      Syntax.const (mk_nib (Char.ord c div 16)) $
      Syntax.const (mk_nib (Char.ord c mod 16))
  else raise TERM ("call_tr: printable procedure name expected: " ^ str c, []);

fun mk_string [] = Syntax.const @{const_syntax Nil}
  | mk_string (c::cs) = Syntax.const @{const_syntax Cons} $ mk_char c $ mk_string cs;

fun is_prefix_or_suffix s t =
  can (unprefix s) t orelse can (unsuffix s) t;


(** hoare data **)

fun is_global_comp ctxt name =
  (case StateSpace.get_comp (Context.Proof ctxt) name of
    SOME (_, ln) => is_prefix_or_suffix "globals" (Long_Name.base_name ln)
  | NONE => false);


(** parsing and printing **)

(* quote/antiquote *)

val antiquoteCur = @{syntax_const "_antiquoteCur"};
val antiquoteOld = @{syntax_const "_antiquoteOld"};

fun intern_const_syntax consts =
  Consts.intern_syntax consts #> perhaps Long_Name.dest_hidden;

fun is_global ctxt name =
  let
    val thy = Proof_Context.theory_of ctxt;
    val consts = Proof_Context.consts_of ctxt;
  in
    (case Sign.const_type thy (intern_const_syntax consts name) of
      NONE => is_global_comp ctxt name
    | SOME T => String.isPrefix globalsN (Long_Name.base_name (fst (dest_Type (domain_type T)))))
    handle Match => false
  end;

exception UNDEFINED of string

(* FIXME: if is_state_var etc. is reimplemented, rethink about when adding the deco to
   the records *)

fun first_successful_tr _ [] = raise TERM ("first_successful_tr: no success",[])
  | first_successful_tr f [x] = f x
  | first_successful_tr f (x::xs) = f x handle TERM _ => first_successful_tr f xs;

fun statespace_lookup_tr ctxt ps s n =
  let
    val cn = map Hoare.clique_name (#active_procs (Hoare.get_data ctxt));
    val procs = ps @ cn;
    val names =
      n :: map (fn p => (suffix (Hoare.par_deco p) (unsuffixI Hoare.deco n))) procs;
  in first_successful_tr (StateSpace.gen_lookup_tr ctxt s) names
  end;

fun statespace_update_tr ctxt ps id n v s =
  let
    val cn = map Hoare.clique_name (#active_procs (Hoare.get_data ctxt));
    val procs = ps @ cn;
    val names =
      n :: map (fn p => (suffix (Hoare.par_deco p) (unsuffixI Hoare.deco n))) procs;
  in first_successful_tr (fn n => StateSpace.gen_update_tr id ctxt n v s) names
  end;

local
  fun is_record_sel ctxt =
    let val consts = Proof_Context.consts_of ctxt;
    in can (Consts.the_const consts) o intern_const_syntax consts end;
in

fun lookup_comp ctxt ps name =
  if is_record_sel ctxt name
  then
    if is_global ctxt name
    then (fn s => Syntax.free name $ (Syntax.free "globals" $ s))
    else (fn s => Syntax.free name $ s)
  else
    let
      val sel = Syntax.const (if is_global_comp ctxt name then "globals" else "locals");
    in (fn s => statespace_lookup_tr ctxt ps (sel $ s) name) end;

(*
FIXME:
update of global and local components:
One should generally provide functions:
glob_upd:: ('g => 'g) => 's => 's
loc_upd:: ('l => 'l) => 's => 's
so that global and local updates can nicely be composed.
loc_upd for the record implementation is vacuous.
Right now for example an assignment of NEW to a global variable returns
a funny repeated update of global components...

This would make the composition more straightforward...
Basically one wants the map on a component rather then the update. Maps can
be composed nicer...
*)
fun K_rec_syntax v = Abs ("_", dummyT, incr_boundvars 1 v);

fun update_comp ctxt ps atomic id name value =
  if is_record_sel ctxt name
  then
    let
      val upd = Syntax.free (suffix Record.updateN name) $ K_rec_syntax value;
    in
      if atomic andalso is_global ctxt name
      then (fn s =>
        Syntax.free globals_updateN $ (K_rec_syntax (upd $ (Syntax.free globalsN $ s))) $ s)
      else (fn s => upd $ s)
    end
  else
    let
      val reg = if is_global_comp ctxt name then "globals" else "locals";
      val upd = Syntax.free (reg ^ Record.updateN);
      val sel = Syntax.free reg;
    in
      fn s =>
        if atomic then
          upd $ (K_rec_syntax (statespace_update_tr ctxt ps id name value (sel $ s))) $ s
        else statespace_update_tr ctxt ps id name value s
    end;

end;

fun antiquote_global_tr ctxt off i t =
  let
    fun mk n t = lookup_comp ctxt [] n (Bound (i + off n));
     (*if is_global ctxt n then t$(Free ("globals",dummyT)$Bound (i + off n))
       else t$Bound (i + off n)*)
  in
    (case t of
      Free  (n, _) => mk n t
    | Const (n, _) => mk n t
    | _ => t $ Bound i)
  end;


fun antiquote_off_tr offset ctxt name =
  let
    fun tr i ((t as Const (c, _)) $ u) =
          if c = name then antiquote_global_tr ctxt offset i (tr i u)
          else tr i t $ tr i u
      | tr i (t $ u) = tr i t $ tr i u
      | tr i (Abs (x, T, t)) = Abs (x, T, tr (i + 1) t)
      | tr _ a = a;
  in tr 0 end;


val antiquote_tr = antiquote_off_tr (K 0)

fun quote_tr ctxt name t = Abs ("s", dummyT, antiquote_tr ctxt name (Term.incr_boundvars 1 t));

fun antiquoteCur_tr ctxt t = antiquote_tr ctxt antiquoteCur (Term.incr_boundvars 1 t);


fun antiquote_varname_tr anti [n] =
  (case n of
    Free (v, T) => Syntax.const anti $ Free (Hoare.varname v, T)
  | Const (c, T) => Syntax.const anti $ Const (Hoare.varname c, T)
  | _ => Syntax.const anti $ n);



fun antiquoteOld_tr ctxt [s, n] =
  (case n of
    Free (v, T) => lookup_comp ctxt [] (Hoare.varname v) s
  | Const (c, T) => lookup_comp ctxt [] (Hoare.varname c) s
  | _ => n $ s);

fun antiquote_tr' ctxt name =
  let
    fun is_state i t =
      (case t of
        Bound j => i = j
      | Const (g,_) $ Bound j =>
          i = j andalso member (op =) [globalsN, localsN] (Long_Name.base_name g)
      | _ => false);
    fun tr' i (t $ u) =
       if is_state i u then Syntax.const name $ tr' i (Hoare.undeco ctxt t)
       else tr' i t $ tr' i u
      | tr' i (Abs (x, T, t)) = Abs (x, T, tr' (i + 1) t)
      | tr' i a = if a = Bound i then raise Match else a;
  in tr' 0 end;

fun quote_tr' ctxt name (Abs (_, _, t)) = Term.incr_boundvars ~1 (antiquote_tr' ctxt name t)
  | quote_tr' ctxt name (t as (Const _)) (* eta contracted *) =
      Syntax.const name $ Hoare.undeco ctxt t
  | quote_tr' _ _ _ = raise Match;



local
fun state_test (t as Const (g,_) $ u) f  =
      if member (op =) [localsN, globalsN] (Long_Name.base_name g) then f u else f t
  | state_test u f = f u;
in

fun antiquote_applied_only_to P =
  let
     fun test i (t $ u) =
       state_test u
         (fn Bound j =>
               if j=i then  P t
               else test i t andalso test i u
           | u => test i t andalso test i u)
       | test i (Abs (x, T, t)) = test (i + 1) t
       | test i a = true;
  in test 0 end;


fun antiquote_mult_tr' ctxt is_selector current old  =
  let
    fun tr' i (t $ u) =
          state_test u
            (fn Bound j =>
                  if j = i then Syntax.const current $ tr' i (Hoare.undeco ctxt t)
                  else if is_selector t (* other quantified states *)
                  then Syntax.const old $ Bound j $ tr' i (Hoare.undeco ctxt t)
                  else  tr' i t $ tr' i u
              | pre as ((Const (m,_) $ (s as Free _))) (* pre state *) =>
                  if (m = @{syntax_const "_bound"} orelse m = @{syntax_const "_free"})
                    andalso is_selector t
                  then Syntax.const old $ pre $ tr' i (Hoare.undeco ctxt t)
                  else tr' i t $ pre
              | pre as ((Const (m,_) $ (s as Var _))) (* pre state *) =>
                  if m = @{syntax_const "_var"} andalso is_selector t
                  then Syntax.const old $ pre $ tr' i (Hoare.undeco ctxt t)
                  else tr' i t $ pre
              | u => tr' i t $ tr' i u)
      | tr' i (Abs (x, T, t)) = Abs (x, T, tr' (i + 1) t)
      | tr' i a = if a = Bound i then raise Match else a;
  in tr' 0 end;
end;

fun quote_mult_tr' ctxt is_selector current old  (Abs (_, _, t)) =
      Term.incr_boundvars ~1 (antiquote_mult_tr' ctxt is_selector current old t)
  | quote_mult_tr' _ _ _ _ _ = raise Match;

fun app_quote_tr' ctxt f (t :: ts) =
      Term.list_comb (f $ quote_tr' ctxt antiquoteCur t, ts)
  | app_quote_tr' _ _ _ = raise Match;

fun app_quote_mult_tr' ctxt is_selector f (t :: ts) =
      Term.list_comb (f $ quote_mult_tr' ctxt is_selector antiquoteCur antiquoteOld  t, ts)
  | app_quote_mult_tr' _ _ _ _ = raise Match;


fun atomic_var_tr ctxt ps name value =
  update_comp ctxt ps true false name value;


fun heap_var_tr ctxt hp p value =
  let
    fun upd s =
      update_comp ctxt [] true false hp
        (Syntax.const @{const_syntax fun_upd} $ lookup_comp ctxt [] hp s $ p $ value) s;
  in upd end;

fun get_arr_var (Const (@{const_syntax List.nth},_) $ arr $ i) =
      (case get_arr_var arr of
         SOME (name,p,is) => SOME (name,p,i::is)
       | NONE => NONE)
  | get_arr_var (Const (@{syntax_const "_antiquoteCur"},_) $ Free (var,_)) =
     if Hoare.is_state_var var then SOME (var,NONE,[]) else NONE
  | get_arr_var (Const (@{syntax_const "_antiquoteCur"},_) $ Const (var,_)) =
     if Hoare.is_state_var var then SOME (var,NONE,[]) else NONE
  | get_arr_var ((Const (@{syntax_const "_antiquoteCur"},_) $ Free (hp,_)) $ p) =
     if Hoare.is_state_var hp then SOME (hp,SOME p,[]) else NONE
  | get_arr_var ((Const (@{syntax_const "_antiquoteCur"},_) $ Const (hp,_)) $ p) =
     if Hoare.is_state_var hp then SOME (hp,SOME p,[]) else NONE
  | get_arr_var _ = NONE


fun arr_var_tr ctxt ps name arr pos value idxs  =
  let
    fun sel_tr [] = arr
      | sel_tr (i::is) = Syntax.const @{const_syntax nth} $ sel_tr is $ i;

    fun lupd_tr value [] _ = value
      | lupd_tr value (i::is) idxs  =
          Syntax.const @{const_syntax list_update} $ sel_tr idxs $ i $ lupd_tr value is (i::idxs);


    val value' = lupd_tr value idxs [];
  in case pos of
       NONE   => atomic_var_tr ctxt ps name value'
     | SOME p => heap_var_tr ctxt name p value'
  end;

fun get_arr_mult_var (Const (@{syntax_const "_antiquoteCur"},_) $ Free (var,_)) =
     if Hoare.is_state_var var then SOME (var,NONE) else NONE
  | get_arr_mult_var (Const (@{syntax_const "_antiquoteCur"},_) $ Const (var,_)) =
     if Hoare.is_state_var var then SOME (var,NONE) else NONE
  | get_arr_mult_var ((Const (@{syntax_const "_antiquoteCur"},_) $ Free (hp,_)) $ p) =
     if Hoare.is_state_var hp then SOME (hp,SOME p) else NONE
  | get_arr_mult_var ((Const (@{syntax_const "_antiquoteCur"},_) $ Const (hp,_)) $ p) =
     if Hoare.is_state_var hp then SOME (hp,SOME p) else NONE
  | get_arr_mult_var _ = NONE

fun arr_mult_var_tr ctxt ps name arr pos vals idxs  =
  let
    val value' = Syntax.const @{const_syntax list_multupd} $ arr $ idxs $ vals;
  in
    case pos of
      NONE => atomic_var_tr ctxt ps name value'
    | SOME p => heap_var_tr ctxt name p value'
  end;

fun update_tr ctxt ps off_var off_val e
        (v as Const (@{syntax_const "_antiquoteCur"},_) $ Free (var,_)) =
      if Hoare.is_state_var var then atomic_var_tr ctxt ps var e
      else raise TERM ("no proper lvalue", [v])
  | update_tr ctxt ps off_var off_val e
        ((v as Const (@{syntax_const "_antiquoteCur"},_) $ Free (hp, _)) $ p) =
      if Hoare.is_state_var hp
      then heap_var_tr ctxt hp (antiquote_off_tr off_val ctxt antiquoteCur p) e
      else raise TERM ("no proper lvalue",[v])
  | update_tr ctxt ps off_var off_val e
        (v as Const (@{const_syntax list_multsel}, _) $ arr $ idxs) =
      (case get_arr_mult_var arr of
         SOME (var, pos) =>
            let
              val pos' = Option.map (antiquote_off_tr off_val ctxt antiquoteCur) pos;
              val var' = lookup_comp ctxt ps var (Bound (off_var var));
              val arr' = case pos' of NONE => var' | SOME p => var' $ p;
              val idxs' = antiquote_off_tr off_val ctxt antiquoteCur idxs;
            in arr_mult_var_tr ctxt ps var arr' pos' e idxs' end
       | NONE =>  raise TERM ("no proper lvalue", [v]))
  | update_tr ctxt ps off_var off_val e v =
      (case get_arr_var v of
        SOME (var,pos,idxs) =>
          let
            val pos' = Option.map (antiquote_off_tr off_val ctxt antiquoteCur) pos;
            val var' = lookup_comp ctxt ps var (Bound (off_var var));
            val arr' = case pos' of NONE => var' | SOME p => var' $ p;
            val idxs' = rev (map (antiquote_off_tr off_val ctxt antiquoteCur) idxs);
          in arr_var_tr ctxt ps var arr' pos' e idxs' end
      | NONE => raise TERM ("no proper lvalue", [v]))
  | update_tr _ _ _ _ e t = raise TERM ("update_tr", [t])


fun app_assign_tr f ctxt (ts as [v, e]) =
      let
        fun offset v = 0;
      in f $ Abs ("s", dummyT, update_tr ctxt [] offset offset (antiquoteCur_tr ctxt e) v (Bound 0))
      end
  | app_assign_tr _ _ ts = raise TERM ("assign_tr", ts);


val assign_tr = app_assign_tr (Syntax.const @{const_syntax Basic});
val raise_tr = app_assign_tr (Syntax.const @{const_syntax raise});


fun basic_assign_tr ctxt (ts as [v, e]) =
      let
        fun offset v = 0;
      in update_tr ctxt [] offset offset (antiquoteCur_tr ctxt e) v
      end
  | basic_assign_tr _ ts = raise TERM ("basic_assign_tr", ts);

fun basic_assigns_tr ctxt [t] =
      let
        fun dest_basic (Const (@{syntax_const "_BAssign"}, _) $ v $ e) =
              basic_assign_tr ctxt [v,e]
          | dest_basic _ = raise Match;

        fun dest_basics (Const (@{syntax_const "_basics"}, _) $ x $ xs) =
              dest_basic x :: dest_basics xs
          | dest_basics (t as Const (@{syntax_const "_BAssign"}, _) $_ $ _) =
              [dest_basic t]
          | dest_basics _ = []
        val upds = dest_basics t;
      in Abs ("s", dummyT, fold (fn upd => fn s => upd s) upds (Bound 0))
      end
  | basic_assigns_tr _ ts = raise TERM ("basic_assigns_tr", ts);

fun basic_tr ctxt [t] =
  Syntax.const @{const_syntax Basic} $
    (Abs ("s", dummyT,
      antiquote_tr ctxt @{syntax_const "_antiquoteCur"} (Term.incr_boundvars 1 t) $ Bound 0));

fun init_tr ctxt [Const (var,_),comp,value] =
      let
        fun dest_set (Const (@{const_syntax Set.empty}, _)) = []
          | dest_set (Const (@{const_syntax insert}, _) $ x $ xs) = x :: dest_set xs;

        fun dest_list (Const (@{const_syntax Nil}, _)) = []
          | dest_list (Const (@{const_syntax Cons}, _) $ Free (x, _) $ xs) = x :: dest_list xs;

        fun dest_val_list (Const (@{const_syntax Nil}, _)) = []
          | dest_val_list (Const (@{const_syntax Cons},_) $ x $ xs) =
              dest_set x :: dest_val_list xs
          | dest_val_list t = [dest_set t];

        val values =
          (case value of
            Const (@{const_syntax Cons}, _) $ _ $ _ =>
              map mk_list (transpose (dest_val_list value))
          | Const (@{const_syntax insert}, _) $ _ $ _ =>
              dest_set value
          | _ => raise TERM ("unknown variable initialization", []))
        val comps = dest_list comp;
        fun mk_upd var c v =
          Syntax.free (suffix Record.updateN (Hoare.varname (suffix ("_" ^ c) var))) $ v;
        val upds = map2 (mk_upd var) comps values;
        val app_upds = fold (fn upd => fn s => upd $ s) upds;
        val upd =
          if is_global ctxt (Hoare.varname (suffix ("_" ^ hd comps) var)) then
            Syntax.free (suffix Record.updateN globalsN) $
              app_upds (Syntax.free globalsN $ Bound 0) $ Bound 0
          else app_upds (Bound 0)
      in
        Syntax.const @{const_syntax Basic} $ Abs ("s", dummyT, upd)
      end
  | init_tr _ _ = raise Match;


fun new_tr ctxt (ts as [var,size,init]) =
      let
        fun offset v = 0;
        fun dest_init (Const (@{syntax_const "_newinit"}, _) $ Const (var, _) $ v) = (var, v)
          | dest_init _ = raise Match;

        fun dest_inits (Const (@{syntax_const "_newinits"}, _) $ x $ xs) =
              dest_init x :: dest_inits xs
          | dest_inits (t as (Const (@{syntax_const "_newinit"}, _) $_ $ _)) = [dest_init t]
          | dest_inits _ = raise Match;

        val g = Syntax.free globalsN $ Bound 0;
        val alloc = lookup_comp ctxt [] allocN (Bound 0);
        val new = Syntax.free "new" $ (Syntax.const @{const_syntax set} $ alloc);  (* FIXME new !? *)

        fun mk_upd (var,v) =
          let
            val varn = Hoare.varname var;
            val var' = lookup_comp ctxt [] varn (Bound 0);
          in
            update_comp ctxt [] false false varn
              (Syntax.const @{const_syntax fun_upd} $ var' $ new $ v)
          end;

        val inits = map mk_upd (dest_inits init);
        val free = lookup_comp ctxt [] freeN (Bound 0);
        val freetest = Syntax.const @{const_syntax Orderings.less_eq} $ size $ free;

        val alloc_upd =
          update_comp ctxt [] false false allocN
            (Syntax.const @{const_syntax Cons} $ new $ alloc);
        val free_upd =
          update_comp ctxt [] false false freeN
            (Syntax.const @{const_syntax Groups.minus} $ free $ size);

        val g' =
          Syntax.free (suffix Record.updateN globalsN) $
            K_rec_syntax (fold (fn upd => fn s => upd s) (alloc_upd :: free_upd :: inits) g) $
            Bound 0;
        val cond =
          Syntax.const @{const_syntax If} $ freetest $
            update_tr ctxt [] offset offset new var g' $
            update_tr ctxt [] offset offset Null var (Bound 0);

      in Syntax.const @{const_syntax Basic} $ Abs ("s", dummyT, cond)
      end
  | new_tr _ ts = raise TERM ("new_tr",ts);

fun nnew_tr ctxt (ts as [var,size,init]) =
      let
        fun offset v = 0;
        fun dest_init (Const (@{syntax_const "_newinit"}, _) $ Const (var, _) $ v) = (var, v)
          | dest_init _ = raise Match;

        fun dest_inits (Const (@{syntax_const "_newinits"}, _) $ x $ xs) =
              dest_init x :: dest_inits xs
          | dest_inits (t as (Const (@{syntax_const "_newinit"}, _) $ _ $ _)) =
              [dest_init t]
          | dest_inits _ = raise Match;

        val g = Syntax.free globalsN $ Bound 0;
        val alloc = lookup_comp ctxt [] allocN (Bound 0);
        val new = Syntax.free "new" $ (Syntax.const @{const_syntax set} $ alloc);  (* FIXME new !? *)

        fun mk_upd (var,v) =
          let
            val varn = Hoare.varname var;
            val var' = lookup_comp ctxt [] varn (Bound 0);
          in
            update_comp ctxt [] false false varn
              (Syntax.const @{const_syntax fun_upd} $ var' $ new $ v)
          end;

        val inits = map mk_upd (dest_inits init);
        val free = lookup_comp ctxt [] freeN (Bound 0);
        val freetest = Syntax.const @{const_syntax Orderings.less_eq} $ size $ free;

        val alloc_upd =
          update_comp ctxt [] false false allocN
            (Syntax.const @{const_syntax Cons} $ new $ alloc);
        val free_upd =
          update_comp ctxt [] false false freeN
            (Syntax.const @{const_syntax Groups.minus} $ free $ size);

        val g' =
          Syntax.free (suffix Record.updateN globalsN) $
            K_rec_syntax (fold (fn upd => fn s => upd s) (alloc_upd :: inits @ [free_upd]) g) $
            Bound 0;
        val cond =
          Syntax.const @{const_syntax if_rel} $ Abs ("s", dummyT, freetest) $
            Abs ("s", dummyT, update_tr ctxt [] offset offset new var g') $
            Abs ("s", dummyT, update_tr ctxt [] offset offset Null var (Bound 0)) $
            Abs ("s", dummyT, update_tr ctxt [] offset offset new var g');

      in Syntax.const @{const_syntax Spec} $ cond
      end
  | nnew_tr _ ts = raise TERM ("nnew_tr", ts);

fun loc_tr ctxt (ts as [init, bdy]) =
  let
    fun dest_init (Const (@{syntax_const "_locinit"}, _) $ Const (var,_) $ v) = (var, v)
      | dest_init (Const (@{syntax_const "_locnoinit"}, _) $ Const (var, _)) =
           (var, Syntax.const antiquoteCur $ Syntax.free (Hoare.varname var))
           (* FIXME could skip this dummy initialisation v := v s and
              derive non init variables in the print translation from
              the return function instead the init function *)
      | dest_init _ = raise Match;

    fun dest_inits (Const (@{syntax_const "_locinits"}, _) $ x $ xs) = dest_init x :: dest_inits xs
      | dest_inits (t as (Const (@{syntax_const "_locinit"}, _) $ _ $ _)) = [dest_init t]
      | dest_inits (t as (Const (@{syntax_const "_locnoinit"}, _) $ _)) = [dest_init t]
      | dest_inits _ = raise Match;

    fun mk_init_upd (var, v) =
      update_comp ctxt [] true false var (antiquoteCur_tr ctxt v);

    fun mk_ret_upd var =
      update_comp ctxt [] true false var (lookup_comp ctxt [] var (Bound 1));

    val var_vals = map (apfst Hoare.varname) (dest_inits init);
    val ini = Abs ("s", dummyT, fold mk_init_upd var_vals (Bound 0));
    val ret = Abs ("s",dummyT, Abs ("t",dummyT, fold (mk_ret_upd o fst) var_vals (Bound 0)));
    val c = Abs ("i", dummyT, Abs ("t", dummyT, Syntax.const @{const_syntax Skip}));

  in Syntax.const @{const_syntax block} $ ini $ bdy $ ret $ c end

infixr 9 &;

fun (NONE & NONE) = NONE
  | ((SOME x) & NONE) = SOME x
  | (NONE & (SOME x)) = SOME x
  | ((SOME x) & (SOME y)) = SOME (Syntax.const @{const_syntax HOL.conj} $ x $ y);

fun mk_imp (l,SOME r) = SOME (HOLogic.mk_imp (l, r))
  | mk_imp (l,NONE) = NONE;


local

fun le l r =
  Syntax.const @{const_syntax Orderings.less} $ l $ r;

fun in_range t = Syntax.free "in_range" $ t;   (* FIXME ?? *)

fun not_zero t =
  Syntax.const @{const_syntax Not} $
    (Syntax.const @{const_syntax HOL.eq} $ t $ Syntax.const @{const_syntax Groups.zero});

fun not_Null t =
  Syntax.const @{const_syntax Not} $
    (Syntax.const @{const_syntax HOL.eq} $ t $ Syntax.free "Simpl_Heap.Null");   (* FIXME ?? *)

fun in_length i l =
  Syntax.const @{const_syntax Orderings.less} $ i $
    (Syntax.const @{const_syntax size} $ l);

fun is_pos t =
  Syntax.const @{const_syntax Orderings.less_eq} $ Syntax.const @{const_syntax Groups.zero} $ t;


fun infer_type ctxt t =
  Syntax.check_term ctxt (Exn.release (#2 (Syntax_Phases.decode_term ctxt ([], Exn.Res t))));


(* NOTE: operations on actual terms *)

fun is_arr (Const (@{const_name List.nth},_) $ l $ e) = is_arr l
  | is_arr (Const (a, _) $ Bound 0) = Hoare.is_state_var a
  | is_arr (Const (a,_) $ (Const (globals,_) $ Bound 0)) = Hoare.is_state_var a
  | is_arr ((Const (hp,_) $ (Const (globals,_) $ Bound 0)) $ p) = Hoare.is_state_var hp
  | is_arr _ = false;

fun dummyfyT (TFree x) = TFree x
  | dummyfyT (TVar x) = dummyT
  | dummyfyT (Type (c, Ts)) =
     let
       val Ts' = map dummyfyT Ts;
     in if exists (fn T => T = dummyT) Ts' then dummyT else Type (c, Ts') end;

fun guard ctxt Ts (add as (Const (@{const_name Groups.plus},_) $ l $ r)) =
      guard ctxt Ts l & guard ctxt Ts r & SOME (in_range add)
  | guard ctxt Ts (sub as (Const (@{const_name Groups.minus},_) $ l $ r)) =
      let
        val g =
          (if fastype_of1 (Ts,sub) = HOLogic.natT then le r l else in_range sub)
            handle TERM _ => error ("guard generation, cannot determine type of: " ^
              Syntax.string_of_term ctxt sub);
      in guard ctxt Ts l & guard ctxt Ts r & SOME g end
  | guard ctxt Ts (mul as (Const (@{const_name Groups.times},_) $ l $r)) =
      guard ctxt Ts l & guard ctxt Ts r & SOME (in_range mul)
  | guard ctxt Ts (Const (@{const_name HOL.conj},_) $ l $ r) =
      guard ctxt Ts l & mk_imp (l,guard ctxt Ts r)
  | guard ctxt Ts (Const (@{const_name HOL.disj},_) $ l $ r) =
      guard ctxt Ts l & mk_imp (HOLogic.Not $ l,guard ctxt Ts r)
  | guard ctxt Ts (dv as (Const (@{const_name Rings.divide},_) $ l $ r)) =
      guard ctxt Ts l & guard ctxt Ts r & SOME (not_zero r) & SOME (in_range dv) (* FIXME: Make more concrete guard...*)
  | guard ctxt Ts (Const (@{const_name Divides.div_class.mod},_) $ l $ r) =
      guard ctxt Ts l & guard ctxt Ts r & SOME (not_zero r)
  | guard ctxt Ts (un as (Const (@{const_name Groups.uminus},_) $ n)) =
      guard ctxt Ts n & SOME (in_range un)
  | guard ctxt Ts (Const (@{const_name Int.nat},_) $ i) =
      guard ctxt Ts i & SOME (is_pos i)
  | guard ctxt Ts (i as (Const (@{const_abbrev Int.int},_) $ n)) =
      guard ctxt Ts n & SOME (in_range i)
  | guard ctxt Ts (Const (@{const_name List.nth},_) $ l $ e) =
      if is_arr l then guard ctxt Ts l & guard ctxt Ts e & SOME (in_length e l)
      else NONE (*oder default?*)
  | guard ctxt Ts (Const (hp,_) $ (Const (globals,_) $ Bound 0) $ p) =
      if Hoare.is_state_var hp then guard ctxt Ts p & SOME (not_Null p)(*& SOME (in_alloc p)*)
      else guard ctxt Ts p

(*  | guard (Const (@{const_name "list_update"},_)$l$i$e) =
      if is_arr l then guard i & SOME (in_length i l) & guard e else NONE*) (* oder default?*)
(*  | guard (Const (upd,_)$e$s) = for procedure parameters,like default but left to right
      if is_some (try (unsuffix updateN) upd) then guard s & guard e else guard e & guard s *)
  | guard ctxt Ts t =
      fold_rev (fn l => fn r => guard ctxt Ts l & r) (snd (strip_comb t)) NONE (* default *)
  | guard _ _ _ = NONE;

in

 fun mk_guard ctxt t =
   let
      (* We apply type inference first, so that we can generate different guards,
         depending on the type, e.g. int vs. nat *)
      val Abs (_, T, t') = map_types dummyfyT (infer_type ctxt (Abs ("s", dummyT, t)));
   in guard ctxt [T] t' end;

end;
(* FIXME: make guard function a parameter of all parse-translations that need it.*)

val _ = Theory.setup (Context.theory_map (Hoare.install_generate_guard mk_guard));


fun mk_singleton_guard f g =
  Syntax.const @{const_syntax Cons} $
    (Syntax.const @{const_syntax Pair} $ Syntax.const f $
      (Syntax.const @{const_syntax Collect} $ Abs ("s", dummyT, g))) $
    Syntax.const @{const_syntax Nil};

fun guarded_Assign_tr ctxt (ts as [v, e]) =
      let
        val ass = assign_tr ctxt [v, e];
        val guard = Hoare.generate_guard ctxt;
        (* By the artificial "=" between left and right-hand side we get a bigger term and thus
           more information for type-inference *)
      in
        case guard (Syntax.const @{const_syntax HOL.eq} $
            antiquoteCur_tr ctxt v $ antiquoteCur_tr ctxt e) of
          NONE => ass
        | SOME g =>
            Syntax.const @{const_syntax guards} $ mk_singleton_guard @{const_syntax False} g $ ass
      end
  | guarded_Assign_tr _ ts = raise Match;

fun guarded_New_tr ctxt (ts as [var, size, init]) =
      let
        val new = new_tr ctxt [var, size, init];
        val guard = Hoare.generate_guard ctxt;
      in
        case guard (antiquoteCur_tr ctxt var) of
          NONE => new
        | SOME g =>
            Syntax.const @{const_syntax guards} $ mk_singleton_guard @{const_syntax False} g $ new
      end
  | guarded_New_tr _ ts = raise TERM ("guarded_New_tr", ts);

fun guarded_NNew_tr ctxt (ts as [var, size, init]) =
      let
        val new = nnew_tr ctxt [var, size, init];
        val guard = Hoare.generate_guard ctxt;
      in
        case guard (antiquoteCur_tr ctxt var) of
          NONE => new
        | SOME g =>
            Syntax.const @{const_syntax guards} $ mk_singleton_guard @{const_syntax False} g $ new
      end
  | guarded_NNew_tr _ ts = raise TERM ("guarded_NNew_tr", ts);


fun guarded_While_tr ctxt (ts as [b,I,V,c]) =
      let
        val guard = Hoare.generate_guard ctxt;
        val cnd as Abs (_, _, b') = quote_tr ctxt antiquoteCur b;
        val b'' = Syntax.const @{const_syntax Collect} $ cnd;
      in
        case guard b' of
          NONE => Syntax.const @{const_syntax whileAnno} $ b'' $ I $ V $ c
        | SOME g =>
            Syntax.const @{const_syntax whileAnnoG} $
              mk_singleton_guard @{const_syntax False} g $ b'' $ I $ V $ c
      end
  | guarded_While_tr _ ts = raise Match;

fun guarded_WhileFix_tr ctxt (ts as [b as (_ $ Abs (_, _, b')), I, V, c]) =
      let
        val guard = Hoare.generate_guard ctxt;
      in
        case guard b' of
          NONE => Syntax.const @{const_syntax whileAnnoFix} $ b $ I $ V $ c
        | SOME g =>
            Syntax.const @{const_syntax whileAnnoGFix} $
              mk_singleton_guard @{const_syntax False} g $ b $ I $ V $ c
      end
  | guarded_WhileFix_tr _ ts = raise Match;

fun guarded_Cond_tr ctxt (ts as [b, c, d]) =
      let
        val guard = Hoare.generate_guard ctxt;
        val cnd as Abs (_, _, b') = quote_tr ctxt @{syntax_const "_antiquoteCur"} b;
        val cond =
          Syntax.const @{const_syntax Cond} $ (Syntax.const @{const_syntax Collect} $ cnd) $ c $ d;
      in
        case guard b' of
          NONE => cond
        | SOME g =>
            Syntax.const @{const_syntax guards} $ mk_singleton_guard @{const_syntax False} g $ cond
      end
  | guarded_Cond_tr _ ts = raise Match;


(* parsing procedure calls *)

fun dest_pars (Const (@{syntax_const "_par"}, _) $ p) = [p]
  | dest_pars (Const (@{syntax_const "_pars"}, _) $ p $ ps) = dest_pars p @ dest_pars ps
  | dest_pars t = raise TERM ("dest_pars", [t]);

fun dest_actuals (Const (@{syntax_const "_actuals_empty"}, _)) = []
  | dest_actuals (Const (@{syntax_const "_actuals"}, _) $ pars) = dest_pars pars
  | dest_actuals t = raise TERM ("dest_actuals", [t]);


fun mk_call_tr ctxt grd Call formals pn pt actuals has_args cont =
  let
    val fcall = cont <> NONE;
    val state_kind =
      the_default (Hoare.get_default_state_kind ctxt)
        (Hoare.get_state_kind pn ctxt);
    fun init_par_tr name arg =
      update_comp ctxt [] false false name (antiquoteCur_tr ctxt arg);

    fun result_par_tr name arg =
      let
        fun offset_old n = 2;
        fun offset n = if is_global ctxt n then 0 else 2;
      in
        update_tr ctxt [pn] offset offset_old
          (lookup_comp ctxt [] name (Bound 1)) arg
      end;

    val _ = if not (StateSpace.get_silent (Context.Proof ctxt)) andalso
               ((not fcall andalso length formals <> length actuals)
                 orelse
                (fcall andalso length formals <> length actuals + 1))
            then raise
                TERM ("call_tr: number of formal (" ^ string_of_int (length formals) ^
                      ") and actual (" ^ string_of_int (length actuals) ^
                      ") parameters for \"" ^ unsuffix Hoare.proc_deco pn ^
                      "\" do not match.", [])
            else ();

    val globals =
      [Syntax.const globals_updateN $ (K_rec_syntax (Const (globalsN, dummyT) $ Bound 0))];
    val ret = Abs ("s", dummyT, Abs ("t", dummyT, Library.foldr (op $) (globals, Bound 1)));

    val val_formals = filter (fn (kind, _) => kind = Hoare.In) formals;
    val res_formals = filter (fn (kind, _) => kind = Hoare.Out) formals;

    val (val_actuals, res_actuals) = chop (length val_formals) actuals;
    val init_bdy =
      let
        val state =
          (case state_kind of
            Hoare.Record => Bound 0
          | Hoare.Function => Syntax.const localsN $ Bound 0);
        val upds = fold2 (fn (_, name) => init_par_tr name) val_formals val_actuals state;
      in
        (case state_kind of
          Hoare.Record => upds
        | Hoare.Function => Syntax.const locals_updateN $ K_rec_syntax upds $ Bound 0)
      end;
    val init = Abs ("s", dummyT, init_bdy);


    val call =
      (case cont of
        NONE => (* Procedure call *)
            let
              val results =
                map (fn ((_, name), arg) => result_par_tr name arg)
                  (rev (res_formals ~~ res_actuals));
              val res =
                Abs ("i", dummyT, Abs ("t", dummyT,
                    Syntax.const @{const_syntax Basic} $
                      Abs ("s", dummyT, fold_rev (fn f => fn s => f s) results (Bound 0))));
            in if has_args then Call $init $ pt $ ret $ res else Call $ pt end
        | SOME c => (* Function call *)
            let
              val res =
                (case res_formals of
                  [(_, n)] => Abs ("s", dummyT, lookup_comp ctxt [] n (Bound 0))
                | _ =>
                    if StateSpace.get_silent (Context.Proof ctxt)
                    then Abs ("s", dummyT, lookup_comp ctxt [] "dummy" (Bound 0))
                    else raise TERM ("call_tr: function " ^ pn ^ "may only have one result parameter", []));
            in Call $ init $ pt $ ret $ res $ c end)
    val guard = Hoare.generate_guard  ctxt;
  in
    if grd
    then
      (case fold_rev (fn arg => fn g => guard (antiquoteCur_tr ctxt arg) & g)
          (res_actuals @ val_actuals) NONE of
        NONE => call
      | SOME g =>
          Syntax.const @{const_syntax guards} $ mk_singleton_guard @{const_syntax False} g $ call)
    else call
  end;


(* FIXME: What is prfx for, maybe unused *)
fun dest_procname ctxt prfx false (Const (p, _)) =
      (prfx ^ suffix Hoare.proc_deco p, mk_string (String.explode p))
  | dest_procname ctxt prfx false (t as Free (p, T)) =
      (prfx ^ suffix Hoare.proc_deco p, Free (suffix Hoare.proc_deco p, T))
  | dest_procname ctxt prfx false (Const (@{syntax_const "_free"},_) $ Free (p,T)) =
      (prfx ^ suffix Hoare.proc_deco p, Free (suffix Hoare.proc_deco p, T))
  | dest_procname ctxt prfx false (t as (Const (@{syntax_const "_antiquoteCur"},_) $ Const (p, _))) =
      (prfx ^ Hoare.resuffix Hoare.deco Hoare.proc_deco p, t)
  | dest_procname ctxt prfx false (t as (Const (@{syntax_const "_antiquoteCur"}, _) $ Free (p, _))) =
      (prfx ^ Hoare.resuffix Hoare.deco Hoare.proc_deco p, t)
  | dest_procname ctxt prfx false (t as Const (p, _) $ _) =
      (prfx ^ Hoare.resuffix Hoare.deco Hoare.proc_deco p, t) (* antiquoteOld *)
  | dest_procname ctxt prfx false (t as Free (p,_)$_)  =
      (prfx ^ Hoare.resuffix Hoare.deco Hoare.proc_deco p, t) (* antiquoteOld *)
  | dest_procname ctxt prfx false (t as Const (@{syntax_const "_antiquoteOld"}, _) $ _ $ Const (p, _)) =
      (prfx ^ suffix Hoare.proc_deco p, t)
  | dest_procname ctxt prfx false (t as Const (@{syntax_const "_antiquoteOld"}, _) $ _ $ Free (p,_)) =
      (prfx ^ suffix Hoare.proc_deco p, t)
  (* FIXME StateFun.lookup !? *)
  | dest_procname ctxt prfx false (t as Const (@{const_name "StateFun.lookup"}, _) $ _ $ Free (p, _) $ _) =
      (prfx ^ suffix Hoare.proc_deco (Hoare.remdeco' p), t) (* antiquoteOld *)

  | dest_procname ctxt prfx false t = (prfx, t)
  | dest_procname ctxt prfx true t =
      let fun quote t = Abs ("s", dummyT, antiquoteCur_tr ctxt t)
      in
        (case quote t of
          (t' as Abs (_, _, Free (p, _) $ Bound 0)) =>
            (prfx ^ Hoare.resuffix Hoare.deco Hoare.proc_deco p, t')
        (* FIXME StateFun.lookup !? *)
        | (t' as Abs (_, _, Const (@{const_name "StateFun.lookup"}, _) $ _ $ Free (p, _) $ (_ $ Bound 0))) =>
            (prfx ^ suffix Hoare.proc_deco (Hoare.remdeco' p), t')
        | t' => (prfx, t'))
      end

fun gen_call_tr prfx dyn grd ctxt p actuals has_args cont =
  let
    fun Call false true NONE = Const (@{const_syntax call}, dummyT)
      | Call false false NONE = Const (@{const_syntax Call}, dummyT)
      | Call true true NONE = Const (@{const_syntax dynCall}, dummyT)
      | Call false true (SOME c) = Const (@{const_syntax fcall}, dummyT)
      | Call _ _ _ = raise TERM ("gen_call_tr: no proper procedure call", []);

    val (pn, pt) = dest_procname ctxt prfx dyn (Term_Position.strip_positions p);
  in
    (case Hoare.get_params pn ctxt of
      SOME formals =>
        mk_call_tr ctxt grd (Call dyn has_args cont) formals pn pt actuals has_args cont
    | NONE =>
        if StateSpace.get_silent (Context.Proof ctxt)
        then mk_call_tr ctxt grd (Call dyn has_args cont) [] pn pt [] has_args cont
        else raise TERM ("gen_call_tr: procedure " ^ quote pn ^ " not defined", []))
  end;

fun call_tr dyn grd ctxt [p, actuals] =
      gen_call_tr "" dyn grd ctxt p (dest_actuals actuals) true NONE
  | call_tr _ _ _  t = raise TERM ("call_tr", t);

fun call_ass_tr dyn grd ctxt [l, p, actuals] =
      gen_call_tr "" dyn grd ctxt p (dest_actuals actuals @ [l]) true NONE
  | call_ass_tr  _ _ _ t = raise TERM ("call_ass_tr", t);

fun proc_tr ctxt [p, actuals] =
      gen_call_tr "" false false ctxt p (dest_actuals actuals) false NONE
  | proc_tr _  t = raise TERM ("proc_tr", t);

fun proc_ass_tr ctxt [l, p, actuals] =
      gen_call_tr "" false false ctxt p (dest_actuals actuals @ [l]) false NONE
  | proc_ass_tr _ t = raise TERM ("proc_ass_tr", t);

fun fcall_tr ctxt [p, actuals, c] =
      gen_call_tr "" false false ctxt p (dest_actuals actuals) true (SOME c)
  | fcall_tr _ t = raise TERM ("fcall_tr", t);


(* printing procedure calls *)

fun upd_tr' ctxt (x_upd, T) =
  (case try (unsuffix' Record.updateN) x_upd of
    SOME x =>
      (Hoare.chopsfx Hoare.deco (Hoare.extern ctxt x),
       if T = dummyT then T else Term.domain_type T)
  | NONE =>
      (case try (unsuffix Hoare.deco) x_upd of
        SOME _ => (Hoare.remdeco ctxt x_upd, T)
      | NONE => raise Match));


fun update_name_tr' ctxt (Free x) = Const (upd_tr' ctxt x)
  | update_name_tr' ctxt ((c as Const (@{syntax_const "_free"}, _)) $ Free x) =
      (*c $*) Const (upd_tr' ctxt x)
  | update_name_tr' ctxt (Const x) = Const (upd_tr' ctxt x)
  | update_name_tr' _ _ = raise Match;

fun term_name_eq (Const (x, _)) (Const (y, _)) = (x = y)
  | term_name_eq (Free (x, _)) (Free (y, _)) = (x = y)
  | term_name_eq (Var (x, _)) (Var (y, _)) = (x = y)
  | term_name_eq (a $ b) (c $ d) = term_name_eq a c andalso term_name_eq b d
  | term_name_eq (Abs (s, _, a)) (Abs (t, _, b)) = (s = t) andalso term_name_eq a b
  | term_name_eq _ _ = false;

fun list_update_tr' l (r as Const (@{const_syntax list_update},_) $ l' $ i $ e) =
      if term_name_eq l l'
      then
        let
          fun sel_arr a [i] (Const (@{const_syntax nth},_) $ a' $ i') =
                term_name_eq a a' andalso i = i'
            | sel_arr a (i::is) (Const (@{const_syntax nth},_) $ sel $ i') =
                i = i' andalso sel_arr a is sel
            | sel_arr _ _ _ = false;

          fun tr' a idxs (e as Const (@{const_syntax list_update}, _) $ sel $ i $ e') =
                if sel_arr a idxs sel then tr' a (i :: idxs) e'
                else (idxs, e)
            | tr' _ idxs e = (idxs, e);

          val (idxs, e') = tr' l [i] e;
          val lft = fold_rev (fn i => fn arr => Syntax.const @{const_syntax nth} $ arr $ i) idxs l;
        in (lft,e') end
      else (l, r)
  | list_update_tr' l r  = (l, r);

fun list_mult_update_tr' l (r as Const (@{const_syntax list_multupd},_) $ var $ idxs $ values) =
      (Syntax.const @{const_syntax list_multsel} $ var $ idxs, values)
  | list_mult_update_tr' l r = (l, r);

fun update_tr' l (r as Const (@{const_syntax fun_upd}, _) $
        (hp as (Const (@{syntax_const "_antiquoteCur"}, _) $ _)) $ p $ value) =
      if term_name_eq l hp then
        (case value of
          (Const (@{const_syntax list_update}, _) $ _ $ _ $ _) => list_update_tr' (l $ p) value
        | (Const (@{const_syntax list_multupd},_) $ _ $ _ $ _) => list_mult_update_tr' (l $ p) value
        | _ => (l $ p, value))
      else (l, r)
  | update_tr' l (r as Const (@{const_syntax list_update},_) $
        (var as (Const (@{syntax_const "_antiquoteCur"}, _) $ _)) $ i $ value) =
      if term_name_eq l var then list_update_tr' l r else (l, r)
  | update_tr' l (r as Const (@{const_syntax list_multupd}, _) $
        (var as (Const (@{syntax_const "_antiquoteCur"}, _) $ _)) $ idxs $ values) =
      if term_name_eq l var then list_mult_update_tr' l r else (l, r)
  | update_tr' l r = (l, r);


fun dest_K_rec (Abs (_, _, v)) =
      if member (op =) (loose_bnos v) 0 then NONE else SOME (incr_boundvars ~1 v)
  | dest_K_rec (Abs (_, _, Abs (_, _, v) $ Bound 0)) = (* eta expanded version *)
      let val lbv = loose_bnos v;
      in if member (op =) lbv 0 orelse member (op =) lbv 1
         then NONE else SOME (incr_boundvars ~2 v)
      end
  | dest_K_rec _ = NONE;

local
fun uncover (upd,v) =
  (case (upd, v) of
    (Const (cupd, _), upd' $ dest $ constr $ n $ (Const (@{const_syntax K_statefun}, _) $ v') $ s) =>
      if member (op =) [globals_updateN, locals_updateN] (Long_Name.base_name cupd)
      then (case s of (Const (g, _) $ _) =>
               if member (op =) [localsN, globalsN] (Long_Name.base_name g)
               then (n, v')
               else raise Match
             | _ => raise Match)
       else (upd, v)
  | (Const (gupd, _), upd' $ k $ s) =>
      (case dest_K_rec k of
        SOME v' =>
          if Long_Name.base_name gupd = globals_updateN
          then
            (case s of
              Const (gl, _) $ _ =>
                if Long_Name.base_name gl = globalsN (* assignment *)
                then (upd',v')
                else raise Match
            | _ => raise Match)
          else (upd, v)
      | _ => (upd, v))
  | (Const (upd_glob, _), upd' $ v') =>
      if Long_Name.base_name upd_glob = upd_globalsN (* result parameter *)
      then (upd', v') else (upd, v)
  | _ => (upd, v));
in

fun global_upd_tr' upd k =
  (case dest_K_rec k of
    SOME v => uncover (upd, v)
  | NONE => uncover (upd, k));

end;


fun dest_updates (t as (upd as Const (u, _)) $ k $ state) =
      (case dest_K_rec k of
        SOME value =>
          if member (op =) [globals_updateN, locals_updateN] (Long_Name.base_name u)
          then dest_updates value
          else if can (unsuffix Record.updateN) u orelse Long_Name.base_name u = upd_globalsN
          then (upd,value)::dest_updates state
          else raise Match
      | NONE => raise Match)
  | dest_updates (t as (upd as Const (u,_))$k) =
      (case dest_K_rec k of
        SOME value =>
          if member (op =) [globals_updateN, locals_updateN] (Long_Name.base_name u)
          then dest_updates value
          else if can (unsuffix Record.updateN) u orelse Long_Name.base_name u = upd_globalsN
          then [(upd,value)]
          else if Long_Name.base_name u = globalsN then [] else raise Match
      | NONE => []) (* t could be just (globals $ s) *)
  | dest_updates ((Const (u, _)) $ _ $ _ $ n $ (Const (@{const_syntax K_statefun},_) $ value) $ state) =
      if Long_Name.base_name u = Long_Name.base_name StateFun.updateN
      then (n, value) :: dest_updates state
      else raise Match
  | dest_updates t = [];

(* FIXME: externalize names properly before removing decoration! *)
fun init_tr' ctxt [Abs (_,_,t)] =
  let
    val upds  =
      case dest_updates t of
        us as [(Const (gupd, _), v)] =>
          if Long_Name.base_name gupd = globals_updateN
          then dest_updates v else us
      | us => us;

    val comps =
      map (fn (Const (u, _)) => Symbol.explode (unsuffix (Hoare.deco ^ Record.updateN) u))
        (map fst upds);
    val prfx = maxprefixs (op =) comps;

    fun dest_list (Const (@{const_syntax Nil}, _)) = []
      | dest_list (Const (@{const_syntax Cons}, _) $ x $ xs) = x :: dest_list xs
      | dest_list t = [t];

    fun mk_set [] = Syntax.const @{const_syntax Set.empty}
      | mk_set (x :: xs) = Syntax.const @{const_syntax insert} $ x $ mk_set xs;

    val l = length prfx;
    val _ = if l <= 1 then raise Match else ();
    val comp = mk_list (map (Syntax.const o implode o drop l) comps);
    val vals = map mk_set (transpose (map (dest_list o snd) upds));
    val v = case vals of [v] => v | vs => mk_list vs;
  in
    Syntax.const @{syntax_const "_Init"} $
      Syntax.const (implode (fst (split_last prfx))) $ comp $ v
  end;


local
fun tr' ctxt c (upd,v) =
  let
    val l = Syntax.const antiquoteCur $ update_name_tr' ctxt upd;
    val r = quote_tr' ctxt antiquoteCur (Abs ("s", dummyT, v));
    val (l', r') = update_tr' l r;
  in (c $ l' $ r') end;

in
fun app_assign_tr' c ctxt (Abs (s, _, upd $ v $ Bound 0) :: ts) =
      tr' ctxt c (global_upd_tr' upd v)
  | app_assign_tr' c ctxt ((upd $ v) :: ts) =
      (case upd of
        u $ v => raise Match
      | _ => tr' ctxt c (global_upd_tr' upd v))
  | app_assign_tr' _ _ _ = raise Match;
end;

val assign_tr' = app_assign_tr' (Syntax.const @{syntax_const "_Assign"});
val raise_tr' = app_assign_tr' (Syntax.const @{syntax_const "_raise"});

fun split_Let' ((l as Const (@{const_syntax Let'}, _)) $ x $ t) =
      let val (recomb,t') = split_Let' t
      in (fn t => l $ x $ recomb t, t') end
  | split_Let' (Abs (x, T, t)) =
     let val (recomb, t') = split_Let' t
     in if t' = t
        then (I, t') (* Get rid of last abstraction *)
        else (fn t => Abs (x, T, recomb t), t')
     end
  | split_Let' ((s as Const (@{const_syntax case_prod},_)) $ t) =
     let val (recomb, t') = split_Let' t
     in (fn t => s $ recomb t, t') end
  | split_Let' t = (I, t)

fun basic_tr' ctxt [Abs (s, T, t)] =
  let
    val (has_let, t') =
      case t of
        ((t' as (Const (@{const_syntax Let'},_) $ _ $ _)) $ Bound 0) => (true, t')
      | _ => (false, t);
    val (recomb, t'') = split_Let' t';
    val upds = dest_updates t'';
    val _ = if length upds <= 1 andalso not has_let then raise Match else ();
    val ass =
      map (fn (u, v) => app_assign_tr' (Syntax.const @{syntax_const "_BAssign"}) ctxt
            [Abs ("s",dummyT,u$v$Bound 0)]) upds;
    val basics = foldr1 (fn (x, ys) => Syntax.const @{syntax_const "_basics"} $ x $ ys) (rev ass);
  in
    Syntax.const @{syntax_const "_Basic"} $
      quote_tr' ctxt @{syntax_const "_antiquoteCur"} (Abs (s, T, recomb basics))
  end;

fun loc_tr' ctxt [init, bdy, return, c] =
      (let
        val upds =
          (case init of
            Abs (_, _, t as (upd $ v $ s)) => dest_updates t
          | upd $ v => dest_updates (upd $ v $ Bound 0)
          | _ => raise Match);

        fun mk_locinit c v =
          Syntax.const @{syntax_const "_locinit"} $
            Syntax.const c $ quote_tr' ctxt antiquoteCur (Abs ("s", dummyT, v));

        fun init_or_not c c' v =
          if c = c' then
            Syntax.const @{syntax_const "_locnoinit"} $ Syntax.const (Hoare.remdeco ctxt c')
          else mk_locinit (Hoare.remdeco ctxt c) v;

        fun mk_init (Const (c, _), (v as (Const (c', _) $ Bound 0))) =
              init_or_not (unsuffix' Record.updateN c) c' v
          | mk_init (Const (c, _), v) =
              mk_locinit (unsuffix' (Hoare.deco ^ Record.updateN) (Hoare.extern ctxt c)) v
          | mk_init ((f as Const (@{syntax_const "_free"}, _)) $ Free (c, _), v) =
              (case v of
                Const (lookup, _) $ _ $
                  (Const (@{syntax_const "_free"}, _) $ Free (c', _)) $
                  (Const (locals,_) $ Bound 0) =>
                if Long_Name.base_name lookup = Long_Name.base_name StateFun.lookupN
                  andalso Long_Name.base_name locals = localsN
                then init_or_not c c' v
                else mk_locinit (Hoare.remdeco' c) v
              | _ => mk_locinit (Hoare.remdeco' c) v)
          | mk_init _ = raise Match;

        val inits =
          foldr1 (fn (t, u) => Syntax.const @{syntax_const "_locinits"} $ t $ u)
            (map mk_init (rev upds));
      in Syntax.const @{syntax_const "_Loc"} $ inits $ bdy end handle Fail _ => raise Match)
  | loc_tr' _ _ = raise Match;


fun actuals_tr' acts =
  (case acts of
    [] => Syntax.const @{syntax_const "_actuals_empty"}
  | xs => Syntax.const @{syntax_const "_actuals"} $
        foldr1 (fn (l, r) => (Syntax.const @{syntax_const "_pars"} $ l $ r)) xs);


fun gen_call_tr' ctxt Call CallAss init p return c =
  let
    fun get_init_updates (Abs (s, _, upds)) = dest_updates upds
      | get_init_updates upds = dest_updates upds;

    fun get_res_updates (Abs (i, _, Abs (t, _, Const (@{const_syntax Basic}, _) $ Abs (s, _, upds)))) =
          dest_updates upds
      | get_res_updates (Abs (i, _, Abs (t, _, Const (@{const_syntax Basic}, _) $ upds))) =
          dest_updates upds
      | get_res_updates _ = raise Match;

      fun init_par_tr' par =
        Syntax.const @{syntax_const "_par"} $ quote_tr' ctxt antiquoteCur (Abs ("s", dummyT, par));
      val init_actuals =
        map (fn (_, value) => init_par_tr' value) (rev (get_init_updates init));

      fun tr' c (upd, v) =
        let
          val l = Syntax.const antiquoteCur $ update_name_tr' ctxt upd;
          val r =
            quote_tr' ctxt antiquoteCur
              (quote_tr' ctxt antiquoteCur
                (quote_tr' ctxt antiquoteCur
                  (Abs ("i", dummyT, Abs ("t", dummyT, Abs ("s", dummyT, v))))));
          val (l', _) = update_tr' l r;
        in c $ l' end;

      fun ret_par_tr' (upd, v) =
        tr' (Syntax.const @{syntax_const "_par"}) (global_upd_tr' upd v);

      val res_updates = rev (get_res_updates c);
      val res_actuals = map ret_par_tr' res_updates;
  in if Config.get ctxt use_call_tr' then
        (case res_actuals of
          [l] => CallAss $ l $ p $ actuals_tr' init_actuals
         | _ => Call $ p $ actuals_tr' (init_actuals @ res_actuals))
     else raise Match
  end;

fun gen_fcall_tr' ctxt init p return result c =
  let
    fun get_init_updates (Abs (s, _, upds)) = dest_updates upds
      | get_init_updates _ = raise Match;

    fun init_par_tr' par =
      Syntax.const @{syntax_const "_par"} $ quote_tr' ctxt antiquoteCur (Abs ("s", dummyT, par));
    val init_actuals =
      map (fn (_, value) => init_par_tr' value) (rev (get_init_updates init));

    val (v, c') =
      (case c of
        Abs abs => Syntax_Trans.atomic_abs_tr' abs
      | _ => raise Match);
  in
    if Config.get ctxt use_call_tr' then
      Syntax.const @{syntax_const "_FCall"} $ p $ actuals_tr' init_actuals $ v $ c'
    else raise Match
  end;


fun pname_tr' ctxt ((f as Const (@{syntax_const "_free"}, _)) $ Free (p, T)) =
      (*f$*) Const (unsuffix' Hoare.proc_deco p, T)
  | pname_tr' ctxt (Free (p, T)) = Const (unsuffix' Hoare.proc_deco p, T)
  | pname_tr' ctxt p =
      let
        (* from HOL strings to ML strings *)
        fun dest_nib c =    (* FIXME authentic syntax *)
          (case raw_explode c of
            ["N", "i", "b", "b", "l", "e", h] =>
              if "0" <= h andalso h <= "9" then ord h - ord "0"
              else if "A" <= h andalso h <= "F" then ord h - ord "A" + 10
              else raise Match
          | _ => raise Match);

        fun dest_chr (Const (@{const_syntax Char},_) $ Const (c1, _) $ Const (c2,_)) =
              let val c = Char.chr (dest_nib c1 * 16 + dest_nib c2)
              in if Char.isPrint c then c else raise Match end
          | dest_chr _ = raise Match;

        fun dest_string (Const (@{const_syntax Nil}, _)) = []
          | dest_string (Const (@{const_syntax Cons}, _) $ c $ cs) = dest_chr c :: dest_string cs
          | dest_string _ = raise Match;
        in
          (case try dest_string p of
            SOME name => Syntax.const (String.implode name)
          | NONE => antiquote_mult_tr' ctxt (K true) antiquoteCur antiquoteOld p)
        end;

fun call_tr' ctxt [init, p, return, result] =
      gen_call_tr' ctxt
        (Const (@{syntax_const "_Call"}, dummyT))
        (Const (@{syntax_const "_CallAss"}, dummyT)) init (pname_tr' ctxt p) return result
  | call_tr' _ _ = raise Match;


fun dyn_call_tr' ctxt [init, p, return, result] =
      let val p' = quote_tr' ctxt antiquoteCur p
      in
        gen_call_tr' ctxt
          (Const (@{syntax_const "_DynCall"}, dummyT))
          (Const (@{syntax_const "_DynCallAss"}, dummyT)) init p' return result
      end
  | dyn_call_tr' _ _ = raise Match;

fun proc_tr' ctxt [p] =
      let
        val p' = pname_tr' ctxt p;
        val pn = fst (dest_procname ctxt "" false p');
        val formals = the (Hoare.get_params pn ctxt) handle Option.Option => raise Match;
        val val_formals = map_filter (fn (Hoare.In, p) => SOME p | _ => NONE) formals;
        val res_formals = map_filter (fn (Hoare.Out, p) => SOME p | _ => NONE) formals;
        fun mkpar n =
          Syntax.const @{syntax_const "_par"} $
            (Syntax.const antiquoteCur $ Syntax.const (Hoare.remdeco ctxt n));
      in
        if not (print_mode_active "NoProc")
        then
          (case res_formals of
            [r] =>
              Syntax.const @{syntax_const "_ProcAss"} $
                (Syntax.const antiquoteCur $
                  Syntax.const (Hoare.remdeco ctxt r)) $
                p' $ actuals_tr' (map mkpar val_formals)
          | _ =>
              Syntax.const @{syntax_const "_Proc"} $ p' $
                actuals_tr' (map mkpar (val_formals @ res_formals)))
         else raise Match
      end
  | proc_tr' _ _ = raise Match;

fun fcall_tr' ctxt [init, p, return, result, c] =
      gen_fcall_tr' ctxt init (pname_tr' ctxt p) return result c
  | fcall_tr' _ _ = raise Match;


(* misc. print translations *)

fun assert_tr' ctxt ((t as Abs (_, _, p)) :: ts) =
      let
        fun selector (Const (c, T)) = Hoare.is_state_var c
          | selector (Const (l, _) $ _ $ _) =
              Long_Name.base_name l = Long_Name.base_name StateFun.lookupN
          | selector t = false;

        fun fix_state (Const (@{const_syntax HOL.eq},_) $ (Const (@{syntax_const "_free"}, _) $ _)) = true
          | fix_state (Const (@{const_syntax HOL.eq},_) $ (Const (@{syntax_const "_bound"}, _) $ _)) = true
          | fix_state (Const (@{const_syntax HOL.eq},_) $ (Const (@{syntax_const "_var"}, _) $ _)) = true
          | fix_state (Const (@{const_syntax HOL.eq},_) $ Free _) = true
          | fix_state (Const (@{const_syntax HOL.eq},_) $ Bound _) = true
          | fix_state (Const (@{const_syntax HOL.eq},_) $ Var _) = true
          | fix_state _ = false;
      in
        if antiquote_applied_only_to (fn t => selector t orelse fix_state t) p
          andalso not (print_mode_active "NoAssertion")
        then app_quote_mult_tr' ctxt selector (Syntax.const @{syntax_const "_Assert"}) (t :: ts)
        else raise Match
      end
  | assert_tr' _ _ = raise Match


fun bexp_tr' name ctxt ((Const (@{const_syntax Collect}, _) $ t) :: ts) =
      app_quote_tr' ctxt (Syntax.const name) (t :: ts)
  | bexp_tr' _ _ _ = raise Match;



fun new_tr' ctxt
        [Abs (s,_,
          Const (@{const_syntax If}, _) $
          (Const (@{const_syntax Orderings.less_eq},_) $ size $ free) $
          (upd $ new $ (gupd $ Abs (_, _, inits_free_alloc) $ Bound 0)) $
          (upd' $ null $ Bound 0))] =
      let
        fun mk_init (Const (upd, _), Const (@{const_syntax fun_upd},_) $ _ $ _ $ v) =
              let val var = unsuffix' Hoare.deco
                (unsuffix' Record.updateN (Hoare.extern ctxt upd))
              in Syntax.const @{syntax_const "_newinit"} $ Syntax.const var $ v end
          | mk_init ((f as Const (@{syntax_const "_free"}, _)) $
                Free (var, T), Const (@{const_syntax fun_upd},_) $ _ $ _ $ v) =
              Syntax.const @{syntax_const "_newinit"} $
                (f $ Free (Hoare.remdeco' var, T)) $ v;

        val inits_free_allocs = dest_updates inits_free_alloc;

        val inits = map mk_init (take (length inits_free_allocs - 2) (inits_free_allocs));
        val inits' =
          foldr1 (fn (t1, t2) => Syntax.const @{syntax_const "_newinits"} $ t1 $ t2) (rev inits);

        fun tr' (upd, v) =
          let
            val l = Syntax.const antiquoteCur $ update_name_tr' ctxt upd;
            val r = quote_tr' ctxt antiquoteCur (Abs (s, dummyT, v));
            val (l', r') = update_tr' l r
          in l' end;

        val l = tr' (global_upd_tr' upd' null);

      in Syntax.const @{syntax_const "_New"} $ l $ size $ inits' end
  | new_tr' _ _ = raise Match;

fun nnew_tr' ctxt
        [Const (@{const_syntax if_rel},_) $
          (Abs (s, _, Const (@{const_syntax Orderings.less_eq}, _) $ size $ free)) $
          (Abs (_, _, upd $ new $ (gupd $ (Abs (_, _, free_inits_alloc)) $ Bound 0))) $
          (Abs (_, _, (upd' $ null $ Bound 0))) $ _] =
      let
        fun mk_init (Const (upd, _), Const (@{const_syntax fun_upd}, _) $ _ $ _ $ v) =
              let val var = unsuffix' Hoare.deco
                (unsuffix' Record.updateN (Hoare.extern ctxt upd))
              in Syntax.const @{syntax_const "_newinit"} $ Syntax.const var $ v end
          | mk_init ((f as Const (@{syntax_const "_free"}, _)) $ Free (var, T),
                Const (@{const_syntax fun_upd}, _) $_ $ _ $ v) =
              Syntax.const @{syntax_const "_newinit"} $
                (f $ Free (Hoare.remdeco' var, T)) $ v;

        val free_inits_allocs = dest_updates free_inits_alloc;

        val inits = map mk_init (take (length free_inits_allocs - 2) (tl free_inits_allocs));
        val inits' =
          foldr1 (fn (t1, t2) => Syntax.const @{syntax_const "_newinits"} $ t1 $ t2) (rev inits);

        fun tr' (upd, v) =
          let
            val l = Syntax.const antiquoteCur $ update_name_tr' ctxt upd;
            val r = quote_tr' ctxt antiquoteCur (Abs (s, dummyT, v));
            val (l', r') = update_tr' l r;
          in l' end;

        val l = tr' (global_upd_tr' upd' null);

      in Syntax.const @{syntax_const "_NNew"} $ l $ size $ inits' end
  | nnew_tr' _ _ = raise Match;


fun switch_tr' ctxt [v, vs] =
  let
    fun case_tr' (Const (@{const_syntax Pair}, _) $ V $ c) =
          Syntax.const @{syntax_const "_switchcase"} $ V $ c
      | case_tr' _ = raise Match;

    fun dest_list (Const (@{const_syntax Nil}, _)) = []
      | dest_list (Const (@{const_syntax Cons}, _) $ x $ xs) = x :: dest_list xs
      | dest_list t = raise Match;

    fun ltr' [] = raise Match
      | ltr' [Vc] = Syntax.const @{syntax_const "_switchcasesSingle"} $ case_tr' Vc
      | ltr' (Vc :: xs) = Syntax.const @{syntax_const "_switchcasesCons"} $ case_tr' Vc $ ltr' xs;

   in app_quote_tr' ctxt (Syntax.const @{syntax_const "_Switch"}) (v :: [ltr' (dest_list vs)]) end;

fun bind_tr' ctxt [e, Abs abs] =
      let
        val (v, c) = Syntax_Trans.atomic_abs_tr' abs;
        val e' =
          case e of
            Abs a => e
          | t as Const _ => Abs ("s", dummyT, t $ Bound 0)
          | _ => raise Match;
      in app_quote_tr' ctxt (Syntax.const @{syntax_const "_Bind"}) [e', v, c] end
  | bind_tr' _ _ = raise Match;


local
  fun dest_list (Const (@{const_syntax Nil}, _)) = []
    | dest_list (Const (@{const_syntax Cons}, _) $ x $ xs) = x :: dest_list xs
    | dest_list _ = raise Match;

  fun guard_tr' fg =
    let val (flag, g) = HOLogic.dest_prod fg
    in
      if flag aconv @{term True} then Syntax.const @{syntax_const "_guarantee"} $ g
      else if flag aconv @{term False} then g
      else fg
    end handle TERM _ => fg;

  fun guards_lst_tr' [fg] = guard_tr' fg
    | guards_lst_tr' (t :: ts) =
        Syntax.const @{syntax_const "_grds"} $ guard_tr' t $ guards_lst_tr' ts
    | guards_lst_tr' [] = raise Match;

  fun cond_guards_lst_tr' ctxt ts =
    if Config.get ctxt hide_guards then Syntax.const @{syntax_const "_hidden_grds"}
    else guards_lst_tr' ts;
in
  fun guards_tr' ctxt [gs, c] =
        Syntax.const @{syntax_const "_guards"} $ cond_guards_lst_tr' ctxt (dest_list gs) $ c
    | guards_tr' _ _ = raise Match;

  fun whileAnnoG_tr' ctxt [gs, cond as (Const (@{const_syntax Collect}, _) $ b), I, V, c] =
        let
          val b' =
            (case assert_tr' ctxt [b] of
              Const (@{syntax_const "_Assert"}, _) $ b' => b'
            | _ => cond) handle Match => cond;

        in
          Syntax.const @{syntax_const "_While_guard_inv_var"} $
            cond_guards_lst_tr' ctxt (dest_list gs) $ b' $ I $ V $
            (Syntax.const @{syntax_const "_DoPre"} $ c)
        end
    | whileAnnoG_tr' _ _ = raise Match;

  fun whileAnnoGFix_tr' ctxt [gs, cond as (Const (@{const_syntax Collect}, _) $ b), I, V, c] =
    let
      val b' =
        (case assert_tr' ctxt [b] of
          Const (@{syntax_const "_Assert"}, _) $ b' => b'
        | _ => cond) handle Match => cond;
    in
      (case maps strip_abs_vars [I, V, c] of
        [] => raise Match
      | ((x, T) :: xs) =>
          let
            val (x', I') = Syntax_Trans.atomic_abs_tr' (x, T, strip_abs_body I);
            val (_ , V') = Syntax_Trans.atomic_abs_tr' (x, T, strip_abs_body V);
            val (_ , c') = Syntax_Trans.atomic_abs_tr' (x, T, strip_abs_body c);
          in
            Syntax.const @{syntax_const "_WhileFix_guard_inv_var"} $
              cond_guards_lst_tr' ctxt (dest_list gs) $ b' $ x' $ I' $ V' $
              (Syntax.const @{syntax_const "_DoPre"} $ c')
          end)
    end;
end


end;
