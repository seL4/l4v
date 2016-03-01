(*  Title:      generalise_state.ML

    Author:     Norbert Schirmer, TU Muenchen

Copyright (C) 2005-2007 Norbert Schirmer 

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


signature SPLIT_STATE =
sig
  val isState: term -> bool
  val abs_state: term -> term option
  val abs_var: Proof.context -> term -> (string * typ)
  val split_state: Proof.context -> string -> typ -> term -> (term * term list)
  val ex_tac: Proof.context -> term list -> tactic
    (* the term-list is the list of selectors as
       returned by split_state. They may be used to
       construct the instatiation of the existentially
       quantified state.
    *)
end;

functor GeneraliseFun (structure SplitState: SPLIT_STATE) =
struct

val genConj = @{thm generaliseConj};
val genImp = @{thm generaliseImp};
val genImpl = @{thm generaliseImpl};
val genAll = @{thm generaliseAll};
val gen_all = @{thm generalise_all};
val genEx = @{thm generaliseEx};
val genRefl = @{thm generaliseRefl};
val genRefl' = @{thm generaliseRefl'};
val genTrans = @{thm generaliseTrans};
val genAllShift = @{thm generaliseAllShift};

val gen_allShift = @{thm generalise_allShift};
val meta_spec = @{thm meta_spec};
val protectRefl = @{thm protectRefl};
val protectImp = @{thm protectImp};

fun gen_thm decomp (t,ct) = 
  let
    val (ts,cts,recomb) = decomp (t,ct)
  in recomb (map (gen_thm decomp) (ts~~cts)) end;


fun dest_prop (Const (@{const_name Pure.prop}, _) $ P) = P
  | dest_prop t = raise TERM ("dest_prop", [t]);

fun prem_of thm = #1 (Logic.dest_implies (dest_prop (Thm.prop_of thm)));
fun conc_of thm = #2 (Logic.dest_implies (dest_prop (Thm.prop_of thm)));

fun dest_All (Const (@{const_name "All"},_)$t) = t
  | dest_All t = raise TERM ("dest_All",[t]);



fun SIMPLE_OF ctxt rule prems = 
  let
    val mx = fold (fn thm => fn i => Int.max (Thm.maxidx_of thm,i)) prems 0;
  in DistinctTreeProver.discharge ctxt prems (Thm.incr_indexes (mx + 1) rule) end;

infix 0 OF_RAW
fun tha OF_RAW thb = thb COMP (Drule.incr_indexes thb tha);

fun SIMPLE_OF_RAW ctxt tha thb = SIMPLE_OF ctxt tha [thb]; 


datatype qantifier = Meta_all | Hol_all | Hol_ex

fun list_exists (vs, x) =
  fold_rev (fn (x, T) => fn P => HOLogic.exists_const T $ Abs (x, T, P)) vs x;

fun spec' cv thm =
  let (* thm = Pure.prop ((all x. P x) ==> Q), where "all" is meta or HOL *) 
      val (ct1,ct2) = thm |> Thm.cprop_of |> Thm.dest_comb |> #2 
                      |> Thm.dest_comb |> #2 |> Thm.dest_comb;
  in
     (case Thm.term_of ct1 of 
       Const (@{const_name "Trueprop"},_) 
        => let 
             val (Var (sP,_)$Var (sV,sVT)) = HOLogic.dest_Trueprop (Thm.concl_of spec);
             val cvT = Thm.ctyp_of_cterm cv;
             val vT = Thm.typ_of cvT;
           in Thm.instantiate 
                ([(dest_TVar sVT, cvT)],
                 [((sP, vT --> HOLogic.boolT), #2 (Thm.dest_comb ct2)),
                 ((sV, vT), cv)])
                spec
           end
      | Const (@{const_name Pure.all},_)
        => let 
             val (Var (sP,_)$Var (sV,sVT)) = Thm.concl_of meta_spec;
             val cvT = Thm.ctyp_of_cterm cv;
             val vT = Thm.typ_of cvT;
           in Thm.instantiate 
                ([(dest_TVar sVT, cvT)],
                 [((sP, vT --> propT), ct2),
                 ((sV, vT),cv)])
                meta_spec
           end
      | _ => raise THM ("spec'",0,[thm]))
  end;


fun split_thm qnt ctxt s T t = 
  let
    val (t',vars) = SplitState.split_state ctxt s T t;
    val vs = map (SplitState.abs_var ctxt) vars;

    val prop = (case qnt of
                  Meta_all => Logic.list_all (vs,t')
                | Hol_all  => HOLogic.mk_Trueprop (HOLogic.list_all (vs, t'))
                | Hol_ex   => Logic.mk_implies 
                                (HOLogic.mk_Trueprop (list_exists (vs, t')),
                                 HOLogic.mk_Trueprop (HOLogic.mk_exists (s,T,t))))
  in (case qnt of
        Hol_ex => Goal.prove ctxt [] [] prop (fn _ => SplitState.ex_tac ctxt vars)
      | _ => let 
               val rP = conc_of genRefl';
               val thm0 = Thm.instantiate ([], [(dest_Var rP, Thm.cterm_of ctxt prop)]) genRefl';
               fun elim_all v thm =
                 let 
                   val cv = Thm.cterm_of ctxt v;
                   val spc = Goal.protect 0 (spec' cv thm);
                 in SIMPLE_OF ctxt genTrans [thm,spc] end;
               val thm = fold elim_all vars thm0;
             in thm end)
   end;

  


fun eta_expand ctxt ct = 
  let
    val mi = Thm.maxidx_of_cterm ct;
    val T = domain_type (Thm.typ_of_cterm ct);
    val x = Thm.cterm_of ctxt (Var (("s",mi+1),T));
  in Thm.lambda x (Thm.apply ct x) end;

fun split_abs ctxt ct =
  (case Thm.term_of ct of
     Abs x => (x, Thm.dest_abs NONE ct)
   | _ => split_abs ctxt (eta_expand ctxt ct))
            
fun decomp ctxt (Const (@{const_name HOL.conj}, _) $ t $ t', ct) =
      ([t,t'],snd (Drule.strip_comb ct), fn [thm,thm'] => SIMPLE_OF ctxt genConj [thm,thm'])
  | decomp ctxt ((allc as Const (@{const_name "All"},aT)) $ f, ct) = 
       let 
         val cf = snd (Thm.dest_comb ct);
         val (abst as (x,T,_),(cx',cb)) = split_abs ctxt cf;    
         val Free (x',_) = Thm.term_of cx';
         val (Const (@{const_name Pure.all},_)$Abs (s,_,_)) = genAll |> Thm.prems_of |> hd |> dest_prop;
         val genAll' = Drule.rename_bvars [(s,x)] genAll;
         val (Const (@{const_name Pure.all},_)$Abs (s',_,_)) = genAllShift |> Thm.prems_of |> hd |> dest_prop;
         val genAllShift' = Drule.rename_bvars [(s',x)] genAllShift;
       in if SplitState.isState (allc$Abs abst)
          then ([Thm.term_of cb],[cb], fn [thm] => 
                       let val P = HOLogic.dest_Trueprop (dest_prop (prem_of thm));
                           val thm' = split_thm Hol_all ctxt x' T P;
                           val thm1 = genAllShift' OF_RAW 
                                        Goal.protect 0 (Thm.forall_intr cx' (Goal.conclude thm'));
                           val thm2 = genAll' OF_RAW 
                                        Goal.protect 0 (Thm.forall_intr cx' (Goal.conclude thm));
                       in SIMPLE_OF ctxt genTrans [thm1,thm2]
                       end)
          else ([Thm.term_of cb],[cb], fn [thm] => 
                        genAll' OF_RAW Goal.protect 0 (Thm.forall_intr cx' (Goal.conclude thm)))
       end
  | decomp ctxt ((exc as Const (@{const_name "Ex"},_)) $ f, ct) =
       let
         val cf = snd (Thm.dest_comb ct);
         val (abst as (x,T,_),(cx',cb)) = split_abs ctxt cf;    
         val Free (x',_) = Thm.term_of cx';
         val (Const (@{const_name Pure.all},_)$Abs (s,_,_)) = genEx |> Thm.prems_of |> hd |> dest_prop;
         val genEx' = Drule.rename_bvars [(s,x)] genEx;
       in if SplitState.isState (exc$Abs abst)
          then ([Thm.term_of cb],[cb], fn [thm] => 
                       let val P = HOLogic.dest_Trueprop (dest_prop (prem_of thm));
                           val thm' = split_thm Hol_ex ctxt x' T P;
                       in SIMPLE_OF_RAW ctxt protectImp (Goal.protect 0 thm') end )
          else ([Thm.term_of cb],[cb], fn [thm] => 
                       genEx' OF_RAW Goal.protect 0 (Thm.forall_intr cx' (Goal.conclude thm)))
       end
  | decomp ctxt (Const (@{const_name HOL.implies},_)$P$Q, ct) =
       let 
         val [cP,cQ] = (snd (Drule.strip_comb ct));
       in ([Q],[cQ],fn [thm] =>
             let
               val X = genImp |> Thm.concl_of |> dest_prop |> Logic.dest_implies |> #1 
                       |> dest_prop |> HOLogic.dest_Trueprop |> HOLogic.dest_imp |> #1 
                       |> dest_Var;
               val genImp' = Thm.instantiate ([],[(X,cP)]) genImp;
             in SIMPLE_OF ctxt genImp' [thm] end)
       end 
  | decomp ctxt (Const (@{const_name Pure.imp},_)$P$Q, ct) =
       let 
         val [cP,cQ] = (snd (Drule.strip_comb ct));
       in ([Q],[cQ],fn [thm] =>
             let
               val X = genImpl |> Thm.concl_of |> dest_prop |> Logic.dest_implies |> #1 
                       |> dest_prop  |> Logic.dest_implies |> #1 
                       |> dest_Var;
               val genImpl' = Thm.instantiate ([],[(X,cP)]) genImpl;
             in SIMPLE_OF ctxt genImpl' [thm] end) 
       end
  | decomp ctxt ((allc as Const (@{const_name Pure.all},_)) $ f, ct) =
       let 
         val cf = snd (Thm.dest_comb ct);
         val (abst as (x,T,_),(cx',cb)) = split_abs ctxt cf;    
         val Free (x',_) = Thm.term_of cx';
         val (Const (@{const_name Pure.all},_)$Abs (s,_,_)) = gen_all |> Thm.prems_of |> hd |> dest_prop;
         val gen_all' = Drule.rename_bvars [(s,x)] gen_all;
         val (Const (@{const_name Pure.all},_)$Abs (s',_,_)) = gen_allShift |> Thm.prems_of |> hd |> dest_prop;
         val gen_allShift' = Drule.rename_bvars [(s',x)] gen_allShift;
       in if SplitState.isState (allc$Abs abst)
          then ([Thm.term_of cb],[cb], fn [thm] => 
                       let val P = dest_prop (prem_of thm);
                           val thm' = split_thm Meta_all ctxt x' T P;
                           val thm1 = gen_allShift' OF_RAW 
                                       Goal.protect 0 (Thm.forall_intr cx' (Goal.conclude thm'));
                           val thm2 = gen_all' OF_RAW 
                                       Goal.protect 0 (Thm.forall_intr cx' (Goal.conclude thm));
                       in SIMPLE_OF ctxt genTrans [thm1,thm2]
                       end)
          else ([Thm.term_of cb],[cb], fn [thm] => 
                    gen_all' OF_RAW Goal.protect 0 (Thm.forall_intr cx' (Goal.conclude thm)))
       end
  | decomp ctxt (Const (@{const_name "Trueprop"},_)$P, ct) = ([P],snd (Drule.strip_comb ct),fn [thm] => thm)
  | decomp ctxt (t, ct) = ([],[], fn [] => 
                         let val rP = HOLogic.dest_Trueprop (dest_prop (conc_of genRefl));
                         in  Thm.instantiate ([],[(dest_Var rP, ct)]) genRefl end)

fun generalise ctxt ct = gen_thm (decomp ctxt) (Thm.term_of ct,ct);

(*
  -------- (init)
  #C ==> #C
*)
fun init ct = Thm.instantiate' [] [SOME ct] protectRefl;

fun generalise_over_tac ctxt P i st = 
  let 
    val t = List.nth (Thm.prems_of st, i - 1);  (* FIXME !? *)
  in (case P t of
       SOME t' =>
        let
          val ct = Thm.cterm_of ctxt t';
          val meta_spec_protect' = infer_instantiate ctxt [(("x", 0), ct)] @{thm meta_spec_protect};
        in 
          (init (Thm.adjust_maxidx_cterm 0 (List.nth (Drule.cprems_of st, i - 1)))
           |> resolve_tac ctxt [meta_spec_protect'] 1
           |> Seq.maps (fn st' =>
                Thm.bicompose NONE {flatten = true, match = false, incremented = false}
                        (false, Goal.conclude st', Thm.nprems_of st') i st))
        end
      | NONE => no_tac st)
  end;

fun generalise_over_all_states_tac ctxt i =
  REPEAT (generalise_over_tac ctxt SplitState.abs_state i);

fun generalise_tac ctxt i st =
  let 
    val ct = List.nth (Drule.cprems_of st, i - 1);
    val ct' = Thm.dest_equals_rhs (Thm.cprop_of (Thm.eta_conversion ct));
    val r = Goal.conclude (generalise ctxt ct');
  in (init (Thm.adjust_maxidx_cterm 0 (List.nth (Drule.cprems_of st, i - 1)))
      |> (resolve_tac ctxt [r] 1 THEN resolve_tac ctxt [Drule.protectI] 1)
      |> Seq.maps (fn st' =>
            Thm.bicompose NONE {flatten = true, match = false, incremented = false}
                    (false, Goal.conclude st', Thm.nprems_of st') i st))
  end

fun GENERALISE ctxt i = 
  generalise_over_all_states_tac ctxt i THEN 
  generalise_tac ctxt i

end;






