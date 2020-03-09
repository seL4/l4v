(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory MoreCorres
imports "Lib.ExtraCorres"
begin

(* FIXME: move all of this into ExtraCorres *)

(*
 * If both systems perform non-determinism where the splits are
 * equivalent, we can prove each pair separately.
 *)
lemma corres_alternate_match:
  "\<lbrakk> corres_underlying sr nf nf' r P P' a c;
     corres_underlying sr nf nf' r P P' b d \<rbrakk> \<Longrightarrow>
   corres_underlying sr nf nf' r P P' (a \<sqinter> b) (c \<sqinter> d)"
  apply (simp add: corres_underlying_def alternative_def)
  apply (clarsimp)
  apply (drule (1) bspec, clarsimp)+
  apply fastforce
  done

(*
 * If the concrete system performs non-determinism where the abstract
 * system does not, we must show that both branches of the concrete
 * system refine the abstract system.
 *)
lemma corres_alternate_split:
  "\<lbrakk> corres_underlying sr nf nf' r P Q a x;
     corres_underlying sr nf nf' r P' Q' a y \<rbrakk> \<Longrightarrow>
   corres_underlying sr nf nf' r (P and P') (Q and Q') a (x \<sqinter> y)"
  apply (simp add: corres_underlying_def alternative_def)
  apply (clarsimp)
  apply (drule (1) bspec, clarsimp)+
  apply fastforce
  done

(*
 * Two select statements are equivalent if the concrete's select set is
 * a subset of the abstract's select set.
 *)
lemma corres_select_equiv:
  "\<lbrakk> \<forall>a' \<in> A'. \<exists>a \<in> A. r a a' \<rbrakk> \<Longrightarrow> corres_underlying sr nf nf' r \<top> \<top> (select A) (select A')"
  apply (clarsimp simp: corres_underlying_def)
  apply (clarsimp simp: split_def)
  apply (clarsimp simp: select_def)
  done

(*
 * Where there is an 'if' statement in the concrete system not present
 * in the abstract system, we must show that both branches are a  valid
 * refinement. Happily, we get to assume the outcome of the 'if'
 * statement when proving the refinement.
 *
 * This will likely need to be used with 'stronger_corres_guard_imp'.
 *)
lemma corres_if_rhs:
  "\<lbrakk>  G \<Longrightarrow> corres_underlying sr nf nf' rvr P  Q  a b;
     \<not>G \<Longrightarrow> corres_underlying sr nf nf' rvr P' Q' a c \<rbrakk> \<Longrightarrow>
   corres_underlying sr nf nf' rvr
       (\<lambda>s. (G \<longrightarrow> P s) \<and> (\<not>G \<longrightarrow> P' s)) (\<lambda>s. (G \<longrightarrow> Q s) \<and> (\<not>G \<longrightarrow> Q' s))
       a (if G then b else c)"
  by (auto elim: corres_guard_imp)

(* Bind distributes over non-deterministic choice. *)
lemma alternative_bind_distrib: "((f \<sqinter> g) >>= h) = ((f >>= h) \<sqinter> (g >>= h))"
  apply (auto simp: alternative_def bind_def split_def intro!: prod_eqI)
  done

(* Bind distributes over non-deterministic choice. *)
lemma alternative_bind_distrib_2: "(do f; (a \<sqinter> b) od) = ((do f; a od) \<sqinter> (do f; b od))"
  apply (auto simp: alternative_def bind_def split_def intro!: prod_eqI)
  done

(* "bindE" distributes over non-deterministic choice. *)
lemma alternative_bindE_distrib: "((f \<sqinter> g) >>=E h) = ((f >>=E h) \<sqinter> (g >>=E h))"
  by (simp add: bindE_def alternative_bind_distrib)

(*
 * Two arbitrary return statements correspond if our return relation
 * doesn't care about them.
 *)
lemma corres_return_dc [simp]:
  "corres_underlying sr nf nf' dc \<top> \<top> (return a) (return b)"
  apply (clarsimp simp: corres_underlying_def dc_def return_def)
  done

(* If our return relation doesn't matter, return statements are meaningless. *)
lemma corres_return_dc_rhs:
  "corres_underlying sr nf nf' dc G G' P P' \<Longrightarrow> corres_underlying sr nf nf' dc G G' P (do P'; return a od)"
  by (fastforce simp: corres_underlying_def dc_def return_def bind_def)

(* If our return relation doesn't matter, return statements are meaningless. *)
lemma corres_return_dc_lhs:
  "corres_underlying sr nf nf' dc G G' P P'
    \<Longrightarrow> corres_underlying sr nf nf' dc G G' (do P; return a od) P'"
  by (simp add: liftM_def[symmetric])

(* liftE distributes inside bind. *)
lemma liftE_distrib: "(liftE (A >>= (\<lambda>_. B))) = ((liftE A) >>=E (\<lambda>x. (liftE B)))"
  apply (clarsimp simp: liftE_def bindE_def)
  apply (subst bind_assoc)+
  apply (clarsimp simp: bind_def lift_def)
  done

(* liftE distributes inside alternate. *)
lemma liftE_alternative_distrib: "(liftE (a \<sqinter> b)) = ((liftE a) \<sqinter> (liftE b))"
  by (metis alternative_bind_distrib bindE_returnOk liftE_bindE)

lemma corres_skip_catch:
  "corres_underlying sr nf nf' dc P P' f g \<Longrightarrow>
   corres_underlying sr nf nf' dc P P' f (g <catch> (\<lambda>_. return x))"
  by (clarsimp simp: corres_underlying_def catch_def return_def bind_def
                     split_def
               split: sum.splits)

end
