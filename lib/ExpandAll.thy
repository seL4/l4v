(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory ExpandAll (* FIXME: bitrotted *)
imports "~~/src/HOL/Main"
begin

lemma expand_forall:
  "\<lbrakk> \<And>x. f (g x) = h x; (\<forall>x. f x) = P; surj g \<rbrakk> \<Longrightarrow> (\<forall>x. h x) = P"
  apply (simp add: surj_def)
  apply metis
  done

lemma expand_exists:
  "\<lbrakk> \<And>x. f (g x) = h x; (\<exists>x. f x) = P; surj g \<rbrakk> \<Longrightarrow> (\<exists>x. h x) = P"
  apply (simp add: surj_def)
  apply metis
  done

lemma expand_one_split:
  "\<lbrakk> \<And>a. (\<forall>b. P a b) = Q a \<rbrakk> \<Longrightarrow> (\<forall>v. (\<lambda>(a, b). P a b) v) = (\<forall>a. Q a)"
  "\<lbrakk> \<And>a. (\<exists>b. P a b) = Q a \<rbrakk> \<Longrightarrow> (\<exists>v. (\<lambda>(a, b). P a b) v) = (\<exists>a. Q a)"
  by simp+

ML {*
(* given patterns, e.g. fst, snd, replace
  \<forall>x. P (fst x) (snd x) with \<forall>x y. P x y

  more useful for things that aren't actually tuples,
  e.g. replace \<forall>xs. P (xs ! 0) (xs ! 2) with \<forall>x y. P x y

  pats here is a function for finding such pats

  ditto \<exists>x. P (fst x) (snd x)
*)

fun lambda_tuple [x] body =
      lambda x body
  | lambda_tuple (x::xs) body =
      HOLogic.mk_split (lambda x (lambda_tuple xs body))
  | lambda_tuple [] body =
      raise TERM ("lambda_tuple: empty", [body])

fun expand_forall_pats ctxt pats tac t = let
    val (T, bdy, thm) = case t of
        (Const (@{const_name All}, T) $ bdy) => (T, bdy, @{thm expand_forall})
      | (Const (@{const_name Ex}, T) $ bdy) => (T, bdy, @{thm expand_exists})
      | _ => raise TERM ("expand_forall_pats: not All or Ex", [t])

    val thy = Proof_Context.theory_of ctxt

    val x = Variable.variant_frees ctxt [bdy]
        [("x", domain_type (domain_type T))]
      |> the_single |> Free

    val bdy_x = betapply (bdy, x)
    val pat_xs = pats x bdy_x |> sort_distinct Term_Ord.fast_term_ord

    val ys = map (fn pat_x => ("y", fastype_of pat_x)) pat_xs
     |> Variable.variant_frees ctxt [bdy_x] |> map Free

    val f = Pattern.rewrite_term thy (pat_xs ~~ ys) [] bdy_x
      |> tap (fn f => exists_subterm (curry (op =) x) f
      andalso raise TERM ("expand_forall_pats: not all converted",
          [x] @ pat_xs @ ys))
      |> lambda_tuple ys

    val g = lambda x (HOLogic.mk_tuple pat_xs)

    val numsplits = length pat_xs - 1

  in cterm_instantiate
    [(@{cpat "?f\<Colon>?'b \<Rightarrow> bool"}, Thm.cterm_of ctxt f),
        (@{cpat "?g\<Colon>?'a \<Rightarrow> ?'b"}, Thm.cterm_of ctxt g),
        (@{cpat "?h\<Colon>?'a \<Rightarrow> bool"}, Thm.cterm_of ctxt bdy)]
    thm
    |> EVERY (
        replicate numsplits (rtac @{thm trans[OF split_conv]} 1)
      @ [rtac @{thm refl} 1]
      @ replicate numsplits (resolve_tac ctxt @{thms expand_one_split} 1)
      @ [rtac @{thm refl} 1, tac pat_xs])
    |> Seq.hd
  end

fun mk_expand_forall_simproc s T pats tac thy
  = let
    val opT = (T --> HOLogic.boolT) --> HOLogic.boolT
    val P = Free ("P", T --> HOLogic.boolT)
  in Simplifier.simproc_global_i thy s
      [Const (@{const_name All}, opT) $ P, Const (@{const_name Ex}, opT) $ P]
      (fn ctxt  => (try (expand_forall_pats ctxt pats (tac ctxt) #> mk_meta_eq)))
  end
*}

ML {*
fun get_nths xs (t as (Const (@{const_name nth}, _) $ ys $ _))
    = if xs aconv ys then [t] else []
  | get_nths xs (t as (Const (@{const_name hd}, _) $ ys))
    = if xs aconv ys then [t] else []
  | get_nths xs (f $ x) = get_nths xs f @ get_nths xs x
  | get_nths xs (Abs (_, _, t)) = get_nths xs t
  | get_nths _ _ = []
*}

lemma surj_via_mapI:
  "surj (\<lambda>g. f (map g [0 ..< n])) \<Longrightarrow> surj (\<lambda>xs. f xs)"
  by (auto simp add: surj_def)

lemma surj_tup_apply_eq:
  "surj (\<lambda>f. (f x, g f)) = (\<forall>v. surj (\<lambda>f. g (f (x := v))))"
  apply (simp add: surj_def)
  apply (rule arg_cong[where f=All, OF ext])+
  apply safe
   apply (metis fun_upd_triv)
  apply (rule_tac x="f (x := y)" for f y in exI, fastforce)
  done

lemma surj_apply:
  "surj (\<lambda>f. f x)"
  by auto

lemma hd_map:
  "xs \<noteq> [] \<Longrightarrow> hd (map f xs) = f (hd xs)"
  by (clarsimp simp: neq_Nil_conv)


ML {*
fun inst_surj_via_mapI ctxt nths = let
    fun get_nth (f $ (@{term Suc} $ n))
      = get_nth (f $ n) + 1
      | get_nth (Const (@{const_name nth}, _) $ _ $ n)
      = HOLogic.dest_number n |> snd
      | get_nth (Const (@{const_name hd}, _) $ _) = 0
      | get_nth t = raise TERM ("get_nth", [t])
    val max_n = map get_nth nths |> foldr1 (uncurry Integer.max)
    val n = HOLogic.mk_number @{typ nat} (max_n + 1)
      |> Thm.cterm_of ctxt
    val t = cterm_instantiate [(@{cpat "?n\<Colon>nat"}, n)] @{thm surj_via_mapI}
    val ss = put_simpset (simpset_of @{context}) ctxt addsimps @{thms surj_tup_apply_eq surj_apply hd_map}
            (* FIXME: should build up right simpset instead of taking the current one *)
  in rtac t 1 THEN simp_tac ss 1 end
*}

ML {*
val t = expand_forall_pats @{context} get_nths
  (inst_surj_via_mapI @{context})
  @{term "\<forall>xs. xs ! 1 + xs ! 3 + xs ! 42 + hd xs < (12 :: nat)"}
*}

ML {*
val expand_forall_nths_simproc
  = mk_expand_forall_simproc "expand_forall_nths" @{typ "'a list"}
    get_nths inst_surj_via_mapI @{theory}
*}

lemma test:
  "(\<forall>xs. xs ! Suc 0 = 1 \<and> xs ! 2 = 3 \<longrightarrow> P (xs ! Suc 0 + xs ! 2)) = P (1 + 3)
      \<and> (\<exists>xs. xs ! 3 = xs ! 4)"
  apply (tactic {* simp_tac (put_simpset HOL_basic_ss @{context} addsimprocs [expand_forall_nths_simproc]) 1 *})
  apply simp
  done

end
