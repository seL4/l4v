theory Strengthen

imports Lib

begin

text {* Strengthen *}

definition
  "strengthen_imp rel x y = (x = y \<or> rel x y)"

lemma strengthen_imp_refl:
  "strengthen_imp rel x x"
  by (simp add: strengthen_imp_def)

lemma strengthen_impI:
  "rel x y \<Longrightarrow> strengthen_imp rel x y"
  by (simp add: strengthen_imp_def)

lemmas imp_to_strengthen = strengthen_impI[where rel="op \<longrightarrow>"]

lemma use_strengthen_imp:
  "strengthen_imp (op \<longrightarrow>) P Q \<Longrightarrow> P \<Longrightarrow> Q"
  by (simp add: strengthen_imp_def)

ML {*
structure Make_Strengthen_Rule = struct

fun imp_list t = let
    val (x, y) = Logic.dest_implies t
  in x :: imp_list y end handle TERM _ => [t]

fun mk_ex (xnm, T) t = HOLogic.exists_const T $ Term.lambda (Var (xnm, T)) t
fun mk_all (xnm, T) t = HOLogic.all_const T $ Term.lambda (Var (xnm, T)) t

fun do_mk ctxt thm = let
    val atomize = Object_Logic.atomize_prems ctxt (Thm.cprop_of thm)
    val thm2 = Thm.equal_elim atomize thm
    val xs = imp_list (Thm.term_of (Thm.rhs_of atomize))
    val xs = map HOLogic.dest_Trueprop xs
      handle TERM _ => raise TERM ("Make_Strengthen_Rule.mk: Trueprop", xs)
    val (concl :: rev_prems) = rev xs
    val prem = fold (curry HOLogic.mk_conj) (rev rev_prems) @{term True}
    val free_concl = Term.add_vars concl []
    val free_prem = Term.add_vars prem []
    val ord = prod_ord Term_Ord.indexname_ord Term_Ord.typ_ord
    val ex_free_prem = Ord_List.subtract ord (Ord_List.make ord free_concl)
        (Ord_List.make ord free_prem)
    val ex_prem = fold mk_ex ex_free_prem prem
    val imp = (@{term "strengthen_imp (op -->)"}
        $ ex_prem $ concl)
    val rule = @{term Trueprop} $ fold mk_all free_concl imp |> Thm.cterm_of ctxt
  in Goal.prove_internal ctxt [] rule
    (K (
      REPEAT_DETERM (rtac @{thm allI} 1)
      THEN rtac @{thm strengthen_impI} 1
      THEN rtac @{thm impI} 1
      THEN (REPEAT_DETERM (etac @{thm exE} 1))
      THEN rtac thm2 1
      THEN ALLGOALS (fn i => REPEAT_DETERM_N (length xs - i - 1) (dtac @{thm conjunct2} i))
      THEN ALLGOALS (dtac @{thm conjunct1})
      THEN ALLGOALS atac
    ))
      |> Object_Logic.rulify ctxt
  end

fun mk_thm ctxt thm = (HOLogic.dest_Trueprop (Thm.prop_of thm);
        thm RS @{thm imp_to_strengthen})
    handle TERM _ => do_mk ctxt thm
    handle THM _ => raise THM ("Make_Strengthen_Rule.mk_thm:"
        ^ " not impl or meta-impl", 1, [thm])

end
*}

ML {*
Make_Strengthen_Rule.mk_thm @{context} @{thm nat.induct}
*}

ML {*

structure Strengthen = struct

structure Congs = Generic_Data
(struct
    type T = thm list
    val empty = []
    val extend = I
    val merge = Thm.merge_thms;
end);

val strg_add = Thm.declaration_attribute 
                    (fn thm =>                      
                        (Congs.map (Thm.add_thm thm)));

val strg_del = Thm.declaration_attribute 
                    (fn thm =>                      
                        (Congs.map (Thm.del_thm thm))); 
  
val setup =
  Attrib.setup @{binding "strg"} (Attrib.add_del strg_add strg_del)
    "strengthening congruence rules";

infix 1 THEN_ALL_NEW_SOLVED;

(* Like THEN_ALL_NEW but insists at least one goal is solved
   by the various applications of tac2. *)
fun (tac1 THEN_ALL_NEW_SOLVED tac2) i st =
  st |> (tac1 i THEN SOLVED' (fn _ => fn st' =>
    Seq.INTERVAL tac2 i (i + Thm.nprems_of st' - Thm.nprems_of st) st') 52);

fun apply_strg ctxt congs rules = let
  in resolve_tac ctxt rules
    ORELSE' ((resolve_tac ctxt congs
            THEN_ALL_NEW_SOLVED (fn i => TRY (apply_strg ctxt congs rules i)))
        THEN_ALL_NEW rtac @{thm strengthen_imp_refl})
  end

fun strengthen ctxt thms = let
    val congs = Congs.get (Context.Proof ctxt)
    val rules = map (Make_Strengthen_Rule.mk_thm ctxt) thms
  in rtac @{thm use_strengthen_imp}
    THEN' apply_strg ctxt congs rules end

val strengthen_args =
  Attrib.thms >> curry (fn (rules, ctxt) =>
    Method.SIMPLE_METHOD (
      strengthen ctxt rules 1
    )
  );

end

*}

setup "Strengthen.setup"

method_setup strengthen = {* Strengthen.strengthen_args *}
  "strengthen the goal"

text {* Important strengthen congruence rules. *}

lemma strengthen_imp_imp:
  "strengthen_imp (op \<longrightarrow>) A B = (A \<longrightarrow> B)"
  "strengthen_imp (swp (op \<longrightarrow>)) A B = (B \<longrightarrow> A)"
  by (simp_all add: strengthen_imp_def swp_def)

context begin

private abbreviation(input)
  "stimp_ord a \<equiv> strengthen_imp (op \<le>) (a :: 'a :: preorder)"
private abbreviation(input)
  "stimp_ord2 a \<equiv> strengthen_imp (swp (op \<le>)) (a :: 'a :: preorder)"

lemma strengthen_imp_ord:
  "stimp_ord A B = (A \<le> B)"
  "stimp_ord2 A B = (B \<le> A)"
  by (auto simp add: strengthen_imp_def swp_def)

private declare strengthen_imp_ord[simp]
private declare strengthen_imp_imp[simp]

lemma strengthen_imp_conj [strg]:
  "\<lbrakk> strengthen_imp (op \<longrightarrow>) A A'; strengthen_imp (op \<longrightarrow>) B B' \<rbrakk>
    \<Longrightarrow> strengthen_imp (op \<longrightarrow>) (A \<and> B) (A' \<and> B')"
  by (simp add: strengthen_imp_imp)

lemma strengthen_imp_conj2 [strg]:
  "\<lbrakk> strengthen_imp (swp (op \<longrightarrow>)) A A'; strengthen_imp (swp (op \<longrightarrow>)) B B' \<rbrakk>
    \<Longrightarrow> strengthen_imp (swp (op \<longrightarrow>)) (A \<and> B) (A' \<and> B')"
  by simp

lemma strengthen_imp_disj [strg]:
  "\<lbrakk> strengthen_imp (op \<longrightarrow>) A A'; strengthen_imp (op \<longrightarrow>) B B' \<rbrakk>
    \<Longrightarrow> strengthen_imp (op \<longrightarrow>) (A \<or> B) (A' \<or> B')"
  by simp

lemma strengthen_imp_disj2 [strg]:
  "\<lbrakk> strengthen_imp (swp (op \<longrightarrow>)) A A'; strengthen_imp (swp (op \<longrightarrow>)) B B' \<rbrakk>
    \<Longrightarrow> strengthen_imp (swp (op \<longrightarrow>)) (A \<or> B) (A' \<or> B')"
  by simp

lemma strengthen_imp [strg]:
  "\<lbrakk> strengthen_imp (swp (op \<longrightarrow>)) X X'; strengthen_imp (op \<longrightarrow>) Y Y' \<rbrakk>
    \<Longrightarrow> strengthen_imp (op \<longrightarrow>) (X \<longrightarrow> Y) (X' \<longrightarrow> Y')"
  by simp

lemma strengthen_imp2 [strg]:
  "\<lbrakk> strengthen_imp (op \<longrightarrow>) X X'; strengthen_imp (swp (op \<longrightarrow>)) Y Y' \<rbrakk>
    \<Longrightarrow> strengthen_imp (swp (op \<longrightarrow>)) (X \<longrightarrow> Y) (X' \<longrightarrow> Y')"
  by simp

lemma strengthen_all[strg]:
  "\<lbrakk> \<And>x. strengthen_imp (op \<longrightarrow>) (P x) (Q x) \<rbrakk>
    \<Longrightarrow> strengthen_imp (op \<longrightarrow>) (\<forall>x. P x) (\<forall>x. Q x)"
  by auto

lemma strengthen_all2[strg]:
  "\<lbrakk> \<And>x. strengthen_imp (swp (op \<longrightarrow>)) (P x) (Q x) \<rbrakk>
    \<Longrightarrow> strengthen_imp (swp (op \<longrightarrow>)) (\<forall>x. P x) (\<forall>x. Q x)"
  by auto

lemma strengthen_ex[strg]:
  "\<lbrakk> \<And>x. strengthen_imp (op \<longrightarrow>) (P x) (Q x) \<rbrakk>
    \<Longrightarrow> strengthen_imp (op \<longrightarrow>) (\<exists>x. P x) (\<exists>x. Q x)"
  by auto

lemma strengthen_ex2[strg]:
  "\<lbrakk> \<And>x. strengthen_imp (swp (op \<longrightarrow>)) (P x) (Q x) \<rbrakk>
    \<Longrightarrow> strengthen_imp (swp (op \<longrightarrow>)) (\<exists>x. P x) (\<exists>x. Q x)"
  by auto

lemma strengthen_Ball[strg]:
  "\<lbrakk> \<And>x. strengthen_imp (op \<longrightarrow>) (P x) (Q x);
        stimp_ord2 S S' \<rbrakk>
    \<Longrightarrow> strengthen_imp (op \<longrightarrow>) (\<forall>x \<in> S. P x) (\<forall>x \<in> S. Q x)"
  by auto

lemma strengthen_Ball2[strg]:
  "\<lbrakk> \<And>x. strengthen_imp (swp (op \<longrightarrow>)) (P x) (Q x);
        stimp_ord S S' \<rbrakk>
    \<Longrightarrow> strengthen_imp (swp (op \<longrightarrow>)) (\<forall>x \<in> S. P x) (\<forall>x \<in> S'. Q x)"
  by auto

lemma strengthen_Bex[strg]:
  "\<lbrakk> \<And>x. strengthen_imp (op \<longrightarrow>) (P x) (Q x);
        stimp_ord2 S S' \<rbrakk>
    \<Longrightarrow> strengthen_imp (op \<longrightarrow>) (\<exists>x \<in> S. P x) (\<exists>x \<in> S. Q x)"
  by auto

lemma strengthen_Bex2[strg]:
  "\<lbrakk> \<And>x. strengthen_imp (swp (op \<longrightarrow>)) (P x) (Q x);
        stimp_ord S S' \<rbrakk>
    \<Longrightarrow> strengthen_imp (swp (op \<longrightarrow>)) (\<exists>x \<in> S. P x) (\<exists>x \<in> S. Q x)"
  by auto

lemma strengthen_Collect[strg]:
  "\<lbrakk> \<And>x. strengthen_imp (op \<longrightarrow>) (P x) (P' x) \<rbrakk>
    \<Longrightarrow> stimp_ord {x. P x} {x. P' x}"
  by auto

lemma strengthen_Collect2[strg]:
  "\<lbrakk> \<And>x. strengthen_imp (swp (op \<longrightarrow>)) (P x) (P' x) \<rbrakk>
    \<Longrightarrow> stimp_ord2 {x. P x} {x. P' x}"
  by auto

lemma strengthen_mem[strg]:
  "\<lbrakk> strengthen_imp (op \<le>) S S' \<rbrakk>
    \<Longrightarrow> strengthen_imp (op \<longrightarrow>) (x \<in> S) (x \<in> S')"
  by auto

lemma strengthen_mem2[strg]:
  "\<lbrakk> strengthen_imp (swp (op \<le>)) S S' \<rbrakk>
    \<Longrightarrow> strengthen_imp (swp (op \<longrightarrow>)) (x \<in> S) (x \<in> S')"
  by auto

lemma strengthen_ord[strg]:
  "stimp_ord2 x x' \<Longrightarrow> stimp_ord y y'
    \<Longrightarrow> strengthen_imp (op \<longrightarrow>) (x \<le> y) (x' \<le> y')"
  by (simp, metis order_trans)

lemma strengthen_ord2[strg]:
  "stimp_ord x x' \<Longrightarrow> stimp_ord2 y y'
    \<Longrightarrow> strengthen_imp (swp (op \<longrightarrow>)) (x \<le> y) (x' \<le> y')"
  by (simp, metis order_trans)

lemma strengthen_strict_ord[strg]:
  "stimp_ord2 x x' \<Longrightarrow> stimp_ord y y'
    \<Longrightarrow> strengthen_imp (op \<longrightarrow>) (x < y) (x' < y')"
  by (simp, metis order_le_less_trans order_less_le_trans)

lemma strengthen_strict_ord2[strg]:
  "stimp_ord x x' \<Longrightarrow> stimp_ord2 y y'
    \<Longrightarrow> strengthen_imp (swp (op \<longrightarrow>)) (x < y) (x' < y')"
  by (simp, metis order_le_less_trans order_less_le_trans)

(* FIXME: add image, revimage, restrict_map, Int, Un, all variants
   of big set UN/INT syntax, all relevant order stuff, etc. *)

lemma imp_consequent:
  "P \<longrightarrow> Q \<longrightarrow> P" by simp

end

text {* Test case. *}

lemma foo:
  assumes x: "\<And>x. P x \<longrightarrow> Q x"
  shows "{x. x \<noteq> None \<and> P (the x)} \<subseteq> {y. \<forall>x. y = Some x \<longrightarrow> Q x}"
  apply (strengthen x)
  apply clarsimp
  done

end
