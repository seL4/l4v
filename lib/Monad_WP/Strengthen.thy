(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Strengthen
imports Main
begin

text {* Strengthen *}

locale strengthen_implementation begin

definition "st P rel x y = (x = y \<or> (P \<and> rel x y) \<or> (\<not> P \<and> rel y x))"

definition "failed == True"

definition elim :: "prop \<Rightarrow> prop"
where
 "elim (P :: prop) == P"

definition "oblig (P :: prop) == P"

end

notation strengthen_implementation.elim ("{elim| _ |}")
notation strengthen_implementation.oblig ("{oblig| _ |}")
notation strengthen_implementation.failed ("<strg-failed>")

syntax 
  "_ap_strg_bool" :: "['a, 'a] => 'a"  ("_ =strg<--|=> _")
  "_ap_wkn_bool" :: "['a, 'a] => 'a"  ("_ =strg-->|=> _")
  "_ap_ge_bool" :: "['a, 'a] => 'a"  ("_ =strg<=|=> _")
  "_ap_le_bool" :: "['a, 'a] => 'a"  ("_ =strg>=|=> _")

syntax(xsymbols) 
  "_ap_strg_bool" :: "['a, 'a] => 'a"  ("_ =strg\<longleftarrow>|=> _")
  "_ap_wkn_bool" :: "['a, 'a] => 'a"  ("_ =strg\<longrightarrow>|=> _")
  "_ap_ge_bool" :: "['a, 'a] => 'a"  ("_ =strg\<le>|=> _")
  "_ap_le_bool" :: "['a, 'a] => 'a"  ("_ =strg\<ge>|=> _")

translations
  "P =strg\<longleftarrow>|=> Q" == "CONST strengthen_implementation.st (CONST False) (CONST HOL.implies) P Q"
  "P =strg\<longrightarrow>|=> Q" == "CONST strengthen_implementation.st (CONST True) (CONST HOL.implies) P Q"
  "P =strg\<le>|=> Q" == "CONST strengthen_implementation.st (CONST False) (CONST Orderings.less_eq) P Q"
  "P =strg\<ge>|=> Q" == "CONST strengthen_implementation.st (CONST True) (CONST Orderings.less_eq) P Q"

context strengthen_implementation begin

lemma failedI:
  "<strg-failed>"
  by (simp add: failed_def)

lemma strengthen_refl:
  "st P rel x x"
  by (simp add: st_def)

lemma strengthenI:
  "rel x y \<Longrightarrow> st True rel x y"
  "rel y x \<Longrightarrow> st False rel x y"
  by (simp_all add: st_def)

lemmas imp_to_strengthen = strengthenI(2)[where rel="op \<longrightarrow>"]
lemmas rev_imp_to_strengthen = strengthenI(1)[where rel="op \<longrightarrow>"]
lemmas ord_to_strengthen = strengthenI[where rel="op \<le>"]

lemma use_strengthen_imp:
  "st False (op \<longrightarrow>) Q P \<Longrightarrow> P \<Longrightarrow> Q"
  by (simp add: st_def)

lemma strengthen_Not:
  "st False rel x y \<Longrightarrow> st (\<not> True) rel x y"
  "st True rel x y \<Longrightarrow> st (\<not> False) rel x y"
  by auto

lemmas gather =
    swap_prems_eq[where A="PROP (Trueprop P)" and B="PROP (elim Q)" for P Q]
    swap_prems_eq[where A="PROP (Trueprop P)" and B="PROP (oblig Q)" for P Q]

lemma mk_True_imp:
  "P \<equiv> True \<longrightarrow> P"
  by simp

lemma narrow_quant:
  "(\<And>x. PROP P \<Longrightarrow> PROP (Q x)) \<equiv> (PROP P \<Longrightarrow> (\<And>x. PROP (Q x)))"
  "(\<And>x. (R \<longrightarrow> S x)) \<equiv> PROP (Trueprop (R \<longrightarrow> (\<forall>x. S x)))"
  "(\<And>x. (S x \<longrightarrow> R)) \<equiv> PROP (Trueprop ((\<exists>x. S x) \<longrightarrow> R))"
  apply (simp_all add: atomize_all)
  apply rule
   apply assumption
  apply assumption
  done

ML {*
structure Make_Strengthen_Rule = struct

fun binop_conv' cv1 cv2 = Conv.combination_conv (Conv.arg_conv cv1) cv2;

val mk_elim = Conv.rewr_conv @{thm elim_def[symmetric]}
val mk_oblig = Conv.rewr_conv @{thm oblig_def[symmetric]}

fun count_vars t = Term.fold_aterms
    (fn (Var v) => Termtab.map_default (Var v, 0) (fn x => x + 1)
        | _ => I) t Termtab.empty

fun gather_to_imp ctxt drule pattern = let
    val pattern = (if drule then "D" :: pattern else pattern)
    fun inner pat ct = case (head_of (Thm.term_of ct), pat) of
        (@{term Pure.imp}, ("E" :: pat)) => binop_conv' mk_elim (inner pat) ct
      | (@{term Pure.imp}, ("O" :: pat)) => binop_conv' mk_oblig (inner pat) ct
      | (@{term Pure.imp}, _) => binop_conv' (Object_Logic.atomize ctxt) (inner (drop 1 pat)) ct
      | (_, []) => Object_Logic.atomize ctxt ct
      | (_, pat) => raise THM ("gather_to_imp: leftover pattern: " ^ commas pat, 1, [])
    fun simp thms = Raw_Simplifier.rewrite ctxt false thms
    fun ensure_imp ct = case strip_comb (Thm.term_of ct) |> apsnd (map head_of)
     of
        (@{term Pure.imp}, _) => Conv.arg_conv ensure_imp ct
      | (@{term HOL.Trueprop}, [@{term HOL.implies}]) => Conv.all_conv ct
      | (@{term HOL.Trueprop}, _) => Conv.arg_conv (Conv.rewr_conv @{thm mk_True_imp}) ct
      | _ => raise CTERM ("gather_to_imp", [ct])
    val gather = simp @{thms gather}
        then_conv (if drule then Conv.all_conv else simp @{thms atomize_conjL})
        then_conv simp @{thms atomize_imp}
        then_conv ensure_imp
  in Conv.fconv_rule (inner pattern then_conv gather) end

fun imp_list t = let
    val (x, y) = Logic.dest_implies t
  in x :: imp_list y end handle TERM _ => [t]

fun mk_ex (xnm, T) t = HOLogic.exists_const T $ Term.lambda (Var (xnm, T)) t
fun mk_all (xnm, T) t = HOLogic.all_const T $ Term.lambda (Var (xnm, T)) t

fun quantify_vars ctxt drule thm = let
    val (lhs, rhs) = Thm.concl_of thm |> HOLogic.dest_Trueprop
      |> HOLogic.dest_imp
    val all_vars = count_vars (Thm.prop_of thm)
    val new_vars = count_vars (if drule then rhs else lhs)
    val quant = filter (fn v => Termtab.lookup new_vars v = Termtab.lookup all_vars v)
            (Termtab.keys new_vars)
        |> map (Thm.cterm_of ctxt)
  in fold Thm.forall_intr quant thm
    |> Conv.fconv_rule (Raw_Simplifier.rewrite ctxt false @{thms narrow_quant})
  end

fun mk_strg (typ, pat) ctxt thm = let
    val drule = typ = "D" orelse typ = "D'"
    val imp = gather_to_imp ctxt drule pat thm
      |> (if typ = "I'" orelse typ = "D'"
          then quantify_vars ctxt drule else I)
  in if typ = "I" orelse typ = "I'"
    then imp RS @{thm imp_to_strengthen}
    else if drule then imp RS @{thm rev_imp_to_strengthen}
    else if typ = "lhs" then imp RS @{thm ord_to_strengthen(1)}
    else if typ = "rhs" then imp RS @{thm ord_to_strengthen(2)}
    else raise THM ("mk_strg: unknown type: " ^ typ, 1, [thm])
 end

fun auto_mk ctxt thm = let
    val concl_C = try (fst o dest_Const o head_of
        o HOLogic.dest_Trueprop) (Thm.concl_of thm)
  in case (Thm.nprems_of thm, concl_C) of
    (_, SOME @{const_name failed}) => thm
  | (_, SOME @{const_name st}) => thm
  | (0, SOME @{const_name HOL.implies}) => (thm RS @{thm imp_to_strengthen}
      handle THM _ => @{thm failedI})
  | _ => mk_strg ("I'", []) ctxt thm
  end

fun mk_strg_args (SOME (typ, pat)) ctxt thm = mk_strg (typ, pat) ctxt thm
  | mk_strg_args NONE ctxt thm = auto_mk ctxt thm

val arg_pars = Scan.option (Scan.first (map Args.$$$ ["I", "I'", "D", "D'", "lhs", "rhs"])
  -- Scan.repeat (Args.$$$ "E" || Args.$$$ "O" || Args.$$$ "_"))

val setup =
      Attrib.setup @{binding "mk_strg"}
          ((Scan.lift arg_pars -- Args.context)
              >> (fn (args, ctxt) => Thm.rule_attribute [] (K (mk_strg_args args ctxt))))
          "put rule in 'strengthen' form"

end
*}

end

setup Make_Strengthen_Rule.setup

text {* Quick test. *}

lemmas foo = nat.induct[mk_strg I O O]
    nat.induct[mk_strg D O]
    nat.induct[mk_strg I' E]
    exI[mk_strg I'] exI[mk_strg I]

context strengthen_implementation begin

lemma do_elim:
  "PROP P \<Longrightarrow> PROP elim (PROP P)"
  by (simp add: elim_def)

lemma intro_oblig:
  "PROP P \<Longrightarrow> PROP oblig (PROP P)"
  by (simp add: oblig_def)

ML {*

structure Strengthen = struct

structure Congs = Theory_Data
(struct
    type T = thm list
    val empty = []
    val extend = I
    val merge = Thm.merge_thms;
end);

val tracing = Attrib.config_bool @{binding strengthen_trace} (K false)

fun map_context_total f (Context.Theory t) = (Context.Theory (f t))
  | map_context_total f (Context.Proof p)
    = (Context.Proof (Context.raw_transfer (f (Proof_Context.theory_of p)) p))

val strg_add = Thm.declaration_attribute 
        (fn thm => map_context_total (Congs.map (Thm.add_thm thm)));

val strg_del = Thm.declaration_attribute 
        (fn thm => map_context_total (Congs.map (Thm.del_thm thm)));
  
val setup =
  Attrib.setup @{binding "strg"} (Attrib.add_del strg_add strg_del)
    "strengthening congruence rules"
    #> snd tracing;

val do_elim = SUBGOAL (fn (t, i) => case (head_of (Logic.strip_assums_concl t)) of
    @{term elim} => eresolve0_tac @{thms do_elim} i
  | _ => all_tac)

infix 1 THEN_TRY_ALL_NEW;

(* Like THEN_ALL_NEW but allows failure, although at least one subsequent
   method must succeed. *)
fun (tac1 THEN_TRY_ALL_NEW tac2) i st = let
    fun inner b j st = if i > j then (if b then all_tac else no_tac) st
      else ((tac2 j THEN inner true (j - 1)) ORELSE inner b (j - 1)) st
  in st |> (tac1 i THEN (fn st' =>
    inner false (i + Thm.nprems_of st' - Thm.nprems_of st) st')) end

fun maybe_trace_tac false _ _ = K all_tac
  | maybe_trace_tac true ctxt msg = SUBGOAL (fn (t, _) => let
    val tr = Pretty.big_list msg [Syntax.pretty_term ctxt t]
  in
    Pretty.writeln tr;
    all_tac
  end)

fun apply_strg ctxt trace congs rules = EVERY' [
    maybe_trace_tac trace ctxt "apply_strg",
    DETERM o TRY o resolve_tac ctxt @{thms strengthen_Not},
    DETERM o ((resolve_tac ctxt rules THEN_ALL_NEW do_elim)
        ORELSE' (resolve_tac ctxt congs THEN_TRY_ALL_NEW
            (fn i => apply_strg ctxt trace congs rules i)))
]

fun do_strg ctxt congs rules
    = apply_strg ctxt (Config.get ctxt (fst tracing)) congs rules
        THEN_ALL_NEW (TRY o resolve_tac ctxt @{thms strengthen_refl intro_oblig})

fun strengthen ctxt thms = let
    val congs = Congs.get (Proof_Context.theory_of ctxt)
    val rules = map (Make_Strengthen_Rule.auto_mk ctxt) thms
  in resolve0_tac @{thms use_strengthen_imp}
    THEN' do_strg ctxt congs rules end

val strengthen_args =
  Attrib.thms >> curry (fn (rules, ctxt) =>
    Method.SIMPLE_METHOD (
      strengthen ctxt rules 1
    )
  );

end

*}

end

setup "Strengthen.setup"

method_setup strengthen = {* Strengthen.strengthen_args *}
  "strengthen the goal"

text {* Important strengthen congruence rules. *}

context strengthen_implementation begin

lemma strengthen_imp_imp[simp]:
  "st True (op \<longrightarrow>) A B = (A \<longrightarrow> B)"
  "st False (op \<longrightarrow>) A B = (B \<longrightarrow> A)"
  by (simp_all add: st_def)

abbreviation(input)
  "st_ord t \<equiv> st t (op \<le> :: ('a :: preorder) \<Rightarrow> _)"

lemma strengthen_imp_ord[simp]:
  "st_ord True A B = (A \<le> B)"
  "st_ord False A B = (B \<le> A)"
  by (auto simp add: st_def)

lemma strengthen_imp_conj [strg]:
  "\<lbrakk> B \<Longrightarrow> st F (op \<longrightarrow>) A A'; st F (op \<longrightarrow>) B B' \<rbrakk>
    \<Longrightarrow> st F (op \<longrightarrow>) (A \<and> B) (A' \<and> B')"
  by (cases F, auto)

lemma strengthen_imp_disj [strg]:
  "\<lbrakk> \<not> B \<Longrightarrow> st F (op \<longrightarrow>) A A'; st F (op \<longrightarrow>) B B' \<rbrakk>
    \<Longrightarrow> st F (op \<longrightarrow>) (A \<or> B) (A' \<or> B')"
  by (cases F, auto)

lemma strengthen_imp_implies [strg]:
  "\<lbrakk> st (\<not> F) (op \<longrightarrow>) X X'; X \<Longrightarrow> st F (op \<longrightarrow>) Y Y' \<rbrakk>
    \<Longrightarrow> st F (op \<longrightarrow>) (X \<longrightarrow> Y) (X' \<longrightarrow> Y')"
  by (cases F, auto)

lemma strengthen_all[strg]:
  "\<lbrakk> \<And>x. st F (op \<longrightarrow>) (P x) (Q x) \<rbrakk>
    \<Longrightarrow> st F (op \<longrightarrow>) (\<forall>x. P x) (\<forall>x. Q x)"
  by (cases F, auto)

lemma strengthen_ex[strg]:
  "\<lbrakk> \<And>x. st F (op \<longrightarrow>) (P x) (Q x) \<rbrakk>
    \<Longrightarrow> st F (op \<longrightarrow>) (\<exists>x. P x) (\<exists>x. Q x)"
  by (cases F, auto)

lemma strengthen_Ball[strg]:
  "\<lbrakk> st_ord (Not F) S S';
        \<And>x. x \<in> S \<Longrightarrow> st F (op \<longrightarrow>) (P x) (Q x) \<rbrakk>
    \<Longrightarrow> st F (op \<longrightarrow>) (\<forall>x \<in> S. P x) (\<forall>x \<in> S'. Q x)"
  by (cases F, auto)

lemma strengthen_Bex[strg]:
  "\<lbrakk> st_ord F S S';
        \<And>x. x \<in> S \<Longrightarrow> st F (op \<longrightarrow>) (P x) (Q x) \<rbrakk>
    \<Longrightarrow> st F (op \<longrightarrow>) (\<exists>x \<in> S. P x) (\<exists>x \<in> S'. Q x)"
  by (cases F, auto)

lemma strengthen_Collect[strg]:
  "\<lbrakk> \<And>x. st F (op \<longrightarrow>) (P x) (P' x) \<rbrakk>
    \<Longrightarrow> st_ord F {x. P x} {x. P' x}"
  by (cases F, auto)

lemma strengthen_mem[strg]:
  "\<lbrakk> st_ord F S S' \<rbrakk>
    \<Longrightarrow> st F (op \<longrightarrow>) (x \<in> S) (x \<in> S')"
  by (cases F, auto)

lemma strengthen_ord[strg]:
  "st_ord (\<not> F) x x' \<Longrightarrow> st_ord F y y'
    \<Longrightarrow> st F (op \<longrightarrow>) (x \<le> y) (x' \<le> y')"
  by (cases F, simp_all, (metis order_trans)+)

lemma strengthen_strict_ord[strg]:
  "st_ord (\<not> F) x x' \<Longrightarrow> st_ord F y y'
    \<Longrightarrow> st F (op \<longrightarrow>) (x < y) (x' < y')"
  by (cases F, simp_all, (metis order_le_less_trans order_less_le_trans)+)

lemma strengthen_image[strg]:
  "st_ord F S S' \<Longrightarrow> st_ord F (f ` S) (f ` S')"
  by (cases F, auto)

lemma strengthen_vimage[strg]:
  "st_ord F S S' \<Longrightarrow> st_ord F (f -` S) (f -` S')"
  by (cases F, auto)

lemma strengthen_Int[strg]:
  "st_ord F A A' \<Longrightarrow> st_ord F B B' \<Longrightarrow> st_ord F (A \<inter> B) (A' \<inter> B')"
  by (cases F, auto)

lemma strengthen_Un[strg]:
  "st_ord F A A' \<Longrightarrow> st_ord F B B' \<Longrightarrow> st_ord F (A \<union> B) (A' \<union> B')"
  by (cases F, auto)

(* FIXME: add all variants
   of big set UN/INT syntax, maps, all relevant order stuff, etc. *)

lemma imp_consequent:
  "P \<longrightarrow> Q \<longrightarrow> P" by simp

end

text {* Test cases. *}

lemma 
  assumes x: "\<And>x. P x \<longrightarrow> Q x"
  shows "{x. x \<noteq> None \<and> P (the x)} \<subseteq> {y. \<forall>x. y = Some x \<longrightarrow> Q x}"
  apply (strengthen x)
  apply clarsimp
  done

locale strengthen_silly_test begin

definition
  silly :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "silly x y = (x \<le> y)"

lemma silly_trans:
  "silly x y \<Longrightarrow> silly y z \<Longrightarrow> silly x z"
  by (simp add: silly_def)

lemma silly_refl:
  "silly x x"
  by (simp add: silly_def)

lemma foo:
  "silly x y \<Longrightarrow> silly a b \<Longrightarrow> silly b c
    \<Longrightarrow> silly x y \<and> (\<forall>x :: nat. silly a c )"
  using [[strengthen_trace = true]]
  apply (strengthen silly_trans[mk_strg I E])+
  apply (strengthen silly_refl)
  apply simp
  done

end

end
