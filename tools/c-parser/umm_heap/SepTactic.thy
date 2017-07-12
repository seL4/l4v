(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* License: BSD, terms see file ./LICENSE *)

theory SepTactic
imports SepInv
begin

section "sep_point_tac"

definition sep_conj_extract :: "heap_assert \<Rightarrow> heap_assert" where
  "sep_conj_extract \<equiv> id"

definition sep_points :: "heap_assert \<Rightarrow> heap_assert" where
  "sep_points P \<equiv> P \<and>\<^sup>* sep_true"

lemma sep_conj_extract1D:
  "(P \<and>\<^sup>* Q) s \<Longrightarrow> sep_conj_extract (P \<and>\<^sup>* Q) s"
  by (simp add: sep_conj_extract_def)

lemma sep_conj_extract2D:
  "sep_conj_extract P s \<Longrightarrow> P s \<and> (sep_conj_extract P \<and>\<^sup>* sep_true) s"
  by (auto simp: sep_conj_extract_def elim: sep_conj_sep_true)

lemma sep_conj_extract_assoc:
  "sep_conj_extract ((P \<and>\<^sup>* Q) \<and>\<^sup>* R) = sep_conj_extract (P \<and>\<^sup>* (Q \<and>\<^sup>* R))"
  by (simp add: sep_conj_ac)

lemma sep_conj_extract_decomposeD:
  "(sep_conj_extract (P \<and>\<^sup>* Q) \<and>\<^sup>* sep_true) s \<Longrightarrow> sep_points P s \<and>
      (sep_conj_extract Q \<and>\<^sup>* sep_true) s"
apply (rule conjI)
 apply(simp add: sep_conj_extract_def sep_points_def sep_conj_ac)
 apply(erule (1) sep_conj_impl, simp)
apply(simp add: sep_conj_extract_def sep_conj_ac)
apply(subst (asm) sep_conj_assoc [symmetric])
apply(subst (asm) sep_conj_com)
apply(subst (asm) sep_conj_assoc)
apply(erule (1) sep_conj_impl)
apply simp
done

lemma sep_conj_extract_decomposeD2:
  "(sep_conj_extract P \<and>\<^sup>* sep_true) s \<Longrightarrow> sep_points P s"
  by (simp add: sep_conj_extract_def sep_points_def)

lemma sep_point_mapD:
  "sep_points (p \<mapsto>\<^sup>i\<^sub>g v) s \<Longrightarrow> (p \<hookrightarrow>\<^sup>i\<^sub>g v) s"
  by (simp add: sep_points_def sep_map_inv_def sep_map'_inv_def sep_map'_def
                sep_conj_ac)

lemma sep_point_map_excD:
  "sep_points (p \<mapsto>\<^sub>g v) s \<Longrightarrow> (p \<hookrightarrow>\<^sub>g v) s"
  by (simp add: sep_points_def sep_map'_def)

lemma sep_point_otherD:
  "sep_points P s \<Longrightarrow> True"
  by (rule TrueI)

ML {*

val sep_point_ds = [@{thm sep_point_mapD}, @{thm sep_point_map_excD}]

fun sep_point_tacs ds ctxt  = [
    REPEAT1 (dresolve_tac ctxt [@{thm sep_conj_extract1D}] 1),
    REPEAT1 (dresolve_tac ctxt [@{thm sep_conj_extract2D}] 1),
    clarify_tac ctxt 1,
    TRY (full_simp_tac (put_simpset HOL_ss ctxt addsimps
        [@{thm sep_conj_extract_assoc}]) 1),
    REPEAT (dresolve_tac ctxt [@{thm sep_conj_extract_decomposeD},
        @{thm sep_conj_extract_decomposeD2}] 1 THEN
        clarify_tac ctxt 1),
    TRY (full_simp_tac ctxt 1),
    REPEAT (dresolve_tac ctxt (sep_point_ds@ds) 1),
    REPEAT (dresolve_tac ctxt [@{thm sep_point_otherD}] 1),
    TRY (full_simp_tac ctxt 1)
  ]

fun sep_point_tac ds ctxt = EVERY (sep_point_tacs ds ctxt)
*}

method_setup sep_point_tac =
  "Attrib.thms >> (fn thms => Method.SIMPLE_METHOD o sep_point_tac thms)"
  "extract points-to facts from separation assertions in assumptions"

lemma "(P \<and>\<^sup>* p \<mapsto>\<^sub>g v \<and>\<^sup>* Q) s \<Longrightarrow> (p \<hookrightarrow>\<^bsub>g\<^esub> v) s"
  by sep_point_tac


section "sep_exists_tac"

ML{*
fun sep_exists_tac ctxt = full_simp_tac
    (put_simpset HOL_ss ctxt addsimps [@{thm "sep_conj_exists1"}, @{thm "sep_conj_exists2"}])
*}

method_setup sep_exists_tac =
  "Scan.succeed (Method.SIMPLE_METHOD' o sep_exists_tac)"
  "push existentials inside separation assertions to the outside"

lemma "(P \<and>\<^sup>* (\<lambda>s. (\<exists>x. Q x s))) s \<Longrightarrow> \<exists>x. (P \<and>\<^sup>* Q x) s"
  by sep_exists_tac

section "sep_select_tac"

definition sep_mark :: "heap_assert \<Rightarrow> heap_assert" where
  "sep_mark \<equiv> id"

definition sep_mark2 :: "heap_assert \<Rightarrow> heap_assert" where
  "sep_mark2 \<equiv> id"

lemma sep_mark2_id:
  "sep_mark2 P = P"
  by (simp add: sep_mark2_def)

lemma sep_markI:
  "(\<box> \<and>\<^sup>* sep_mark (P \<and>\<^sup>* Q)) s \<Longrightarrow> (P \<and>\<^sup>* Q) s"
  by (simp add: sep_mark_def sep_conj_empty)

lemma sep_mark_match:
  "(R \<and>\<^sup>* sep_mark2 P \<and>\<^sup>* Q) s \<Longrightarrow> (R \<and>\<^sup>* sep_mark (P \<and>\<^sup>* Q)) s"
  by (simp add: sep_mark_def sep_mark2_def)

lemma sep_mark_match2:
  "(R \<and>\<^sup>* sep_mark2 P) s \<Longrightarrow> (R \<and>\<^sup>* sep_mark P) s"
  by (simp add: sep_mark_def sep_mark2_def)

lemma sep_mark_mismatch:
  "((R \<and>\<^sup>* P) \<and>\<^sup>* sep_mark Q) s \<Longrightarrow> (R \<and>\<^sup>* sep_mark (P \<and>\<^sup>* Q)) s"
  by (simp add: sep_mark_def sep_conj_ac)

lemma sep_mark_mismatch2:
  "(R \<and>\<^sup>* P) s \<Longrightarrow> (R \<and>\<^sup>* sep_mark P) s"
  by (simp add: sep_mark_def)

lemma sep_emp_rem:
  "P s \<Longrightarrow> (\<box> \<and>\<^sup>* P) s"
  by (simp add: sep_conj_empty)

lemma sep_mark2_left:
  "(P \<and>\<^sup>* (sep_mark2 Q \<and>\<^sup>* R)) = (sep_mark2 Q \<and>\<^sup>* (P \<and>\<^sup>* R))"
  by (rule sep_conj_left_com)

lemma sep_mark2_left2:
  "(P \<and>\<^sup>* sep_mark2 Q) = (sep_mark2 Q \<and>\<^sup>* P)"
  by (rule sep_conj_com)

ML {*

(* Replace all occurrences of an underscore that does not have an alphanumeric
   on either side of it *)
local
  val dummy_char = #" ";
  fun get_next (x::_) = x
    | get_next [] = dummy_char;
  fun nth_id n = "SEPTAC"^(Int.toString n);

  fun ok_char c = not (Char.isAlphaNum c);

  fun can_replace (prev,cur,last) =
        (ok_char prev) andalso (cur = #"_") andalso (ok_char last);

  fun replace_usc n prev_char (x::xs) =
      let val (xs', ys) = replace_usc (n+1) x xs
      in
        if can_replace (prev_char,x,get_next xs)
        then (nth_id n::xs', nth_id n::ys)
        else (String.str x::xs', ys)
      end
    | replace_usc _ _ [] = ([],[])
in
  val rusc = apfst String.concat o replace_usc 0 dummy_char o String.explode
end;

(* some tests *)
rusc "(_ +\<^sub>p _) \<mapsto> _";
rusc "_ \<mapsto>\<^sub>_ _";
rusc "_";
rusc "_ O_o _"
*}

ML{*

fun sep_select_tacs s ctxt  =
  let val (str, vars) = rusc s
      val subst = [((Lexicon.read_indexname "P", Position.none), str)]
      val fixes = map (fn v => (Binding.name v, NONE, Mixfix.NoSyn)) vars
  in
  [
    TRY (simp_tac (put_simpset HOL_ss ctxt addsimps [@{thm sep_conj_assoc}]) 1),
    resolve_tac ctxt [@{thm sep_markI}] 1,
    REPEAT (Rule_Insts.res_inst_tac ctxt subst fixes @{thm sep_mark_match} 1 ORELSE
      (Rule_Insts.res_inst_tac ctxt subst fixes @{thm sep_mark_match2} 1 ORELSE
      resolve_tac ctxt [@{thm sep_mark_mismatch}] 1 ORELSE
      resolve_tac ctxt [@{thm sep_mark_mismatch2}] 1)),
    TRY (simp_tac (put_simpset HOL_ss ctxt addsimps [@{thm sep_conj_assoc}]) 1),
    resolve_tac ctxt [@{thm sep_emp_rem}] 1,
    TRY (simp_tac (put_simpset HOL_ss ctxt addsimps [@{thm sep_mark2_left},
      @{thm sep_mark2_left2}]) 1),
    TRY (simp_tac (put_simpset HOL_ss ctxt addsimps [@{thm sep_mark2_id}]) 1)
  ]
  end

fun sep_select_tac s ctxt = SELECT_GOAL (EVERY (sep_select_tacs s ctxt))

fun lift_parser p (ctxt,ts) =
  let val (r, ts') = p ts
  in (r, (ctxt,ts')) end
*}

method_setup sep_select_tac =
  {* lift_parser Args.name >> (fn s => Method.SIMPLE_METHOD' o sep_select_tac s) *}
  "takes a target conjunct in the goal and reorders it to the front"

lemma
  "\<And>R x f n. ((P::heap_assert) \<and>\<^sup>* fac x n \<and>\<^sup>* R (f x)) s"
apply(sep_select_tac "fac _ _")
apply(sep_select_tac "R _")
apply(sep_select_tac "fac x _")
apply(sep_select_tac "R _")
oops

lemma
  "((P::heap_assert) \<and>\<^sup>* fac x n) s"
apply(sep_select_tac "fac _ _")
oops

lemma
  "((P::heap_assert) \<and>\<^sup>* long_name) s"
  apply(sep_select_tac "long_name")
oops

consts c_guard :: "'a::c_type ptr_guard"

lemma sep_heap_update'_hrs:
  "(c_guard \<turnstile>\<^sub>s\<^sup>i p \<and>\<^sup>* (p \<mapsto>\<^sup>i\<^sub>c_guard v \<longrightarrow>\<^sup>* P)) (lift_state s) \<Longrightarrow>
      P (lift_state (hrs_mem_update (heap_update p (v::'a::mem_type)) s))"
  by (case_tac s)
     (simp add: hrs_mem_update_def, erule sep_heap_update')

lemma sep_map_lift_wp_hrs:
  "\<lbrakk> \<exists>v. (p \<mapsto>\<^sup>i\<^sub>c_guard v \<and>\<^sup>* (p \<mapsto>\<^sup>i\<^sub>c_guard v \<longrightarrow>\<^sup>* P v)) (lift_state s) \<rbrakk>
      \<Longrightarrow> P (lift (hrs_mem s) (p::'a::mem_type ptr)) (lift_state s)"
  by (case_tac s)
     (simp add: hrs_mem_def, erule sep_map_lift_wp)

lemma ptr_retyp_sep_cut'_wp_hrs:
  "\<lbrakk> (sep_cut' (ptr_val p) (size_of TYPE('a)) \<and>\<^sup>* (c_guard \<turnstile>\<^sub>s\<^sup>i p \<longrightarrow>\<^sup>* P))
      (lift_state s); c_guard (p::'a::mem_type ptr) \<rbrakk>
      \<Longrightarrow> P (lift_state (hrs_htd_update (ptr_retyp p) s))"
  by (case_tac s)
     (simp add: hrs_htd_update_def, erule (1) ptr_retyp_sep_cut'_wp)

ML {*

fun destruct bs (Bound n)      = Free (List.nth (bs,n))
  | destruct bs (Abs (s,ty,t)) = destruct ((s,ty)::bs) t
  | destruct bs (l$r)          = destruct bs l $ destruct bs r
  | destruct _  x              = x

fun schems (Abs (_,_,t)) = schems t
  | schems (l$r)         = schems l + schems r
  | schems (Var _)       = 1
  | schems _             = 0

fun hrs_mem_update (Const (@{const_name "HeapRawState.hrs_mem_update"},_)$_$s) = SOME s
  | hrs_mem_update _                                             = NONE

fun hrs_htd_update (Const (@{const_name "HeapRawState.hrs_htd_update"},_)$_$s) = SOME s
  | hrs_htd_update _                                             = NONE

fun lift_state_arg _   _  (Const (@{const_name "TypHeap.lift_state"},_)$s) = SOME s
  | lift_state_arg thy nc (l$r)                              =
        (case lift_state_arg thy nc r of
          SOME s => if nc orelse hrs_mem_update s <> NONE orelse
                        hrs_htd_update s <> NONE then SOME s
                        else lift_state_arg thy nc l
         | NONE   => lift_state_arg thy nc l)
  | lift_state_arg thy nc (Abs (_,_,t))                      =
        lift_state_arg thy nc t
  | lift_state_arg _ _ _ =
        NONE (*error (Sign.string_of_term thy s)*)

fun term_of_thm thm = Thm.term_of (Thm.cprop_of thm)

fun lift_tac ctxt s old_schems =
  Rule_Insts.res_inst_tac ctxt [((Lexicon.read_indexname "s",Position.none),s)] [] @{thm sep_map_lift_wp_hrs} 1 THEN
  (fn thm => if schems (term_of_thm thm) = old_schems then all_tac thm
                 else no_tac thm)

fun heap_update_tac ctxt s =
  Rule_Insts.res_inst_tac ctxt [((Lexicon.read_indexname "s",Position.none),s)] [] @{thm sep_heap_update'_hrs} 1

fun ptr_retyp_tac ctxt s =
  Rule_Insts.res_inst_tac ctxt [((Lexicon.read_indexname "s",Position.none),s)] [] @{thm ptr_retyp_sep_cut'_wp_hrs} 1

fun sep_wp_step_tac' ctxt lift_only s old_schems = let
  fun prt s = (
    case s of
        Free (a, _) => a
      | _ => raise TERM ("Not a free variable",[s]))
  val state = prt s
  val step = case hrs_mem_update s of
               SOME s => heap_update_tac ctxt (prt s)
             | NONE => case hrs_htd_update s of
                         SOME s => ptr_retyp_tac ctxt (prt s)
                       | NONE => no_tac
in
  TRY (lift_tac ctxt state old_schems) THEN (if lift_only then all_tac else step)
end

fun sep_wp_step_tac ctxt lift_only thm = let
  val t = term_of_thm thm
  val thy = Proof_Context.theory_of ctxt
  val old_schems = schems t
  val s = lift_state_arg thy lift_only (destruct [] t)
in
  (case s of
    SOME state => sep_wp_step_tac' ctxt lift_only state old_schems
   | NONE => no_tac) thm
end

fun sep_wp_tac ctxt = (REPEAT (sep_wp_step_tac ctxt false)) THEN sep_wp_step_tac ctxt true

*}

method_setup sep_wp_tac =
  "Scan.succeed (Method.SIMPLE_METHOD o sep_wp_tac)"
  "apply WP separation logic rules to goal"


(* see testfiles/sep_example_pre_list.thy for a more detailed example *)
lemma
  "((\<lambda>z. lift (hrs_mem s) (p::(32 word) ptr) + 1 = 2) \<and>\<^sup>* P) (lift_state s)"
apply sep_wp_tac
oops


end
