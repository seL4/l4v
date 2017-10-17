(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory CProof
imports
  "umm_heap/SepFrame"
  "Simpl/Vcg"
  "umm_heap/StructSupport"
  "umm_heap/ArrayAssertion"
begin

(* name generation is the only thing this theory wants, but that
   depends on Absyn, which depends on a bunch of other stuff. *)
ML_file "General.ML"
ML_file "openUnsynch.ML"
ML_file "SourcePos.ML"
ML_file "SourceFile.ML"
ML_file "Region.ML"
ML_file "Binaryset.ML"
ML_file "Feedback.ML"
ML_file "basics.ML"
ML_file "MString.ML"

ML_file "TargetNumbers-sig.ML"
ML_file "./umm_heap/$L4V_ARCH/TargetNumbers.ML"

ML_file "RegionExtras.ML"
ML_file "Absyn-CType.ML"
ML_file "Absyn-Expr.ML"
ML_file "Absyn-StmtDecl.ML"
ML_file "Absyn.ML"
ML_file "Absyn-Serial.ML"
ML_file "name_generation.ML"


(* set up hoare package to rewrite state updates more *)
setup {*
  Hoare.add_foldcongsimps [@{thm "update_update"}, @{thm "o_def"}]
*}


(* Syntax for apply antiquotation parsing explicitly *)
syntax
  "_quote"  :: "'b => ('a => 'b)"  ("([.[_].])" [0] 1000)

(* Override assertion translation so we can apply the parse translations below
   and add \<star> syntax. *)
syntax
  "_heap" :: "'b \<Rightarrow> ('a \<Rightarrow> 'b)"
  "_heap_state" :: "'a" ("\<zeta>") (* FIXME: horrible syntax *)
  "_heap_stateOld" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b" ("\<^bsup>_\<^esup>\<zeta>" [100] 100) (* FIXME: horrible syntax *)

  "_derefCur" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b" ("\<star>_" [100] 100)
  "_derefOld" :: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b" ("\<^bsup>_\<^esup>\<star>_" [100,100] 100)

translations
  "{|b|}" => "CONST Collect (_quote (_heap b))"

definition sep_app :: "(heap_state \<Rightarrow> bool) \<Rightarrow> heap_state \<Rightarrow> bool" where
  "sep_app P s \<equiv> P s"

definition hrs_id :: "heap_raw_state \<Rightarrow> heap_raw_state" where
  "hrs_id \<equiv> id"

declare hrs_id_def [simp add]

parse_translation {*
let
  fun ac x = Syntax.const "_antiquoteCur" $ Syntax.const x
  fun aco x y = Syntax.const y $ (Syntax.const "globals" $ x)
  fun hd a = a NameGeneration.global_heap_var
  fun d a = Syntax.const "hrs_htd" $ hd a
  fun repl (Abs (s,T,t)) = Abs (s,T,repl t)
    | repl (Const ("_h_t_valid",_)$x) = Syntax.const "h_t_valid" $ d ac $ Syntax.const "c_guard" $ x
    | repl (Const ("_derefCur",_)$x) = Syntax.const "the" $
        (Syntax.const "lift_t" $ hd ac $ x)
    | repl (Const ("_derefOld",_)$x$y) = Syntax.const "the" $
        (Syntax.const "lift_t" $ hd (aco x) $ y)
    | repl (Const ("_heap_state",_)) = Syntax.const "hrs_id" $ hd ac
    | repl (Const ("_heap_stateOld",_)$x) = Syntax.const "hrs_id" $ hd (aco x)
    | repl (x$y) = repl x $ repl y
    | repl x = x
  fun heap_assert_tr [b] = repl b
    | heap_assert_tr ts = raise TERM ("heap_assert_tr", ts);
in [("_heap",K heap_assert_tr)] end;
*}


(* Separation logic assertion parse translation *)
parse_translation {*
let
  fun ac x = Syntax.const "_antiquoteCur" $ Syntax.const x
  fun aco x y = Syntax.const y $ (Syntax.const "globals" $ x)
  fun hd a = Syntax.const "lift_state" $ (a NameGeneration.global_heap_var)
  fun st2 (Abs (s,T,t)) n = Abs (s,T,st2 t (n+1))
    | st2 (Bound k) n = Bound (if k < n then k else k + 1)
    | st2 (x$y) n = st2 x n $ st2 y n
    | st2 x _ = x
  fun st1 (Abs (s,T,t)) n = Abs (s,T,st1 t (n+1))
    | st1 (Bound k) n = Bound (if k < n then k else k + 1)
    | st1 (Const ("sep_empty",_)) n = Syntax.const "sep_empty" $ Bound n
    | st1 (Const ("sep_map",_)$x$y) n = Syntax.const "sep_map" $
        (st2 x n) $ (st2 y n) $ Bound n
    | st1 (Const ("sep_map'",_)$x$y) n = Syntax.const "sep_map'" $
        (st2 x n) $ (st2 y n) $ Bound n
    | st1 (Const ("sep_conj",_)$x$y) n = Syntax.const "sep_conj" $
        (nst2 x n) $ (nst2 y n) $ Bound n
    | st1 (Const ("sep_impl",_)$x$y) n = Syntax.const "sep_impl" $
        (nst2 x n) $ (nst2 y n) $ Bound n
    | st1 (x$y) n = st1 x n $ st1 y n
    | st1 x _ = x
  and new_heap t = Abs ("s",dummyT,st1 t 0)
  and nst2 x n = new_heap (st2 x n);
  fun sep_tr [t] = Syntax.const "sep_app" $ (*new_heap *) t $ hd ac
    | sep_tr ts = raise TERM ("sep_tr", ts);
in [("_sep_assert",K sep_tr)] end;
*}


definition c_null_guard :: "'a::c_type ptr_guard" where
  "c_null_guard \<equiv> \<lambda>p. 0 \<notin> {ptr_val p..+size_of TYPE('a)}"

lemma c_null_guard:
  "c_null_guard (p::'a::mem_type ptr) \<Longrightarrow> p \<noteq> NULL"
apply(clarsimp simp: c_null_guard_def)
apply(erule notE)
apply(rule intvl_self)
apply simp
done

overloading c_guard_def \<equiv> c_guard begin
definition
c_guard_def:  "c_guard_def \<equiv> \<lambda>p. ptr_aligned p \<and> c_null_guard p"
end

definition
c_fnptr_guard_def: "c_fnptr_guard (fnptr::unit ptr) \<equiv> ptr_val fnptr \<noteq> 0"

lemma c_guardD:
  "c_guard (p::'a::mem_type ptr) \<Longrightarrow> ptr_aligned p \<and> p \<noteq> NULL"
apply(clarsimp simp: c_guard_def)
apply(drule c_null_guard)
apply simp
done

lemma c_guard_ptr_aligned:
  "c_guard p \<Longrightarrow> ptr_aligned p"
  by (simp add: c_guard_def)

lemma c_guard_NULL:
  "c_guard (p::'a::mem_type ptr) \<Longrightarrow> p \<noteq> NULL"
  by (simp add: c_guardD)

lemma c_guard_NULL_simp [simp]:
  "\<not> c_guard (NULL::'a::mem_type ptr)"
  by (force dest: c_guard_NULL)

lemma c_guard_mono:
  "guard_mono (c_guard::'a::mem_type ptr_guard) (c_guard::'b::mem_type ptr_guard)"
apply(clarsimp simp: guard_mono_def c_guard_def)
apply(subgoal_tac   "guard_mono (ptr_aligned::'a::mem_type ptr_guard) (ptr_aligned::'b::mem_type ptr_guard)")
 prefer 2
 apply(rule ptr_aligned_mono)
apply(clarsimp simp: guard_mono_def)
apply(clarsimp simp: ptr_aligned_def)
apply(clarsimp simp: c_null_guard_def typ_uinfo_t_def)
apply(frule field_lookup_export_uinfo_Some_rev)
apply clarsimp
apply(drule_tac p=p in field_tag_sub)
apply(clarsimp simp: field_lvalue_def field_offset_def field_offset_untyped_def typ_uinfo_t_def)
apply(subgoal_tac "size_td k = size_of TYPE('b)")
 apply simp
 apply fast
apply(clarsimp simp: size_of_def)
apply(subst typ_uinfo_size [symmetric])
apply(drule_tac s="export_uinfo k" in sym)
apply(subst typ_uinfo_t_def)
apply simp
done

lemma c_guard_NULL_fl:
  "\<lbrakk> c_guard (p::'a::mem_type ptr);
      field_lookup (typ_info_t TYPE('a)) f 0 = Some (t,n);
      export_uinfo t = typ_uinfo_t TYPE('b::mem_type) \<rbrakk> \<Longrightarrow> 0 < &(p\<rightarrow>f)"
apply(insert c_guard_mono)
apply(clarsimp simp: guard_mono_def)
apply((erule allE)+)
apply(erule impE)
 apply rule
  apply assumption
 apply(drule field_lookup_export_uinfo_Some)
 apply(simp add: typ_uinfo_t_def)
apply(drule field_lookup_export_uinfo_Some)
apply(simp add: field_lvalue_def field_offset_def field_offset_untyped_def typ_uinfo_t_def)
apply(unfold c_guard_def)
apply clarsimp
apply(drule c_null_guard)+
apply clarsimp
done

lemma c_guard_ptr_aligned_fl:
  "\<lbrakk> c_guard (p::'a::mem_type ptr);
      field_lookup (typ_info_t TYPE('a)) f 0 = Some (t,n);
      export_uinfo t = typ_uinfo_t TYPE('b::mem_type) \<rbrakk> \<Longrightarrow>
      ptr_aligned ((Ptr &(p\<rightarrow>f))::'b ptr)"
apply(insert c_guard_mono)
apply(clarsimp simp: guard_mono_def)
apply((erule allE)+)
apply(erule impE)
 apply rule
  apply assumption
 apply(drule field_lookup_export_uinfo_Some)
 apply(simp add: typ_uinfo_t_def)
apply(drule field_lookup_export_uinfo_Some)
apply(unfold c_guard_def)
apply(simp add: field_lvalue_def field_offset_def field_offset_untyped_def typ_uinfo_t_def)
done

(* StrictC guard separation syntax translations *)

(* FIXME: make these abbreviations *)
syntax
  "_sep_map" :: "'a::c_type ptr \<Rightarrow> 'a \<Rightarrow> heap_assert" ("_ \<mapsto> _" [56,51] 56)
  "_sep_map_any" :: "'a::c_type ptr \<Rightarrow> heap_assert" ("_ \<mapsto> -" [56] 56)
  "_sep_map'" :: "'a::c_type ptr \<Rightarrow> 'a \<Rightarrow> heap_assert" ("_ \<hookrightarrow>  _" [56,51] 56)
  "_sep_map'_any" :: "'a::c_type ptr \<Rightarrow> heap_assert" ("_ \<hookrightarrow> -" [56] 56)
  "_tagd" :: "'a::c_type ptr \<Rightarrow> heap_assert" ("\<turnstile>\<^sub>s _" [99] 100)

translations
  "p \<mapsto> v" == "p \<mapsto>\<^sup>i\<^sub>(CONST c_guard) v"
  "p \<mapsto> -" == "p \<mapsto>\<^sup>i\<^sub>(CONST c_guard) -"
  "p \<hookrightarrow> v" == "p \<hookrightarrow>\<^sup>i\<^sub>(CONST c_guard) v"
  "p \<hookrightarrow> -" == "p \<hookrightarrow>\<^sup>i\<^sub>(CONST c_guard) -"
  "\<turnstile>\<^sub>s p" == "CONST c_guard \<turnstile>\<^sub>s\<^sup>i p"

term "x \<mapsto> y"
term "(x \<mapsto> y \<and>\<^sup>* y \<mapsto> z) s"
term "(x \<mapsto> y \<and>\<^sup>* y \<mapsto> z) \<and>\<^sup>* x \<mapsto> y"
term "\<turnstile>\<^sub>s p"

lemma sep_map_NULL [simp]:
  "NULL \<mapsto> (v::'a::mem_type) = sep_false"
  by (force simp: sep_map_def sep_map_inv_def c_guard_def
            dest: lift_typ_heap_g sep_conjD c_null_guard)

lemma sep_map'_NULL_simp [simp]:
  "NULL \<hookrightarrow> (v::'a::mem_type) = sep_false"
apply(simp add: sep_map'_def sep_map'_inv_def sep_conj_ac)
apply(subst sep_conj_com, subst sep_map_inv_def [symmetric])
apply simp
done

lemma sep_map'_ptr_aligned:
  "(p \<hookrightarrow> v) s \<Longrightarrow> ptr_aligned p"
apply(rule c_guard_ptr_aligned)
apply(erule sep_map'_g)
done

lemma sep_map'_NULL:
  "(p \<hookrightarrow> (v::'a::mem_type)) s \<Longrightarrow> p \<noteq> NULL"
apply(rule c_guard_NULL)
apply(erule sep_map'_g)
done

lemma tagd_sep_false [simp]:
  "\<turnstile>\<^sub>s (NULL::'a::mem_type ptr) = sep_false"
  by (auto simp: tagd_inv_def tagd_def dest!: sep_conjD s_valid_g)

(* Print translations for pointer dereferencing in program statements and
   expressions.
*)
syntax (output)
  "_Deref" :: "'b \<Rightarrow> 'b" ("*_" [1000] 1000)
  "_AssignH" :: "'b => 'b => ('a,'p,'f) com" ("(2*_ :==/ _)" [30, 30] 23)

print_translation {*
let
  fun deref (Const ("_antiquoteCur",_)$Const (h,_)) p =
      if h=NameGeneration.global_heap then Syntax.const "_Deref" $ p else
        raise Match
    | deref h p = raise Match
  fun lift_tr [h,p] = deref h p
    | lift_tr ts = raise Match
  fun deref_update (Const ("heap_update",_)$l$r$(Const ("_antiquoteCur",_)$
    Const (h,_))) =
      if h=NameGeneration.global_heap then Syntax.const "_AssignH" $ l $ r
        else raise Match
    | deref_update x = raise Match
  (* First we need to determine if this is a heap update or normal assign *)
  fun deref_assign (Const ("_antiquoteCur",_)$Const (h,_)) r =
      if h=NameGeneration.global_heap then deref_update r else
        raise Match
    | deref_assign l r = raise Match
  fun assign_tr [l,r] = deref_assign l r
    | assign_tr ts = raise Match
in [("CTypesDefs.lift",K lift_tr),("_Assign",K assign_tr)] end;
*}

print_translation {*
let
  fun sep_app_tr [l,r] = Syntax.const "_sep_assert" $ l
    | sep_app_tr ts = raise Match
in [("sep_app",K sep_app_tr)] end;
*}

syntax "_h_t_valid" :: "'a::c_type ptr \<Rightarrow> bool" ("\<Turnstile>\<^sub>t _" [99] 100)

(* will only work when globals record is defined
term "\<lbrace> \<Turnstile>\<^sub>t bar \<rbrace>" *)

abbreviation
  "lift_t_c" :: "heap_mem \<times> heap_typ_desc \<Rightarrow> 'a::c_type typ_heap"
where
  "lift_t_c s == lift_t c_guard s"

syntax
  "_h_t_valid" :: "heap_typ_desc \<Rightarrow> 'a::c_type ptr \<Rightarrow> bool"  ("_ \<Turnstile>\<^sub>t _" [99,99] 100)
translations
  "d \<Turnstile>\<^sub>t p" == "d,CONST c_guard \<Turnstile>\<^sub>t p"

lemma h_t_valid_c_guard:
  "d \<Turnstile>\<^sub>t p \<Longrightarrow> c_guard p"
  by (clarsimp simp: h_t_valid_def)

lemma h_t_valid_NULL [simp]:
  "\<not> d \<Turnstile>\<^sub>t (NULL::'a::mem_type ptr)"
  by (clarsimp simp: h_t_valid_def dest!: c_guard_NULL)

lemma h_t_valid_ptr_aligned:
  "d \<Turnstile>\<^sub>t p  \<Longrightarrow> ptr_aligned p"
  by (auto simp: h_t_valid_def dest: c_guard_ptr_aligned)

lemma lift_t_NULL:
  "lift_t_c s (NULL::'a::mem_type ptr) = None"
apply(case_tac s)
apply(auto simp: lift_t_if)
done

lemma lift_t_ptr_aligned [simp]:
  "lift_t_c s p = Some v \<Longrightarrow> ptr_aligned p"
  by (auto dest: lift_t_g c_guard_ptr_aligned)

lemmas c_typ_rewrs = typ_rewrs h_t_valid_ptr_aligned lift_t_NULL

datatype c_exntype = Break | Return | Continue
datatype strictc_errortype =
         Div_0
       | C_Guard (* merge of Alignment and Null_Dereference *)
       | MemorySafety
       | ShiftError
       | SideEffects
       | ArrayBounds
       | SignedArithmetic
       | DontReach
       | GhostStateError
       | UnspecifiedSyntax
       | OwnershipError
       | UndefinedFunction
       | AdditionalError string
       | ImpossibleSpec

definition
  unspecified_syntax_error :: "string => bool"
where
  "unspecified_syntax_error s = False"

lemmas hrs_simps = hrs_mem_update_def hrs_mem_def hrs_htd_update_def
    hrs_htd_def

lemma sep_map'_lift_lift:
  fixes pa :: "'a :: mem_type ptr" and xf :: "'a \<Rightarrow> 'b :: mem_type"
  assumes fl: "(field_lookup (typ_info_t TYPE('a)) f 0) \<equiv>
  Some (adjust_ti (typ_info_t TYPE('b)) xf (xfu \<circ> (\<lambda>x _. x)), m')"
  and   xf_xfu: "fg_cons xf (xfu \<circ> (\<lambda>x _. x))"
  shows "(pa \<hookrightarrow> v)(lift_state h) \<Longrightarrow> CTypesDefs.lift (fst h) (Ptr &(pa\<rightarrow>f)) = xf v"
  using fl xf_xfu
  apply -
  apply (clarsimp simp: o_def)
  apply (rule sep_map'_lift [OF sep_map'_field_map_inv, where g1=c_guard])
      apply (subst (asm) surjective_pairing [where t = h])
      apply assumption
     apply fastforce
    apply (subst export_tag_adjust_ti2 [OF _ wf_lf wf_desc])
     apply (simp add: fg_cons_def)
    apply (rule meta_eq_to_obj_eq [OF typ_uinfo_t_def, symmetric])
   apply (rule guard_mono_True)
  apply (subst access_ti\<^sub>0_update_ti)
  apply (subst access_ti\<^sub>0_to_bytes)
  apply (subst o_def)
  apply (rule inv_p [symmetric])
  done

lemma lift_t_update_fld_other:
  fixes val :: "'b :: mem_type" and ptr :: "'a :: mem_type ptr"
  assumes   fl: "field_ti TYPE('a) f = Some (adjust_ti (typ_info_t TYPE('b)) xf (xfu \<circ> (\<lambda>x _. x)))"
  and   xf_xfu: "fg_cons xf (xfu \<circ> (\<lambda>x _. x))"
  and     disj: "typ_uinfo_t TYPE('c :: mem_type) \<bottom>\<^sub>t typ_uinfo_t TYPE('b)"
  and       cl: "lift_t c_guard hp ptr = Some z"
  shows "(lift_t c_guard (hrs_mem_update (heap_update (Ptr &(ptr\<rightarrow>f)) val) hp)) =
  (lift_t c_guard hp :: 'c :: mem_type typ_heap)"
  (is "?LHS = ?RHS")
proof -
  let ?ati = "adjust_ti (typ_info_t TYPE('b)) xf (xfu \<circ> (\<lambda>x _. x))"
  have eui: "typ_uinfo_t TYPE('b) = export_uinfo (?ati)" using xf_xfu
    apply (subst export_tag_adjust_ti2 [OF _ wf_lf wf_desc])
    apply (simp add: fg_cons_def )
    apply (rule meta_eq_to_obj_eq [OF typ_uinfo_t_def])
    done

  have cl': "lift_t c_guard (fst hp, snd hp) ptr = Some z" using cl by simp

  show ?thesis using fl
    apply (clarsimp simp add: hrs_mem_update_def split_def field_ti_def split: option.splits)
    apply (subst typ_rewrs(5))
      apply (rule lift_t_mono)
       apply assumption
      apply (rule cl')
       apply (rule eui [symmetric])
      apply (rule guard_mono_True)
     apply (rule disj)
    apply simp
    done
qed

lemma idupdate_compupdate_fold_congE:
  assumes idu: "\<And>r. upd (\<lambda>x. accr r) r = r"
  assumes cpu: "\<And>f f' r. upd f (upd f' r) = upd (f o f') r"
  and       r: "r = r'" and v: "accr r' = v'"
  and       f: "\<And>v. v' = v \<Longrightarrow> f v = f' v"
  shows        "upd f r = upd f' r'"
  apply (subgoal_tac "upd (f o (\<lambda>x. accr r')) r' = upd (f' o (\<lambda>x. accr r')) r'")
   apply (simp add: cpu[symmetric] idu r)
  apply (simp add: o_def f v)
  done

lemma field_lookup_field_ti:
  "field_lookup (typ_info_t TYPE('a :: c_type)) f 0 \<equiv> Some (a, b) \<Longrightarrow> field_ti TYPE('a) f = Some a"
  unfolding field_ti_def by simp

definition
  lvar_nondet_init :: "(('c,'d) state_scheme \<Rightarrow> 'a) \<Rightarrow> (('a \<Rightarrow> 'a) \<Rightarrow> (('c, 'd) state_scheme \<Rightarrow> ('c, 'd) state_scheme))
           \<Rightarrow> (('c, 'd) state_scheme, 'x, 'e) com"
where
  "lvar_nondet_init accessor upd \<equiv> Spec {(s, t). \<exists>v. t = (upd (\<lambda>_. v)) s}"

axiomatization
  asm_semantics :: "string \<Rightarrow> addr list
    \<Rightarrow> (heap_mem \<times> 'a) \<Rightarrow> (addr \<times> (heap_mem \<times> 'a)) set"
and
  asm_fetch :: "'s \<Rightarrow> (heap_mem \<times> 'a)"
and
  asm_store :: "('s \<Rightarrow> 'b) \<Rightarrow> (heap_mem \<times> 'a) \<Rightarrow> 's \<Rightarrow> 's"
where
  asm_semantics_enabled:
    "\<forall>iv. asm_semantics nm addr iv \<noteq> {}"
and
  asm_store_eq:
    "\<forall>x s. ghost_data (asm_store ghost_data x s) = ghost_data s"

definition
  asm_spec :: "'a itself \<Rightarrow> ('g \<Rightarrow> 'b) \<Rightarrow> bool \<Rightarrow> string
    \<Rightarrow> (addr \<Rightarrow> ('g, 's) state_scheme \<Rightarrow> ('g, 's) state_scheme)
    \<Rightarrow> (('g, 's) state_scheme \<Rightarrow> addr list)
    \<Rightarrow> (('g, 's) state_scheme \<times> ('g, 's) state_scheme) set"
where
  "asm_spec ti gdata vol spec lhs vs
    = {(s, s'). \<exists>(v', (gl' :: (heap_mem \<times> 'a)))
            \<in> asm_semantics spec (vs s) (asm_fetch (globals s)).
        s' = lhs v' (globals_update (asm_store gdata gl') s)}"

lemma asm_spec_enabled:
  "\<exists>s'. (s, s') \<in> asm_spec ti gdata vol spec lhs vs"
  using asm_semantics_enabled[rule_format, where nm = spec
    and addr="vs s" and iv="asm_fetch (globals s)"]
  by (auto simp add: asm_spec_def)

lemma asm_specE:
  assumes s: "(s, s') \<in> asm_spec (ti :: 'a itself) gdata vol spec lhs vs"
  and concl: "\<And>v' gl'. \<lbrakk> (v', (gl' :: (heap_mem \<times> 'a))) \<in> asm_semantics spec (vs s) (asm_fetch (globals s));
        s' = lhs v' (globals_update (asm_store gdata gl') s);
        gdata (asm_store gdata gl' (globals s)) = gdata (globals s) \<rbrakk>
        \<Longrightarrow> P"
  shows "P"
  using s concl
  by (clarsimp simp: asm_spec_def asm_store_eq)

lemmas state_eqE = arg_cong[where f="\<lambda>s. (globals s, state.more s)", elim_format]

lemmas asm_store_eq_helper
    = arg_cong2[where f="op =" and a="asm_store f v s"]
      arg_cong2[where f="op =" and c="asm_store f v s"]
  for f v s

definition
  asm_semantics_ok_to_ignore :: "'a itself \<Rightarrow> bool \<Rightarrow> string \<Rightarrow> bool"
where
  "asm_semantics_ok_to_ignore ti volatile specifier
    = (\<forall>xs gl. snd ` asm_semantics specifier xs (gl :: (heap_mem \<times> 'a)) = {gl})"

end
