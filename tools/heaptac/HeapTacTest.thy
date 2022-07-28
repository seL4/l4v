
theory HeapTacTest
imports HeapTac
begin

text {* The basic idea is that we wish to take a term Q and construct a term P such that

        H |- P = Q.
    
        where H is some set of hypotheses obtained by assuming some of the premises of a set of
        rewrite rules.  There will be some magic here to figure out which rules to apply, so this
        is not going to be a generic tactic (as opposed to e.g. strengthen)
     *}


declare [[populate_globals=true]]
declare [[record_codegen = false]]
declare [[allow_underscore_idents = true]]

install_C_file memsafe "test.c"

(* Testing MemoCache *)
ML_val
\<open>
let 
  fun doit f t   = (tracing ("Hi, got " ^ Syntax.string_of_term @{context} t); 
                   case t of
                       a $ b => f a $ f b
                     | _     => t
                     )
  val cache = MemoCache.create Termtab.empty Termtab.lookup Termtab.update doit
  val t1    = @{term True}
  val t2    = @{term False}
  val t3    = @{term "True \<longrightarrow> False"}
in
  (cache t1; tracing "t1"; cache t3; tracing "t1"; cache t1; tracing "t2"; cache t2)
end;
\<close>

context test
begin

abbreviation "IG \<equiv> {SignedArithmetic,ShiftError}"

abbreviation (input) "triple P c Q \<equiv> \<Gamma> \<turnstile>\<^bsub>/IG\<^esub> P c Q"

local_setup \<open>Umm_Support.local_setup\<close>

ML_val \<open>
let val ct = @{cterm "CLIFT(foo_C)
    (hrs_mem_update (heap_update (PTR(32 word)
                                  &(PTR(baz_C) &(PTR(bar_C) &((p :: foobatbaz_C ptr)\<rightarrow>[''foo_bar_C''])\<rightarrow>[''bar_baz_C'']) \<rightarrow> [''baz_x_C'']))
                                  v) hp)"}
    val ct' = @{cterm "CLIFT(foobatbaz_C)
    (hrs_mem_update (heap_update (PTR(32 signed word)
                                  &(PTR(baz_C) &((p :: bar_C ptr)\<rightarrow>[''bar_baz_C'']) \<rightarrow> [''baz_x_C'']))
                                  v) hp)"}
in
  Umm_Support.lift_t_simproc_fun @{context} ct
end
\<close>

ML_val \<open>
  let val tm0 =  @{term "(PTR(32 signed word)
                        &(PTR(baz_C) &(PTR(bar_C) &((p :: foobatbaz_C ptr)\<rightarrow>[''foo_bar_C''])\<rightarrow>[''bar_baz_C'']) \<rightarrow> [''baz_x_C'']))"}
      val tm =  @{term "(PTR(baz_C) &((p :: foobatbaz_C ptr)\<rightarrow>[''foo_baz_C'']))"}
      val r = Umm_Support.determine_type_relationship (Umm_Support.umm_thm_info_for @{context})  @{typ "foo_C"} tm0
  in r
  end
\<close>
(* lemma eq_into_imp2: "x == y ==> PROP Trueprop y \<Longrightarrow> PROP Trueprop x" by simp*)



(* TESTS *)

lemma triangle_test:
  "CLIFT(bar_C) (hrs_mem_update (heap_update (PTR(baz_C) &((p :: foobatbaz_C ptr)\<rightarrow>[''foo_baz_C''])) v) hp) = CLIFT(bar_C) hp"
  apply umm_strg
  oops

(*
  ML_val
   \<open> let open Umm_Support
     val {goal, context = goal_ctxt, ...} = @{Isar.goal}; 
     val (focus as {params, asms, concl, ...}, goal') =
       Subgoal.focus_params goal_ctxt 1 NONE goal; 
     val lhs = (* Thm.dest_arg*) (Thm.dest_arg concl)
     val tinfo = Umm_Support.umm_thm_info_for goal_ctxt
     val ptr  = @{term "(PTR(baz_C) &((p :: foobatbaz_C ptr)\<rightarrow>[''foo_baz_C'']))"}
     val path = Umm_Support.dest_pointer_path ptr

     val lift_typ =  @{typ bar_C}
(*     val r = determine_type_relationship tinfo lift_typ ptr *)
(*     val thm = Umm_Support.lift_t_heap_update_conv @{context} lhs  *)
    fun type_is_child c p = #sub_typ_cache tinfo (c, p)
    val find_fld_path = get_index (fn (_, typ) => type_is_child typ lift_typ)
    val r = find_fld_path path
    val r' = type_is_child @{typ baz_C} @{typ bar_C}
    val SOME (idx, _) = find_fld_path path 
    val (_, typ') = List.nth (path, idx - 1)  
(*
    val x =  repeat_conv_n 1 (move_heap_field_upd_conv tinfo goal_ctxt) lhs
*)
    in  (r, Option.map Lazy.force r')
    end

   \<close>
*)


(* Random stuff below *)


lemma "A \<and> CLIFT(32 word)
               (hrs_mem_update (heap_update (PTR(32 signed word)
                                         &(PTR(baz_C) &(PTR(bar_C) &((p :: foobatbaz_C ptr)\<rightarrow>[''foo_bar_C''])\<rightarrow>[''bar_baz_C'']) \<rightarrow> [''baz_x_C'']))
                                           v) hp) = X"
  apply umm_strg
  apply simp
  oops

lemma 
  fixes p :: "foobatbaz_C ptr"
  defines "ptr \<equiv> PTR(32 signed word) &(PTR(baz_C) &(PTR(bar_C) &(p \<rightarrow>[''foo_bar_C''])\<rightarrow>[''bar_baz_C'']) \<rightarrow> [''baz_x_C''])"
  shows "A \<and> CLIFT(32 signed word) (hrs_mem_update (heap_update ptr v) hp) (PTR(32 signed word) &((q :: baz_C ptr) \<rightarrow> [''baz_x_C'']))  = X"
  unfolding ptr_def
  apply umm_strg
  oops

lemma 
  fixes p :: "foobatbaz_C ptr"
  defines "ptr \<equiv> PTR(32 signed word) &(PTR(baz_C) &(PTR(bar_C) &(p \<rightarrow>[''foo_bar_C''])\<rightarrow>[''bar_baz_C'']) \<rightarrow> [''baz_x_C''])"
  assumes "Z = (if CLIFT(32 signed word) (hrs_mem_update (heap_update ptr v) hp) (PTR(32 signed word) &((q :: baz_C ptr) \<rightarrow> [''baz_x_C''])) = X then 1 else 0)"
  and    "True = True"
  shows "Y = (if CLIFT(32 signed word) (hrs_mem_update (heap_update ptr v) hp) (PTR(32 signed word) &((q :: baz_C ptr) \<rightarrow> [''baz_x_C''])) = X then 1 else 0)"
  using assms unfolding ptr_def
  apply -
  apply umm_strg_asms
  oops


lemma "CLIFT(bar_C)
    (hrs_mem_update (heap_update (PTR(32 word)
                                  &(PTR(baz_C) &(PTR(bar_C) &((p :: foobatbaz_C ptr)\<rightarrow>[''foo_bar_C''])\<rightarrow>[''bar_baz_C'']) \<rightarrow> [''baz_x_C'']))
                                  v) hp) = X"
  apply umm_strg
  oops

(* Not actually true *)
lemma "\<forall>s. triple \<lbrace>s. True\<rbrace> (\<acute>ret__int :== PROC do_something(\<acute>foo, \<acute>contains_foo, \<acute>no_foo)) {t. CLIFT(foo_C) (t_hrs_' (globals t)) = CLIFT(foo_C) (t_hrs_' (globals s)) }"
  apply vcg 
  apply(intro conjI)
  prefer 8
  apply umm_strg
           apply simp
  oops

lemma "\<forall>(x :: baz_C ptr). 
    CLIFT(baz_C) (hrs_mem_update (heap_update (PTR(32 signed word) &((ptr :: baz_C ptr) \<rightarrow> [''baz_x_C''])) v) hp) = Y \<and>
    CLIFT(baz_C) (hrs_mem_update (heap_update (PTR(32 signed word) &(x \<rightarrow> [''baz_x_C''])) v) hp) = X"
  apply umm_strg
  oops

end

end