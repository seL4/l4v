(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*
 * Test force/prevent heap abstraction.
 *)

theory heap_lift_force_prevent
imports "AutoCorres.AutoCorres"
begin

external_file "heap_lift_force_prevent.c"
install_C_file "heap_lift_force_prevent.c"

autocorres [
    no_heap_abs = unlifted_a unlifted_b,
    force_heap_abs = lifted_a lifted_b,
    ts_force nondet = unlifted_a unlifted_b lifted_a lifted_b
    ] "heap_lift_force_prevent.c"

context heap_lift_force_prevent begin

lemma heap_w32_hrs_mem [simp]:
    "\<lbrakk> is_valid_w32 (lift_global_heap s) p; heap_w32 (lift_global_heap s) p = a \<rbrakk>
      \<Longrightarrow> h_val (hrs_mem (t_hrs_' s)) p = a"
  by (fastforce simp: lifted_globals_ext_simps(3) lifted_globals_ext_simps(4) h_val_simple_lift)

lemma lifted_a_wp [wp]:
    "\<lbrace> \<lambda>s. is_valid_w32 s p \<and> (\<exists>a. heap_w32 s p = a \<and> P a s) \<rbrace> lifted_a' p \<lbrace> \<lambda>r s. P r s \<rbrace>"
  by (clarsimp simp: lifted_a'_def, wp, auto)

lemma unlifted_a_wp [wp]:
    "\<lbrace> \<lambda>s. c_guard p \<and> P (h_val (hrs_mem (t_hrs_' s)) p) s \<rbrace>
                  unlifted_a' p \<lbrace> \<lambda>r s. P r s \<rbrace>"
  by (clarsimp simp: unlifted_a'_def, wp, auto)

lemma lifted_b_wp [wp]:
    "\<lbrace> \<lambda>s. is_valid_w32 s p \<and> (\<exists>a. heap_w32 s p = a \<and> P (a * 3) s) \<rbrace> lifted_b' p \<lbrace> \<lambda>r s. P r s \<rbrace>"
  apply (clarsimp simp: lifted_b'_def)
  including no_pre apply wp
  apply (auto simp: simple_lift_c_guard lift_global_heap_def field_simps)
  done

lemma unlifted_b_wp [wp]:
    "\<lbrace> \<lambda>s. heap_ptr_valid (hrs_htd (t_hrs_' s)) p
           \<and> (\<forall>t. lift_global_heap t = lift_global_heap s \<longrightarrow> P (h_val (hrs_mem (t_hrs_' t)) p * 3) t) \<rbrace>
              unlifted_b' p \<lbrace> \<lambda>r s. P r s \<rbrace>"
  apply (clarsimp simp: unlifted_b'_def)
  apply wp
  apply (rule conjI)
   apply (metis simple_lift_c_guard simple_lift_def)
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: lift_global_heap_def )
   apply (unfold simple_lift_def)
   apply (clarsimp  split: option.splits)
  apply (clarsimp simp: field_simps)
  apply (erule allE, erule (1) impE)
  apply (subgoal_tac "h_val (hrs_mem (t_hrs_' s)) p = h_val (hrs_mem (t_hrs_' t)) p"
                     "heap_w32 (lift_global_heap s) p = h_val (hrs_mem (t_hrs_' t)) p")
    apply clarsimp
   apply (clarsimp simp: lift_global_heap_def)
   apply (drule fun_cong [where x = p])
   apply (clarsimp simp: simple_lift_def)
  apply (metis heap_w32_hrs_mem lifted_globals_ext_simps(4) simple_lift_def)
  done

end

end

