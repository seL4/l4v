(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory SubMonad_AI
imports KHeap_AI
begin

(* SubMonadLib *)
lemma submonad_do_machine_op:
  "submonad machine_state (machine_state_update \<circ> K) \<top> do_machine_op"
  apply unfold_locales
       apply (clarsimp simp: ext stateAssert_def do_machine_op_def o_def gets_def
                             get_def bind_def return_def submonad_fn_def)+
  done

interpretation submonad_do_machine_op:
  submonad machine_state "(machine_state_update \<circ> K)" \<top> do_machine_op
  by (rule submonad_do_machine_op)

lemma submonad_args_pspace:
  "submonad_args kheap (kheap_update o (\<lambda>x _. x)) \<top>"
  by (simp add: submonad_args_def)

schematic_goal assert_get_tcb_pspace:
  "gets_the (get_tcb t) = submonad_fn kheap (kheap_update o (\<lambda>x _. x)) \<top> ?f"
  apply (unfold gets_the_def)
  apply (rule submonad_bind_alt [OF submonad_args_pspace])
     apply (rule gets_submonad [OF submonad_args_pspace _ refl])
     apply (simp add: get_tcb_def read_object_def)
    apply (rule assert_opt_submonad [OF submonad_args_pspace])
   apply simp
  apply (rule empty_fail_assert_opt)
  done

lemma assert_get_thread_do_machine_op_comm:
  "empty_fail m' \<Longrightarrow>
   do x \<leftarrow> gets_the (get_tcb t); y \<leftarrow> do_machine_op m'; n x y od =
   do y \<leftarrow> do_machine_op m'; x \<leftarrow> gets_the (get_tcb t); n x y od"
  apply (rule submonad_comm2 [OF _ _ submonad_do_machine_op])
        apply (rule submonad_args_pspace)
       apply (rule assert_get_tcb_pspace)
      apply (simp add: empty_fail_cond)+
  done

end
