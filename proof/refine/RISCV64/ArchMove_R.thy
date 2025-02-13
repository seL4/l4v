(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Arch specific lemmas that should be moved into theory files before Refine *)

theory ArchMove_R
imports
  Move_R
begin

(* Use one of these forms everywhere, rather than choosing at random. *)
lemmas cte_index_repair = mult.commute[where a="(2::'a::len word) ^ cte_level_bits"]
lemmas cte_index_repair_sym = cte_index_repair[symmetric]

lemma invs_valid_ioc[elim!]: "invs s \<Longrightarrow> valid_ioc s"
  by (clarsimp simp add: invs_def valid_state_def)

context Arch begin arch_global_naming

(* Move to Arch_Structs_A *)
definition ppn_len :: nat where
  "ppn_len \<equiv> LENGTH(pte_ppn_len)"

(* Move to Deterministic_AI *)
crunch copy_global_mappings
  for valid_etcbs[wp]: valid_etcbs (wp: mapM_x_wp')

lemma get_pt_mapM_x_lower:
  assumes g: "\<And>P pt x. \<lbrace> \<lambda>s. P (kheap s pt_ptr) \<rbrace> g pt x \<lbrace> \<lambda>_ s. P (kheap s pt_ptr) \<rbrace>"
  assumes y: "ys \<noteq> []"
  notes [simp] = gets_map_def get_object_def gets_def get_def bind_def return_def
                 assert_opt_def fail_def opt_map_def
  shows "do pt \<leftarrow> get_pt pt_ptr; mapM_x (g pt) ys od
          = mapM_x (\<lambda>y. get_pt pt_ptr >>= (\<lambda>pt. g pt y)) ys"
  apply (rule get_mapM_x_lower
                [where P="\<lambda>opt_pt s. case kheap s pt_ptr of
                                       Some (ArchObj (PageTable pt)) \<Rightarrow> opt_pt = Some pt
                                     | _ \<Rightarrow> opt_pt = None",
                 OF _ _ _ y])
    apply (wp g)
   apply (case_tac "kheap s pt_ptr"; simp; rename_tac ko; case_tac ko; simp;
          rename_tac ako; case_tac ako; simp)+
  done

end

end
