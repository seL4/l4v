(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
  CSpace refinement
*)

theory CSpace_R
imports ArchCSpace1_R
begin

(* transfer facts from partial locales (with extra assumptions) into complete locales
   (since we can satisfy these assumptions) *)

context mdb_insert_child begin

sublocale mdb_insert_child_gen
  by (unfold_locales;
      fastforce simp: dest_no_parent_n[simplified n_def] elim!: subtree_trans)+

end

context mdb_insert_sib begin

sublocale mdb_insert_sib_gen
  by (unfold_locales;
      fastforce simp: dest_no_parent_n[simplified n_def] src_no_mdb_parent parent_preserved)+

end

context mdb_inv_preserve begin

sublocale mdb_inv_preserve_gen by unfold_locales

lemmas descendants_of = descendants_of

end

context mdb_swap begin

sublocale mdb_swap_gen
  by (unfold_locales; fastforce elim: isMDBParentOf_eq)+

end

context mdb_inv_preserve begin

sublocale mdb_inv_preserve_gen
  by unfold_locales

lemmas preserve_stuff = preserve_stuff
lemmas untyped_inc' = untyped_inc'

end

lemma setCTE_pred_tcb_at':
  "\<lbrace>pred_tcb_at' proj P t\<rbrace>
     setCTE c cte
   \<lbrace>\<lambda>rv. pred_tcb_at' proj P t\<rbrace>"
  unfolding pred_tcb_at'_def setCTE_def
  apply (rule setObject_cte_obj_at_tcb')
   apply (simp add: tcb_to_itcb'_def)+
  done

locale mdb_move =
  mdb_ptr m _ _ src src_cap src_node
    for m src src_cap src_node +

  fixes dest cap'

  fixes old_dest_node
  assumes dest: "m dest = Some (CTE NullCap old_dest_node)"
  assumes prev: "mdbPrev old_dest_node = 0"
  assumes nxt: "mdbNext old_dest_node = 0"

  assumes parency: "weak_derived' src_cap cap'"
  assumes not_null: "src_cap \<noteq> NullCap"
  assumes neq: "src \<noteq> dest"

  fixes n
  defines "n \<equiv>
    modify_map
     (modify_map
       (modify_map
         (modify_map
           (modify_map m dest (cteCap_update (\<lambda>_. cap')))
             src (cteCap_update (\<lambda>_. NullCap)))
           dest (cteMDBNode_update (\<lambda>m. src_node)))
         src (cteMDBNode_update (\<lambda>m. nullMDBNode)))
       (mdbPrev src_node) (cteMDBNode_update (mdbNext_update (\<lambda>_. dest)))"

  fixes m'
  defines "m' \<equiv>
  modify_map n (mdbNext src_node)
               (cteMDBNode_update (mdbPrev_update (\<lambda>_. dest)))"
begin
interpretation Arch . (*FIXME: arch-split*)


lemmas src = m_p

lemma [intro?]:
  shows src_0: "src \<noteq> 0"
  and  dest_0: "dest \<noteq> 0"
  using no_0 src dest
  by (auto simp: no_0_def)

lemma src_neq_next:
  "src \<noteq> mdbNext src_node"
  by simp

lemma src_neq_prev:
  "src \<noteq> mdbPrev src_node"
  by simp

lemmas src_neq_next2 = src_neq_next [symmetric]
lemmas src_neq_prev2 = src_neq_prev [symmetric]

lemma n:
  "n = modify_map (m(dest \<mapsto> CTE cap' src_node,
                     src \<mapsto> CTE capability.NullCap nullMDBNode))
                  (mdbPrev src_node)
                  (cteMDBNode_update (mdbNext_update (\<lambda>_. dest)))"
  using neq src dest no_0
  by (simp add: n_def modify_map_apply)

lemma dest_no_parent [iff]:
  "m \<turnstile> dest \<rightarrow> x = False" using dest nxt
  by (auto dest: subtree_next_0)

lemma dest_no_child [iff]:
  "m \<turnstile> x \<rightarrow> dest = False" using dest prev
  by (auto dest: subtree_prev_0)

lemma src_no_parent [iff]:
  "n \<turnstile> src \<rightarrow> x = False"
  apply clarsimp
  apply (erule subtree_next_0)
   apply (auto simp add: n modify_map_def nullPointer_def)
  done

lemma no_0_n: "no_0 n" by (simp add: n_def no_0)
lemma  no_0': "no_0 m'" by (simp add: m'_def no_0_n)

lemma next_neq_dest [iff]:
  "mdbNext src_node \<noteq> dest"
  using dlist src dest prev dest_0 no_0
  by (fastforce simp add: valid_dlist_def no_0_def Let_def)

lemma prev_neq_dest [simp]:
  "mdbPrev src_node \<noteq> dest"
  using dlist src dest nxt dest_0 no_0
  by (fastforce simp add: valid_dlist_def no_0_def Let_def)

lemmas next_neq_dest2 [simp] = next_neq_dest [symmetric]
lemmas prev_neq_dest2 [simp] = prev_neq_dest [symmetric]

lemma dlist':
  "valid_dlist m'"
  using src dest prev neq nxt dlist no_0
  apply (simp add: m'_def n no_0_def)
  apply (simp add: valid_dlist_def Let_def)
  apply clarsimp
  apply (case_tac cte)
  apply (rename_tac cap node)
  apply (rule conjI)
   apply (clarsimp simp: modify_map_def nullPointer_def split: if_split_asm)
      apply (case_tac z)
      apply fastforce
     apply (case_tac z)
     apply (rename_tac capability mdbnode)
     apply clarsimp
     apply (rule conjI)
      apply fastforce
     apply clarsimp
     apply (rule conjI, fastforce)
     apply clarsimp
     apply (rule conjI)
      apply clarsimp
      apply (subgoal_tac "mdbNext mdbnode = mdbPrev src_node")
       prefer 2
       apply fastforce
      apply (subgoal_tac "mdbNext mdbnode = src")
       prefer 2
       apply fastforce
      apply fastforce
     apply clarsimp
     apply (rule conjI)
      apply clarsimp
      apply (frule_tac x=src in spec, erule allE, erule (1) impE)
      apply fastforce
     subgoal by fastforce
    subgoal by fastforce
   apply (rule conjI, clarsimp)
    apply fastforce
   apply (clarsimp, rule conjI, fastforce)
   apply (clarsimp, rule conjI)
    apply clarsimp
    apply (frule_tac x=src in spec, erule allE, erule (1) impE)
    subgoal by fastforce
   subgoal by fastforce
  apply (clarsimp simp: modify_map_def nullPointer_def split: if_split_asm)
     apply (case_tac z)
     apply (clarsimp, rule conjI, fastforce)
     apply (clarsimp, rule conjI, fastforce)
     apply (clarsimp, rule conjI)
      apply clarsimp
      apply (frule_tac x=src in spec, erule allE, erule (1) impE)
      subgoal by fastforce
     apply (clarsimp, rule conjI)
      apply clarsimp
      apply (frule_tac x=src in spec, erule allE, erule (1) impE)
      subgoal by fastforce
     subgoal by fastforce
    apply (case_tac z)
    subgoal by fastforce
   subgoal by fastforce
  apply (rule conjI)
   apply clarsimp
   apply fastforce
  apply clarsimp
  apply (rule conjI, fastforce)
  apply (clarsimp, rule conjI)
   apply clarsimp
   apply (frule_tac x=src in spec, erule allE, erule (1) impE)
   subgoal by fastforce
  apply (clarsimp, rule conjI)
   apply clarsimp
   apply (frule_tac x=src in spec, erule allE, erule (1) impE)
   subgoal by fastforce
  subgoal by fastforce
  done

lemma src_no_child [iff]:
  "n \<turnstile> x \<rightarrow> src = False"
proof -
  from src_neq_next
  have "m' src = Some (CTE capability.NullCap nullMDBNode)"
    by (simp add: m'_def n modify_map_def)
  hence "m' \<turnstile> x \<rightarrow> src = False" using dlist' no_0'
    by (auto elim!: subtree_prev_0 simp: nullPointer_def)
  thus ?thesis by (simp add: m'_def)
qed

lemma dest_not_parent [iff]:
  "m \<turnstile> dest parentOf c = False"
  using dest by (simp add: parentOf_def)

lemma dest_source [iff]:
  "(m \<turnstile> dest \<leadsto> x) = (x = 0)"
  using dest nxt by (simp add: next_unfold')

lemma dest_no_target [iff]:
  "m \<turnstile> p \<leadsto> dest = False"
  using dlist no_0 prev dest
  by (fastforce simp: valid_dlist_def Let_def no_0_def next_unfold')

lemma parent_preserved:
  "isMDBParentOf cte' (CTE cap' src_node) =
   isMDBParentOf cte' (CTE src_cap src_node)"
  using parency unfolding weak_derived'_def
  apply (cases cte')
  apply (simp add: isMDBParentOf_CTE sameRegionAs_def2 del: isArchFrameCap_capMasterCap)
  done

lemma children_preserved:
  "isMDBParentOf (CTE cap' src_node) cte' =
   isMDBParentOf (CTE src_cap src_node) cte'"
  using parency unfolding weak_derived'_def
  apply (cases cte')
  apply (simp add: isMDBParentOf_CTE sameRegionAs_def2)
  done

lemma no_src_subtree_n_m:
  assumes no_src: "\<not> m \<turnstile> p \<rightarrow> src" "p \<noteq> src" "p \<noteq> dest"
  assumes px: "n \<turnstile> p \<rightarrow> x"
  shows "m \<turnstile> p \<rightarrow> x" using px
proof induct
  case (direct_parent c)
  thus ?case using neq no_src no_loops
    apply -
    apply (case_tac "c=dest")
     apply (cases "m (mdbPrev src_node)")
      apply (unfold n)[1]
      apply (subst (asm) modify_map_None, simp)+
      apply (clarsimp simp: mdb_next_update)
     apply (rename_tac cte')
     apply clarsimp
     apply (subgoal_tac "p = mdbPrev src_node")
      prefer 2
      apply (simp add: n)
      apply (subst (asm) modify_map_apply, simp)
      apply (clarsimp simp:_mdb_next_update split: if_split_asm)
     apply clarsimp
     apply (simp add: n)
     apply (subst (asm) modify_map_apply, simp)+
     apply (insert dest)[1]
     apply (clarsimp simp add: parentOf_def mdb_next_unfold)
     apply (subgoal_tac "m \<turnstile> mdbPrev src_node \<rightarrow> src")
      apply simp
     apply (rule subtree.direct_parent)
       apply (rule prev_leadstoI)
         apply (rule src)
        apply (insert no_0, clarsimp simp: no_0_def)[1]
       apply (rule dlist)
      apply (rule src_0)
     apply (simp add: parentOf_def src parent_preserved)
    apply (rule subtree.direct_parent)
      apply (simp add: n)
      apply (cases "m (mdbPrev src_node)")
       apply (subst (asm) modify_map_None, simp)+
       apply (simp add: mdb_next_update)
      apply (subst (asm) modify_map_apply, simp)+
      apply (simp add: mdb_next_update split: if_split_asm)
     apply assumption
    apply (simp add: n)
    apply (cases "m (mdbPrev src_node)")
     apply (subst (asm) modify_map_None, simp)+
     apply (clarsimp simp add: parentOf_def split: if_split_asm)
    apply (subst (asm) modify_map_apply, simp)+
    apply (clarsimp simp add: parentOf_def split: if_split_asm)
    done
next
  case (trans_parent c c')
  thus ?case using neq no_src
    apply -
    apply (case_tac "c' = dest")
     apply clarsimp
     apply (subgoal_tac "c = mdbPrev src_node")
      prefer 2
      apply (simp add: n)
      apply (cases "m (mdbPrev src_node)")
       apply (subst (asm) modify_map_None, simp)+
       apply (clarsimp simp: mdb_next_update split: if_split_asm)
      apply (subst (asm) modify_map_apply, simp)+
      apply (clarsimp simp: mdb_next_update split: if_split_asm)
     apply clarsimp
     apply (cases "m (mdbPrev src_node)")
      apply (unfold n)[1]
      apply (subst (asm) modify_map_None, simp)+
      apply (clarsimp simp: mdb_next_update)
     apply (subgoal_tac "m \<turnstile> p \<rightarrow> src")
      apply simp
     apply (rule subtree.trans_parent, assumption)
       apply (rule prev_leadstoI)
         apply (rule src)
        apply (insert no_0, clarsimp simp: no_0_def)[1]
       apply (rule dlist)
      apply (rule src_0)
     apply (clarsimp simp: n)
     apply (subst (asm) modify_map_apply, simp)+
     apply (clarsimp simp: parentOf_def src parent_preserved
                     split: if_split_asm)
    apply (rule subtree.trans_parent, assumption)
      apply (simp add: n)
      apply (cases "m (mdbPrev src_node)")
       apply (subst (asm) modify_map_None, simp)+
       apply (simp add: mdb_next_update split: if_split_asm)
      apply (subst (asm) modify_map_apply, simp)+
      apply (simp add: mdb_next_update split: if_split_asm)
     apply assumption
    apply (simp add: n)
    apply (cases "m (mdbPrev src_node)")
     apply (subst (asm) modify_map_None, simp)+
     apply (clarsimp simp: parentOf_def split: if_split_asm)
    apply (subst (asm) modify_map_apply, simp)+
    apply (clarsimp simp: parentOf_def split: if_split_asm)
    done
qed

lemma subtree_m_n:
  assumes p_neq: "p \<noteq> dest" "p \<noteq> src"
  assumes px: "m \<turnstile> p \<rightarrow> x"
  shows "if x = src then n \<turnstile> p \<rightarrow> dest else n \<turnstile> p \<rightarrow> x" using px
proof induct
  case (direct_parent c)
  thus ?case using p_neq
    apply -
    apply simp
    apply (rule conjI)
     apply clarsimp
     apply (drule leadsto_is_prev)
        apply (rule src)
       apply (rule dlist)
      apply (rule no_0)
     apply (clarsimp simp: parentOf_def)
     apply (rule subtree.direct_parent)
       apply (simp add: n modify_map_apply mdb_next_update)
      apply (rule dest_0)
     apply (clarsimp simp: n modify_map_apply parentOf_def
                           neq [symmetric] src parent_preserved)
    apply clarsimp
    apply (rule subtree.direct_parent)
      apply (simp add: n)
      apply (cases "m (mdbPrev src_node)")
       apply (subst modify_map_None, simp)
       apply (simp add: mdb_next_update)
      apply (subst modify_map_apply, simp)
      apply (clarsimp simp: mdb_next_update)
      apply (drule prev_leadstoD)
         apply (rule src)
        apply (rule dlist)
       apply (rule no_0)
      apply simp
     apply assumption
    apply (simp add: n)
    apply (cases "m (mdbPrev src_node)")
     apply (subst modify_map_None, simp)
     apply (clarsimp simp add: parentOf_def)
    apply (subst modify_map_apply, simp)
    apply (clarsimp simp add: parentOf_def)
    apply fastforce
    done
next
  case (trans_parent c c')
  thus ?case using p_neq
    apply -
    apply (clarsimp split: if_split_asm)
    apply (erule subtree.trans_parent)
      apply (clarsimp simp: next_unfold' src n)
      apply (cases "m (mdbPrev src_node)")
       apply (subst modify_map_None, simp)
       apply (clarsimp simp add: neq [symmetric] src split: option.splits)
      apply (subst modify_map_apply, simp)
      apply (clarsimp simp add: neq [symmetric] src split: option.splits)
     apply assumption
    apply (clarsimp simp: mdb_next_unfold src n)
    apply (cases "m (mdbPrev src_node)")
     apply (subst modify_map_None, simp)
     apply (simp add: parentOf_def)
    apply (subst modify_map_apply, simp)
    apply (fastforce simp add: parentOf_def)
    apply (rule conjI)
     apply clarsimp
     apply (cases "m c", simp add: mdb_next_unfold)
     apply (drule leadsto_is_prev)
       apply (rule src)
      apply (rule dlist)
     apply (rule no_0)
     apply clarsimp
     apply (erule subtree.trans_parent)
       apply (simp add: n modify_map_apply mdb_next_update)
      apply (rule dest_0)
     apply (clarsimp simp: n modify_map_apply parentOf_def neq [symmetric] src)
     apply (rule conjI, clarsimp)
     apply (clarsimp simp: parent_preserved)
    apply clarsimp
    apply (erule subtree.trans_parent)
      apply (simp add: n)
      apply (cases "m (mdbPrev src_node)")
       apply (subst modify_map_None, simp)
       apply (clarsimp simp add: mdb_next_update)
      apply (subst modify_map_apply, simp)
      apply (clarsimp simp add: mdb_next_update)
      apply (rule conjI, clarsimp)
      apply clarsimp
      apply (drule prev_leadstoD, rule src, rule dlist, rule no_0)
      apply simp
     apply assumption
    apply (simp add: n)
    apply (cases "m (mdbPrev src_node)")
     apply (subst modify_map_None, simp)
     apply (clarsimp simp add: parentOf_def)
    apply (subst modify_map_apply, simp)
    apply (fastforce simp add: parentOf_def)
    done
qed

lemmas neq_sym [simp] = neq [symmetric]

lemmas src_prev_loop [simp] =
  subtree_prev_loop [OF src no_loops dlist no_0]

lemma subtree_src_dest:
  "m \<turnstile> src \<rightarrow> x \<Longrightarrow> n \<turnstile> dest \<rightarrow> x"
  apply (erule subtree.induct)
   apply (clarsimp simp: mdb_next_unfold src)
   apply (rule subtree.direct_parent)
     apply (simp add: n)
     apply (cases "m (mdbPrev src_node)")
      apply (subst modify_map_None, simp)
      apply (simp add: mdb_next_update)
     apply (subst modify_map_apply, simp)
     apply (simp add: mdb_next_update)
    apply assumption
   apply (simp add: n)
   apply (clarsimp simp add: modify_map_def parentOf_def src children_preserved)
  apply (subgoal_tac "c'' \<noteq> src")
   prefer 2
   apply (drule (3) subtree.trans_parent)
   apply clarsimp
  apply (erule subtree.trans_parent)
    apply (simp add: n)
    apply (cases "m (mdbPrev src_node)")
     apply (subst modify_map_None, simp)
     apply (simp add: mdb_next_update)
     apply fastforce
    apply (subst modify_map_apply, simp)
    apply (simp add: mdb_next_update)
    apply fastforce
   apply assumption
  apply (fastforce simp: n modify_map_def parentOf_def src children_preserved)
  done

lemma src_next [simp]:
  "m \<turnstile> src \<leadsto> mdbNext src_node"
  by (simp add: next_unfold' src)

lemma dest_no_trancl_target [simp]:
  "m \<turnstile> x \<leadsto>\<^sup>+ dest = False"
  by (clarsimp dest!: tranclD2)

lemma m'_next:
  "\<lbrakk>m' p = Some (CTE cte' node'); m p = Some (CTE cte node)\<rbrakk>
    \<Longrightarrow> mdbNext node'
      = (if p = src then 0
         else if p = dest then mdbNext src_node
         else if mdbNext node = src then dest
         else mdbNext node)"
  apply(simp, intro conjI impI)
       apply(clarsimp simp: n m'_def modify_map_def split: if_split_asm)
      apply(clarsimp simp: n m'_def modify_map_def nullPointer_def)
     apply(subgoal_tac "mdbPrev src_node = p")
      prefer 2
      apply(erule dlistEn)
       apply(simp)
      apply(case_tac "cte'a")
      apply(clarsimp simp: src)
     apply(clarsimp simp: n m'_def modify_map_def split: if_split_asm)
    apply(clarsimp simp: dest n m'_def modify_map_def)
   apply(clarsimp simp: n m'_def modify_map_def nullPointer_def)
  apply(clarsimp simp: n m'_def modify_map_def split: if_split_asm)
  apply(insert m_p no_0)
  apply(erule_tac p=src in dlistEp)
   apply(clarsimp simp: no_0_def)
  apply(clarsimp)
  done


lemma mdb_next_from_dest:
  "n \<turnstile> dest \<leadsto>\<^sup>+ x \<Longrightarrow> m \<turnstile> src \<leadsto>\<^sup>+ x"
  apply (erule trancl_induct)
   apply (rule r_into_trancl)
   apply (simp add: n modify_map_def next_unfold' src)
  apply (cases "m (mdbPrev src_node)")
   apply (simp add: n)
   apply (subst (asm) modify_map_None, simp)+
   apply (clarsimp simp: mdb_next_update split: if_split_asm)
   apply (fastforce intro: trancl_into_trancl)
  apply (simp add: n)
  apply (subst (asm) modify_map_apply, simp)+
  apply (clarsimp simp: mdb_next_update split: if_split_asm)
   apply (subgoal_tac "m \<turnstile> src \<leadsto>\<^sup>+ src")
    apply simp
   apply (erule trancl_into_trancl)
   apply (rule prev_leadstoI, rule src)
    apply (insert no_0)[1]
    apply (clarsimp simp add: no_0_def)
   apply (rule dlist)
  apply (fastforce intro: trancl_into_trancl)
  done

lemma dest_loop:
  "n \<turnstile> dest \<rightarrow> dest = False"
  apply clarsimp
  apply (drule subtree_mdb_next)
  apply (drule mdb_next_from_dest)
  apply simp
  done


lemma subtree_dest_src:
  "n \<turnstile> dest \<rightarrow> x \<Longrightarrow> m \<turnstile> src \<rightarrow> x"
  apply (erule subtree.induct)
   apply (clarsimp simp: mdb_next_unfold src)
   apply (rule subtree.direct_parent)
     apply (simp add: n)
     apply (cases "m (mdbPrev src_node)")
      apply (subst (asm) modify_map_None, simp)+
      apply (clarsimp simp add: mdb_next_update next_unfold src)
     apply (subst (asm) modify_map_apply, simp)+
     apply (clarsimp simp add: mdb_next_update  next_unfold src)
    apply assumption
   apply (simp add: n)
   apply (simp add: modify_map_def parentOf_def)
   apply (clarsimp simp: src children_preserved)
  apply (subgoal_tac "c' \<noteq> dest")
   prefer 2
   apply clarsimp
  apply (subgoal_tac "c'' \<noteq> dest")
   prefer 2
   apply clarsimp
   apply (drule (3) trans_parent)
   apply (simp add: dest_loop)
  apply (subgoal_tac "c' \<noteq> mdbPrev src_node")
   prefer 2
   apply clarsimp
  apply (erule subtree.trans_parent)
    apply (simp add: n)
    apply (cases "m (mdbPrev src_node)")
     apply (subst (asm) modify_map_None, simp)+
     apply (simp add: mdb_next_update nullPointer_def split: if_split_asm)
    apply (subst (asm) modify_map_apply, simp)+
    apply (simp add: mdb_next_update nullPointer_def split: if_split_asm)
   apply assumption
  apply (clarsimp simp add: n modify_map_def parentOf_def src children_preserved
                  split: if_split_asm)
  done

lemma subtree_n_m:
  assumes p_neq: "p \<noteq> dest" "p \<noteq> src"
  assumes px: "n \<turnstile> p \<rightarrow> x"
  shows "if x = dest then m \<turnstile> p \<rightarrow> src else m \<turnstile> p \<rightarrow> x" using px
proof induct
  case (direct_parent c)
  thus ?case using p_neq
    apply clarsimp
    apply (rule conjI)
     apply clarsimp
     apply (subgoal_tac "p = mdbPrev src_node")
      prefer 2
      apply (drule mdb_next_modify_prev [where x="mdbNext src_node" and f="\<lambda>_. dest", THEN iffD2])
      apply (fold m'_def)
      apply (drule leadsto_is_prev)
         apply (fastforce simp: n m'_def modify_map_def)
        apply (rule dlist')
       apply (rule no_0')
      apply simp
     apply clarsimp
     apply (rule subtree.direct_parent)
       apply (rule prev_leadstoI)
         apply (rule src)
        apply (insert no_0)[1]
        apply (clarsimp simp add: next_unfold' n modify_map_def no_0_def split: if_split_asm)
       apply (rule dlist)
      apply (rule src_0)
     apply (clarsimp simp: parentOf_def n modify_map_def src parent_preserved)
    apply clarsimp
    apply (rule subtree.direct_parent)
      apply (simp add: n)
      apply (cases "m (mdbPrev src_node)")
       apply (subst (asm) modify_map_None, simp)+
       apply (simp add: next_unfold' mdb_next_unfold)
      apply (subst (asm) modify_map_apply, simp)+
      apply (simp add: mdb_next_update split: if_split_asm)
     apply assumption
    apply (simp add: n)
    apply (clarsimp simp add: parentOf_def modify_map_def split: if_split_asm)
    done
next
  case (trans_parent c c')
  thus ?case using p_neq
    apply -
    apply (simp split: if_split_asm)
     apply clarsimp
     apply (subgoal_tac "c' = mdbNext src_node")
      prefer 2
      apply (clarsimp simp add: mdb_next_unfold n modify_map_def)
     apply clarsimp
     apply (erule subtree.trans_parent)
       apply (simp add: mdb_next_unfold src)
      apply assumption
     apply (clarsimp simp add: parentOf_def modify_map_def n split: if_split_asm)
    apply (rule conjI)
     apply clarsimp
     apply (subgoal_tac "c = mdbPrev src_node")
      prefer 2
      apply (drule mdb_next_modify_prev [where x="mdbNext src_node" and f="\<lambda>_. dest", THEN iffD2])
      apply (fold m'_def)
      apply (drule leadsto_is_prev)
         apply (fastforce simp: n m'_def modify_map_def)
        apply (rule dlist')
       apply (rule no_0')
      apply simp
     apply clarsimp
     apply (erule subtree.trans_parent)
       apply (rule prev_leadstoI)
         apply (rule src)
        apply (insert no_0)[1]
        apply (clarsimp simp: next_unfold' no_0_def n modify_map_def)
       apply (rule dlist)
      apply (rule src_0)
     apply (clarsimp simp: parentOf_def n modify_map_def src
                           parent_preserved split: if_split_asm)
    apply clarsimp
    apply (erule subtree.trans_parent)
      apply (clarsimp simp add: n modify_map_def mdb_next_unfold nullPointer_def split: if_split_asm)
     apply assumption
    apply (clarsimp simp add: n modify_map_def parentOf_def split: if_split_asm)
    done
qed

lemma descendants:
  "descendants_of' p m' =
  (if p = src
   then {}
   else if p = dest
   then descendants_of' src m
   else descendants_of' p m - {src} \<union>
        (if src \<in> descendants_of' p m then {dest} else {}))"
  apply (rule set_eqI)
  apply (simp add: descendants_of'_def m'_def)
  apply (auto simp: subtree_m_n intro: subtree_src_dest subtree_dest_src no_src_subtree_n_m)
  apply (auto simp: subtree_n_m)
  done
end

context mdb_move_abs
begin

end

context mdb_move
begin

end

lemma updateCap_dynamic_duo:
  "\<lbrakk> (rv, s') \<in> fst (updateCap x cap s); pspace_aligned' s; pspace_distinct' s \<rbrakk>
       \<Longrightarrow> pspace_aligned' s' \<and> pspace_distinct' s'"
  unfolding updateCap_def
  apply (rule conjI)
   apply (erule use_valid | wp | assumption)+
  done

declare const_apply[simp]

lemma next_slot_eq2:
  "\<lbrakk>case n q of None \<Rightarrow> next_slot p t' m' = x | Some q' \<Rightarrow> next_slot p (t'' q') (m'' q') = x;
    case n q of None \<Rightarrow> (t' = t \<and> m' = m) | Some q' \<Rightarrow> t'' q' = t \<and> m'' q' = m\<rbrakk>
    \<Longrightarrow> next_slot p t m = x"
  apply(simp split: option.splits)
  done

lemma set_cap_not_quite_corres':
  assumes cr:
  "pspace_relation (kheap s) (ksPSpace s')"
  "cur_thread s    = ksCurThread s'"
  "idle_thread s   = ksIdleThread s'"
  "machine_state s = ksMachineState s'"
  "work_units_completed s = ksWorkUnitsCompleted s'"
  "domain_index s  = ksDomScheduleIdx s'"
  "domain_list s   = ksDomSchedule s'"
  "cur_domain s    = ksCurDomain s'"
  "domain_time s   = ksDomainTime s'"
  "(x,t') \<in> fst (updateCap p' c' s')"
  "valid_objs s" "pspace_aligned s" "pspace_distinct s" "cte_at p s"
  "pspace_aligned' s'" "pspace_distinct' s'"
  "interrupt_state_relation (interrupt_irq_node s) (interrupt_states s) (ksInterruptState s')"
  "(arch_state s, ksArchState s') \<in> arch_state_relation"
  assumes c: "cap_relation c c'"
  assumes p: "p' = cte_map p"
  shows "\<exists>t. ((),t) \<in> fst (set_cap c p s) \<and>
             pspace_relation (kheap t) (ksPSpace t') \<and>
             cdt t              = cdt s \<and>
             cdt_list t         = cdt_list (s) \<and>
             scheduler_action t = scheduler_action (s) \<and>
             ready_queues t     = ready_queues (s) \<and>
             is_original_cap t  = is_original_cap s \<and>
             interrupt_state_relation (interrupt_irq_node t) (interrupt_states t)
                              (ksInterruptState t') \<and>
             (arch_state t, ksArchState t') \<in> arch_state_relation \<and>
             cur_thread t    = ksCurThread t' \<and>
             idle_thread t   = ksIdleThread t' \<and>
             machine_state t = ksMachineState t' \<and>
             work_units_completed t = ksWorkUnitsCompleted t' \<and>
             domain_index t  = ksDomScheduleIdx t' \<and>
             domain_list t   = ksDomSchedule t' \<and>
             cur_domain t    = ksCurDomain t' \<and>
             domain_time t   = ksDomainTime t'"
  apply (rule set_cap_not_quite_corres)
                using cr
                apply (fastforce simp: c p)+
                done

context begin interpretation Arch . (*FIXME: arch-split*)
lemma cteMove_corres:
  assumes cr: "cap_relation cap cap'"
  notes trans_state_update'[symmetric,simp]
  shows
  "corres dc (einvs and
              cte_at ptr and
              cte_wp_at (\<lambda>c. c = cap.NullCap) ptr' and
              valid_cap cap and tcb_cap_valid cap ptr' and K (ptr \<noteq> ptr'))
             (invs' and
              cte_wp_at' (\<lambda>c. weak_derived' cap' (cteCap c) \<and> cteCap c \<noteq> NullCap) (cte_map ptr) and
              cte_wp_at' (\<lambda>c. cteCap c = NullCap) (cte_map ptr'))
          (cap_move cap ptr ptr') (cteMove cap' (cte_map ptr) (cte_map ptr'))"
  (is "corres _ ?P ?P' _ _")
  supply subst_all [simp del]
  supply if_cong[cong]
  apply (simp add: cap_move_def cteMove_def const_def)
  apply (rule corres_symb_exec_r)
     defer
     apply (rule getCTE_sp)
    apply wp
   apply (rule no_fail_pre, wp)
   apply (clarsimp simp add: cte_wp_at_ctes_of)
  apply (rule corres_assert_assume)
   prefer 2
   apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (rule corres_assert_assume)
   prefer 2
   apply clarsimp
   apply (drule invs_mdb')
   apply (clarsimp simp: cte_wp_at_ctes_of valid_mdb'_def valid_mdb_ctes_def)
   apply (case_tac oldCTE)
   apply (clarsimp simp: valid_nullcaps_def initMDBNode_def)
   apply (erule allE)+
   apply (erule (1) impE)
   apply (clarsimp simp: nullPointer_def)
  apply (rule corres_symb_exec_r)
     defer
     apply (rule getCTE_sp)
    apply wp
   apply (rule no_fail_pre, wp)
   apply (clarsimp simp add: cte_wp_at_ctes_of)
  apply (rule corres_no_failI)
   apply (rule no_fail_pre, wp hoare_weak_lift_imp)
   apply (clarsimp simp add: cte_wp_at_ctes_of)
   apply (drule invs_mdb')
   apply (clarsimp simp: valid_mdb'_def valid_mdb_ctes_def)
   apply (rule conjI)
    apply clarsimp
    apply (erule (2) valid_dlistEp, simp)
   apply clarsimp
   apply (erule (2) valid_dlistEn, simp)
  apply (clarsimp simp: in_monad state_relation_def)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (case_tac oldCTE)
  apply (rename_tac x old_dest_node)
  apply (case_tac cte)
  apply (rename_tac src_cap src_node)
  apply clarsimp
  apply (subgoal_tac "\<exists>c. caps_of_state a ptr = Some c")
   prefer 2
   apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply clarsimp
  apply (subgoal_tac "cap_relation c src_cap")
   prefer 2
   apply (drule caps_of_state_cteD)
   apply (drule (1) pspace_relation_ctes_ofI)
     apply fastforce
    apply fastforce
   apply fastforce
   apply (drule_tac p=ptr' in set_cap_not_quite_corres, assumption+)
            apply fastforce
           apply fastforce
          apply fastforce
         apply (erule cte_wp_at_weakenE, rule TrueI)
        apply fastforce
       apply fastforce
      apply assumption
     apply fastforce
    apply (rule cr)
   apply (rule refl)
  apply (clarsimp simp: split_def)
  apply (rule bind_execI, assumption)
  apply (drule_tac p=ptr and c="cap.NullCap" in set_cap_not_quite_corres')
                 apply assumption+
            apply (frule use_valid [OF _ set_cap_valid_objs])
             apply fastforce
            apply assumption
           apply (frule use_valid [OF _ set_cap_aligned])
            apply fastforce
           apply assumption
          apply (frule use_valid [OF _ set_cap_distinct])
           apply fastforce
          apply assumption
         apply (frule use_valid [OF _ set_cap_cte_at])
          prefer 2
          apply assumption
         apply assumption
        apply (drule updateCap_stuff)
        apply (elim conjE mp, fastforce)
       apply (drule updateCap_stuff)
       apply (elim conjE mp, fastforce)
      apply assumption
     apply simp
    apply simp
   apply (rule refl)
  apply clarsimp
  apply (rule bind_execI, assumption)
  apply(subgoal_tac "mdb_move_abs ptr ptr' (cdt a) a")
  apply (frule mdb_move_abs'.intro)
   prefer 2
   apply(rule mdb_move_abs.intro)
      apply(clarsimp)
     apply(fastforce elim!: cte_wp_at_weakenE)
    apply(simp)
   apply(simp)
  apply (clarsimp simp: exec_gets exec_get exec_put set_cdt_def
                        set_original_def bind_assoc modify_def
         |(rule bind_execI[where f="cap_move_ext x y z x'" for x y z x'], clarsimp simp: mdb_move_abs'.cap_move_ext_det_def2 update_cdt_list_def set_cdt_list_def put_def) | rule refl )+
  apply (clarsimp simp: put_def)
  apply (clarsimp simp: invs'_def valid_state'_def)
  apply (frule updateCap_dynamic_duo, fastforce, fastforce)
  apply (frule(2) updateCap_dynamic_duo [OF _ conjunct1 conjunct2])
  apply (subgoal_tac "no_0 (ctes_of b)")
   prefer 2
   apply fastforce
  apply (frule(1) use_valid [OF _ updateCap_no_0])
  apply (frule(2) use_valid [OF _ updateCap_no_0, OF _ use_valid [OF _ updateCap_no_0]])
  apply (elim conjE)
  apply (drule (4) updateMDB_the_lot', elim conjE)
  apply (drule (4) updateMDB_the_lot, elim conjE)
  apply (drule (4) updateMDB_the_lot, elim conjE)
  apply (drule (4) updateMDB_the_lot, elim conjE)
  apply (drule updateCap_stuff, elim conjE, erule (1) impE)
  apply (drule updateCap_stuff)
  apply (subgoal_tac "pspace_distinct' b \<and> pspace_aligned' b")
   prefer 2
   apply (elim valid_pspaceE' conjE)
   apply (rule conjI; assumption)
  apply (simp only: )
  apply (thin_tac "ctes_of t = s" for t s)+
  apply (thin_tac "ksMachineState t = p" for t p)+
  apply (thin_tac "ksCurThread t = p" for t p)+
  apply (thin_tac "ksIdleThread t = p" for t p)+
  apply (thin_tac "ksReadyQueues t = p" for t p)+
  apply (thin_tac "ksSchedulerAction t = p" for t p)+
  apply (subgoal_tac "\<forall>p. cte_at p ta = cte_at p a")
   prefer 2
   subgoal by (simp add: set_cap_cte_eq)
  apply (clarsimp simp add: swp_def cte_wp_at_ctes_of simp del: split_paired_All)
  apply (subgoal_tac "cte_at ptr' a")
   prefer 2
   apply (erule cte_wp_at_weakenE, rule TrueI)
  apply (subgoal_tac "cte_map ptr \<noteq> cte_map ptr'")
   prefer 2
   apply (erule (2) cte_map_inj)
     apply fastforce
    apply fastforce
   apply fastforce
  apply (rule conjI)
   subgoal by (clarsimp simp: ghost_relation_typ_at set_cap_a_type_inv data_at_def)
  apply (thin_tac "gsCNodes t = p" for t p)+
  apply (thin_tac "ksMachineState t = p" for t p)+
  apply (thin_tac "ksCurThread t = p" for t p)+
  apply (thin_tac "ksWorkUnitsCompleted t = p" for t p)+
  apply (thin_tac "ksIdleThread t = p" for t p)+
  apply (thin_tac "ksReadyQueues t = p" for t p)+
  apply (thin_tac "ksSchedulerAction t = p" for t p)+
  apply (thin_tac "cur_thread t = p" for t p)+
  apply (thin_tac "domain_index t = p" for t p)+
  apply (thin_tac "domain_time t = p" for t p)+
  apply (thin_tac "cur_domain t = p" for t p)+
  apply (thin_tac "scheduler_action t = p" for t p)+
  apply (thin_tac "ready_queues t = p" for t p)+
  apply (thin_tac "idle_thread t = p" for t p)+
  apply (thin_tac "machine_state t = p" for t p)+
  apply (thin_tac "work_units_completed t = p" for t p)+
  apply (thin_tac "ksArchState t = p" for t p)+
  apply (thin_tac "gsUserPages t = p" for t p)+
  apply (thin_tac "ksCurDomain t = p" for t p)+
  apply (thin_tac "ksInterruptState t = p" for t p)+
  apply (thin_tac "ksDomScheduleIdx t = p" for t p)+
  apply (thin_tac "ksDomainTime t = p" for t p)+
  apply (thin_tac "ksDomSchedule t = p" for t p)+
  apply (thin_tac "ctes_of t = p" for t p)+
  apply (thin_tac "pspace_relation t p" for t p)+
  apply (thin_tac "interrupt_state_relation s t p" for s t p)+
  apply (thin_tac "ghost_relation s t p" for s t p)+
  apply (thin_tac "sched_act_relation t p" for t p)+
  apply (thin_tac "ready_queues_relation t p" for t p)+
  apply (subst conj_assoc[symmetric])
  apply (rule conjI)
   defer
   apply (drule set_cap_caps_of_state_monad)+
   apply (simp add: modify_map_mdb_cap)
   apply (simp add: modify_map_apply)
   apply (clarsimp simp add: revokable_relation_def simp del: fun_upd_apply)
   apply simp
   apply (rule conjI)
    apply clarsimp
    apply (erule_tac x="fst ptr" in allE)
    apply (erule_tac x="snd ptr" in allE)
    apply simp
    apply (erule impE)
     subgoal by (clarsimp simp: cte_wp_at_caps_of_state null_filter_def split: if_split_asm)
    apply simp
   apply clarsimp
   apply (subgoal_tac "null_filter (caps_of_state a) (aa,bb) \<noteq> None")
    prefer 2
    subgoal by (clarsimp simp only: null_filter_def cap.simps option.simps
                               fun_upd_def simp_thms
          split: if_splits)
   apply clarsimp
   apply (subgoal_tac "cte_at (aa,bb) a")
    prefer 2
    apply (drule null_filter_caps_of_stateD)
    apply (erule cte_wp_cte_at)
   apply (frule_tac p="(aa,bb)" and p'="ptr'" in cte_map_inj, assumption+)
      apply fastforce
     apply fastforce
    apply fastforce
   apply (clarsimp split: if_split_asm)
   apply (subgoal_tac "(aa,bb) \<noteq> ptr")
    apply (frule_tac p="(aa,bb)" and p'="ptr" in cte_map_inj, assumption+)
       apply fastforce
      apply fastforce
     apply fastforce
    subgoal by clarsimp
   subgoal by (simp add: null_filter_def split: if_splits) (*long *)
  apply (subgoal_tac "mdb_move (ctes_of b) (cte_map ptr) src_cap src_node (cte_map ptr') cap' old_dest_node")
   prefer 2
   apply (rule mdb_move.intro)
    apply (rule mdb_ptr.intro)
     apply (rule vmdb.intro)
     apply (simp add: valid_pspace'_def valid_mdb'_def)
    apply (erule mdb_ptr_axioms.intro)
   apply (rule mdb_move_axioms.intro)
        apply assumption
       apply (simp add: nullPointer_def)
      apply (simp add: nullPointer_def)
     apply (erule weak_derived_sym')
    apply clarsimp
   apply assumption
  apply (rule conjI)
   apply (simp (no_asm) add: cdt_relation_def)
   apply clarsimp
   apply (subst mdb_move.descendants, assumption)
   apply (subst mdb_move_abs.descendants[simplified fun_upd_apply])
    apply (rule mdb_move_abs.intro)
       apply fastforce
      apply (fastforce elim!: cte_wp_at_weakenE)
     apply simp
    subgoal by simp
   apply (case_tac "(aa,bb) = ptr", simp)
   apply (subgoal_tac "cte_map (aa,bb) \<noteq> cte_map ptr")
    prefer 2
    apply (erule (2) cte_map_inj, fastforce, fastforce, fastforce)
   apply (case_tac "(aa,bb) = ptr'")
    subgoal by (simp add: cdt_relation_def del: split_paired_All)
   apply (subgoal_tac "cte_map (aa,bb) \<noteq> cte_map ptr'")
    prefer 2
    apply (erule (2) cte_map_inj, fastforce, fastforce, fastforce)
   apply (simp only: if_False)
   apply simp
   apply (subgoal_tac "descendants_of' (cte_map (aa, bb)) (ctes_of b) =
                       cte_map ` descendants_of (aa, bb) (cdt a)")
    prefer 2
    subgoal by (simp add: cdt_relation_def del: split_paired_All)
   apply simp
   apply (rule conjI)
    apply clarsimp
    apply (subst inj_on_image_set_diff15)
       apply (rule inj_on_descendants_cte_map)
          apply fastforce
         apply fastforce
        apply fastforce
       apply fastforce
      apply (rule subset_refl)
     subgoal by simp
    subgoal by simp
   apply clarsimp
   apply (drule (1) cte_map_inj_eq)
       apply (erule descendants_of_cte_at)
       apply fastforce
      apply fastforce
     apply fastforce
    apply fastforce
   subgoal by clarsimp
  apply(clarsimp simp: cdt_list_relation_def)

  apply(subst next_slot_eq2)
    apply(simp split: option.splits)
    apply(intro conjI impI)
     apply(rule mdb_move_abs'.next_slot_no_parent)
       apply(simp, fastforce, simp)
    apply(intro allI impI)
    apply(rule mdb_move_abs'.next_slot)
      apply(simp, fastforce, simp)
   subgoal by(fastforce split: option.splits)
  apply(case_tac "ctes_of b (cte_map (aa, bb))")
   subgoal by (clarsimp simp: modify_map_def split: if_split_asm)
  apply(case_tac ab)
  apply(frule mdb_move.m'_next)
    apply(simp, fastforce)
  apply(case_tac "(aa, bb) = ptr")
   apply(simp)
  apply(case_tac "(aa, bb) = ptr'")
   apply(case_tac "next_slot ptr (cdt_list (a)) (cdt a)")
    subgoal by(simp)
   apply(simp)
   apply(erule_tac x="fst ptr" in allE)
   apply(erule_tac x="snd ptr" in allE)
   subgoal by(clarsimp split: if_split_asm)
  apply(frule invs_mdb, frule invs_valid_pspace)
  apply(frule finite_depth)
  apply simp
  apply(case_tac "next_slot (aa, bb) (cdt_list (a)) (cdt a) = Some ptr")
   apply(frule(3) cte_at_next_slot)
   apply(erule_tac x=aa in allE, erule_tac x=bb in allE)
   subgoal by (clarsimp simp: cte_map_inj_eq valid_pspace_def split: if_split_asm)
  apply(simp)
  apply(case_tac "next_slot (aa, bb) (cdt_list (a)) (cdt a)")
   subgoal by(simp)
  apply(frule(3) cte_at_next_slot)
  apply(frule(3) cte_at_next_slot')
  apply(erule_tac x=aa in allE, erule_tac x=bb in allE)
  by(clarsimp simp: cte_map_inj_eq valid_pspace_def split: if_split_asm)

lemmas cur_tcb_lift =
  hoare_lift_Pf [where f = ksCurThread and P = tcb_at', folded cur_tcb'_def]

lemma valid_bitmapQ_lift:
  assumes prq: "\<And>P. \<lbrace>\<lambda>s. P (ksReadyQueues s) \<rbrace> f \<lbrace>\<lambda>_ s. P (ksReadyQueues s)\<rbrace>"
  and     prqL1: "\<And>P. \<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksReadyQueuesL1Bitmap s)\<rbrace>"
  and     prqL2: "\<And>P. \<lbrace>\<lambda>s. P (ksReadyQueuesL2Bitmap s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksReadyQueuesL2Bitmap s)\<rbrace>"
  shows   "\<lbrace>Invariants_H.valid_bitmapQ\<rbrace> f \<lbrace>\<lambda>_. Invariants_H.valid_bitmapQ\<rbrace>"
  unfolding valid_bitmapQ_def bitmapQ_def
  apply (wp hoare_vcg_all_lift)
   apply (wps prq prqL1 prqL2)
  apply (rule hoare_vcg_prop, assumption)
  done

lemma bitmapQ_no_L1_orphans_lift:
  assumes prq: "\<And>P. \<lbrace>\<lambda>s. P (ksReadyQueues s) \<rbrace> f \<lbrace>\<lambda>_ s. P (ksReadyQueues s)\<rbrace>"
  and     prqL1: "\<And>P. \<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksReadyQueuesL1Bitmap s)\<rbrace>"
  and     prqL2: "\<And>P. \<lbrace>\<lambda>s. P (ksReadyQueuesL2Bitmap s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksReadyQueuesL2Bitmap s)\<rbrace>"
  shows   "\<lbrace> bitmapQ_no_L1_orphans \<rbrace> f \<lbrace>\<lambda>_. bitmapQ_no_L1_orphans \<rbrace>"
  unfolding valid_bitmapQ_def bitmapQ_def bitmapQ_no_L1_orphans_def
  apply (wp hoare_vcg_all_lift)
   apply (wps prq prqL1 prqL2)
  apply (rule hoare_vcg_prop, assumption)
  done

lemma bitmapQ_no_L2_orphans_lift:
  assumes prq: "\<And>P. \<lbrace>\<lambda>s. P (ksReadyQueues s) \<rbrace> f \<lbrace>\<lambda>_ s. P (ksReadyQueues s)\<rbrace>"
  and     prqL1: "\<And>P. \<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksReadyQueuesL1Bitmap s)\<rbrace>"
  and     prqL2: "\<And>P. \<lbrace>\<lambda>s. P (ksReadyQueuesL2Bitmap s)\<rbrace> f \<lbrace>\<lambda>_ s. P (ksReadyQueuesL2Bitmap s)\<rbrace>"
  shows   "\<lbrace> bitmapQ_no_L2_orphans \<rbrace> f \<lbrace>\<lambda>_. bitmapQ_no_L2_orphans \<rbrace>"
  unfolding valid_bitmapQ_def bitmapQ_def bitmapQ_no_L2_orphans_def
  apply (wp hoare_vcg_all_lift)
   apply (wps prq prqL1 prqL2)
  apply (rule hoare_vcg_prop, assumption)
  done

lemma setCTE_norqL1 [wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s)\<rbrace> setCTE ptr cte \<lbrace>\<lambda>r s. P (ksReadyQueuesL1Bitmap s) \<rbrace>"
  by (clarsimp simp: valid_def dest!: setCTE_pspace_only)

lemma setCTE_norqL2 [wp]:
  "\<lbrace>\<lambda>s. P (ksReadyQueuesL2Bitmap s)\<rbrace> setCTE ptr cte \<lbrace>\<lambda>r s. P (ksReadyQueuesL2Bitmap s) \<rbrace>"
  by (clarsimp simp: valid_def dest!: setCTE_pspace_only)

crunch cteInsert
  for nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  and norq[wp]:  "\<lambda>s. P (ksReadyQueues s)"
  and norqL1[wp]: "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  and norqL2[wp]: "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
  and typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: updateObject_cte_inv crunch_wps ignore_del: setObject)

lemmas updateMDB_typ_ats [wp] = typ_at_lifts [OF updateMDB_typ_at']
lemmas updateCap_typ_ats [wp] = typ_at_lifts [OF updateCap_typ_at']
lemmas cteInsert_typ_ats [wp] = typ_at_lifts [OF cteInsert_typ_at']

lemma setObject_cte_ct:
  "\<lbrace>\<lambda>s. P (ksCurThread s)\<rbrace> setObject t (v::cte) \<lbrace>\<lambda>rv s. P (ksCurThread s)\<rbrace>"
  by (clarsimp simp: valid_def setCTE_def[symmetric] dest!: setCTE_pspace_only)

crunch cteInsert
  for ct[wp]: "\<lambda>s. P (ksCurThread s)"
  (wp: setObject_cte_ct hoare_drop_imps)
end
context mdb_insert
begin
interpretation Arch . (*FIXME: arch-split*)
lemma n_src_dest:
  "n \<turnstile> src \<leadsto> dest"
  by (simp add: n_direct_eq)

lemma dest_chain_0 [simp, intro!]:
  "n \<turnstile> dest \<leadsto>\<^sup>+ 0"
  using chain_n n_dest
  by (simp add: mdb_chain_0_def) blast

lemma m_tranclD:
  "m \<turnstile> p \<leadsto>\<^sup>+ p' \<Longrightarrow> p' \<noteq> dest \<and> (p = dest \<longrightarrow> p' = 0) \<and> n \<turnstile> p \<leadsto>\<^sup>+ p'"
  apply (erule trancl_induct)
   apply (rule context_conjI, clarsimp)
   apply (rule context_conjI, clarsimp)
   apply (cases "p = src")
    apply simp
    apply (rule trancl_trans)
     apply (rule r_into_trancl)
     apply (rule n_src_dest)
    apply (rule r_into_trancl)
    apply (simp add: n_direct_eq)
   apply (cases "p = dest", simp)
   apply (rule r_into_trancl)
   apply (simp add: n_direct_eq)
  apply clarsimp
  apply (rule context_conjI, clarsimp)
  apply (rule context_conjI, clarsimp simp: mdb_next_unfold)
  apply (case_tac "y = src")
   apply clarsimp
   apply (erule trancl_trans)
   apply (rule trancl_trans)
    apply (rule r_into_trancl)
    apply (rule n_src_dest)
   apply (rule r_into_trancl)
   apply (simp add: n_direct_eq)
  apply (case_tac "y = dest", simp)
  apply (erule trancl_trans)
  apply (rule r_into_trancl)
  apply (simp add: n_direct_eq)
  done

lemma n_trancl_eq':
  "n \<turnstile> p \<leadsto>\<^sup>+ p' =
  (if p' = dest then m \<turnstile> p \<leadsto>\<^sup>* src
   else if p = dest then m \<turnstile> src \<leadsto>\<^sup>+ p'
   else m \<turnstile> p \<leadsto>\<^sup>+ p')"
  apply (rule iffI)
   apply (erule trancl_induct)
    apply (clarsimp simp: n_direct_eq)
    apply (fastforce split: if_split_asm)
   apply (clarsimp simp: n_direct_eq split: if_split_asm)
      apply fastforce
     apply fastforce
    apply (fastforce intro: trancl_trans)
   apply (fastforce intro: trancl_trans)
  apply (simp split: if_split_asm)
    apply (drule rtranclD)
    apply (erule disjE)
     apply (fastforce intro: n_src_dest)
    apply (clarsimp dest!: m_tranclD)
    apply (erule trancl_trans)
    apply (fastforce intro: n_src_dest)
   apply (drule m_tranclD, clarsimp)
   apply (drule tranclD)
   apply clarsimp
   apply (insert n_src_dest)[1]
   apply (drule (1) next_single_value)
   subgoal by (clarsimp dest!: rtrancl_eq_or_trancl[THEN iffD1])
  apply (drule m_tranclD)
  apply clarsimp
  done

lemma n_trancl_eq:
  "n \<turnstile> p \<leadsto>\<^sup>+ p' =
  (if p' = dest then p = src \<or> m \<turnstile> p \<leadsto>\<^sup>+ src
   else if p = dest then m \<turnstile> src \<leadsto>\<^sup>+ p'
   else m \<turnstile> p \<leadsto>\<^sup>+ p')"
  by (safe; clarsimp simp: n_trancl_eq'
                    dest!: rtrancl_eq_or_trancl[THEN iffD1]
                   intro!: rtrancl_eq_or_trancl[THEN iffD2]
                     cong: if_cong)

lemma n_rtrancl_eq:
  "n \<turnstile> p \<leadsto>\<^sup>* p' =
  (if p' = dest then p = dest \<or> p \<noteq> dest \<and> m \<turnstile> p \<leadsto>\<^sup>* src
   else if p = dest then p' \<noteq> src \<and> m \<turnstile> src \<leadsto>\<^sup>* p'
   else m \<turnstile> p \<leadsto>\<^sup>* p')"
  apply clarsimp
  by (safe; clarsimp simp: n_trancl_eq'
                       dest!: rtrancl_eq_or_trancl[THEN iffD1]
                      intro!: rtrancl_eq_or_trancl[THEN iffD2])

lemma n_cap:
  "n p = Some (CTE cap node) \<Longrightarrow>
  \<exists>node'. if p = dest then cap = c' \<and> m p = Some (CTE dest_cap node')
          else m p = Some (CTE cap node')"
  by (simp add: n src dest new_src_def new_dest_def split: if_split_asm)

lemma m_cap:
  "m p = Some (CTE cap node) \<Longrightarrow>
  \<exists>node'. if p = dest then cap = dest_cap \<and> n p = Some (CTE c' node')
          else n p = Some (CTE cap node')"
  apply (simp add: n new_src_def new_dest_def)
  apply (cases "p=dest")
   apply (auto simp: src dest)
  done

lemma chunked_m:
  "mdb_chunked m"
  using valid by (simp add: valid_mdb_ctes_def)

lemma derived_region1 [simp]:
  "badge_derived' c' src_cap \<Longrightarrow>
  sameRegionAs c' cap = sameRegionAs src_cap cap"
  by (clarsimp simp add: badge_derived'_def sameRegionAs_def2)

lemma derived_region2 [simp]:
  "badge_derived' c' src_cap \<Longrightarrow>
  sameRegionAs cap c' = sameRegionAs cap src_cap"
  by (clarsimp simp add: badge_derived'_def sameRegionAs_def2)

lemma derived_mdb_chunked_arch_assms[simp]:
  "badge_derived' c' src_cap \<Longrightarrow> mdb_chunked_arch_assms c' = mdb_chunked_arch_assms src_cap"
  by (clarsimp simp: mdb_chunked_arch_assms_def)

lemma chunked_n:
  assumes b: "badge_derived' c' src_cap"
  shows "mdb_chunked n"
  using chunked_m src b
  apply (clarsimp simp: mdb_chunked_def)
  apply (drule n_cap)+
  apply clarsimp
  apply (simp split: if_split_asm)
    apply clarsimp
    apply (erule_tac x=src in allE)
    apply (erule_tac x=p' in allE)
    apply simp
    apply (case_tac "src=p'")
     apply (clarsimp simp: n_trancl_eq)
     apply (clarsimp simp: is_chunk_def n_trancl_eq n_rtrancl_eq n_dest new_dest_def)
     apply (drule (1) trancl_rtrancl_trancl)
     apply simp
    apply (clarsimp simp: n_trancl_eq)
    apply (rule conjI)
     apply (clarsimp simp: is_chunk_def n_trancl_eq n_rtrancl_eq)
     apply (erule_tac x=p'' in allE)
     apply clarsimp
     apply (drule_tac p=p'' in m_cap)
     apply (clarsimp split: if_split_asm)
    apply clarsimp
    apply (clarsimp simp: is_chunk_def n_trancl_eq n_rtrancl_eq n_dest new_dest_def)
    apply (rule conjI)
     apply clarsimp
     apply (erule_tac x=src in allE)
     apply simp
    apply clarsimp
    apply (erule_tac x=p'' in allE)
    apply clarsimp
    apply (drule_tac p=p'' in m_cap)
    apply (clarsimp split: if_split_asm)
   apply (clarsimp simp: n_trancl_eq)
   apply (case_tac "p=src")
    apply (clarsimp simp: is_chunk_def n_trancl_eq n_rtrancl_eq n_dest new_dest_def)
    apply (drule (1) trancl_rtrancl_trancl)
    apply simp
   apply simp
   apply (erule_tac x=p in allE)
   apply (erule_tac x=src in allE)
   apply clarsimp
   apply (rule conjI)
    apply clarsimp
    apply (clarsimp simp: is_chunk_def n_trancl_eq n_rtrancl_eq n_dest new_dest_def)
    apply (erule_tac x=p'' in allE)
    apply clarsimp
    apply (drule_tac p=p'' in m_cap)
    apply clarsimp
   apply clarsimp
   apply (clarsimp simp: is_chunk_def n_trancl_eq n_rtrancl_eq n_dest new_dest_def)
   apply (erule_tac x=p'' in allE)
   apply clarsimp
   apply (drule_tac p=p'' in m_cap)
   apply clarsimp
  apply (clarsimp simp: n_trancl_eq)
  apply (erule_tac x=p in allE)
  apply (erule_tac x=p' in allE)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (simp add: is_chunk_def n_trancl_eq n_rtrancl_eq n_dest new_dest_def)
   apply clarsimp
   apply (rule conjI)
    apply clarsimp
    apply (rule conjI)
     apply clarsimp
     apply (erule sameRegionAsE, simp_all add: sameRegionAs_def3 isCap_simps)[1]
       apply force
      apply (clarsimp simp: isCap_simps)
     apply (clarsimp simp: isCap_simps)
    apply fastforce
   apply clarsimp
   apply (erule_tac x=p'' in allE)
   apply clarsimp
   apply (drule_tac p=p'' in m_cap)
   apply clarsimp
  apply clarsimp
  apply (simp add: is_chunk_def n_trancl_eq n_rtrancl_eq n_dest new_dest_def)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (rule conjI)
    apply clarsimp
    apply (erule_tac x=p in allE, simp, erule(1) sameRegionAs_trans)
   apply fastforce
  apply clarsimp
  apply (erule_tac x=p'' in allE)
  apply clarsimp
  apply (drule_tac p=p'' in m_cap)
  apply clarsimp
  done

end

context mdb_insert_der
begin

lemma untyped_c':
  "untypedRange c' = untypedRange src_cap"
  "isUntypedCap c' = isUntypedCap src_cap"
  using partial_is_derived'
  apply -
   apply (case_tac "isUntypedCap src_cap")
     by (clarsimp simp: gen_isCap_simps freeIndex_update_def X64.is_derived'_def (* FIXME arch-split *)
       badge_derived'_def capMasterCap_def split:if_splits capability.splits)+

lemma capRange_c':
  "capRange c' = capRange src_cap"
  using partial_is_derived' untyped_c'
  apply -
  apply (case_tac "isUntypedCap src_cap")
   apply (clarsimp simp:untypedCapRange)
  apply (rule master_eqI, rule capRange_Master)
  apply simp
  apply (rule arg_cong)
  apply (auto simp: gen_isCap_simps freeIndex_update_def X64.is_derived'_def (* FIXME arch-split *)
                    badge_derived'_def capMasterCap_def
              split: if_splits capability.splits)
  done

lemma untyped_no_parent:
  "isUntypedCap src_cap \<Longrightarrow> \<not> m \<turnstile> src \<rightarrow> p"
  using partial_is_derived' untyped_c'
  (* FIXME arch-split *)
  by (clarsimp simp: X64.is_derived'_def gen_isCap_simps freeIndex_update_def descendants_of'_def)

end

lemma (in mdb_insert) n_revocable:
  "n p = Some (CTE cap node) \<Longrightarrow>
  \<exists>node'. if p = dest then mdbRevocable node = isCapRevocable c' src_cap
          else mdbRevocable node = mdbRevocable node' \<and> m p = Some (CTE cap node')"
  using src dest
  by (clarsimp simp: n new_src_def new_dest_def split: if_split_asm)

lemma (in mdb_insert_der) irq_control_n:
  "irq_control n"
  using src dest partial_is_derived'
  apply (clarsimp simp: irq_control_def)
  apply (frule n_cap)
  apply (drule n_revocable)
  apply (clarsimp split: if_split_asm)
   apply (simp add: X64.is_derived'_def gen_isCap_simps) (* FIXME arch-split *)
  apply (frule irq_revocable, rule irq_control)
  apply clarsimp
  apply (drule n_cap)
  apply (clarsimp split: if_split_asm)
  apply (erule disjE)
   apply (simp add: X64.is_derived'_def gen_isCap_simps) (* FIXME arch-split *)
  apply (erule (1) irq_controlD, rule irq_control)
  done

context mdb_insert_child
begin

lemma untyped_mdb_n:
  shows "untyped_mdb' n"
  using untyped_mdb
  apply (clarsimp simp add: untyped_mdb'_def descendants split del: if_split)
  apply (drule n_cap)+
  apply (clarsimp split: if_split_asm)
   apply (erule disjE, clarsimp)
   apply (simp add: descendants_of'_def)
   apply (erule_tac x=p in allE)
   apply (erule_tac x=src in allE)
   apply (simp add: src untyped_c' capRange_c')
  apply (erule disjE)
   apply clarsimp
   apply (simp add: descendants_of'_def untyped_c')
   apply (erule_tac x=src in allE)
   apply (erule_tac x=p' in allE)
   apply (fastforce simp: src dest: untyped_no_parent)
  apply (case_tac "p=src", simp)
  apply simp
  done

lemma parent_untyped_must_not_usable:
  "\<lbrakk>ptr \<noteq> src; m ptr = Some (CTE ccap node');
    untypedRange ccap = untypedRange src_cap; capAligned src_cap;
    isUntypedCap src_cap \<rbrakk>
   \<Longrightarrow> usableUntypedRange ccap = {}"
  using untyped_inc src
  apply (clarsimp simp:untyped_inc'_def)
  apply (erule_tac x = ptr in allE)
  apply (erule_tac x = src in allE)
  apply clarsimp
  apply (subgoal_tac "isUntypedCap ccap")
   apply clarsimp
   apply (drule_tac p = ptr in untyped_no_parent)
   apply (simp add:descendants_of'_def)
  apply (drule (1) aligned_untypedRange_non_empty)
  apply (case_tac ccap, simp_all add: gen_isCap_simps)
  done

lemma untyped_inc_n:
  "\<lbrakk>capAligned src_cap;isUntypedCap src_cap \<longrightarrow> usableUntypedRange src_cap = {}\<rbrakk>
   \<Longrightarrow> untyped_inc' n"
  using untyped_inc
  apply (clarsimp simp add: untyped_inc'_def descendants split del: if_split)
  apply (drule n_cap)+
  apply (clarsimp split: if_split_asm)
   apply (case_tac "p=dest", simp)
   apply (simp add: descendants_of'_def untyped_c')
   apply (erule_tac x=p in allE)
   apply (erule_tac x=src in allE)
   apply (simp add: src)
   apply (frule_tac p=p in untyped_no_parent)
   apply clarsimp
  apply (erule disjE)
   apply clarsimp
   apply (case_tac "p = src")
     using src
     apply clarsimp
    apply (drule(4) parent_untyped_must_not_usable)
    apply simp
   apply (intro conjI)
      apply clarsimp
     apply clarsimp
     using src
     apply clarsimp
    apply clarsimp
  apply (case_tac "p=dest")
   apply (simp add: descendants_of'_def untyped_c')
   apply (erule_tac x=p' in allE)
   apply (erule_tac x=src in allE)
     apply (clarsimp simp:src)
  apply (frule_tac p=p' in untyped_no_parent)
   apply (case_tac "p' = src")
    apply (clarsimp simp:src)
   apply (elim disjE)
     apply (erule disjE[OF iffD1[OF subset_iff_psubset_eq]])
      apply simp+
     apply (erule disjE[OF iffD1[OF subset_iff_psubset_eq]])
      apply simp+
   apply (clarsimp simp:Int_ac)
  apply (erule_tac x=p' in allE)
   apply (erule_tac x=p in allE)
  apply (case_tac "p' = src")
    apply (clarsimp simp:src descendants_of'_def untyped_c')
   apply (elim disjE)
     apply (erule disjE[OF iffD1[OF subset_iff_psubset_eq]])
      apply (simp,intro conjI,clarsimp+)
     apply (intro conjI)
       apply clarsimp+
     apply (erule disjE[OF iffD1[OF subset_iff_psubset_eq]])
      apply (simp,intro conjI,clarsimp+)
     apply (intro conjI)
       apply clarsimp+
   apply (clarsimp simp:Int_ac,intro conjI,clarsimp+)
  apply (clarsimp simp:descendants_of'_def)
  apply (case_tac "p = src")
   apply simp
   apply (elim disjE)
     apply (erule disjE[OF iffD1[OF subset_iff_psubset_eq]])
      apply (simp,intro conjI,clarsimp+)
     apply (intro conjI)
       apply clarsimp+
     apply (erule disjE[OF iffD1[OF subset_iff_psubset_eq]])
      apply clarsimp+
     apply fastforce
   apply (clarsimp simp:Int_ac,intro conjI,clarsimp+)
  apply (intro conjI)
   apply (elim disjE)
    apply (simp add:Int_ac)+
  apply clarsimp
  done

end

context mdb_insert_sib
begin

lemma untyped_mdb_n:
  shows "untyped_mdb' n"
  using untyped_mdb
  apply (clarsimp simp add: untyped_mdb'_def descendants split del: if_split)
  apply (drule n_cap)+
  apply (clarsimp split: if_split_asm simp: descendants_of'_def capRange_c' untyped_c')
   apply (erule_tac x=src in allE)
   apply (erule_tac x=p' in allE)
   apply (fastforce simp: src dest: untyped_no_parent)
  apply (erule_tac x=p in allE)
  apply (erule_tac x=src in allE)
  apply (simp add: src)
  done

lemma not_untyped: "capAligned c' \<Longrightarrow> \<not>isUntypedCap src_cap"
  using no_child partial_is_derived' ut_rev src
  apply (clarsimp simp: ut_revocable'_def X64.isMDBParentOf_CTE) (* FIXME arch-split *)
  apply (erule_tac x=src in allE)
  apply simp
  apply (clarsimp simp: X64.is_derived'_def freeIndex_update_def gen_isCap_simps capAligned_def
                        badge_derived'_def) (* FIXME arch-split *)
  apply (clarsimp simp: X64.sameRegionAs_def3 capMasterCap_def gen_isCap_simps
                        is_aligned_no_overflow (* FIXME arch-split *)
                  split: capability.splits)
  done

lemma untyped_inc_n:
  assumes c': "capAligned c'"
  shows "untyped_inc' n"
  using untyped_inc not_untyped [OF c']
  apply (clarsimp simp add: untyped_inc'_def descendants split del: if_split)
  apply (drule n_cap)+
  apply (clarsimp split: if_split_asm)
   apply (simp add: descendants_of'_def untyped_c')
  apply (case_tac "p = dest")
   apply (clarsimp simp: untyped_c')
  apply simp
  apply (erule_tac x=p in allE)
  apply (erule_tac x=p' in allE)
  apply simp
  done

end

lemma trancl_prev_update:
  "modify_map m ptr (cteMDBNode_update (mdbPrev_update z)) \<turnstile> x \<leadsto>\<^sup>+ y = m \<turnstile> x \<leadsto>\<^sup>+ y"
  apply (rule iffI)
   apply (erule update_prev_next_trancl2)
  apply (erule update_prev_next_trancl)
  done

lemma rtrancl_prev_update:
  "modify_map m ptr (cteMDBNode_update (mdbPrev_update z)) \<turnstile> x \<leadsto>\<^sup>* y = m \<turnstile> x \<leadsto>\<^sup>* y"
  by (simp add: trancl_prev_update rtrancl_eq_or_trancl)

lemma mdb_chunked_prev_update:
  "mdb_chunked (modify_map m x (cteMDBNode_update (mdbPrev_update f))) = mdb_chunked m"
  apply (simp add: mdb_chunked_def trancl_prev_update rtrancl_prev_update is_chunk_def)
  apply (rule iffI)
   apply clarsimp
   apply (erule_tac x=p in allE)
   apply (erule_tac x=p' in allE)
   apply (erule_tac x=cap in allE)
   apply (simp add: modify_map_if split: if_split_asm)
   apply (erule impE, blast)
   apply (erule allE, erule impE, blast)
   apply clarsimp
   apply blast
  apply clarsimp
  apply (erule_tac x=p in allE)
  apply (erule_tac x=p' in allE)
  apply (erule_tac x=cap in allE)
  apply (simp add: modify_map_if split: if_split_asm)
    apply (erule impE, blast)
    apply clarsimp
    apply blast
   apply (erule allE, erule impE, blast)
   apply clarsimp
   apply blast
  apply clarsimp
  apply blast
  done

lemma descendants_of_prev_update:
  "descendants_of' p (modify_map m x (cteMDBNode_update (mdbPrev_update f))) =
   descendants_of' p m"
  by (simp add: descendants_of'_def)

lemma untyped_mdb_prev_update:
  "untyped_mdb' (modify_map m x (cteMDBNode_update (mdbPrev_update f))) = untyped_mdb' m"
  apply (simp add: untyped_mdb'_def descendants_of_prev_update)
  apply (rule iffI)
   apply clarsimp
   apply (erule_tac x=p in allE)
   apply (erule_tac x=p' in allE)
   apply (erule_tac x=c in allE)
   apply (simp add: modify_map_if split: if_split_asm)
   apply (erule impE, blast)
   apply (erule allE, erule impE, blast)
   apply clarsimp
  apply clarsimp
  apply (erule_tac x=p in allE)
  apply (erule_tac x=p' in allE)
  apply (erule_tac x=c in allE)
  apply (simp add: modify_map_if split: if_split_asm)
  apply clarsimp
  done

lemma untyped_inc_prev_update:
  "untyped_inc' (modify_map m x (cteMDBNode_update (mdbPrev_update f))) = untyped_inc' m"
  apply (simp add: untyped_inc'_def descendants_of_prev_update)
  apply (rule iffI)
   apply clarsimp
   apply (erule_tac x=p in allE)
   apply (erule_tac x=p' in allE)
   apply (erule_tac x=c in allE)
   apply (simp add: modify_map_if split: if_split_asm)
   apply (erule impE, blast)
   apply (erule allE, erule impE, blast)
   apply clarsimp
  apply clarsimp
  apply (erule_tac x=p in allE)
  apply (erule_tac x=p' in allE)
  apply (erule_tac x=c in allE)
  apply (simp add: modify_map_if split: if_split_asm)
  apply clarsimp
  done

lemma is_derived_badge_derived':
  "is_derived' m src cap cap' \<Longrightarrow> badge_derived' cap cap'"
  by (simp add: X64.is_derived'_def) (* FIXME arch-split *)

context begin interpretation Arch . (*FIXME: arch-split*)

lemma cteInsert_mdb_chain_0:
  "\<lbrace>valid_mdb' and pspace_aligned' and pspace_distinct' and (\<lambda>s. src \<noteq> dest) and
    (\<lambda>s. cte_wp_at' (is_derived' (ctes_of s) src cap \<circ> cteCap) src s)\<rbrace>
  cteInsert cap src dest
  \<lbrace>\<lambda>_ s. mdb_chain_0 (ctes_of s)\<rbrace>"
  apply (unfold cteInsert_def updateCap_def)
  apply (simp add: valid_mdb'_def split del: if_split)
  apply (wp updateMDB_ctes_of_no_0 getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of simp del: fun_upd_apply)
  apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift setUntypedCapAsFull_ctes_of
    setUntypedCapAsFull_ctes_of_no_0  mdb_inv_preserve_modify_map
    setUntypedCapAsFull_mdb_chain_0 mdb_inv_preserve_fun_upd | simp del:fun_upd_apply)+
  apply (wp getCTE_wp)+
  apply (clarsimp simp:cte_wp_at_ctes_of simp del:fun_upd_apply)
  apply (subgoal_tac "src \<noteq> 0")
   prefer 2
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (subgoal_tac "dest \<noteq> 0")
   prefer 2
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (rule conjI)
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (case_tac cte)
  apply (rename_tac s_cap s_node)
  apply (case_tac x)
  apply (simp add: nullPointer_def)
  apply (subgoal_tac "mdb_insert (ctes_of s) src s_cap s_node dest NullCap node" for node)
   apply (drule mdb_insert.chain_n)
   apply (rule mdb_chain_0_modify_map_prev)
   apply (simp add:modify_map_apply)
  apply (clarsimp simp: valid_badges_def)
   apply unfold_locales
          apply (assumption|rule refl)+
    apply (simp add: valid_mdb_ctes_def)
   apply (simp add: valid_mdb_ctes_def)
  apply assumption
  done

lemma cteInsert_mdb_chunked:
  "\<lbrace>valid_mdb' and pspace_aligned' and pspace_distinct' and (\<lambda>s. src \<noteq> dest) and
    (\<lambda>s. cte_wp_at' (is_derived' (ctes_of s) src cap \<circ> cteCap) src s)\<rbrace>
  cteInsert cap src dest
  \<lbrace>\<lambda>_ s. mdb_chunked (ctes_of s)\<rbrace>"
  apply (unfold cteInsert_def updateCap_def)
  apply (simp add: valid_mdb'_def split del: if_split)
  apply (wp updateMDB_ctes_of_no_0 getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of simp del: fun_upd_apply)
  apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift setUntypedCapAsFull_ctes_of
    setUntypedCapAsFull_ctes_of_no_0 mdb_inv_preserve_modify_map
    setUntypedCapAsFull_mdb_chunked mdb_inv_preserve_fun_upd,simp)
  apply (wp getCTE_wp)+
  apply (clarsimp simp:cte_wp_at_ctes_of simp del:fun_upd_apply)
  apply (subgoal_tac "src \<noteq> 0")
   prefer 2
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (subgoal_tac "dest \<noteq> 0")
   prefer 2
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (rule conjI)
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (case_tac cte)
  apply (rename_tac s_cap s_node)
  apply (case_tac cteb)
  apply (rename_tac d_cap d_node)
  apply (simp add: nullPointer_def)
  apply (subgoal_tac "mdb_insert (ctes_of s) src s_cap s_node dest NullCap d_node")
   apply (drule mdb_insert.chunked_n, erule is_derived_badge_derived')
   apply (clarsimp simp: modify_map_apply mdb_chunked_prev_update fun_upd_def)
  apply unfold_locales
          apply (assumption|rule refl)+
    apply (simp add: valid_mdb_ctes_def)
   apply (simp add: valid_mdb_ctes_def)
  apply assumption
  done

lemma cteInsert_untyped_mdb:
  "\<lbrace>valid_mdb' and pspace_distinct' and pspace_aligned' and (\<lambda>s. src \<noteq> dest) and
    (\<lambda>s. cte_wp_at' (is_derived' (ctes_of s) src cap \<circ> cteCap) src s)\<rbrace>
  cteInsert cap src dest
  \<lbrace>\<lambda>_ s. untyped_mdb' (ctes_of s)\<rbrace>"
  apply (unfold cteInsert_def updateCap_def)
  apply (simp add: valid_mdb'_def split del: if_split)
  apply (wp updateMDB_ctes_of_no_0 getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of simp del: fun_upd_apply)
  apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift setUntypedCapAsFull_ctes_of
    setUntypedCapAsFull_ctes_of_no_0 mdb_inv_preserve_modify_map
    setUntypedCapAsFull_untyped_mdb' mdb_inv_preserve_fun_upd,simp)
  apply (wp getCTE_wp)+
  apply (clarsimp simp:cte_wp_at_ctes_of simp del:fun_upd_apply)
  apply (subgoal_tac "src \<noteq> 0")
   prefer 2
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (subgoal_tac "dest \<noteq> 0")
   prefer 2
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (rule conjI)
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (case_tac cte)
  apply (rename_tac s_cap s_node)
  apply (case_tac cteb)
  apply (rename_tac d_cap d_node)
  apply (simp add: nullPointer_def)
  apply (subgoal_tac "mdb_insert_der (ctes_of s) src s_cap s_node dest NullCap d_node cap")
   prefer 2
   apply unfold_locales[1]
            apply (assumption|rule refl)+
      apply (simp add: valid_mdb_ctes_def)
     apply (simp add: valid_mdb_ctes_def)
    apply assumption
   apply assumption
  apply (case_tac "isMDBParentOf (CTE s_cap s_node) (CTE cap
                   (mdbFirstBadged_update (\<lambda>a. isCapRevocable cap s_cap)
                     (mdbRevocable_update (\<lambda>a. isCapRevocable cap s_cap) (mdbPrev_update (\<lambda>a. src) s_node))))")
   apply (subgoal_tac "mdb_insert_child (ctes_of s) src s_cap s_node dest NullCap d_node cap")
    prefer 2
    apply (simp add: mdb_insert_child_def mdb_insert_child_axioms_def)
   apply (drule mdb_insert_child.untyped_mdb_n)
   apply (clarsimp simp: modify_map_apply untyped_mdb_prev_update
                         descendants_of_prev_update fun_upd_def)
  apply (subgoal_tac "mdb_insert_sib (ctes_of s) src s_cap s_node dest NullCap d_node cap")
   prefer 2
   apply (simp add: mdb_insert_sib_def mdb_insert_sib_axioms_def)
  apply (drule mdb_insert_sib.untyped_mdb_n)
  apply (clarsimp simp: modify_map_apply untyped_mdb_prev_update
                        descendants_of_prev_update fun_upd_def)
  done

lemma valid_mdb_ctes_maskedAsFull:
  "\<lbrakk>valid_mdb_ctes m;m src = Some (CTE s_cap s_node)\<rbrakk>
   \<Longrightarrow> valid_mdb_ctes (m(src \<mapsto> CTE (maskedAsFull s_cap cap) s_node))"
  apply (clarsimp simp: maskedAsFull_def)
  apply (intro conjI impI)
  apply (frule mdb_inv_preserve_updateCap
    [where m = m and slot = src and index = "max_free_index (capBlockSize cap)"])
    apply simp
   apply (drule mdb_inv_preserve_sym)
   apply (clarsimp simp:valid_mdb_ctes_def modify_map_def)
   apply (frule mdb_inv_preserve.preserve_stuff,simp)
   apply (frule mdb_inv_preserve.by_products,simp)
   apply (rule mdb_inv_preserve.untyped_inc')
    apply (erule mdb_inv_preserve_sym)
    apply (clarsimp split:if_split_asm simp: isCap_simps max_free_index_def)
   apply simp
  apply (subgoal_tac "m = m(src \<mapsto> CTE s_cap s_node)")
   apply simp
  apply (rule ext)
  apply clarsimp
  done

lemma capAligned_maskedAsFull:
  "capAligned s_cap \<Longrightarrow> capAligned (maskedAsFull s_cap cap)"
 apply (case_tac s_cap)
   apply (clarsimp simp:isCap_simps capAligned_def maskedAsFull_def max_free_index_def)+
 done

lemma maskedAsFull_derived':
  "\<lbrakk>m src = Some (CTE s_cap s_node); is_derived' m ptr b c\<rbrakk>
   \<Longrightarrow> is_derived' (m(src \<mapsto> CTE (maskedAsFull s_cap cap) s_node)) ptr b c"
  apply (subgoal_tac "m(src \<mapsto> CTE (maskedAsFull s_cap cap) s_node)
     = (modify_map m src (cteCap_update (\<lambda>_. maskedAsFull s_cap cap)))")
   apply simp
   apply (clarsimp simp:maskedAsFull_def is_derived'_def)
   apply (intro conjI impI)
    apply (simp add:modify_map_def del:cteCap_update.simps)
   apply (subst same_master_descendants)
       apply simp
      apply (clarsimp simp:isCap_simps capASID_def )+
   apply (clarsimp simp:modify_map_def)
   done

lemma maskedAsFull_usable_empty:
  "\<lbrakk>capMasterCap cap = capMasterCap s_cap;
    isUntypedCap (maskedAsFull s_cap cap)\<rbrakk>
   \<Longrightarrow> usableUntypedRange (maskedAsFull s_cap cap) = {}"
  apply (simp add:isCap_simps maskedAsFull_def max_free_index_def split:if_split_asm)
   apply fastforce+
  done

lemma capAligned_master:
  "\<lbrakk>capAligned cap; capMasterCap cap = capMasterCap ncap\<rbrakk> \<Longrightarrow> capAligned ncap"
  apply (case_tac cap)
   apply (clarsimp simp:capAligned_def)+
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability)
   apply (clarsimp simp:capAligned_def)+
  done

lemma cteInsert_untyped_inc':
  "\<lbrace>valid_mdb' and pspace_distinct' and pspace_aligned' and valid_objs' and (\<lambda>s. src \<noteq> dest) and
    (\<lambda>s. cte_wp_at' (is_derived' (ctes_of s) src cap \<circ> cteCap) src s)\<rbrace>
  cteInsert cap src dest
  \<lbrace>\<lambda>_ s. untyped_inc' (ctes_of s)\<rbrace>"
  apply (unfold cteInsert_def updateCap_def)
  apply (simp add: valid_mdb'_def split del: if_split)
  apply (wp updateMDB_ctes_of_no_0 getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of simp del: fun_upd_apply)
  apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift setUntypedCapAsFull_ctes_of
    setUntypedCapAsFull_ctes_of_no_0 mdb_inv_preserve_modify_map
    setUntypedCapAsFull_untyped_mdb' mdb_inv_preserve_fun_upd)
  apply (wp getCTE_wp setUntypedCapAsFull_ctes)+
  apply (clarsimp simp:cte_wp_at_ctes_of simp del:fun_upd_apply)
  apply (subgoal_tac "src \<noteq> 0")
   prefer 2
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (subgoal_tac "dest \<noteq> 0")
   prefer 2
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (rule conjI)
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (case_tac cte)
  apply (rename_tac s_cap s_node)
  apply (case_tac cteb)
  apply (rename_tac d_cap d_node)
  apply (simp add: nullPointer_def)
  apply (subgoal_tac "mdb_insert_der
    (modify_map (ctes_of s) src (cteCap_update (\<lambda>_. maskedAsFull s_cap cap)))
    src (maskedAsFull s_cap cap) s_node dest NullCap d_node cap")
   prefer 2
   apply unfold_locales[1]
          apply (clarsimp simp:modify_map_def valid_mdb_ctes_maskedAsFull)+
      apply (erule(2) valid_mdb_ctesE[OF valid_mdb_ctes_maskedAsFull])
      apply (clarsimp simp:modify_map_def)
     apply (erule(2) valid_mdb_ctesE[OF valid_mdb_ctes_maskedAsFull])
    apply simp
   apply (clarsimp simp:modify_map_def maskedAsFull_derived')
  apply (case_tac "isMDBParentOf (CTE (maskedAsFull s_cap cap) s_node) (CTE cap
                   (mdbFirstBadged_update (\<lambda>a. isCapRevocable cap (maskedAsFull s_cap cap))
                   (mdbRevocable_update (\<lambda>a. isCapRevocable  cap (maskedAsFull s_cap cap))
                   (mdbPrev_update (\<lambda>a. src) s_node))))")
   apply (subgoal_tac "mdb_insert_child
     (modify_map (ctes_of s) src (cteCap_update (\<lambda>_. maskedAsFull s_cap cap)))
     src (maskedAsFull s_cap cap) s_node dest NullCap d_node cap")
    prefer 2
    apply (simp add: mdb_insert_child_def mdb_insert_child_axioms_def)
    apply (drule mdb_insert_child.untyped_inc_n)
      apply (rule capAligned_maskedAsFull[OF valid_capAligned])
      apply (erule(1) ctes_of_valid_cap')
     apply (intro impI maskedAsFull_usable_empty)
      apply (clarsimp simp:is_derived'_def badge_derived'_def)
     apply simp
   apply (clarsimp simp: modify_map_apply untyped_inc_prev_update maskedAsFull_revokable
                         descendants_of_prev_update)
  apply (subgoal_tac "mdb_insert_sib
    (modify_map (ctes_of s) src (cteCap_update (\<lambda>_. maskedAsFull s_cap cap)))
    src (maskedAsFull s_cap cap) s_node dest NullCap d_node cap")
   prefer 2
   apply (simp add: mdb_insert_sib_def mdb_insert_sib_axioms_def)
  apply (drule mdb_insert_sib.untyped_inc_n)
   apply (rule capAligned_master[OF valid_capAligned])
   apply (erule(1) ctes_of_valid_cap')
    apply (clarsimp simp:is_derived'_def badge_derived'_def)
  apply (clarsimp simp: modify_map_apply untyped_inc_prev_update maskedAsFull_revokable
                        descendants_of_prev_update)
  done

lemma irq_control_prev_update:
  "irq_control (modify_map m x (cteMDBNode_update (mdbPrev_update f))) = irq_control m"
  apply (simp add: irq_control_def)
  apply (rule iffI)
   apply clarsimp
   apply (simp only: modify_map_if)
   apply (erule_tac x=p in allE)
   apply (simp (no_asm_use) split: if_split_asm)
   apply (case_tac "x=p")
    apply fastforce
   apply clarsimp
   apply (erule_tac x=p' in allE)
   apply simp
   apply (case_tac "x=p'")
    apply simp
   apply fastforce
  apply clarsimp
  apply (erule_tac x=p in allE)
  apply (simp add: modify_map_if split: if_split_asm)
   apply clarsimp
   apply (case_tac "x=p'")
    apply clarsimp
   apply clarsimp
  apply clarsimp
  apply (case_tac "x=p'")
   apply clarsimp
  apply clarsimp
  done

lemma cteInsert_irq_control:
  "\<lbrace>valid_mdb' and pspace_distinct' and pspace_aligned' and (\<lambda>s. src \<noteq> dest) and
    (\<lambda>s. cte_wp_at' (is_derived' (ctes_of s) src cap \<circ> cteCap) src s)\<rbrace>
  cteInsert cap src dest
  \<lbrace>\<lambda>_ s. irq_control (ctes_of s)\<rbrace>"
  apply (unfold cteInsert_def updateCap_def)
  apply (simp add: valid_mdb'_def split del: if_split)
  apply (wp updateMDB_ctes_of_no_0 getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of simp del: fun_upd_apply)
  apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift setUntypedCapAsFull_ctes_of
    setUntypedCapAsFull_ctes_of_no_0 setUntypedCapAsFull_irq_control mdb_inv_preserve_fun_upd
    mdb_inv_preserve_modify_map,simp)
  apply (wp getCTE_wp)+
  apply (clarsimp simp:cte_wp_at_ctes_of simp del:fun_upd_apply)
  apply (subgoal_tac "src \<noteq> 0")
   prefer 2
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (subgoal_tac "dest \<noteq> 0")
   prefer 2
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (rule conjI)
   apply (fastforce simp: valid_mdb_ctes_def no_0_def)
  apply (case_tac cte)
  apply (rename_tac s_cap s_node)
  apply (case_tac cteb)
  apply (rename_tac d_cap d_node)
  apply (simp add: nullPointer_def)
  apply (subgoal_tac "mdb_insert_der (ctes_of s) src s_cap s_node dest NullCap d_node cap")
   prefer 2
   apply unfold_locales[1]
            apply (assumption|rule refl)+
      apply (simp add: valid_mdb_ctes_def)
     apply (simp add: valid_mdb_ctes_def)
    apply assumption+
  apply (drule mdb_insert_der.irq_control_n)
  apply (clarsimp simp: modify_map_apply irq_control_prev_update fun_upd_def)
  done

lemma capMaster_isUntyped:
  "capMasterCap c = capMasterCap c' \<Longrightarrow> isUntypedCap c = isUntypedCap c'"
  by (simp add: capMasterCap_def isCap_simps split: capability.splits)

lemma capMaster_capRange:
  "capMasterCap c = capMasterCap c' \<Longrightarrow> capRange c = capRange c'"
  by (simp add: capMasterCap_def arch_capMasterCap_def capRange_def
           split: capability.splits arch_capability.splits)

lemma capMaster_untypedRange:
  "capMasterCap c = capMasterCap c' \<Longrightarrow> untypedRange c = untypedRange c'"
  by (simp add: capMasterCap_def capRange_def split: capability.splits arch_capability.splits)

lemma capMaster_capClass:
  "capMasterCap c = capMasterCap c' \<Longrightarrow> capClass c = capClass c'"
  by (simp add: capMasterCap_def arch_capMasterCap_def capRange_def
           split: capability.splits arch_capability.splits)

lemma distinct_zombies_nonCTE_modify_map:
  "\<And>m x f. \<lbrakk> \<And>cte. cteCap (f cte) = cteCap cte \<rbrakk>
     \<Longrightarrow> distinct_zombies (modify_map m x f) = distinct_zombies m"
  apply (simp add: distinct_zombies_def modify_map_def o_def)
  apply (rule_tac f=distinct_zombie_caps in arg_cong)
  apply (rule ext)
  apply simp
  apply (simp add: map_option.compositionality o_def)
  done

lemma updateCapFreeIndex_dlist:
  assumes preserve:"\<And>m m'. mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
 "\<lbrace>\<lambda>s. P (valid_dlist (Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE \<and> isUntypedCap (cteCap c)) src s\<rbrace>
  updateCap src (capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE))
 \<lbrace>\<lambda>r s. P (valid_dlist (Q (ctes_of s)))\<rbrace>"
  apply (wp updateCap_ctes_of_wp)
  apply (subgoal_tac "mdb_inv_preserve (Q (ctes_of s)) (Q (modify_map (ctes_of s) src
              (cteCap_update (\<lambda>_. capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE)))))")
    apply (drule mdb_inv_preserve.preserve_stuff)
    apply simp
  apply (rule preserve)
  apply (rule mdb_inv_preserve_updateCap)
    apply (clarsimp simp:cte_wp_at_ctes_of)+
done

lemma setUntypedCapAsFull_valid_dlist:
  assumes preserve:
  "\<And>m m'. mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
  "\<lbrace>\<lambda>s. P (valid_dlist (Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE) src s\<rbrace>
   setUntypedCapAsFull (cteCap srcCTE) cap src
   \<lbrace>\<lambda>r s. P (valid_dlist (Q (ctes_of s)))\<rbrace>"
  apply (clarsimp simp:setUntypedCapAsFull_def split:if_splits,intro conjI impI)
   apply (wp updateCapFreeIndex_dlist)
   apply (clarsimp simp:preserve cte_wp_at_ctes_of)+
  apply wp
  apply clarsimp
  done

lemma valid_dlist_prevD:
  "\<lbrakk>m p = Some cte;valid_dlist m;mdbPrev (cteMDBNode cte) \<noteq> 0\<rbrakk>
   \<Longrightarrow> (\<exists>cte'. m (mdbPrev (cteMDBNode cte)) = Some cte' \<and>
               mdbNext (cteMDBNode cte') = p)"
  by (clarsimp simp:valid_dlist_def Let_def)

lemma valid_dlist_nextD:
  "\<lbrakk>m p = Some cte;valid_dlist m;mdbNext (cteMDBNode cte) \<noteq> 0\<rbrakk>
   \<Longrightarrow> (\<exists>cte'. m (mdbNext (cteMDBNode cte)) = Some cte' \<and>
               mdbPrev (cteMDBNode cte') = p)"
  by (clarsimp simp:valid_dlist_def Let_def)

lemma no_loops_no_l2_loop:
  "\<lbrakk>valid_dlist m; no_loops m; m p = Some cte;mdbPrev (cteMDBNode cte) = mdbNext (cteMDBNode cte)\<rbrakk>
       \<Longrightarrow> mdbNext (cteMDBNode cte) = 0"
  apply (rule ccontr)
  apply (subgoal_tac "m \<turnstile> p \<leadsto> (mdbNext (cteMDBNode cte))")
   prefer 2
   apply (clarsimp simp:mdb_next_rel_def mdb_next_def)
  apply (subgoal_tac "m \<turnstile> (mdbNext (cteMDBNode cte)) \<leadsto> p")
   prefer 2
   apply (clarsimp simp:mdb_next_rel_def mdb_next_def)
   apply (frule(2) valid_dlist_nextD)
   apply clarsimp
   apply (frule(1) valid_dlist_prevD)
   apply simp+
  apply (drule(1) transitive_closure_trans)
  apply (simp add:no_loops_def)
  done

lemma cteInsert_no_0:
  "\<lbrace>valid_mdb' and pspace_aligned' and pspace_distinct' and
    (\<lambda>s. src \<noteq> dest) and K (capAligned cap) and valid_objs' and
    (\<lambda>s. cte_wp_at' (is_derived' (ctes_of s) src cap \<circ> cteCap) src s)\<rbrace>
   cteInsert cap src dest
   \<lbrace>\<lambda>_ s. no_0 (ctes_of s) \<rbrace>"
  apply (rule hoare_name_pre_state)
  apply clarsimp
  apply (unfold cteInsert_def updateCap_def)
  apply (simp add: valid_mdb'_def split del: if_split)
  apply (wp updateMDB_ctes_of_no_0 getCTE_wp')
      apply (clarsimp simp: cte_wp_at_ctes_of simp del: fun_upd_apply)
      apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift setUntypedCapAsFull_ctes_of
        setUntypedCapAsFull_ctes_of_no_0 mdb_inv_preserve_modify_map getCTE_wp
        setUntypedCapAsFull_valid_dlist mdb_inv_preserve_fun_upd | simp)+
  apply (intro conjI impI)
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (clarsimp simp:valid_mdb_ctes_def no_0_def)
  done

lemma cteInsert_valid_dlist:
  "\<lbrace>valid_mdb' and pspace_aligned' and pspace_distinct' and
    (\<lambda>s. src \<noteq> dest) and K (capAligned cap) and valid_objs' and
    (\<lambda>s. cte_wp_at' (is_derived' (ctes_of s) src cap \<circ> cteCap) src s)\<rbrace>
   cteInsert cap src dest
   \<lbrace>\<lambda>_ s. valid_dlist (ctes_of s) \<rbrace>"
  apply (rule hoare_name_pre_state)
  apply clarsimp
  apply (unfold cteInsert_def updateCap_def)
  apply (simp add: valid_mdb'_def split del: if_split)
  apply (wp updateMDB_ctes_of_no_0 getCTE_wp')
      apply (clarsimp simp: cte_wp_at_ctes_of simp del: fun_upd_apply)
      apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift setUntypedCapAsFull_ctes_of
        setUntypedCapAsFull_ctes_of_no_0 mdb_inv_preserve_modify_map getCTE_wp
        setUntypedCapAsFull_valid_dlist mdb_inv_preserve_fun_upd | simp)+
  apply (intro conjI impI)
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (intro conjI)
   apply (clarsimp simp:valid_mdb_ctes_def no_0_def)+
  apply (frule mdb_chain_0_no_loops)
   apply (simp add:no_0_def)
  apply (rule valid_dlistI)
   apply (case_tac "p = dest")
    apply (clarsimp simp:modify_map_def nullPointer_def split:if_split_asm)+
   apply (frule(2) valid_dlist_prevD)
    apply simp
    apply (subgoal_tac "mdbPrev (cteMDBNode ctea) \<noteq> mdbNext (cteMDBNode ctea)")
    prefer 2
     apply (clarsimp)
     apply (drule(3) no_loops_no_l2_loop[rotated -1],simp)
    apply (subgoal_tac "mdbPrev (cteMDBNode ctea) \<noteq> dest")
    apply clarsimp+
   apply (frule_tac p = p and m = "ctes_of sa" in valid_dlist_prevD)
    apply simp+
   apply fastforce
  apply (case_tac "p = dest")
   apply (clarsimp simp:modify_map_def nullPointer_def split:if_split_asm)+
   apply (frule(2) valid_dlist_nextD,clarsimp)
  apply (clarsimp simp:modify_map_def nullPointer_def split:if_split_asm)
   apply (frule(2) valid_dlist_nextD)
    apply simp
    apply (subgoal_tac "mdbPrev (cteMDBNode ctea) \<noteq> mdbNext (cteMDBNode ctea)")
    prefer 2
     apply (clarsimp)
     apply (drule(3) no_loops_no_l2_loop[rotated -1],simp)
     apply clarsimp
     apply (intro conjI impI)
      apply clarsimp+
     apply (drule_tac cte = cte' in no_loops_no_l2_loop,simp)
      apply simp+
   apply (frule(2) valid_dlist_nextD)
    apply clarsimp
   apply (frule_tac p = p and m = "ctes_of sa" in valid_dlist_nextD)
    apply clarsimp+
   apply (rule conjI)
    apply fastforce
   apply (intro conjI impI,clarsimp+)
   apply (frule_tac valid_dlist_nextD)
    apply clarsimp+
  apply (frule_tac valid_dlist_nextD)
  apply clarsimp+
  done

lemma valid_arch_badges_mdbPrev_update[simp]:
  "valid_arch_badges cap cap' (mdbPrev_update f node) = valid_arch_badges cap cap' node"
  by (simp add: valid_arch_badges_def)

lemma valid_arch_badges_master_eq:
  "capMasterCap src_cap = capMasterCap cap \<Longrightarrow>
   valid_arch_badges src_cap cap' node = valid_arch_badges cap cap' node"
  by (auto simp: valid_arch_badges_def isCap_simps)

lemmas valid_arch_badges_master = valid_arch_badges_master_eq[THEN iffD1]

lemma valid_arch_badges_firstBadged:
  "\<lbrakk> valid_arch_badges cap cap' node; mdbFirstBadged node = mdbFirstBadged node' \<rbrakk> \<Longrightarrow>
   valid_arch_badges cap cap' node'"
  by (simp add: valid_arch_badges_def)

lemma cteInsert_mdb' [wp]:
  "\<lbrace>valid_mdb' and pspace_aligned' and pspace_distinct' and (\<lambda>s. src \<noteq> dest) and K (capAligned cap) and valid_objs' and
   (\<lambda>s. cte_wp_at' (is_derived' (ctes_of s) src cap \<circ> cteCap) src s) \<rbrace>
  cteInsert cap src dest
  \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  apply (simp add:valid_mdb'_def valid_mdb_ctes_def)
  apply (rule_tac Q'="\<lambda>r s. valid_dlist (ctes_of s) \<and> irq_control (ctes_of s) \<and>
               no_0 (ctes_of s) \<and> mdb_chain_0 (ctes_of s) \<and>
               mdb_chunked (ctes_of s) \<and> untyped_mdb' (ctes_of s) \<and> untyped_inc' (ctes_of s) \<and>
               Q s" for Q
     in hoare_strengthen_post)
   prefer 2
   apply clarsimp
   apply assumption
  apply (rule hoare_name_pre_state)
  apply (wp cteInsert_no_0 cteInsert_valid_dlist cteInsert_mdb_chain_0 cteInsert_untyped_inc'
            cteInsert_mdb_chunked cteInsert_untyped_mdb cteInsert_irq_control)
  apply (unfold cteInsert_def)
  apply (unfold cteInsert_def updateCap_def)
  apply (simp add: valid_mdb'_def split del: if_split)
  apply (wp updateMDB_ctes_of_no_0 getCTE_wp')
      apply (clarsimp simp: cte_wp_at_ctes_of simp del: fun_upd_apply)
      apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift setUntypedCapAsFull_ctes_of
        setUntypedCapAsFull_ctes_of_no_0
        setUntypedCapAsFull_valid_dlist setUntypedCapAsFull_distinct_zombies
        setUntypedCapAsFull_valid_badges setUntypedCapAsFull_caps_contained
        setUntypedCapAsFull_valid_nullcaps setUntypedCapAsFull_ut_revocable
        setUntypedCapAsFull_class_links setUntypedCapAsFull_reply_masters_rvk_fb
        mdb_inv_preserve_fun_upd
        mdb_inv_preserve_modify_map getCTE_wp| simp del:fun_upd_apply)+
  apply (clarsimp simp:cte_wp_at_ctes_of simp del:fun_upd_apply)
  defer
  apply (clarsimp simp:valid_mdb_ctes_def valid_mdb'_def simp del:fun_upd_apply)+
  apply (case_tac cte)
  apply (rename_tac cap1 node1)
  apply (case_tac x)
  apply (rename_tac cap2 node2)
  apply (case_tac node1)
  apply (case_tac node2)
  apply (clarsimp simp:valid_mdb_ctes_def no_0_def nullPointer_def)
  apply (intro conjI impI)
  apply clarsimp
  apply (rename_tac s src_cap word1 word2 bool1a bool2a bool1 bool2)
proof -
  fix s :: kernel_state
  fix bool1 bool2 src_cap word1 word2 bool1a bool2a
  let ?c1 = "(CTE src_cap (MDB word1 word2 bool1a bool2a))"
  let ?c2 = "(CTE capability.NullCap (MDB 0 0 bool1 bool2))"
  let ?C = "(modify_map
             (modify_map
               (modify_map ((ctes_of s)(dest \<mapsto> CTE cap (MDB 0 0 bool1 bool2))) dest
                 (cteMDBNode_update (\<lambda>a. MDB word1 src (isCapRevocable cap src_cap) (isCapRevocable cap src_cap))))
               src (cteMDBNode_update (mdbNext_update (\<lambda>_. dest))))
             word1 (cteMDBNode_update (mdbPrev_update (\<lambda>_. dest))))"
  let ?m = "ctes_of s"
  let ?prv = "\<lambda>cte. mdbPrev (cteMDBNode cte)"
  let ?nxt = "\<lambda>cte. mdbNext (cteMDBNode cte)"

  assume "pspace_distinct' s" and "pspace_aligned' s" and srcdest: "src \<noteq> dest"
     and dest0: "dest \<noteq> 0"
     and cofs: "ctes_of s src = Some ?c1" and cofd: "ctes_of s dest = Some ?c2"
     and is_der: "is_derived' (ctes_of s) src cap src_cap"
     and aligned: "capAligned cap"
     and vd: "valid_dlist ?m"
     and no0: "?m 0 = None"
     and chain: "mdb_chain_0 ?m"
     and badges: "valid_badges ?m"
     and chunk: "mdb_chunked ?m"
     and contained: "caps_contained' ?m"
     and untyped_mdb: "untyped_mdb' ?m"
     and untyped_inc: "untyped_inc' ?m"
     and class_links: "class_links ?m"
     and distinct_zombies: "distinct_zombies ?m"
     and irq: "irq_control ?m"
     and reply_masters_rvk_fb: "reply_masters_rvk_fb ?m"
     and vn: "valid_nullcaps ?m"
     and ut_rev:"ut_revocable' ?m"

  have no_loop: "no_loops ?m"
     apply (rule mdb_chain_0_no_loops[OF chain])
     apply (simp add:no_0_def no0)
     done

  have badge: "badge_derived' cap src_cap"
     using is_der
     by (clarsimp simp:is_derived'_def)

  have vmdb: "valid_mdb_ctes ?m"
    by (auto simp: vmdb_def valid_mdb_ctes_def no_0_def, fact+)

  have src0: "src \<noteq> 0"
    using cofs no0 by clarsimp

  have destnull:
    "cte_mdb_prop ?m dest (\<lambda>m. mdbPrev m = 0 \<and> mdbNext m = 0)"
    using cofd unfolding cte_mdb_prop_def
    by auto

  have srcwd: "?m \<turnstile> src \<leadsto> word1"
    using cofs by (simp add: next_unfold')

  have w1ned[simp]: "word1 \<noteq> dest"
  proof (cases "word1 = 0")
    case True thus ?thesis using dest0 by auto
  next
    case False
    thus ?thesis using cofs cofd src0 dest0 False vd
      by - (erule (1) valid_dlistEn, (clarsimp simp: nullPointer_def)+)
  qed

  have w2ned[simp]: "word2 \<noteq> dest"
  proof (cases "word2 = 0")
    case True thus ?thesis using dest0 by auto
  next
    case False
    thus ?thesis using cofs cofd src0 dest0 False vd
      by - (erule (1) valid_dlistEp, (clarsimp simp: nullPointer_def)+)
  qed

  have w1nes[simp]: "word1 \<noteq> src" using vmdb cofs
    by - (drule (1) no_self_loop_next, simp)

  have w2nes[simp]: "word2 \<noteq> src" using vmdb cofs
    by - (drule (1) no_self_loop_prev, simp)

  from is_der have notZomb1: "\<not> isZombie cap"
    by (clarsimp simp: isCap_simps is_derived'_def badge_derived'_def)

  from is_der have notZomb2: "\<not> isZombie src_cap"
    by (clarsimp simp: isCap_simps is_derived'_def)

  from badge have masters: "capMasterCap cap = capMasterCap src_cap"
     by (clarsimp simp: badge_derived'_def)

  note blah[simp] = w2nes[symmetric] w1nes[symmetric] w1ned[symmetric]
    w2ned[symmetric] srcdest srcdest[symmetric]

  have mdb_next_disj:
   "\<And>p p'. (?C \<turnstile> p \<leadsto> p' \<Longrightarrow>
   ?m \<turnstile> p \<leadsto> p' \<and> p \<noteq> src \<and> p'\<noteq> dest \<and> (p' = word1 \<longrightarrow> p' = 0)
   \<or> p = src \<and> p' = dest \<or> p = dest \<and> p' = word1)"
   apply (case_tac "p = src")
   apply (clarsimp simp:mdb_next_unfold modify_map_cases)
   apply (case_tac "p = dest")
   apply (clarsimp simp:mdb_next_unfold modify_map_cases)+
   using cofs cofd vd no0
   apply -
   apply (case_tac "p = word1")
    apply clarsimp
    apply (intro conjI)
     apply clarsimp
     apply (frule_tac p = "word1" and m = "?m" in valid_dlist_nextD)
      apply clarsimp+
     apply (frule_tac p = "mdbNext node" and m = "?m" in valid_dlist_nextD)
      apply clarsimp+
    apply (frule_tac p = "mdbNext node" in no_loops_no_l2_loop[OF _ no_loop])
     apply simp+
  apply (intro conjI)
   apply clarsimp
    apply (frule_tac p = p and m = "?m" in valid_dlist_nextD)
     apply (clarsimp+)[3]
  apply (intro impI)
  apply (rule ccontr)
  apply clarsimp
    apply (frule_tac p = src and m = "?m" in valid_dlist_nextD)
  apply clarsimp+
    apply (frule_tac p = p and m = "?m" in valid_dlist_nextD)
  apply clarsimp+
  done

  have ctes_ofD:
   "\<And>p cte. \<lbrakk>?C p = Some cte; p\<noteq> dest; p\<noteq> src\<rbrakk> \<Longrightarrow> \<exists>cteb. (?m p = Some cteb \<and> cteCap cte = cteCap cteb)"
   by (clarsimp simp:modify_map_def split:if_splits)


  show "valid_badges ?C"
  using srcdest badge cofs badges cofd
  unfolding valid_badges_def valid_arch_badges_def (* FIXME: arch-split, use AARCH64 version *)
  apply (intro impI allI)
  apply (drule mdb_next_disj)
  apply (elim disjE)
    defer
    apply (clarsimp simp:modify_map_cases dest0 src0)
    apply (clarsimp simp: Retype_H.isCapRevocable_def isCapRevocable_def badge_derived'_def)
    subgoal by (case_tac src_cap,auto simp:isCap_simps sameRegionAs_def)
  apply (clarsimp simp:modify_map_cases valid_badges_def)
    apply (frule_tac x=src in spec, erule_tac x=word1 in allE, erule allE, erule impE)
    apply fastforce
    apply simp
    apply (clarsimp simp:mdb_next_unfold badge_derived'_def split: if_split_asm)
    apply (thin_tac "All P" for P)
    subgoal by (cases src_cap,
       auto simp:mdb_next_unfold isCap_simps sameRegionAs_def Let_def split: if_splits)
  apply (case_tac "word1 = p'")
     apply (clarsimp simp:modify_map_cases valid_badges_def mdb_next_unfold src0 dest0 no0)+
  apply (case_tac "p = dest")
   apply (clarsimp simp:dest0 src0 no0)+
  apply (case_tac z)
  apply (rename_tac capability mdbnode)
  apply clarsimp
  apply (drule_tac x = p in spec,drule_tac x = "mdbNext mdbnode" in spec)
  by (auto simp:isCap_simps sameRegionAs_def)

  from badge
  have isUntyped_eq: "isUntypedCap cap = isUntypedCap src_cap"
   apply (clarsimp simp:badge_derived'_def)
   apply (case_tac cap,auto simp:isCap_simps)
   done

  from badge
  have [simp]: "capRange cap = capRange src_cap"
   apply (clarsimp simp:badge_derived'_def)
   apply (case_tac cap)
     apply (clarsimp simp:isCap_simps capRange_def)+
    (* 5 subgoals *)
    apply (rename_tac arch_capability)
    apply (case_tac arch_capability)
     (* 9 subgoals *)
     apply (clarsimp simp:isCap_simps capRange_def)+
   done

  have [simp]: "untypedRange cap = untypedRange src_cap"
     using badge
     apply (clarsimp simp:badge_derived'_def dest!:capMaster_untypedRange)
     done

  from contained badge srcdest cofs cofd is_der no0
  show "caps_contained' ?C"
  apply (clarsimp simp add: caps_contained'_def)
  apply (case_tac "p = dest")
   apply (case_tac "p' = dest")
    apply (clarsimp simp:modify_map_def split:if_splits)
    apply (case_tac src_cap,auto)[1]
   apply (case_tac "p' = src")
    apply (clarsimp simp:modify_map_def split:if_splits)
    apply (clarsimp simp:badge_derived'_def)
    apply (case_tac src_cap,auto)[1]
   apply (drule(2) ctes_ofD)
   apply (clarsimp simp:modify_map_def split:if_splits)
   apply (frule capRange_untyped)
   apply (erule_tac x=src in allE, erule_tac x=p' in allE, simp)
    apply (case_tac cteb)
    apply (clarsimp)
    apply blast
   apply (case_tac "p' = dest")
    apply (case_tac "p = src")
     apply (clarsimp simp:modify_map_def split:if_splits)
     apply (drule capRange_untyped)
     subgoal by (case_tac cap,auto simp:isCap_simps badge_derived'_def)
    apply (clarsimp simp:modify_map_def split:if_splits)
    apply (drule_tac x = word1 in spec)
    apply (drule_tac x = src in spec)
    apply (case_tac z)
    apply (clarsimp simp:isUntyped_eq)
    apply blast
    apply (drule_tac x = p in spec)
    apply (drule_tac x = src in spec)
    apply (frule capRange_untyped)
    apply (clarsimp simp:isUntyped_eq)
    apply blast
   apply (drule_tac x = p in spec)
   apply (drule_tac x = p' in spec)
   apply (clarsimp simp:modify_map_def split:if_splits)
    apply ((case_tac z,fastforce)+)[5]
   by fastforce+

  show "valid_nullcaps ?C"
  using is_der vn cofs vd no0
  apply (simp add: valid_nullcaps_def srcdest [symmetric])
  apply (clarsimp simp:modify_map_def is_derived'_def)
  apply (rule conjI)
    apply (clarsimp simp: is_derived'_def badge_derived'_def)+
  apply (drule_tac x = word1 in spec)
  apply (case_tac z)
  apply (clarsimp simp:nullMDBNode_def)
  apply (drule(1) valid_dlist_nextD)
    apply simp
   apply clarsimp
  apply (simp add:nullPointer_def src0)
  done

  from vmdb srcdest cofs ut_rev
  show "ut_revocable' ?C"
  apply (clarsimp simp: valid_mdb_ctes_def ut_revocable'_def modify_map_def)
  apply (rule conjI)
   apply clarsimp
   apply (clarsimp simp: Retype_H.isCapRevocable_def isCapRevocable_def isCap_simps)+
   apply auto
  apply (drule_tac x= src in spec)
   apply clarsimp
  apply (case_tac z)
   apply clarsimp
  done

  from class_links srcdest badge cofs cofd no0 vd
  show "class_links ?C"
  unfolding class_links_def
  apply (intro allI impI)
  apply (drule mdb_next_disj)
  apply (elim disjE)
    apply (clarsimp simp:modify_map_def mdb_next_unfold split:if_split_asm)
   apply (clarsimp simp: badge_derived'_def modify_map_def
    split: if_split_asm)
   apply (erule capMaster_capClass)
  apply (clarsimp simp:modify_map_def split:if_splits)
  apply (drule_tac x = src in spec)
  apply (drule_tac x = word1 in spec)
  apply (clarsimp simp:mdb_next_unfold)
  apply (case_tac z)
   apply (clarsimp simp:badge_derived'_def)
  apply (drule capMaster_capClass)
  apply simp
  done

 from distinct_zombies badge
 show "distinct_zombies ?C"
 apply (simp add:distinct_zombies_nonCTE_modify_map)
 apply (erule_tac distinct_zombies_copyMasterE[where x=src])
   apply (rule cofs)
  apply (simp add: masters)
 apply (simp add: notZomb1 notZomb2)
 done

 from reply_masters_rvk_fb is_der
 show "reply_masters_rvk_fb ?C"
   apply (clarsimp simp:reply_masters_rvk_fb_def)
   apply (erule ranE)
   apply (clarsimp simp:modify_map_def split:if_split_asm)
    apply fastforce+
   apply (clarsimp simp:is_derived'_def isCap_simps)
   apply fastforce
 done
qed

crunch cteInsert
  for state_refs_of'[wp]: "\<lambda>s. P (state_refs_of' s)"
  (wp: crunch_wps)

crunch cteInsert
  for aligned'[wp]: pspace_aligned'
  (wp: crunch_wps)

crunch cteInsert
  for pspace_canonical'[wp]: pspace_canonical'
  (wp: crunch_wps)

crunch cteInsert
  for pspace_in_kernel_mappings'[wp]: pspace_in_kernel_mappings'
  (wp: crunch_wps)

crunch cteInsert
  for distinct'[wp]: pspace_distinct'
  (wp: crunch_wps)

crunch cteInsert
  for no_0_obj'[wp]: no_0_obj'
  (wp: crunch_wps)

lemma cteInsert_valid_pspace:
  "\<lbrace>valid_pspace' and valid_cap' cap and (\<lambda>s. src \<noteq> dest) and valid_objs' and
    (\<lambda>s. cte_wp_at' (is_derived' (ctes_of s) src cap \<circ> cteCap) src s)\<rbrace>
  cteInsert cap src dest
  \<lbrace>\<lambda>_. valid_pspace'\<rbrace>"
  unfolding valid_pspace'_def
  apply (rule hoare_pre)
  apply (wp cteInsert_valid_objs)
  apply (fastforce elim: valid_capAligned)
  done

lemma setCTE_ko_wp_at_live[wp]:
  "\<lbrace>\<lambda>s. P (ko_wp_at' live' p' s)\<rbrace>
    setCTE p v
   \<lbrace>\<lambda>rv s. P (ko_wp_at' live' p' s)\<rbrace>"
  apply (clarsimp simp: setCTE_def setObject_def split_def
                        valid_def in_monad ko_wp_at'_def
             split del: if_split
                 elim!: rsubst[where P=P])
  apply (drule(1) updateObject_cte_is_tcb_or_cte [OF _ refl, rotated])
  apply (elim exE conjE disjE)
   apply (clarsimp simp: ps_clear_upd objBits_simps live'_def hyp_live'_def
                         lookupAround2_char1)
   apply (simp add: tcb_cte_cases_def split: if_split_asm)
  apply (clarsimp simp: ps_clear_upd objBits_simps live'_def)
  done

lemma setCTE_iflive':
  "\<lbrace>\<lambda>s. cte_wp_at' (\<lambda>cte'. \<forall>p'\<in>zobj_refs' (cteCap cte')
                          - zobj_refs' (cteCap cte).
                                ko_wp_at' (Not \<circ> live') p' s) p s
      \<and> if_live_then_nonz_cap' s\<rbrace>
     setCTE p cte
   \<lbrace>\<lambda>rv s. if_live_then_nonz_cap' s\<rbrace>"
  unfolding if_live_then_nonz_cap'_def ex_nonz_cap_to'_def
  apply (rule hoare_pre)
   apply (simp only: imp_conv_disj)
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift
             hoare_vcg_ex_lift setCTE_weak_cte_wp_at)
  apply clarsimp
  apply (drule spec, drule(1) mp)
  apply clarsimp
  apply (rule_tac x=cref in exI)
  apply (clarsimp simp: cte_wp_at'_def)
  apply (rule ccontr)
  apply (drule bspec, fastforce)
  apply (clarsimp simp: ko_wp_at'_def)
  done

lemma updateMDB_iflive'[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s\<rbrace>
     updateMDB p m
   \<lbrace>\<lambda>rv s. if_live_then_nonz_cap' s\<rbrace>"
  apply (clarsimp simp: updateMDB_def)
  apply (rule bind_wp [OF _ getCTE_sp])
  apply (wp setCTE_iflive')
  apply (clarsimp elim!: cte_wp_at_weakenE')
  done

lemma updateCap_iflive':
  "\<lbrace>\<lambda>s. cte_wp_at' (\<lambda>cte'. \<forall>p'\<in>zobj_refs' (cteCap cte')
                          - zobj_refs' cap.
                                ko_wp_at' (Not \<circ> live') p' s) p s
      \<and> if_live_then_nonz_cap' s\<rbrace>
     updateCap p cap
   \<lbrace>\<lambda>rv s. if_live_then_nonz_cap' s\<rbrace>"
  apply (simp add: updateCap_def)
  apply (rule bind_wp [OF _ getCTE_sp])
  apply (wp setCTE_iflive')
  apply (clarsimp elim!: cte_wp_at_weakenE')
  done

lemma setCTE_ko_wp_at_not_live[wp]:
  "\<lbrace>\<lambda>s. P (ko_wp_at' (Not \<circ> live') p' s)\<rbrace>
    setCTE p v
   \<lbrace>\<lambda>rv s. P (ko_wp_at' (Not \<circ> live') p' s)\<rbrace>"
  apply (clarsimp simp: setCTE_def setObject_def split_def
                        valid_def in_monad ko_wp_at'_def
             split del: if_split
                 elim!: rsubst[where P=P])
  apply (drule(1) updateObject_cte_is_tcb_or_cte [OF _ refl, rotated])
  apply (elim exE conjE disjE)
   apply (clarsimp simp: ps_clear_upd objBits_simps live'_def hyp_live'_def
                         lookupAround2_char1)
   apply (simp add: tcb_cte_cases_def split: if_split_asm)
  apply (clarsimp simp: ps_clear_upd objBits_simps live'_def)
  done

lemma setUntypedCapAsFull_ko_wp_not_at'[wp]:
  "\<lbrace>\<lambda>s. P (ko_wp_at' (Not \<circ> live') p' s)\<rbrace>
   setUntypedCapAsFull (cteCap srcCTE) cap src
   \<lbrace>\<lambda>r s. P ( ko_wp_at' (Not \<circ> live') p' s)\<rbrace>"
  apply (clarsimp simp:setUntypedCapAsFull_def updateCap_def)
  apply (wp setCTE_ko_wp_at_live setCTE_ko_wp_at_not_live)
done

lemma setUntypedCapAsFull_ko_wp_at'[wp]:
  "\<lbrace>\<lambda>s. P (ko_wp_at' live' p' s)\<rbrace>
   setUntypedCapAsFull (cteCap srcCTE) cap src
   \<lbrace>\<lambda>r s. P ( ko_wp_at' live' p' s)\<rbrace>"
  apply (clarsimp simp:setUntypedCapAsFull_def updateCap_def)
  apply (wp setCTE_ko_wp_at_live setCTE_ko_wp_at_live)
  done

(*FIXME:MOVE*)
lemma zobj_refs'_capFreeIndex_update[simp]:
  "isUntypedCap ctecap \<Longrightarrow>
   zobj_refs' (capFreeIndex_update f (ctecap)) = zobj_refs' ctecap"
  by (case_tac ctecap,auto simp:isCap_simps)

lemma setUntypedCapAsFull_if_live_then_nonz_cap':
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s \<and> cte_wp_at' ((=) srcCTE) src s\<rbrace>
   setUntypedCapAsFull (cteCap srcCTE) cap src
   \<lbrace>\<lambda>rv s. if_live_then_nonz_cap' s\<rbrace>"
  apply (clarsimp simp:if_live_then_nonz_cap'_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift)
   apply (clarsimp simp:setUntypedCapAsFull_def split del: if_split)
   apply (wp hoare_vcg_if_split)
    apply (clarsimp simp:ex_nonz_cap_to'_def cte_wp_at_ctes_of)
    apply (wp updateCap_ctes_of_wp)+
  apply clarsimp
  apply (elim allE impE)
   apply (assumption)
  apply (clarsimp simp:ex_nonz_cap_to'_def cte_wp_at_ctes_of modify_map_def split:if_splits)
  apply (rule_tac x = cref in exI)
  apply (intro conjI impI; clarsimp)
  done


lemma maskedAsFull_simps[simp]:
  "maskedAsFull capability.NullCap cap =  capability.NullCap"
  by (auto simp:maskedAsFull_def)

lemma cteInsert_iflive'[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap' s
      \<and> cte_wp_at' (\<lambda>c. cteCap c = NullCap) dest s\<rbrace>
     cteInsert cap src dest
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: cteInsert_def split del: if_split)
  apply (wp updateCap_iflive' hoare_drop_imps)
       apply (clarsimp simp:cte_wp_at_ctes_of)
       apply (wp hoare_vcg_conj_lift hoare_vcg_ex_lift hoare_vcg_ball_lift getCTE_wp
                 setUntypedCapAsFull_ctes_of setUntypedCapAsFull_if_live_then_nonz_cap')+
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (intro conjI)
  apply (rule_tac x = "case (ctes_of s dest) of Some a \<Rightarrow>a" in exI)
    apply (clarsimp)
    apply (case_tac cte,simp)
  apply clarsimp+
  done

lemma ifunsafe'_def2:
  "if_unsafe_then_cap' =
    (\<lambda>s. \<forall>cref cte. ctes_of s cref = Some cte \<and> cteCap cte \<noteq> NullCap
              \<longrightarrow> (\<exists>cref' cte'. ctes_of s cref' = Some cte'
                                  \<and> cref \<in> cte_refs' (cteCap cte') (irq_node' s)))"
  by (clarsimp intro!: ext
                 simp: if_unsafe_then_cap'_def cte_wp_at_ctes_of
                       ex_cte_cap_to'_def)

lemma ifunsafe'_def3:
  "if_unsafe_then_cap' =
    (\<lambda>s. \<forall>cref cap. cteCaps_of s cref = Some cap \<and> cap \<noteq> NullCap
              \<longrightarrow> (\<exists>cref' cap'. cteCaps_of s cref' = Some cap'
                          \<and> cref \<in> cte_refs' cap' (irq_node' s)))"
  apply (simp add: cteCaps_of_def o_def ifunsafe'_def2)
  apply (fastforce intro!: ext)
  done

lemma tree_cte_cteCap_eq:
  "cte_wp_at' (P \<circ> cteCap) p s = (case_option False P (cteCaps_of s p))"
  apply (simp add: cte_wp_at_ctes_of cteCaps_of_def)
  apply (cases "ctes_of s p", simp_all)
  done

lemma updateMDB_cteCaps_of:
  "\<lbrace>\<lambda>s. P (cteCaps_of s)\<rbrace> updateMDB ptr f \<lbrace>\<lambda>rv s. P (cteCaps_of s)\<rbrace>"
  apply (simp add: cteCaps_of_def)
  apply (wp updateMDB_ctes_of_wp)
  apply (safe elim!: rsubst [where P=P] intro!: ext)
  apply (case_tac "ctes_of s x")
   apply (clarsimp simp: modify_map_def)+
  done

lemma setCTE_ksInterruptState[wp]:
  "\<lbrace>\<lambda>s. P (ksInterruptState s)\<rbrace> setCTE param_a param_b \<lbrace>\<lambda>_ s. P (ksInterruptState s)\<rbrace>"
  by (wp setObject_ksInterrupt updateObject_cte_inv | simp add: setCTE_def)+

crunch cteInsert
  for ksInterruptState[wp]: "\<lambda>s. P (ksInterruptState s)"
  (wp: crunch_wps)

lemmas updateMDB_cteCaps_of_ksInt[wp]
    = hoare_use_eq [where f=ksInterruptState, OF updateMDB_ksInterruptState updateMDB_cteCaps_of]

lemma updateCap_cteCaps_of:
  "\<lbrace>\<lambda>s. P (modify_map (cteCaps_of s) ptr (K cap))\<rbrace> updateCap ptr cap \<lbrace>\<lambda>rv s. P (cteCaps_of s)\<rbrace>"
  apply (simp add: cteCaps_of_def)
  apply (wp updateCap_ctes_of_wp)
  apply (erule rsubst [where P=P])
  apply (case_tac "ctes_of s ptr")
   apply (clarsimp intro!: ext simp: modify_map_def)+
  done

lemmas updateCap_cteCaps_of_int[wp]
    = hoare_use_eq[where f=ksInterruptState, OF updateCap_ksInterruptState updateCap_cteCaps_of]

lemma getCTE_cteCap_wp:
  "\<lbrace>\<lambda>s. case (cteCaps_of s ptr) of None \<Rightarrow> True | Some cap \<Rightarrow> Q cap s\<rbrace> getCTE ptr \<lbrace>\<lambda>rv. Q (cteCap rv)\<rbrace>"
  apply (wp getCTE_wp)
  apply (clarsimp simp: cteCaps_of_def cte_wp_at_ctes_of)
  done

lemma capFreeIndex_update_cte_refs'[simp]:
  "isUntypedCap a \<Longrightarrow> cte_refs' (capFreeIndex_update f a) = cte_refs' a "
  apply (rule ext)
  apply (clarsimp simp:isCap_simps)
  done

lemma cteInsert_ifunsafe'[wp]:
  "\<lbrace>if_unsafe_then_cap' and cte_wp_at' (\<lambda>c. cteCap c = NullCap) dest
        and ex_cte_cap_to' dest\<rbrace>
     cteInsert cap src dest
   \<lbrace>\<lambda>rv s. if_unsafe_then_cap' s\<rbrace>"
  apply (simp add: ifunsafe'_def3 cteInsert_def setUntypedCapAsFull_def
             split del: if_split)
  apply (wp getCTE_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of ex_cte_cap_to'_def
                        cteCaps_of_def
                 dest!: modify_map_K_D
                 split: if_split_asm)
  apply (intro conjI)
    apply clarsimp
    apply (erule_tac x = crefa in allE)
    apply (clarsimp simp:modify_map_def split:if_split_asm)
      apply (rule_tac x = cref in exI)
     apply fastforce
    apply (clarsimp simp:isCap_simps)
    apply (rule_tac x = cref' in exI)
     apply fastforce
  apply (intro conjI impI)
   apply clarsimp
   apply (rule_tac x = cref' in exI)
     apply fastforce
  apply (clarsimp simp:modify_map_def)
  apply (erule_tac x = crefa in allE)
  apply (intro conjI impI)
    apply clarsimp
    apply (rule_tac x = cref in exI)
     apply fastforce
    apply (clarsimp simp:isCap_simps)
    apply (rule_tac x = cref' in exI)
     apply fastforce
done

lemma setCTE_inQ[wp]:
  "\<lbrace>\<lambda>s. P (obj_at' (inQ d p) t s)\<rbrace> setCTE ptr v \<lbrace>\<lambda>rv s. P (obj_at' (inQ d p) t s)\<rbrace>"
  apply (simp add: setCTE_def)
  apply (rule setObject_cte_obj_at_tcb')
   apply (simp_all add: inQ_def)
  done

crunch cteInsert
  for inQ[wp]: "\<lambda>s. P (obj_at' (inQ d p) t s)"
  (wp: crunch_wps)

lemma setCTE_it'[wp]:
  "\<lbrace>\<lambda>s. P (ksIdleThread s)\<rbrace> setCTE c p \<lbrace>\<lambda>_ s. P (ksIdleThread s)\<rbrace>"
  apply (simp add: setCTE_def setObject_def split_def updateObject_cte)
  by (wpsimp+; auto)

lemma setCTE_idle [wp]:
  "\<lbrace>valid_idle'\<rbrace> setCTE p cte \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (simp add: valid_idle'_def)
  apply (rule hoare_lift_Pf [where f="ksIdleThread"])
   apply (intro hoare_vcg_conj_lift; (solves \<open>wpsimp\<close>)?)
   apply (clarsimp simp: setCTE_def)
   apply (rule setObject_cte_obj_at_tcb'[where P="idle_tcb'", simplified])
  apply wpsimp
  done

crunch getCTE
  for it[wp]: "\<lambda>s. P (ksIdleThread s)"

lemma getCTE_no_idle_cap:
  "\<lbrace>valid_global_refs'\<rbrace>
   getCTE p
   \<lbrace>\<lambda>rv s. ksIdleThread s \<notin> capRange (cteCap rv)\<rbrace>"
  apply (wp getCTE_wp)
  apply (clarsimp simp: valid_global_refs'_def valid_refs'_def cte_wp_at_ctes_of)
  apply blast
  done

lemma updateMDB_idle'[wp]:
 "\<lbrace>valid_idle'\<rbrace> updateMDB p m \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (clarsimp simp add: updateMDB_def)
  apply (rule hoare_pre)
  apply (wp | simp add: valid_idle'_def)+
  by fastforce

lemma updateCap_idle':
 "\<lbrace>valid_idle'\<rbrace> updateCap p c \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (simp add: updateCap_def)
  apply (wp | simp)+
  done

crunch setUntypedCapAsFull
  for idle[wp]: "valid_idle'"
  (wp: crunch_wps simp: cte_wp_at_ctes_of)

lemma cteInsert_idle'[wp]:
 "\<lbrace>valid_idle'\<rbrace> cteInsert cap src dest \<lbrace>\<lambda>rv. valid_idle'\<rbrace>"
  apply (simp add: cteInsert_def)
  apply (wp updateMDB_idle' updateCap_idle' | rule hoare_drop_imp | simp)+
  done

lemma setCTE_arch [wp]:
  "\<lbrace>\<lambda>s. P (ksArchState s)\<rbrace> setCTE p c \<lbrace>\<lambda>_ s. P (ksArchState s)\<rbrace>"
  apply (simp add: setCTE_def setObject_def split_def updateObject_cte)
  apply (wpsimp+; auto)
  done

lemma setCTE_valid_arch[wp]:
  "\<lbrace>valid_arch_state'\<rbrace> setCTE p c \<lbrace>\<lambda>_. valid_arch_state'\<rbrace>"
  by (wp valid_arch_state_lift' setCTE_typ_at')

lemma setCTE_global_refs[wp]:
  "\<lbrace>\<lambda>s. P (global_refs' s)\<rbrace> setCTE p c \<lbrace>\<lambda>_ s. P (global_refs' s)\<rbrace>"
  apply (simp add: setCTE_def setObject_def split_def updateObject_cte global_refs'_def)
  apply (wpsimp+; auto)
  done

lemma setCTE_gsMaxObjectSize[wp]:
  "\<lbrace>\<lambda>s. P (gsMaxObjectSize s)\<rbrace> setCTE p c \<lbrace>\<lambda>_ s. P (gsMaxObjectSize s)\<rbrace>"
  apply (simp add: setCTE_def setObject_def split_def updateObject_cte)
  apply (wpsimp+; auto)
  done

lemma setCTE_valid_globals[wp]:
  "\<lbrace>valid_global_refs' and (\<lambda>s. kernel_data_refs \<inter> capRange (cteCap c) = {})
      and (\<lambda>s. 2 ^ capBits (cteCap c) \<le> gsMaxObjectSize s)\<rbrace>
  setCTE p c
  \<lbrace>\<lambda>_. valid_global_refs'\<rbrace>"
  apply (simp add: valid_global_refs'_def valid_refs'_def pred_conj_def)
  apply (rule hoare_lift_Pf2 [where f=global_refs'])
   apply (rule hoare_lift_Pf2 [where f=gsMaxObjectSize])
    apply wp
    apply (clarsimp simp: ran_def valid_cap_sizes'_def)
    apply metis
   apply wp+
  done

lemma updateMDB_global_refs [wp]:
 "\<lbrace>valid_global_refs'\<rbrace> updateMDB p m \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  apply (clarsimp simp add: updateMDB_def)
  apply (rule hoare_pre)
   apply (wp getCTE_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of valid_global_refs'_def valid_refs'_def valid_cap_sizes'_def)
  apply blast
  done

lemma updateCap_global_refs [wp]:
 "\<lbrace>valid_global_refs' and (\<lambda>s. kernel_data_refs \<inter> capRange cap = {})
     and (\<lambda>s. 2 ^ capBits cap \<le> gsMaxObjectSize s)\<rbrace>
  updateCap p cap
  \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  apply (clarsimp simp add: updateCap_def)
  apply (rule hoare_pre)
   apply (wp getCTE_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

crunch cteInsert
  for arch[wp]: "\<lambda>s. P (ksArchState s)"
  (wp: crunch_wps simp: cte_wp_at_ctes_of)

lemma cteInsert_valid_arch [wp]:
 "\<lbrace>valid_arch_state'\<rbrace> cteInsert cap src dest \<lbrace>\<lambda>rv. valid_arch_state'\<rbrace>"
  by (rule valid_arch_state_lift'; wp)

lemma cteInsert_valid_irq_handlers'[wp]:
  "\<lbrace>\<lambda>s. valid_irq_handlers' s \<and> (\<forall>irq. cap = IRQHandlerCap irq \<longrightarrow> irq_issued' irq s)\<rbrace>
     cteInsert cap src dest
   \<lbrace>\<lambda>rv. valid_irq_handlers'\<rbrace>"
  apply (simp add: valid_irq_handlers'_def cteInsert_def
                   irq_issued'_def setUntypedCapAsFull_def)
  apply (wp getCTE_wp)
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (intro conjI impI)
    apply (clarsimp simp:ran_dom modify_map_dom)
    apply (drule bspec)
      apply fastforce
    apply (clarsimp simp:isCap_simps modify_map_def split:if_splits)
  apply (clarsimp simp:ran_dom modify_map_dom)
  apply (drule bspec)
    apply fastforce
  apply (clarsimp simp:modify_map_def split:if_splits)
done

definition
  "safe_ioport_insert' newcap oldcap \<equiv> \<lambda>s.  (cap_ioports' newcap = {} \<or>
      (\<forall>cap''\<in>ran (cteCaps_of s).
          cap_ioports' newcap = cap_ioports' cap'' \<or> cap_ioports' newcap \<inter> cap_ioports' cap'' = {})) \<and>
     cap_ioports' newcap - cap_ioports' oldcap \<subseteq> issued_ioports' (ksArchState s)"

lemma setCTE_arch_ctes_of_wp [wp]:
  "\<lbrace>\<lambda>s. P (ksArchState s) ((ctes_of s)(p \<mapsto> cte))\<rbrace>
  setCTE p cte
  \<lbrace>\<lambda>rv s. P (ksArchState s) (ctes_of s)\<rbrace>"
  apply (simp add: setCTE_def ctes_of_setObject_cte)
  apply (clarsimp simp: setObject_def split_def valid_def in_monad)
  apply (drule(1) updateObject_cte_is_tcb_or_cte[OF _ refl, rotated])
  apply (elim exE conjE disjE rsubst[where P="P (ksArchState s)" for s])
   apply (clarsimp simp: lookupAround2_char1)
   apply (subst map_to_ctes_upd_tcb; assumption?)
    apply (clarsimp simp: mask_def objBits_defs field_simps ps_clear_def3)
   apply (clarsimp simp: tcb_cte_cases_change)
   apply (erule rsubst[where P="P (ksArchState s)" for s])
   apply (rule ext, clarsimp)
   apply (intro conjI impI)
    apply (clarsimp simp: tcb_cte_cases_def split: if_split_asm)
   apply (drule(1) cte_wp_at_tcbI'[where P="(=) cte"])
      apply (simp add: ps_clear_def3 field_simps)
     apply assumption+
   apply (simp add: cte_wp_at_ctes_of)
  by (clarsimp simp: map_to_ctes_upd_cte ps_clear_def3 field_simps mask_def)

lemmas cap_ioports'_simps[simp] = cap_ioports'_def[split_simps capability.split arch_capability.split]

lemma setCTE_irq_states' [wp]:
  "\<lbrace>valid_irq_states'\<rbrace> setCTE x y \<lbrace>\<lambda>_. valid_irq_states'\<rbrace>"
  apply (rule valid_irq_states_lift')
   apply wp
  apply (simp add: setCTE_def)
  apply (wp setObject_ksMachine)
   apply (simp add: updateObject_cte)
   apply (rule hoare_pre)
    apply (wp unless_wp|wpc|simp)+
   apply fastforce
  apply assumption
  done

crunch cteInsert
  for irq_states'[wp]: valid_irq_states'
  (wp: crunch_wps)

crunch cteInsert
  for pred_tcb_at'[wp]: "pred_tcb_at' proj P t"
  (wp: crunch_wps)

lemma setCTE_cteCaps_of[wp]:
  "\<lbrace>\<lambda>s. P ((cteCaps_of s)(p \<mapsto> cteCap cte))\<rbrace>
      setCTE p cte
   \<lbrace>\<lambda>rv s. P (cteCaps_of s)\<rbrace>"
  apply (simp add: cteCaps_of_def)
  apply wp
  apply (clarsimp elim!: rsubst[where P=P] intro!: ext)
  done

crunch setupReplyMaster
  for inQ[wp]: "\<lambda>s. P (obj_at' (inQ d p) t s)"
  and norq[wp]:  "\<lambda>s. P (ksReadyQueues s)"
  and ct[wp]: "\<lambda>s. P (ksCurThread s)"
  and state_refs_of'[wp]: "\<lambda>s. P (state_refs_of' s)"
  and it[wp]: "\<lambda>s. P (ksIdleThread s)"
  and nosch[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  and irq_node'[wp]: "\<lambda>s. P (irq_node' s)"
  (wp: crunch_wps)

lemmas setCTE_cteCap_wp_irq[wp] =
    hoare_use_eq_irq_node' [OF setCTE_ksInterruptState setCTE_cteCaps_of]

crunch setUntypedCapAsFull
  for global_refs'[wp]: "\<lambda>s. P (global_refs' s) "
  (simp: crunch_simps)


lemma setUntypedCapAsFull_valid_refs'[wp]:
  "\<lbrace>\<lambda>s. valid_refs' R (ctes_of s) \<and> cte_wp_at' ((=) srcCTE) src s\<rbrace>
   setUntypedCapAsFull (cteCap srcCTE) cap src
   \<lbrace>\<lambda>yb s. valid_refs' R (ctes_of s)\<rbrace>"
  apply (clarsimp simp:valid_refs'_def setUntypedCapAsFull_def split del:if_splits)
  apply (rule hoare_pre)
  apply (wp updateCap_ctes_of_wp)
  apply (clarsimp simp:ran_dom)
  apply (drule_tac x = y in bspec)
    apply (drule_tac a = y in domI)
    apply (simp add:modify_map_dom)
  apply (clarsimp simp:modify_map_def cte_wp_at_ctes_of
    isCap_simps split:if_splits)
done

crunch setUntypedCapAsFull
  for gsMaxObjectSize[wp]: "\<lambda>s. P (gsMaxObjectSize s)"

lemma setUntypedCapAsFull_sizes[wp]:
  "\<lbrace>\<lambda>s. valid_cap_sizes' sz (ctes_of s) \<and> cte_wp_at' ((=) srcCTE) src s\<rbrace>
    setUntypedCapAsFull (cteCap srcCTE) cap src
  \<lbrace>\<lambda>rv s. valid_cap_sizes' sz (ctes_of s)\<rbrace>"
  apply (clarsimp simp:valid_cap_sizes'_def setUntypedCapAsFull_def split del:if_splits)
  apply (rule hoare_pre)
  apply (wp updateCap_ctes_of_wp | wps)+
  apply (clarsimp simp:ran_dom)
  apply (drule_tac x = y in bspec)
    apply (drule_tac a = y in domI)
    apply (simp add:modify_map_dom)
  apply (clarsimp simp:modify_map_def cte_wp_at_ctes_of
    isCap_simps split:if_splits)
  done

lemma setUntypedCapAsFull_valid_global_refs'[wp]:
  "\<lbrace>\<lambda>s. valid_global_refs' s \<and> cte_wp_at' ((=) srcCTE) src s\<rbrace>
   setUntypedCapAsFull (cteCap srcCTE) cap src
   \<lbrace>\<lambda>yb s. valid_global_refs' s\<rbrace>"
  apply (clarsimp simp: valid_global_refs'_def)
  apply (rule hoare_pre,wps)
  apply wp
  apply simp
done

lemma capMaster_eq_capBits_eq:
  "capMasterCap cap = capMasterCap cap' \<Longrightarrow> capBits cap = capBits cap'"
  by (metis capBits_Master)

lemma valid_global_refsD_with_objSize:
  "\<lbrakk> ctes_of s p = Some cte; valid_global_refs' s \<rbrakk> \<Longrightarrow>
  kernel_data_refs \<inter> capRange (cteCap cte) = {} \<and> global_refs' s \<subseteq> kernel_data_refs
    \<and> 2 ^ capBits (cteCap cte) \<le> gsMaxObjectSize s"
  by (clarsimp simp: valid_global_refs'_def valid_refs'_def valid_cap_sizes'_def ran_def) blast

lemma cteInsert_valid_globals [wp]:
 "\<lbrace>valid_global_refs' and (\<lambda>s. cte_wp_at' (is_derived' (ctes_of s) src cap \<circ> cteCap) src s)\<rbrace>
  cteInsert cap src dest
  \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  apply (simp add: cteInsert_def)
  apply (rule hoare_pre)
   apply (wp getCTE_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of is_derived'_def badge_derived'_def)
  apply (frule capMaster_eq_capBits_eq)
  apply (drule capMaster_capRange)
  apply (drule (1) valid_global_refsD_with_objSize)
  apply simp
  done

crunch cteInsert
  for arch[wp]: "\<lambda>s. P (ksArchState s)"
  (wp: crunch_wps simp: cte_wp_at_ctes_of)

lemma setCTE_ksMachine[wp]:
  "\<lbrace>\<lambda>s. P (ksMachineState s)\<rbrace> setCTE x y \<lbrace>\<lambda>_ s. P (ksMachineState s)\<rbrace>"
  apply (clarsimp simp: setCTE_def)
  apply (wp setObject_ksMachine)
  apply (clarsimp simp: updateObject_cte
                 split: Structures_H.kernel_object.splits)
  apply (safe, (wp unless_wp | simp)+)
  done

crunch cteInsert
  for ksMachine[wp]: "\<lambda>s. P (ksMachineState s)"
  (wp: crunch_wps)

lemma cteInsert_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> cteInsert cap src dest \<lbrace>\<lambda>rv. valid_machine_state'\<rbrace>"
  apply (simp add: cteInsert_def valid_machine_state'_def pointerInDeviceData_def
                   pointerInUserData_def)
  apply (intro hoare_vcg_all_lift hoare_vcg_disj_lift)
   apply (wp setObject_typ_at_inv setObject_ksMachine updateObject_default_inv |
          intro hoare_drop_imp|assumption)+
  done

crunch cteInsert
  for pspace_domain_valid[wp]: "pspace_domain_valid"
  (wp: crunch_wps)

lemma setCTE_ct_not_inQ[wp]:
  "\<lbrace>ct_not_inQ\<rbrace> setCTE ptr cte \<lbrace>\<lambda>_. ct_not_inQ\<rbrace>"
  apply (rule ct_not_inQ_lift [OF setCTE_nosch])
  apply (simp add: setCTE_def ct_not_inQ_def)
  apply (rule hoare_weaken_pre)
  apply (wps setObject_cte_ct)
  apply (rule setObject_cte_obj_at_tcb')
       apply (clarsimp simp add: obj_at'_def)+
  done

crunch cteInsert
  for ct_not_inQ[wp]: "ct_not_inQ"
  (simp: crunch_simps wp: hoare_drop_imp)

lemma setCTE_ksCurDomain[wp]:
  "\<lbrace>\<lambda>s. P (ksCurDomain s)\<rbrace>
      setCTE p cte
   \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
  apply (simp add: setCTE_def)
  apply wp
  done

lemma setObject_cte_ksDomSchedule[wp]: "\<lbrace> \<lambda>s. P (ksDomSchedule s) \<rbrace> setObject ptr (v::cte) \<lbrace> \<lambda>_ s. P (ksDomSchedule s) \<rbrace>"
  apply (simp add: setObject_def split_def)
  apply (wp updateObject_cte_inv | simp)+
  done

lemma setCTE_ksDomSchedule[wp]:
  "\<lbrace>\<lambda>s. P (ksDomSchedule s)\<rbrace>
      setCTE p cte
   \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
  apply (simp add: setCTE_def)
  apply wp
  done

crunch cteInsert
  for ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  (wp:  crunch_wps )

crunch cteInsert
  for ksIdleThread[wp]: "\<lambda>s. P (ksIdleThread s)"
  (wp: crunch_wps)

crunch cteInsert
  for ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  (wp: crunch_wps)

lemma setCTE_tcbDomain_inv[wp]:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t\<rbrace> setCTE ptr v \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t\<rbrace>"
  apply (simp add: setCTE_def)
  apply (rule setObject_cte_obj_at_tcb', simp_all)
  done

crunch cteInsert
  for tcbDomain_inv[wp]: "obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t"
  (wp: crunch_simps hoare_drop_imps)

lemma setCTE_tcbPriority_inv[wp]:
  "\<lbrace>obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t\<rbrace> setCTE ptr v \<lbrace>\<lambda>_. obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t\<rbrace>"
  apply (simp add: setCTE_def)
  apply (rule setObject_cte_obj_at_tcb', simp_all)
  done

crunch cteInsert
  for tcbPriority_inv[wp]: "obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t"
  (wp: crunch_simps hoare_drop_imps)


lemma cteInsert_ct_idle_or_in_cur_domain'[wp]:
  "\<lbrace> ct_idle_or_in_cur_domain' \<rbrace> cteInsert a b c \<lbrace> \<lambda>_. ct_idle_or_in_cur_domain' \<rbrace>"
  apply (rule ct_idle_or_in_cur_domain'_lift)
  apply (wp hoare_vcg_disj_lift)+
  done

lemma setObject_cte_domIdx:
  "\<lbrace>\<lambda>s. P (ksDomScheduleIdx s)\<rbrace> setObject t (v::cte) \<lbrace>\<lambda>rv s. P (ksDomScheduleIdx s)\<rbrace>"
  by (clarsimp simp: valid_def setCTE_def[symmetric] dest!: setCTE_pspace_only)

crunch cteInsert
  for ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  (wp: setObject_cte_domIdx hoare_drop_imps)

crunch cteInsert
  for gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  (wp: setObject_ksPSpace_only updateObject_cte_inv crunch_wps)

definition
  "untyped_derived_eq cap cap'
    = (isUntypedCap cap \<longrightarrow> cap = cap')"

lemma ran_split:
  "inj_on m (dom m)
    \<Longrightarrow> ran (\<lambda>x. if P x then m' x else m x)
        = ((ran m - (ran (restrict_map m (Collect P))))
            \<union> (ran (restrict_map m' (Collect P))))"
  apply (clarsimp simp: ran_def restrict_map_def set_eq_iff)
  apply (safe, simp_all)
  apply (auto dest: inj_onD[OF _ trans[OF _ sym]])
  done

lemma ran_split_eq:
  "inj_on m (dom m)
    \<Longrightarrow> \<forall>x. \<not> P x \<longrightarrow> m' x = m x
    \<Longrightarrow> ran m'
        = ((ran m - (ran (restrict_map m (Collect P))))
            \<union> (ran (restrict_map m' (Collect P))))"
  apply (rule trans[rotated], erule ran_split)
  apply (rule arg_cong[where f=ran])
  apply auto
  done

lemma usableUntypedRange_uniq:
  "cteCaps_of s x = Some cp
    \<Longrightarrow> cteCaps_of s y = Some cp'
    \<Longrightarrow> isUntypedCap cp
    \<Longrightarrow> isUntypedCap cp'
    \<Longrightarrow> capAligned cp
    \<Longrightarrow> capAligned cp'
    \<Longrightarrow> untyped_inc' (ctes_of s)
    \<Longrightarrow> usableUntypedRange cp = usableUntypedRange cp'
    \<Longrightarrow> usableUntypedRange cp \<noteq> {}
    \<Longrightarrow> x = y"
  apply (cases "the (ctes_of s x)")
  apply (cases "the (ctes_of s y)")
  apply (clarsimp simp: cteCaps_of_def)
  apply (frule untyped_incD'[where p=x and p'=y], simp+)
  apply (drule(1) usableRange_subseteq)+
  apply blast
  done

lemma usableUntypedRange_empty:
  "valid_cap' cp s \<Longrightarrow> isUntypedCap cp
    \<Longrightarrow> (usableUntypedRange cp = {}) = (capFreeIndex cp = maxFreeIndex (capBlockSize cp))"
  apply (clarsimp simp: isCap_simps max_free_index_def valid_cap_simps' capAligned_def)
  apply (rule order_trans, rule word_plus_mono_right)
    apply (rule_tac x="2 ^ capBlockSize cp - 1" in word_of_nat_le)
    apply (simp add: unat_2p_sub_1 untypedBits_defs)
   apply (simp add: field_simps is_aligned_no_overflow)
  apply (simp add: field_simps mask_def)
  done

lemma restrict_map_is_map_comp:
  "restrict_map m S = m \<circ>\<^sub>m (\<lambda>x. if x \<in> S then Some x else None)"
  by (simp add: restrict_map_def map_comp_def fun_eq_iff)

lemma untypedZeroRange_to_usableCapRange:
  "untypedZeroRange c = Some (x, y) \<Longrightarrow> valid_cap' c s
    \<Longrightarrow> isUntypedCap c \<and> usableUntypedRange c = {x .. y}
        \<and> x \<le> y"
  apply (clarsimp simp: untypedZeroRange_def split: if_split_asm)
  apply (frule(1) usableUntypedRange_empty)
  apply (clarsimp simp: isCap_simps valid_cap_simps' max_free_index_def)
  apply (simp add: getFreeRef_def mask_def add_diff_eq)
  done

lemma untyped_ranges_zero_delta:
  assumes urz: "untyped_ranges_zero' s"
    and other: "\<forall>p. p \<notin> set xs \<longrightarrow> cps' p = cteCaps_of s p"
     and vmdb: "valid_mdb' s"
     and vobj: "valid_objs' s"
       and eq: "ran (restrict_map (untypedZeroRange \<circ>\<^sub>m cteCaps_of s) (set xs))
           \<subseteq> gsUntypedZeroRanges s
        \<Longrightarrow> utr' = ((gsUntypedZeroRanges s - ran (restrict_map (untypedZeroRange \<circ>\<^sub>m cteCaps_of s) (set xs)))
                \<union> ran (restrict_map (untypedZeroRange \<circ>\<^sub>m cps') (set xs)))"
  notes Collect_const[simp del]
  shows "untyped_ranges_zero_inv cps' utr'"
  apply (subst eq)
   apply (clarsimp simp: urz[unfolded untyped_ranges_zero_inv_def])
   apply (fastforce simp: map_comp_Some_iff restrict_map_Some_iff elim!: ranE)[1]
  apply (simp add: untyped_ranges_zero_inv_def urz[unfolded untyped_ranges_zero_inv_def])
  apply (rule sym, rule trans, rule_tac P="\<lambda>x. x \<in> set xs"
        and m="untypedZeroRange \<circ>\<^sub>m cteCaps_of s" in ran_split_eq)
    apply (rule_tac B="dom (untypedZeroRange \<circ>\<^sub>m (\<lambda>cp. if valid_cap' cp s
      then Some cp else None) \<circ>\<^sub>m cteCaps_of s)" in subset_inj_on[rotated])
     apply (clarsimp simp: map_comp_Some_iff cteCaps_of_def)
     apply (case_tac "the (ctes_of s x)", clarsimp)
     apply (frule ctes_of_valid_cap'[OF _ vobj])
     apply blast
   apply (cut_tac vmdb)
   apply (clarsimp simp: valid_mdb'_def valid_mdb_ctes_def)
    apply (clarsimp intro!: inj_onI simp: map_comp_Some_iff
                     split: if_split_asm)
    apply (drule(1) untypedZeroRange_to_usableCapRange)+
    apply (clarsimp)
    apply (drule(2) usableUntypedRange_uniq, (simp add: valid_capAligned)+)
   apply (simp add: map_comp_def other)
  apply (simp add: restrict_map_is_map_comp)
  done

lemma ran_restrict_map_insert:
  "ran (restrict_map m (insert x S)) = (set_option (m x) \<union> ran (restrict_map m S))"
  by (auto simp add: ran_def restrict_map_Some_iff)

lemmas untyped_ranges_zero_fun_upd
    = untyped_ranges_zero_delta[where xs="[x]" and cps'="cps(x \<mapsto> cp)",
      simplified ran_restrict_map_insert list.simps, simplified] for x cps cp

lemma cteInsert_untyped_ranges_zero[wp]:
 "\<lbrace>untyped_ranges_zero' and (\<lambda>s. src \<noteq> dest) and valid_mdb'
    and valid_objs'
    and cte_wp_at' (untyped_derived_eq cap o cteCap) src\<rbrace>
  cteInsert cap src dest
  \<lbrace>\<lambda>rv. untyped_ranges_zero'\<rbrace>"
  apply (rule hoare_pre)
   apply (rule untyped_ranges_zero_lift, wp)
   apply (simp add: cteInsert_def setUntypedCapAsFull_def)
   apply (wp getCTE_wp' | simp)+
  apply (clarsimp simp: cte_wp_at_ctes_of modify_map_def cteCaps_of_def
                        fun_upd_def[symmetric])
  apply (intro impI conjI allI; erule
    untyped_ranges_zero_delta[where xs="[src, dest]", unfolded cteCaps_of_def],
    simp_all add: ran_restrict_map_insert)
   apply (clarsimp simp: isCap_simps untypedZeroRange_def
                         untyped_derived_eq_def badge_derived'_def
                  split: if_split_asm)
   apply blast
  apply (case_tac "isUntypedCap cap", simp_all add: untyped_derived_eq_def)
  apply (clarsimp simp: isCap_simps untypedZeroRange_def
                        untyped_derived_eq_def badge_derived'_def
                 split: if_split_asm)
  apply blast
  done

crunch cteInsert
  for pspace_canonical'[wp]: "pspace_canonical'"
  (wp: crunch_wps)

crunch cteInsert
  for pspace_in_kernel_mappings'[wp]: "pspace_in_kernel_mappings'"
  (wp: crunch_wps)

crunch cteInsert
  for tcbSchedPrevs_of[wp]: "\<lambda>s. P (tcbSchedPrevs_of s)"
  and tcbSchedNexts_of[wp]: "\<lambda>s. P (tcbSchedNexts_of s)"
  and valid_sched_pointers[wp]: valid_sched_pointers
  and valid_bitmaps[wp]: valid_bitmaps
  (wp: crunch_wps rule: valid_bitmaps_lift)

lemma cteInsert_invs:
 "\<lbrace>invs' and cte_wp_at' (\<lambda>c. cteCap c=NullCap) dest and valid_cap' cap and
  (\<lambda>s. src \<noteq> dest) and (\<lambda>s. cte_wp_at' (is_derived' (ctes_of s) src cap \<circ> cteCap) src s)
  and cte_wp_at' (untyped_derived_eq cap o cteCap) src
  and ex_cte_cap_to' dest and (\<lambda>s. \<forall>irq. cap = IRQHandlerCap irq \<longrightarrow> irq_issued' irq s) \<rbrace>
  cteInsert cap src dest
  \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (wpsimp wp: cur_tcb_lift tcb_in_cur_domain'_lift sch_act_wf_lift
                    valid_irq_node_lift irqs_masked_lift cteInsert_norq
                    sym_heap_sched_pointers_lift)
  apply (auto simp: invs'_def valid_state'_def valid_pspace'_def elim: valid_capAligned)
  done

lemma deriveCap_corres:
 "\<lbrakk>cap_relation c c'; cte = cte_map slot \<rbrakk> \<Longrightarrow>
  corres (ser \<oplus> cap_relation)
         (cte_at slot)
         (pspace_aligned' and pspace_distinct' and cte_at' cte and valid_mdb')
         (derive_cap slot c) (deriveCap cte c')"
  apply (unfold derive_cap_def deriveCap_def)
  apply (case_tac c)
            apply (simp_all add: returnOk_def Let_def is_zombie_def isCap_simps
                          split: sum.splits)
   apply (rule_tac Q="\<lambda>_ _. True" and Q'="\<lambda>_ _. True" in
               corres_initial_splitE [OF ensureNoChildren_corres])
      apply simp
     apply clarsimp
    apply wp+
  apply clarsimp
  apply (rule corres_rel_imp)
   apply (rule corres_guard_imp)
     apply (rule arch_deriveCap_corres)
     apply (clarsimp simp: o_def)+
  done

crunch deriveCap
  for inv[wp]: "P"
  (simp: crunch_simps wp: crunch_wps arch_deriveCap_inv)

lemma valid_NullCap:
  "valid_cap' NullCap = \<top>"
  by (rule ext, simp add: valid_cap_simps' capAligned_def word_bits_def)

lemma deriveCap_valid [wp]:
  "\<lbrace>\<lambda>s. s \<turnstile>' c\<rbrace>
  deriveCap slot c
  \<lbrace>\<lambda>rv s. s \<turnstile>' rv\<rbrace>,-"
  apply (simp add: deriveCap_def split del: if_split)
  apply (rule hoare_pre)
   apply (wp arch_deriveCap_valid | simp add: o_def)+
  apply (simp add: valid_NullCap)
  apply (clarsimp simp: isCap_simps)
  done

lemma lookup_cap_valid':
  "\<lbrace>valid_objs'\<rbrace> lookupCap t c \<lbrace>valid_cap'\<rbrace>, -"
  apply (simp add: lookupCap_def lookupCapAndSlot_def
                   lookupSlotForThread_def split_def)
  apply (wp | simp)+
  done

lemma capAligned_Null [simp]:
  "capAligned NullCap"
  by (simp add: capAligned_def is_aligned_def word_bits_def)

lemma cte_wp_at'_conjI:
  "\<lbrakk> cte_wp_at' P p s; cte_wp_at' Q p s \<rbrakk> \<Longrightarrow> cte_wp_at' (\<lambda>c. P c \<and> Q c) p s"
  by (auto simp add: cte_wp_at'_def)

crunch rangeCheck
  for inv'[wp]: "P"
  (simp: crunch_simps)

lemma lookupSlotForCNodeOp_inv'[wp]:
  "\<lbrace>P\<rbrace> lookupSlotForCNodeOp src croot ptr depth \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: lookupSlotForCNodeOp_def split_def unlessE_def
             cong: if_cong split del: if_split)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps)
  apply simp
  done

(* FIXME: move *)
lemma loadWordUser_inv [wp]:
  "\<lbrace>P\<rbrace> loadWordUser p \<lbrace>\<lambda>rv. P\<rbrace>"
  unfolding loadWordUser_def
  by (wp dmo_inv' loadWord_inv)

lemma capTransferFromWords_inv:
  "\<lbrace>P\<rbrace> capTransferFromWords buffer \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: capTransferFromWords_def)
  apply wp
  done

lemma lct_inv' [wp]:
  "\<lbrace>P\<rbrace> loadCapTransfer b \<lbrace>\<lambda>rv. P\<rbrace>"
  unfolding loadCapTransfer_def
  apply (wp capTransferFromWords_inv)
  done

lemma maskCapRightsNull [simp]:
  "maskCapRights R NullCap = NullCap"
  by (simp add: maskCapRights_def isCap_defs)

lemma maskCapRightsUntyped [simp]:
  "maskCapRights R (UntypedCap d r n f) = UntypedCap d r n f"
  by (simp add: maskCapRights_def isCap_defs Let_def)

declare if_option_Some[simp]

lemma lookup_cap_corres:
  "\<lbrakk> epcptr = to_bl epcptr' \<rbrakk> \<Longrightarrow>
   corres (lfr \<oplus> cap_relation)
     (valid_objs and pspace_aligned and tcb_at thread)
     (valid_objs' and pspace_distinct' and pspace_aligned' and tcb_at' thread)
     (lookup_cap thread epcptr)
     (lookupCap thread epcptr')"
  apply (simp add: lookup_cap_def lookupCap_def lookupCapAndSlot_def)
  apply (rule corres_guard_imp)
    apply (rule corres_splitEE[OF lookupSlotForThread_corres])
      apply (simp add: split_def)
      apply (subst bindE_returnOk[symmetric])
      apply (rule corres_splitEE)
         apply simp
         apply (rule getSlotCap_corres, rule refl)
        apply (rule corres_returnOk [of _ \<top> \<top>])
        apply simp
     apply wp+
   apply auto
  done

lemma ensureEmptySlot_corres:
  "q = cte_map p \<Longrightarrow>
   corres (ser \<oplus> dc) (invs and cte_at p) invs'
                     (ensure_empty p) (ensureEmptySlot q)"
  apply (clarsimp simp add: ensure_empty_def ensureEmptySlot_def unlessE_whenE liftE_bindE)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF get_cap_corres])
      apply (rule corres_trivial)
      apply (case_tac cap, auto simp add: whenE_def returnOk_def)[1]
     apply wp+
   apply (clarsimp simp: invs_valid_objs invs_psp_aligned)
  apply fastforce
  done

lemma ensureEmpty_inv[wp]:
  "\<lbrace>P\<rbrace> ensureEmptySlot p \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: ensureEmptySlot_def unlessE_whenE whenE_def | wp)+

lemma lookupSlotForCNodeOp_corres:
  "\<lbrakk>cap_relation c c'; ptr = to_bl ptr'\<rbrakk>
  \<Longrightarrow> corres (ser \<oplus> (\<lambda>cref cref'. cref' = cte_map cref))
            (valid_objs and pspace_aligned and valid_cap c)
            (valid_objs' and pspace_aligned' and pspace_distinct' and valid_cap' c')
            (lookup_slot_for_cnode_op s c ptr depth)
            (lookupSlotForCNodeOp s c' ptr' depth)"
  apply (simp add: lookup_slot_for_cnode_op_def lookupSlotForCNodeOp_def)
  apply (clarsimp simp: lookup_failure_map_def split_def word_size)
  apply (clarsimp simp: rangeCheck_def[unfolded fun_app_def unlessE_def] whenE_def
                        word_bits_def toInteger_nat fromIntegral_def fromInteger_nat)
  apply (rule corres_lookup_error)
  apply (rule corres_guard_imp)
    apply (rule corres_splitEE)
       apply (rule rab_corres'; simp add: word_bits_def)
      apply (rule corres_trivial)
      apply (clarsimp simp: returnOk_def lookup_failure_map_def
                      split: list.split)
     apply wp+
   apply clarsimp
  apply clarsimp
  done

lemma ensureNoChildren_wp:
  "\<lbrace>\<lambda>s. (descendants_of' p (ctes_of s) \<noteq> {} \<longrightarrow> Q s)
    \<and> (descendants_of' p (ctes_of s) = {} \<longrightarrow> P () s)\<rbrace>
      ensureNoChildren p
   \<lbrace>P\<rbrace>,\<lbrace>\<lambda>_. Q\<rbrace>"
  apply (simp add: ensureNoChildren_def whenE_def)
  apply (wp getCTE_wp')
  apply (clarsimp simp: cte_wp_at_ctes_of nullPointer_def descendants_of'_def)
  apply (intro conjI impI allI)
    apply clarsimp
    apply (drule spec, erule notE, rule subtree.direct_parent)
      apply (simp add:mdb_next_rel_def mdb_next_def)
     apply simp
    apply (simp add: parentOf_def)
   apply clarsimp
   apply (erule (4) subtree_no_parent)
  apply clarsimp
  apply (erule (2) subtree_next_0)
  done

lemma deriveCap_derived:
  "\<lbrace>\<lambda>s. c'\<noteq> capability.NullCap \<longrightarrow> cte_wp_at' (\<lambda>cte. badge_derived' c' (cteCap cte)
                           \<and> capASID c' = capASID (cteCap cte)
                           \<and> cap_asid_base' c' = cap_asid_base' (cteCap cte)
                           \<and> cap_vptr' c' = cap_vptr' (cteCap cte)) slot s
       \<and> valid_objs' s\<rbrace>
  deriveCap slot c'
  \<lbrace>\<lambda>rv s. rv \<noteq> NullCap \<longrightarrow>
          cte_wp_at' (is_derived' (ctes_of s) slot rv \<circ> cteCap) slot s\<rbrace>, -"
  unfolding deriveCap_def badge_derived'_def
  apply (cases c'; (solves \<open>(wp ensureNoChildren_wp | simp add: isCap_simps Let_def
        | clarsimp simp: badge_derived'_def vsCapRef_def
        | erule cte_wp_at_weakenE' disjE
        | rule is_derived'_def[THEN meta_eq_to_obj_eq, THEN iffD2])+\<close>)?)
  apply (rename_tac arch_capability)
  apply (case_tac arch_capability;
         simp add: X64_H.deriveCap_def Let_def isCap_simps
              split: if_split,
         safe)
        apply ((wp throwError_validE_R undefined_validE_R
                  | clarsimp simp: isCap_simps capAligned_def cte_wp_at_ctes_of
                  | drule valid_capAligned
                  | drule(1) bits_low_high_eq
                  | simp add: capBadge_def sameObjectAs_def
                              is_derived'_def isCap_simps up_ucast_inj_eq
                              is_aligned_no_overflow badge_derived'_def
                              capAligned_def capASID_def vsCapRef_def
                  | clarsimp split: option.split_asm)+)
  done

lemma untyped_derived_eq_ArchObjectCap:
  "untyped_derived_eq (capability.ArchObjectCap cap) = \<top>"
  by (rule ext, simp add: untyped_derived_eq_def isCap_simps)

lemma arch_deriveCap_untyped_derived[wp]:
  "\<lbrace>\<lambda>s. cte_wp_at' (\<lambda>cte. untyped_derived_eq c' (cteCap cte)) slot s\<rbrace>
     X64_H.deriveCap slot (capCap c')
   \<lbrace>\<lambda>rv s. cte_wp_at' (untyped_derived_eq rv o cteCap) slot s\<rbrace>, -"
  apply (wpsimp simp: X64_H.deriveCap_def Let_def untyped_derived_eq_ArchObjectCap split_del: if_split
                  wp: undefined_validE_R)
  apply(clarsimp simp: cte_wp_at_ctes_of isCap_simps untyped_derived_eq_def)
  by (case_tac "capCap c'"; fastforce)

lemma deriveCap_untyped_derived:
  "\<lbrace>\<lambda>s. cte_wp_at' (\<lambda>cte. untyped_derived_eq c' (cteCap cte)) slot s\<rbrace>
  deriveCap slot c'
  \<lbrace>\<lambda>rv s. cte_wp_at' (untyped_derived_eq rv o cteCap) slot s\<rbrace>, -"
  apply (simp add: deriveCap_def split del: if_split cong: if_cong)
  apply (rule hoare_pre)
   apply (wp arch_deriveCap_inv | simp add: o_def untyped_derived_eq_ArchObjectCap)+
  apply (clarsimp simp: cte_wp_at_ctes_of isCap_simps untyped_derived_eq_def)
  done

lemma setCTE_corres:
  "cap_relation cap (cteCap cte) \<Longrightarrow>
   corres_underlying {(s, s'). pspace_relation (kheap s) (ksPSpace s')} False True dc
      (pspace_distinct and pspace_aligned and valid_objs and cte_at p)
      (pspace_aligned' and pspace_distinct' and cte_at' (cte_map p))
      (set_cap cap p)
      (setCTE (cte_map p) cte)"
  apply (rule corres_no_failI)
   apply (rule no_fail_pre, wp)
   apply simp
  apply clarsimp
  apply (drule(8) set_cap_not_quite_corres_prequel)
   apply simp
  apply fastforce
  done

(* FIXME: move to StateRelation *)
lemma ghost_relation_of_heap:
  "ghost_relation h ups cns \<longleftrightarrow> ups_of_heap h = ups \<and> cns_of_heap h = cns"
  apply (rule iffI)
   apply (rule conjI)
    apply (rule ext)
    apply (clarsimp simp add: ghost_relation_def ups_of_heap_def)
    apply (drule_tac x=x in spec)
    apply (auto simp: ghost_relation_def ups_of_heap_def
                split: option.splits Structures_A.kernel_object.splits
                       arch_kernel_obj.splits)[1]
    subgoal for x dev sz
     by (drule_tac x = sz in spec,simp)
   apply (rule ext)
   apply (clarsimp simp add: ghost_relation_def cns_of_heap_def)
   apply (drule_tac x=x in spec)+
   apply (rule ccontr)
   apply (simp split: option.splits Structures_A.kernel_object.splits
                      arch_kernel_obj.splits)[1]
   apply (simp split: if_split_asm)
    apply force
   apply (drule not_sym)
   apply clarsimp
   apply (erule_tac x=y in allE)
   apply simp
  apply (auto simp add: ghost_relation_def ups_of_heap_def cns_of_heap_def
              split: option.splits Structures_A.kernel_object.splits
                     arch_kernel_obj.splits if_split_asm)
  done

lemma corres_caps_decomposition:
  assumes x: "corres_underlying {(s, s'). pspace_relation (kheap s) (ksPSpace s')} False True r P P' f g"
  assumes u: "\<And>P. \<lbrace>\<lambda>s. P (new_caps s)\<rbrace> f \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_mdb s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cdt s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_list s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cdt_list (s))\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_rvk s)\<rbrace> f \<lbrace>\<lambda>rv s. P (is_original_cap s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_ctes s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ctes_of s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_ms s)\<rbrace> f \<lbrace>\<lambda>rv s. P (machine_state s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_ms' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksMachineState s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_wuc s)\<rbrace> f \<lbrace>\<lambda>rv s. P (work_units_completed s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_wuc' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksWorkUnitsCompleted s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_ct s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_ct' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksCurThread s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_as s)\<rbrace> f \<lbrace>\<lambda>rv s. P (arch_state s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_as' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksArchState s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_id s)\<rbrace> f \<lbrace>\<lambda>rv s. P (idle_thread s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_id' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksIdleThread s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_irqn s)\<rbrace> f \<lbrace>\<lambda>rv s. P (interrupt_irq_node s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_irqs s)\<rbrace> f \<lbrace>\<lambda>rv s. P (interrupt_states s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_irqs' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksInterruptState s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_ups s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ups_of_heap (kheap s))\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_ups' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (gsUserPages s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_cns s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cns_of_heap (kheap s))\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_cns' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (gsCNodes s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_ready_queues s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ready_queues s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_action s)\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_sa' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksSchedulerAction s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_ksReadyQueues s) (new_tcbSchedNexts_of s) (new_tcbSchedPrevs_of s)
                          (\<lambda>d p. new_inQs d p s)\<rbrace>
                   g \<lbrace>\<lambda>rv s. P (ksReadyQueues s) (tcbSchedNexts_of s) (tcbSchedPrevs_of s)
                               (\<lambda>d p. inQ d p |< (tcbs_of' s))\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_di s)\<rbrace> f \<lbrace>\<lambda>rv s. P (domain_index s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_dl s)\<rbrace> f \<lbrace>\<lambda>rv s. P (domain_list s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_cd s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_domain s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_dt s)\<rbrace> f \<lbrace>\<lambda>rv s. P (domain_time s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_dsi' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksDomScheduleIdx s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_ds' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksDomSchedule s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_cd' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksCurDomain s)\<rbrace>"
             "\<And>P. \<lbrace>\<lambda>s. P (new_dt' s)\<rbrace> g \<lbrace>\<lambda>rv s. P (ksDomainTime s)\<rbrace>"
  assumes z: "\<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> state_relation \<rbrakk>
                       \<Longrightarrow> cdt_relation ((\<noteq>) None \<circ> new_caps s) (new_mdb s) (new_ctes s')"
             "\<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> state_relation \<rbrakk>
                       \<Longrightarrow> cdt_list_relation (new_list s) (new_mdb s) (new_ctes s')"
             "\<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> state_relation \<rbrakk>
                       \<Longrightarrow> sched_act_relation (new_action s) (new_sa' s')"
             "\<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> state_relation \<rbrakk>
                       \<Longrightarrow> ready_queues_relation_2 (new_ready_queues s) (new_ksReadyQueues s')
                                                   (new_tcbSchedNexts_of s') (new_tcbSchedPrevs_of s')
                                                   (\<lambda>d p. new_inQs d p s')"
             "\<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> state_relation \<rbrakk>
                       \<Longrightarrow> revokable_relation (new_rvk s) (null_filter (new_caps s)) (new_ctes s')"
             "\<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> state_relation \<rbrakk>
                       \<Longrightarrow> (new_as s, new_as' s') \<in> arch_state_relation
                            \<and> interrupt_state_relation (new_irqn s) (new_irqs s) (new_irqs' s')
                            \<and> new_ct s = new_ct' s' \<and> new_id s = new_id' s'
                            \<and> new_ms s = new_ms' s' \<and> new_di s = new_dsi' s'
                            \<and> new_dl s = new_ds' s' \<and> new_cd s = new_cd' s' \<and> new_dt s = new_dt' s' \<and> new_wuc s = new_wuc' s'"
             "\<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> state_relation \<rbrakk>
                       \<Longrightarrow> new_ups s = new_ups' s'"
             "\<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> state_relation \<rbrakk>
                       \<Longrightarrow> new_cns s = new_cns' s'"
  shows "corres r P P' f g"
proof -
  have all_ext: "\<And>f f'. (\<forall>p. f p = f' p) = (f = f')"
    by (fastforce intro!: ext)
  have mdb_wp':
    "\<And>ctes. \<lbrace>\<lambda>s. cdt_relation ((\<noteq>) None \<circ> new_caps s) (new_mdb s) ctes\<rbrace>
                f
            \<lbrace>\<lambda>rv s. \<exists>m ca. (\<forall>p. ca p = ((\<noteq>) None \<circ> caps_of_state s) p) \<and> m = cdt s
                            \<and> cdt_relation ca m ctes\<rbrace>"
    apply (wp hoare_vcg_ex_lift hoare_vcg_all_lift u)
    apply (subst all_ext)
    apply (simp add: o_def)
    done
  note mdb_wp = mdb_wp' [simplified all_ext simp_thms]
  have list_wp':
    "\<And>ctes. \<lbrace>\<lambda>s. cdt_list_relation (new_list s) (new_mdb s) ctes\<rbrace>
                f
            \<lbrace>\<lambda>rv s. \<exists>m t. t = cdt_list s \<and> m = cdt s
                            \<and> cdt_list_relation t m ctes\<rbrace>"
    apply (wp hoare_vcg_ex_lift hoare_vcg_all_lift u)
    apply (simp add: o_def)
    done
  note list_wp = list_wp' [simplified all_ext simp_thms]
  have rvk_wp':
    "\<And>ctes. \<lbrace>\<lambda>s. revokable_relation (new_rvk s) (null_filter (new_caps s)) ctes\<rbrace>
                f
            \<lbrace>\<lambda>rv s. revokable_relation (is_original_cap s) (null_filter (caps_of_state s)) ctes\<rbrace>"
    unfolding revokable_relation_def
    apply (simp only: imp_conv_disj)
    apply (wp hoare_vcg_ex_lift hoare_vcg_all_lift hoare_vcg_disj_lift u)
    done
  have exs_wp':
    "\<And>ctes. \<lbrace>\<lambda>s. revokable_relation (new_rvk s) (null_filter (new_caps s)) ctes\<rbrace>
                f
            \<lbrace>\<lambda>rv s. revokable_relation (is_original_cap s) (null_filter (caps_of_state s)) ctes\<rbrace>"
    unfolding revokable_relation_def
    apply (simp only: imp_conv_disj)
    apply (wp hoare_vcg_ex_lift hoare_vcg_all_lift hoare_vcg_disj_lift u)
    done
  note rvk_wp = rvk_wp' [simplified all_ext simp_thms]
  have swp_cte_at:
    "\<And>s. swp cte_at s = ((\<noteq>) None \<circ> caps_of_state s)"
    by (rule ext, simp, subst neq_commute, simp add: cte_wp_at_caps_of_state)
  have abs_irq_together':
    "\<And>P. \<lbrace>\<lambda>s. P (new_irqn s) (new_irqs s)\<rbrace> f
             \<lbrace>\<lambda>rv s. \<exists>irn. interrupt_irq_node s = irn \<and> P irn (interrupt_states s)\<rbrace>"
    by (wp hoare_vcg_ex_lift u, simp)
  note abs_irq_together = abs_irq_together'[simplified]
  show ?thesis
    unfolding state_relation_def swp_cte_at
    apply (rule corres_underlying_decomposition [OF x])
     apply (simp add: ghost_relation_of_heap)
     apply (wpsimp wp: hoare_vcg_conj_lift mdb_wp rvk_wp list_wp u abs_irq_together)+
    apply (intro z[simplified o_def] conjI | simp add: state_relation_def swp_cte_at
          | (drule (1) z(6), simp add: state_relation_def swp_cte_at))+
    done
qed

lemma getCTE_symb_exec_r:
  "corres_underlying sr False nf' dc \<top> (cte_at' p) (return ()) (getCTE p)"
  apply (rule corres_no_failI, wp)
  apply (clarsimp simp: return_def
                 elim!: use_valid [OF _ getCTE_inv])
  done

lemma updateMDB_symb_exec_r:
  "corres_underlying {(s::det_state, s'). pspace_relation (kheap s) (ksPSpace s')} False nf' dc
        \<top> (pspace_aligned' and pspace_distinct' and (no_0 \<circ> ctes_of) and (\<lambda>s. p \<noteq> 0 \<longrightarrow> cte_at' p s))
        (return ()) (updateMDB p m)"
  using no_fail_updateMDB [of p m]
  apply (clarsimp simp: corres_underlying_def return_def no_fail_def)
  apply (drule(1) updateMDB_the_lot, simp, assumption+)
  apply clarsimp
  done

lemma updateMDB_ctes_of_cases:
  "\<lbrace>\<lambda>s. P (modify_map (ctes_of s) p (if p = 0 then id else cteMDBNode_update f))\<rbrace>
     updateMDB p f \<lbrace>\<lambda>rv s. P (ctes_of s)\<rbrace>"
  apply (simp add: updateMDB_def split del: if_split)
  apply (rule hoare_pre, wp getCTE_ctes_of)
  apply (clarsimp simp: modify_map_def map_option_case
                 split: option.split
          | rule conjI ext | erule rsubst[where P=P])+
  apply (case_tac y, simp)
  done

crunch updateMDB
  for ct[wp]: "\<lambda>s. P (ksCurThread s)"

lemma setCTE_state_bits[wp]:
  "\<lbrace>\<lambda>s. P (ksMachineState s)\<rbrace> setCTE p v \<lbrace>\<lambda>rv s. P (ksMachineState s)\<rbrace>"
  "\<lbrace>\<lambda>s. Q (ksIdleThread s)\<rbrace> setCTE p v \<lbrace>\<lambda>rv s. Q (ksIdleThread s)\<rbrace>"
  "\<lbrace>\<lambda>s. R (ksArchState s)\<rbrace> setCTE p v \<lbrace>\<lambda>rv s. R (ksArchState s)\<rbrace>"
  "\<lbrace>\<lambda>s. S (ksInterruptState s)\<rbrace> setCTE p v \<lbrace>\<lambda>rv s. S (ksInterruptState s)\<rbrace>"
  apply (simp_all add: setCTE_def setObject_def split_def)
  apply (wp updateObject_cte_inv | simp)+
  done

crunch updateMDB
  for ms'[wp]: "\<lambda>s. P (ksMachineState s)"
crunch updateMDB
  for idle'[wp]: "\<lambda>s. P (ksIdleThread s)"
crunch updateMDB
  for arch'[wp]: "\<lambda>s. P (ksArchState s)"
crunch updateMDB
  for int'[wp]: "\<lambda>s. P (ksInterruptState s)"

lemma cte_map_eq_subst:
  "\<lbrakk> cte_at p s; cte_at p' s; valid_objs s; pspace_aligned s; pspace_distinct s \<rbrakk>
     \<Longrightarrow> (cte_map p = cte_map p') = (p = p')"
  by (fastforce elim!: cte_map_inj_eq)

lemma revokable_relation_simp:
  "\<lbrakk> (s, s') \<in> state_relation; null_filter (caps_of_state s) p = Some c; ctes_of s' (cte_map p) = Some (CTE cap node) \<rbrakk>
      \<Longrightarrow> mdbRevocable node = is_original_cap s p"
  by (cases p, clarsimp simp: state_relation_def revokable_relation_def)

crunch setCTE
  for gsUserPages[wp]: "\<lambda>s. P (gsUserPages s)"
  and gsCNodes[wp]: "\<lambda>s. P (gsCNodes s)"
  and domain_time[wp]: "\<lambda>s. P (ksDomainTime s)"
  and work_units_completed[wp]: "\<lambda>s. P (ksWorkUnitsCompleted s)"
  (simp: setObject_def wp: updateObject_cte_inv)

lemma set_original_symb_exec_l':
  "corres_underlying {(s, s'). f (kheap s) s'} False nf' dc P P' (set_original p b) (return x)"
  by (simp add: corres_underlying_def return_def set_original_def in_monad Bex_def)

crunch set_cap
  for domain_index[wp]: "\<lambda>s. P (domain_index s)"
  (wp: set_object_wp)

lemma create_reply_master_corres:
  "\<lbrakk> sl' = cte_map sl ; AllowGrant \<in> rights \<rbrakk> \<Longrightarrow>
   corres dc
      (cte_wp_at ((=) cap.NullCap) sl and valid_pspace and valid_mdb and valid_list)
      (cte_wp_at' (\<lambda>c. cteCap c = NullCap \<and> mdbPrev (cteMDBNode c) = 0) sl'
       and valid_mdb' and valid_pspace')
      (do
         y \<leftarrow> set_original sl True;
         set_cap (cap.ReplyCap thread True rights) sl
       od)
      (setCTE sl' (CTE (capability.ReplyCap thread True True) initMDBNode))"
  apply clarsimp
  apply (rule corres_caps_decomposition)
                                 defer
                                 apply (wp|simp add: o_def split del: if_splits)+
          apply (clarsimp simp: o_def cdt_relation_def cte_wp_at_ctes_of
                     split del: if_split cong: if_cong simp del: id_apply)
          apply (case_tac cte, clarsimp)
          apply (fold fun_upd_def)
          apply (subst descendants_of_Null_update')
               apply fastforce
              apply fastforce
             apply assumption
            apply assumption
           apply (simp add: nullPointer_def)
          apply (subgoal_tac "cte_at (a, b) s")
           prefer 2
           apply (drule not_sym, clarsimp simp: cte_wp_at_caps_of_state
                                         split: if_split_asm)
          apply (simp add: state_relation_def cdt_relation_def)
         apply (clarsimp simp: o_def cdt_list_relation_def cte_wp_at_ctes_of
                    split del: if_split cong: if_cong simp del: id_apply)
         apply (case_tac cte, clarsimp)
         apply (clarsimp simp: state_relation_def cdt_list_relation_def)
         apply (simp split: if_split_asm)
         apply (erule_tac x=a in allE, erule_tac x=b in allE)
         apply clarsimp
         apply(case_tac "next_slot (a, b) (cdt_list s) (cdt s)")
          apply(simp)
         apply(simp)
         apply(fastforce simp: valid_mdb'_def valid_mdb_ctes_def valid_nullcaps_def)
        apply (clarsimp simp: state_relation_def)
       apply (clarsimp simp: state_relation_def)
      apply (clarsimp simp add: revokable_relation_def cte_wp_at_ctes_of
                     split del: if_split)
      apply simp
      apply (rule conjI)
       apply (clarsimp simp: initMDBNode_def)
      apply clarsimp
      apply (subgoal_tac "null_filter (caps_of_state s) (a, b) \<noteq> None")
       prefer 2
       apply (clarsimp simp: null_filter_def cte_wp_at_caps_of_state
                      split: if_split_asm)
      apply (subgoal_tac "cte_at (a,b) s")
       prefer 2
       apply clarsimp
       apply (drule null_filter_caps_of_stateD)
       apply (erule cte_wp_cte_at)
      apply (clarsimp split: if_split_asm cong: conj_cong
                       simp: cte_map_eq_subst revokable_relation_simp
                             cte_wp_at_cte_at valid_pspace_def)
     apply (clarsimp simp: state_relation_def)
    apply (clarsimp elim!: state_relationE simp: ghost_relation_of_heap)+
  apply (rule corres_guard_imp)
    apply (rule corres_underlying_symb_exec_l [OF set_original_symb_exec_l'])
     apply (rule setCTE_corres)
     apply simp
    apply wp
   apply (clarsimp simp: cte_wp_at_cte_at valid_pspace_def)
  apply (clarsimp simp: valid_pspace'_def cte_wp_at'_def)
  done

lemma cte_map_nat_to_cref:
  "\<lbrakk> n < 2 ^ b; b < word_bits \<rbrakk> \<Longrightarrow>
   cte_map (p, nat_to_cref b n) = p + (of_nat n * 2^cte_level_bits)"
  apply (clarsimp simp: cte_map_def nat_to_cref_def shiftl_t2n'
                 dest!: less_is_drop_replicate)
  apply (rule arg_cong [where f="\<lambda>x. x * 2^cte_level_bits"])
  apply (subst of_drop_to_bl)
  apply (simp add: word_bits_def)
  apply (subst mask_eq_iff_w2p)
   apply (simp add: word_size)
  apply (simp add: word_less_nat_alt word_size word_bits_def)
  apply (rule order_le_less_trans)
   defer
   apply assumption
  apply (subst unat_of_nat)
  apply (rule mod_less_eq_dividend)
  done

lemma valid_nullcapsE:
  "\<lbrakk> valid_nullcaps m; m p = Some (CTE NullCap n);
    \<lbrakk> mdbPrev n = 0; mdbNext n = 0 \<rbrakk> \<Longrightarrow> P \<rbrakk>
  \<Longrightarrow> P"
  by (fastforce simp: valid_nullcaps_def nullMDBNode_def nullPointer_def)

lemma valid_nullcaps_prev:
  "\<lbrakk> m (mdbPrev n) = Some (CTE NullCap n'); m p = Some (CTE c n);
    no_0 m; valid_dlist m; valid_nullcaps m \<rbrakk> \<Longrightarrow> False"
  apply (erule (1) valid_nullcapsE)
  apply (erule_tac p=p in valid_dlistEp, assumption)
   apply clarsimp
  apply clarsimp
  done

lemma valid_nullcaps_next:
  "\<lbrakk> m (mdbNext n) = Some (CTE NullCap n'); m p = Some (CTE c n);
    no_0 m; valid_dlist m; valid_nullcaps m \<rbrakk> \<Longrightarrow> False"
  apply (erule (1) valid_nullcapsE)
  apply (erule_tac p=p in valid_dlistEn, assumption)
   apply clarsimp
  apply clarsimp
  done

defs noReplyCapsFor_def:
  "noReplyCapsFor \<equiv> \<lambda>t s. \<forall>sl m r. \<not> cte_wp_at' (\<lambda>cte. cteCap cte = ReplyCap t m r) sl s"

lemma pspace_relation_no_reply_caps:
  assumes pspace: "pspace_relation (kheap s) (ksPSpace s')"
  and       invs: "invs s"
  and        tcb: "tcb_at t s"
  and     m_cte': "cte_wp_at' ((=) cte) sl' s'"
  and     m_null: "cteCap cte = capability.NullCap"
  and       m_sl: "sl' = cte_map (t, tcb_cnode_index 2)"
  shows           "noReplyCapsFor t s'"
proof -
  from tcb have m_cte: "cte_at (t, tcb_cnode_index 2) s"
    by (clarsimp elim!: tcb_at_cte_at)
  have m_cte_null:
    "cte_wp_at (\<lambda>c. c = cap.NullCap) (t, tcb_cnode_index 2) s"
    using pspace invs
    apply (frule_tac pspace_relation_cte_wp_atI')
      apply (rule assms)
     apply clarsimp
    apply (clarsimp simp: m_sl)
    apply (frule cte_map_inj_eq)
         apply (rule m_cte)
        apply (erule cte_wp_cte_at)
       apply clarsimp+
    apply (clarsimp elim!: cte_wp_at_weakenE simp: m_null)
    done
  have no_reply_caps:
    "\<forall>sl m r. \<not> cte_wp_at (\<lambda>c. c = cap.ReplyCap t m r) sl s"
    by (rule no_reply_caps_for_thread [OF invs tcb m_cte_null])
  hence noReplyCaps:
    "\<forall>sl m r. \<not> cte_wp_at' (\<lambda>cte. cteCap cte = ReplyCap t m r) sl s'"
    apply (intro allI)
    apply (clarsimp simp: cte_wp_at_neg2 cte_wp_at_ctes_of simp del: split_paired_All)
    apply (frule pspace_relation_cte_wp_atI [OF pspace _ invs_valid_objs [OF invs]])
    apply (clarsimp simp: cte_wp_at_neg2 simp del: split_paired_All)
    apply (drule_tac x="(a, b)" in spec)
    apply (clarsimp simp: cte_wp_cte_at cte_wp_at_caps_of_state)
    apply (case_tac c, simp_all)
    apply fastforce
    done
  thus ?thesis
    by (simp add: noReplyCapsFor_def)
qed

lemma setupReplyMaster_corres:
  "corres dc (einvs and tcb_at t) (invs' and tcb_at' t)
       (setup_reply_master t) (setupReplyMaster t)"
  apply (simp add: setupReplyMaster_def setup_reply_master_def)
  apply (simp add: locateSlot_conv tcbReplySlot_def objBits_def objBitsKO_def)
  apply (simp add: nullMDBNode_def, fold initMDBNode_def)
  apply (rule_tac F="t + 2*2^cte_level_bits = cte_map (t, tcb_cnode_index 2)" in corres_req)
   apply (clarsimp simp: tcb_cnode_index_def2 cte_map_nat_to_cref word_bits_def cte_level_bits_def)
  apply (clarsimp simp: cte_level_bits_def)
  apply (rule stronger_corres_guard_imp)
    apply (rule corres_split[OF get_cap_corres])
      apply (rule corres_when)
       apply fastforce
      apply (rule_tac P'="einvs and tcb_at t" in corres_stateAssert_implied)
       apply (rule create_reply_master_corres; simp)
      apply (subgoal_tac "\<exists>cte. cte_wp_at' ((=) cte) (cte_map (t, tcb_cnode_index 2)) s'
                              \<and> cteCap cte = capability.NullCap")
       apply (fastforce dest: pspace_relation_no_reply_caps
                             state_relation_pspace_relation)
      apply (clarsimp simp: cte_map_def tcb_cnode_index_def cte_wp_at_ctes_of)
     apply (rule_tac Q'="\<lambda>rv. einvs and tcb_at t and
                             cte_wp_at ((=) rv) (t, tcb_cnode_index 2)"
                  in hoare_strengthen_post)
      apply (wp hoare_drop_imps get_cap_wp)
     apply (clarsimp simp: invs_def valid_state_def elim!: cte_wp_at_weakenE)
    apply (rule_tac Q'="\<lambda>rv. valid_pspace' and valid_mdb' and
                            cte_wp_at' ((=) rv) (cte_map (t, tcb_cnode_index 2))"
                 in hoare_strengthen_post)
     apply (wp hoare_drop_imps getCTE_wp')
    apply (rename_tac rv s)
    apply (clarsimp simp: cte_wp_at_ctes_of valid_mdb'_def valid_mdb_ctes_def)
    apply (case_tac rv, fastforce elim: valid_nullcapsE)
   apply (fastforce elim: tcb_at_cte_at)
  apply (clarsimp simp: cte_at'_obj_at' tcb_cte_cases_def cte_map_def)
  apply (clarsimp simp: invs'_def valid_state'_def valid_pspace'_def)
  done

crunch setupReplyMaster
  for tcb'[wp]: "tcb_at' t"
  (wp: crunch_wps)

crunch setupReplyMaster
  for idle'[wp]: "valid_idle'"

(* Levity: added (20090126 19:32:14) *)
declare stateAssert_wp [wp]

lemma setupReplyMaster_valid_mdb:
  "slot = t + 2 ^ objBits (undefined :: cte) * tcbReplySlot \<Longrightarrow>
   \<lbrace>valid_mdb' and valid_pspace' and tcb_at' t\<rbrace>
   setupReplyMaster t
   \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  apply (clarsimp simp: setupReplyMaster_def locateSlot_conv
                        nullMDBNode_def)
  apply (fold initMDBNode_def)
  apply (wp setCTE_valid_mdb getCTE_wp')
  apply clarsimp
  apply (intro conjI)
      apply (case_tac cte)
      apply (fastforce simp: cte_wp_at_ctes_of valid_mdb'_def valid_mdb_ctes_def
                            no_mdb_def
                      elim: valid_nullcapsE)
     apply (frule obj_at_aligned')
      apply (simp add: valid_cap'_def capAligned_def
                       objBits_simps' word_bits_def)+
    apply (clarsimp simp: valid_pspace'_def)
   apply (clarsimp simp: caps_no_overlap'_def capRange_def)
  apply (clarsimp simp: fresh_virt_cap_class_def
                 elim!: ranE)
  apply (clarsimp simp add: noReplyCapsFor_def cte_wp_at_ctes_of)
  apply (case_tac x)
  apply (rename_tac capability mdbnode)
  apply (case_tac capability; simp)
   apply (rename_tac arch_capability)
   apply (case_tac arch_capability; simp)
  apply fastforce
  done

lemma setupReplyMaster_valid_objs [wp]:
  "\<lbrace> valid_objs' and pspace_aligned' and pspace_distinct' and tcb_at' t\<rbrace>
  setupReplyMaster t
  \<lbrace>\<lambda>_. valid_objs'\<rbrace>"
  apply (simp add: setupReplyMaster_def locateSlot_conv)
  apply (wp setCTE_valid_objs getCTE_wp')
  apply (clarsimp)
  apply (frule obj_at_aligned')
   apply (simp add: valid_cap'_def capAligned_def
                    objBits_simps' word_bits_def)+
  done

lemma setupReplyMaster_wps[wp]:
  "\<lbrace>pspace_aligned'\<rbrace> setupReplyMaster t \<lbrace>\<lambda>rv. pspace_aligned'\<rbrace>"
  "\<lbrace>pspace_distinct'\<rbrace> setupReplyMaster t \<lbrace>\<lambda>rv. pspace_distinct'\<rbrace>"
  "slot = cte_map (t, tcb_cnode_index 2) \<Longrightarrow>
   \<lbrace>\<lambda>s. P ((cteCaps_of s)(slot \<mapsto> (capability.ReplyCap t True True))) \<and> P (cteCaps_of s)\<rbrace>
      setupReplyMaster t
   \<lbrace>\<lambda>rv s. P (cteCaps_of s)\<rbrace>"
    apply (simp_all add: setupReplyMaster_def locateSlot_conv)
    apply (wp getCTE_wp | simp add: o_def cte_wp_at_ctes_of)+
  apply clarsimp
  apply (rule_tac x=cte in exI)
  apply (clarsimp simp: tcbReplySlot_def objBits_simps' fun_upd_def word_bits_def
                        tcb_cnode_index_def2 cte_map_nat_to_cref cte_level_bits_def)
  done

crunch setupReplyMaster
  for no_0_obj'[wp]: no_0_obj'
  (wp: crunch_wps simp: crunch_simps)

crunch setupReplyMaster
  for pspace_canonical'[wp]: "pspace_canonical'"
  (wp: crunch_wps simp: crunch_simps)

crunch setupReplyMaster
  for pspace_in_kernel_mappings'[wp]: "pspace_in_kernel_mappings'"
  (wp: crunch_wps simp: crunch_simps)

lemma setupReplyMaster_valid_pspace':
  "\<lbrace>valid_pspace' and tcb_at' t\<rbrace>
     setupReplyMaster t
   \<lbrace>\<lambda>rv. valid_pspace'\<rbrace>"
  apply (simp add: valid_pspace'_def)
  apply (wp setupReplyMaster_valid_mdb)
   apply (simp_all add: valid_pspace'_def)
  done

lemma setupReplyMaster_ifunsafe'[wp]:
  "slot = t + 2 ^ objBits (undefined :: cte) * tcbReplySlot \<Longrightarrow>
   \<lbrace>if_unsafe_then_cap' and ex_cte_cap_to' slot\<rbrace>
     setupReplyMaster t
   \<lbrace>\<lambda>rv s. if_unsafe_then_cap' s\<rbrace>"
  apply (simp add: ifunsafe'_def3 setupReplyMaster_def locateSlot_conv)
  apply (wp getCTE_wp')
  apply (clarsimp simp: ex_cte_cap_to'_def cte_wp_at_ctes_of cteCaps_of_def
                        cte_level_bits_def objBits_simps')
  apply (drule_tac x=crefa in spec)
  apply (rule conjI)
   apply clarsimp
   apply (rule_tac x=cref in exI, fastforce)
  apply clarsimp
  apply (rule_tac x=cref' in exI, fastforce)
  done


lemma setupReplyMaster_iflive'[wp]:
  "\<lbrace>if_live_then_nonz_cap'\<rbrace> setupReplyMaster t \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (simp add: setupReplyMaster_def locateSlot_conv)
  apply (wp setCTE_iflive' getCTE_wp')
  apply (clarsimp elim!: cte_wp_at_weakenE')
  done

lemma setupReplyMaster_global_refs[wp]:
  "\<lbrace>\<lambda>s. valid_global_refs' s \<and> thread \<notin> global_refs' s \<and> tcb_at' thread s
      \<and> ex_nonz_cap_to' thread s \<and> valid_objs' s\<rbrace>
    setupReplyMaster thread
   \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  apply (simp add: setupReplyMaster_def locateSlot_conv)
  apply (wp getCTE_wp')
  apply (clarsimp simp: capRange_def cte_wp_at_ctes_of objBits_simps)
  apply (clarsimp simp: ex_nonz_cap_to'_def cte_wp_at_ctes_of)
  apply (rename_tac "prev_cte")
  apply (case_tac prev_cte, simp)
  apply (frule(1) ctes_of_valid_cap')
  apply (drule(1) valid_global_refsD_with_objSize)+
  apply (clarsimp simp: valid_cap'_def objBits_simps obj_at'_def projectKOs
                 split: capability.split_asm)
  done

crunch setupReplyMaster
  for valid_arch'[wp]: "valid_arch_state'"
  (wp: crunch_wps simp: crunch_simps)

lemma ex_nonz_tcb_cte_caps':
  "\<lbrakk>ex_nonz_cap_to' t s; tcb_at' t s; valid_objs' s; sl \<in> dom tcb_cte_cases\<rbrakk> \<Longrightarrow>
   ex_cte_cap_to' (t + sl) s"
  apply (clarsimp simp: ex_nonz_cap_to'_def ex_cte_cap_to'_def cte_wp_at_ctes_of)
  apply (subgoal_tac "s \<turnstile>' cteCap cte")
   apply (rule_tac x=cref in exI, rule_tac x=cte in exI)
   apply (clarsimp simp: valid_cap'_def obj_at'_def projectKOs dom_def
                  split: cte.split_asm capability.split_asm)
  apply (case_tac cte)
  apply (clarsimp simp: ctes_of_valid_cap')
  done

lemma ex_nonz_cap_not_global':
  "\<lbrakk>ex_nonz_cap_to' t s; valid_objs' s; valid_global_refs' s\<rbrakk> \<Longrightarrow>
   t \<notin> global_refs' s"
  apply (clarsimp simp: ex_nonz_cap_to'_def cte_wp_at_ctes_of)
  apply (frule(1) valid_global_refsD')
  apply clarsimp
  apply (drule orthD1, erule (1) subsetD)
  apply (subgoal_tac "s \<turnstile>' cteCap cte")
   apply (fastforce simp: valid_cap'_def capRange_def capAligned_def
                         is_aligned_no_overflow
                  split: cte.split_asm capability.split_asm)
  apply (case_tac cte)
  apply (clarsimp simp: ctes_of_valid_cap')
  done

crunch setupReplyMaster
  for typ_at'[wp]: "\<lambda>s. P (typ_at' T p s)"
  (wp: crunch_wps simp: crunch_simps)

lemma setCTE_irq_handlers':
  "\<lbrace>\<lambda>s. valid_irq_handlers' s \<and> (\<forall>irq. cteCap cte = IRQHandlerCap irq \<longrightarrow> irq_issued' irq s)\<rbrace>
     setCTE ptr cte
   \<lbrace>\<lambda>rv. valid_irq_handlers'\<rbrace>"
  apply (simp add: valid_irq_handlers'_def cteCaps_of_def irq_issued'_def)
  apply (wp hoare_use_eq [where f=ksInterruptState, OF setCTE_ksInterruptState setCTE_ctes_of_wp])
  apply (auto simp: ran_def)
  done

lemma setupReplyMaster_irq_handlers'[wp]:
  "\<lbrace>valid_irq_handlers'\<rbrace> setupReplyMaster t \<lbrace>\<lambda>rv. valid_irq_handlers'\<rbrace>"
  apply (simp add: setupReplyMaster_def locateSlot_conv)
  apply (wp setCTE_irq_handlers' getCTE_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

crunch setupReplyMaster
  for irq_states'[wp]: valid_irq_states'
  and irqs_masked' [wp]: irqs_masked'
  and pred_tcb_at' [wp]: "pred_tcb_at' proj P t"
  and ksMachine[wp]: "\<lambda>s. P (ksMachineState s)"
  and pspace_domain_valid[wp]: "pspace_domain_valid"
  and ct_not_inQ[wp]: "ct_not_inQ"
  and ksCurDomain[wp]: "\<lambda>s. P (ksCurDomain s)"
  and ksCurThread[wp]: "\<lambda>s. P (ksCurThread s)"
  and ksIdlethread[wp]: "\<lambda>s. P (ksIdleThread s)"
  and ksDomSchedule[wp]: "\<lambda>s. P (ksDomSchedule s)"
  and scheduler_action[wp]: "\<lambda>s. P (ksSchedulerAction s)"
  and obj_at'_inQ[wp]: "obj_at' (inQ d p) t"
  and tcbDomain_inv[wp]: "obj_at' (\<lambda>tcb. P (tcbDomain tcb)) t"
  and tcbPriority_inv[wp]: "obj_at' (\<lambda>tcb. P (tcbPriority tcb)) t"
  and ready_queues[wp]: "\<lambda>s. P (ksReadyQueues s)"
  and ready_queuesL1[wp]: "\<lambda>s. P (ksReadyQueuesL1Bitmap s)"
  and ready_queuesL2[wp]: "\<lambda>s. P (ksReadyQueuesL2Bitmap s)"
  and ksDomScheduleIdx[wp]: "\<lambda>s. P (ksDomScheduleIdx s)"
  and gsUntypedZeroRanges[wp]: "\<lambda>s. P (gsUntypedZeroRanges s)"
  and tcbSchedPrevs_of[wp]: "\<lambda>s. P (tcbSchedPrevs_of s)"
  and tcbSchedNexts_of[wp]: "\<lambda>s. P (tcbSchedNexts_of s)"
  and valid_sched_pointers[wp]: valid_sched_pointers
  (wp: crunch_wps simp: crunch_simps rule: irqs_masked_lift)

lemma setupReplyMaster_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> setupReplyMaster t \<lbrace>\<lambda>_. valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def )
  apply (intro hoare_vcg_all_lift hoare_vcg_disj_lift)
  apply wp+
  done

lemma setupReplyMaster_urz[wp]:
  "\<lbrace>untyped_ranges_zero' and valid_mdb' and valid_objs'\<rbrace>
    setupReplyMaster t
  \<lbrace>\<lambda>rv. untyped_ranges_zero'\<rbrace>"
  apply (simp add: setupReplyMaster_def locateSlot_conv)
  apply (rule hoare_pre)
   apply (wp untyped_ranges_zero_lift getCTE_wp' | simp)+
  apply (clarsimp simp: cte_wp_at_ctes_of fun_upd_def[symmetric])
  apply (subst untyped_ranges_zero_fun_upd, assumption, simp_all)
  apply (clarsimp simp: cteCaps_of_def untypedZeroRange_def Let_def isCap_simps)
  done

lemma not_ioport_cap_cap_ioports'[simp]:"\<not>isArchIOPortCap cap \<Longrightarrow> cap_ioports' cap = {}"
  by (clarsimp simp: isCap_simps cap_ioports'_def split: capability.splits arch_capability.splits)

lemma not_ioport_cap_safe_ioport_insert'[simp]: "\<not>isArchIOPortCap cap \<Longrightarrow> safe_ioport_insert' cap cap' s"
  by (clarsimp simp: safe_ioport_insert'_def isCap_simps)

lemma setupReplyMaster_invs'[wp]:
  "\<lbrace>invs' and tcb_at' t and ex_nonz_cap_to' t\<rbrace>
     setupReplyMaster t
   \<lbrace>\<lambda>rv. invs'\<rbrace>"
  supply raw_tcb_cte_cases_simps[simp] (* FIXME arch-split: legacy, try use tcb_cte_cases_neqs *)
  apply (simp add: invs'_def valid_state'_def)
  apply (rule hoare_pre)
   apply (wp setupReplyMaster_valid_pspace' sch_act_wf_lift tcb_in_cur_domain'_lift ct_idle_or_in_cur_domain'_lift
             valid_queues_lift cur_tcb_lift hoare_vcg_disj_lift sym_heap_sched_pointers_lift
             valid_bitmaps_lift
             valid_irq_node_lift | simp)+
  apply (clarsimp simp: ex_nonz_tcb_cte_caps' valid_pspace'_def
                        objBits_simps' tcbReplySlot_def
                        ex_nonz_cap_not_global' dom_def)
  done

lemma setupReplyMaster_cte_wp_at'':
  "\<lbrace>cte_wp_at' (\<lambda>cte. P (cteCap cte)) p and K (\<not> P NullCap)\<rbrace>
     setupReplyMaster t
   \<lbrace>\<lambda>rv s. cte_wp_at' (P \<circ> cteCap) p s\<rbrace>"
  apply (simp add: setupReplyMaster_def locateSlot_conv tree_cte_cteCap_eq)
  apply (wp getCTE_wp')
  apply (fastforce simp: cte_wp_at_ctes_of cteCaps_of_def)
  done

lemmas setupReplyMaster_cte_wp_at' = setupReplyMaster_cte_wp_at''[unfolded o_def]

lemma setupReplyMaster_cap_to'[wp]:
  "\<lbrace>ex_nonz_cap_to' p\<rbrace> setupReplyMaster t \<lbrace>\<lambda>rv. ex_nonz_cap_to' p\<rbrace>"
  apply (simp add: ex_nonz_cap_to'_def)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_ex_lift setupReplyMaster_cte_wp_at')
  apply clarsimp
  done

definition
  is_arch_update' :: "capability \<Rightarrow> cte \<Rightarrow> bool"
where
  "is_arch_update' cap cte \<equiv> isArchObjectCap cap \<and> capMasterCap cap = capMasterCap (cteCap cte)"

lemma mdb_next_pres:
  "\<lbrakk> m p = Some v;
 mdbNext (cteMDBNode x) = mdbNext (cteMDBNode v) \<rbrakk> \<Longrightarrow>
  m(p \<mapsto> x) \<turnstile> a \<leadsto> b = m \<turnstile> a \<leadsto> b"
  by (simp add: mdb_next_unfold)

lemma mdb_next_trans_next_pres:
  "\<lbrakk> m p = Some v; mdbNext (cteMDBNode x) = mdbNext (cteMDBNode v) \<rbrakk> \<Longrightarrow>
   m(p \<mapsto> x) \<turnstile> a \<leadsto>\<^sup>+ b = m \<turnstile> a \<leadsto>\<^sup>+ b"
  apply (rule iffI)
   apply (erule trancl_induct)
    apply (fastforce simp: mdb_next_pres)
   apply (erule trancl_trans)
   apply (rule r_into_trancl)
   apply (fastforce simp: mdb_next_pres)
  apply (erule trancl_induct)
   apply (rule r_into_trancl)
   apply (simp add: mdb_next_pres del: fun_upd_apply)
  apply (erule trancl_trans)
  apply (fastforce simp: mdb_next_pres simp del: fun_upd_apply)
  done

lemma mdb_next_rtrans_next_pres:
  "\<lbrakk> m p = Some v; mdbNext (cteMDBNode x) = mdbNext (cteMDBNode v) \<rbrakk> \<Longrightarrow>
   m(p \<mapsto> x) \<turnstile> a \<leadsto>\<^sup>* b = m \<turnstile> a \<leadsto>\<^sup>* b"
  by (safe; clarsimp simp: mdb_next_trans_next_pres
                       dest!: rtrancl_eq_or_trancl[THEN iffD1]
                      intro!: rtrancl_eq_or_trancl[THEN iffD2] mdb_next_trans_next_pres[THEN iffD1])


lemma arch_update_descendants':
  "\<lbrakk> is_arch_update' cap oldcte; m p = Some oldcte\<rbrakk> \<Longrightarrow>
  descendants_of' x (m(p \<mapsto> cteCap_update (\<lambda>_. cap) oldcte)) = descendants_of' x m"
  apply (erule same_master_descendants)
  apply (auto simp: is_arch_update'_def isCap_simps)
  done

lemma arch_update_setCTE_mdb:
  "\<lbrace>cte_wp_at' (is_arch_update' cap) p and cte_wp_at' ((=) oldcte) p and valid_mdb'\<rbrace>
  setCTE p (cteCap_update (\<lambda>_. cap) oldcte)
  \<lbrace>\<lambda>rv. valid_mdb'\<rbrace>"
  apply (simp add: valid_mdb'_def)
  apply wp
  apply (clarsimp simp: valid_mdb_ctes_def cte_wp_at_ctes_of simp del: fun_upd_apply)
  apply (rule conjI)
   apply (rule valid_dlistI)
    apply (fastforce split: if_split_asm elim: valid_dlistE)
   apply (fastforce split: if_split_asm elim: valid_dlistE)
  apply (rule conjI)
   apply (clarsimp simp: no_0_def)
  apply (rule conjI)
   apply (simp add: mdb_chain_0_def mdb_next_trans_next_pres)
   apply blast
  apply (rule conjI)
   apply (cases oldcte)
   apply (clarsimp simp: valid_badges_def valid_arch_badges_def mdb_next_pres simp del: fun_upd_apply)
   apply (clarsimp simp: is_arch_update'_def)
   apply (clarsimp split: if_split_asm)
     apply (clarsimp simp: isCap_simps)
    prefer 2
    subgoal by fastforce
   apply (erule_tac x=pa in allE)
   apply (erule_tac x=p in allE)
   apply simp
   apply (simp add: sameRegionAs_def3)
   apply (rule conjI)
    apply (clarsimp simp: isCap_simps)
   apply (clarsimp simp: isCap_simps)
  apply (rule conjI)
   apply (clarsimp simp: caps_contained'_def simp del: fun_upd_apply)
   apply (cases oldcte)
   apply (clarsimp simp: is_arch_update'_def)
   apply (frule capMaster_untypedRange)
   apply (frule capMaster_capRange)
   apply (drule sym [where s="capMasterCap cap"])
   apply (frule masterCap.intro)
   apply (clarsimp simp: masterCap.isUntypedCap split: if_split_asm)
      subgoal by fastforce
     subgoal by fastforce
    apply (erule_tac x=pa in allE)
    apply (erule_tac x=p in allE)
    apply fastforce
   apply (erule_tac x=pa in allE)
   apply (erule_tac x=p' in allE)
   subgoal by fastforce
  apply (rule conjI)
   apply (cases oldcte)
   apply (clarsimp simp: is_arch_update'_def)
   apply (clarsimp simp: mdb_chunked_def mdb_next_trans_next_pres simp del: fun_upd_apply)
   apply (drule sym [where s="capMasterCap cap"])
   apply (frule masterCap.intro)
   apply (clarsimp split: if_split_asm)
     apply (erule_tac x=p in allE)
     apply (erule_tac x=p' in allE)
     apply (clarsimp simp: masterCap.sameRegionAs)
     apply (simp add: masterCap.sameRegionAs is_chunk_def mdb_next_trans_next_pres
                      mdb_next_rtrans_next_pres mdb_chunked_arch_assms_def)
     subgoal by fastforce
    apply (erule_tac x=pa in allE)
    apply (erule_tac x=p in allE)
    apply (clarsimp simp: masterCap.sameRegionAs)
    apply (simp add: masterCap.sameRegionAs is_chunk_def mdb_next_trans_next_pres
                     mdb_next_rtrans_next_pres)
    subgoal by fastforce
   apply (erule_tac x=pa in allE)
   apply (erule_tac x=p' in allE)
   apply clarsimp
   apply (simp add: masterCap.sameRegionAs is_chunk_def mdb_next_trans_next_pres
                    mdb_next_rtrans_next_pres)
   subgoal by fastforce
  apply (rule conjI)
   apply (clarsimp simp: is_arch_update'_def untyped_mdb'_def arch_update_descendants'
                   simp del: fun_upd_apply)
   apply (cases oldcte)
   apply clarsimp
   apply (clarsimp split: if_split_asm)
    apply (clarsimp simp: isCap_simps)
   apply (frule capMaster_isUntyped)
   apply (drule capMaster_capRange)
   apply simp
  apply (rule conjI)
   apply (clarsimp simp: untyped_inc'_def arch_update_descendants'
                   simp del: fun_upd_apply)
   apply (cases oldcte)
   apply (clarsimp simp: is_arch_update'_def)
   apply (drule capMaster_untypedRange)
   apply (clarsimp split: if_split_asm)
     apply (clarsimp simp: isCap_simps)
    apply (clarsimp simp: isCap_simps)
   apply (erule_tac x=pa in allE)
   apply (erule_tac x=p' in allE)
   apply clarsimp
  apply (rule conjI)
   apply (cases oldcte)
   apply (clarsimp simp: valid_nullcaps_def is_arch_update'_def isCap_simps)
  apply (rule conjI)
   apply (cases oldcte)
   apply (clarsimp simp: ut_revocable'_def is_arch_update'_def isCap_simps)
  apply (rule conjI)
   apply (clarsimp simp: class_links_def simp del: fun_upd_apply)
   apply (cases oldcte)
   apply (clarsimp simp: is_arch_update'_def mdb_next_pres)
   apply (drule capMaster_capClass)
   apply (clarsimp split: if_split_asm)
   apply fastforce
  apply (rule conjI)
   apply (erule(1) distinct_zombies_sameMasterE)
   apply (clarsimp simp: is_arch_update'_def)
  apply (clarsimp simp: irq_control_def)
  apply (cases oldcte)
  apply (subgoal_tac "cap \<noteq> IRQControlCap")
   prefer 2
   apply (clarsimp simp: is_arch_update'_def isCap_simps)
  apply (rule conjI)
   apply clarsimp
  apply (simp add: reply_masters_rvk_fb_def)
  apply (erule ball_ran_fun_updI)
  apply (clarsimp simp add: is_arch_update'_def isCap_simps)
  done

lemma capMaster_zobj_refs:
  "capMasterCap c = capMasterCap c' \<Longrightarrow> zobj_refs' c = zobj_refs' c'"
  by (simp add: capMasterCap_def split: capability.splits arch_capability.splits)

lemma cte_refs_Master:
  "cte_refs' (capMasterCap cap) = cte_refs' cap"
  by (rule ext, simp add: capMasterCap_def split: capability.split)

lemma zobj_refs_Master:
  "zobj_refs' (capMasterCap cap) = zobj_refs' cap"
  by (simp add: capMasterCap_def split: capability.split)

lemma capMaster_same_refs:
  "capMasterCap a = capMasterCap b \<Longrightarrow> cte_refs' a = cte_refs' b \<and> zobj_refs' a = zobj_refs' b"
  apply (rule conjI)
   apply (rule master_eqI, rule cte_refs_Master, simp)
  apply (rule master_eqI, rule zobj_refs_Master, simp)
  done

lemma arch_update_setCTE_iflive:
  "\<lbrace>cte_wp_at' (is_arch_update' cap) p and cte_wp_at' ((=) oldcte) p and if_live_then_nonz_cap'\<rbrace>
  setCTE p (cteCap_update (\<lambda>_. cap) oldcte)
  \<lbrace>\<lambda>rv. if_live_then_nonz_cap'\<rbrace>"
  apply (wp setCTE_iflive')
  apply (clarsimp simp: cte_wp_at_ctes_of is_arch_update'_def dest!: capMaster_zobj_refs)
  done

lemma arch_update_setCTE_ifunsafe:
  "\<lbrace>cte_wp_at' (is_arch_update' cap) p and cte_wp_at' ((=) oldcte) p and if_unsafe_then_cap'\<rbrace>
  setCTE p (cteCap_update (\<lambda>_. cap) oldcte)
  \<lbrace>\<lambda>rv s. if_unsafe_then_cap' s\<rbrace>"
  apply (clarsimp simp: ifunsafe'_def2 cte_wp_at_ctes_of pred_conj_def)
  apply (rule hoare_lift_Pf2 [where f=irq_node'])
   prefer 2
   apply wp
  apply wp
  apply (clarsimp simp: cte_wp_at_ctes_of is_arch_update'_def)
  apply (frule capMaster_same_refs)
  apply clarsimp
  apply (rule conjI, clarsimp)
   apply (erule_tac x=p in allE)
   apply clarsimp
   apply (erule impE)
    apply clarsimp
   apply clarsimp
   apply (rule_tac x=cref' in exI)
   apply clarsimp
  apply clarsimp
  apply (erule_tac x=cref in allE)
  apply clarsimp
  apply (rule_tac x=cref' in exI)
  apply clarsimp
  done

lemma setCTE_cur_tcb[wp]:
  "\<lbrace>cur_tcb'\<rbrace> setCTE ptr val \<lbrace>\<lambda>rv. cur_tcb'\<rbrace>"
  by (wp cur_tcb_lift)

lemma setCTE_vms'[wp]:
  "\<lbrace>valid_machine_state'\<rbrace> setCTE ptr val \<lbrace>\<lambda>rv. valid_machine_state'\<rbrace>"
  apply (simp add: valid_machine_state'_def pointerInUserData_def pointerInDeviceData_def )
  apply (intro hoare_vcg_all_lift hoare_vcg_disj_lift)
  apply wp+
  done

lemma arch_update_setCTE_invs:
  "\<lbrace>cte_wp_at' (is_arch_update' cap) p and cte_wp_at' ((=) oldcte) p and invs' and valid_cap' cap\<rbrace>
  setCTE p (cteCap_update (\<lambda>_. cap) oldcte)
  \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
  apply (wp arch_update_setCTE_mdb valid_queues_lift sch_act_wf_lift tcb_in_cur_domain'_lift ct_idle_or_in_cur_domain'_lift
             arch_update_setCTE_iflive arch_update_setCTE_ifunsafe
             valid_irq_node_lift setCTE_typ_at' setCTE_irq_handlers'
             setCTE_pred_tcb_at' irqs_masked_lift
             hoare_vcg_disj_lift untyped_ranges_zero_lift valid_bitmaps_lift
           | simp add: pred_tcb_at'_def)+
  apply (clarsimp simp: valid_global_refs'_def is_arch_update'_def fun_upd_def[symmetric]
                        cte_wp_at_ctes_of isCap_simps untyped_ranges_zero_fun_upd)
  apply (frule capMaster_eq_capBits_eq)
  apply (frule capMaster_isUntyped)
  apply (frule capMaster_capRange)
  apply (clarsimp simp: valid_refs'_def valid_cap_sizes'_def)
  apply (subst untyped_ranges_zero_delta[where xs="[p]"], assumption, simp_all)
   apply (clarsimp simp: ran_restrict_map_insert cteCaps_of_def
                         untypedZeroRange_def Let_def
                         isCap_simps(1-11)[where v="ArchObjectCap ac" for ac])
  apply (rule conjI, fastforce)
  apply fastforce
  done

definition
  "safe_parent_for' m p cap \<equiv>
     \<exists>parent node. m p = Some (CTE parent node) \<and> sameRegionAs parent cap \<and>
                   ((\<exists>irq. cap = IRQHandlerCap irq) \<and> parent = IRQControlCap \<and>
                           (\<forall>p n'. m p \<noteq> Some (CTE cap n'))
                    \<or> isUntypedCap parent \<and> descendants_of' p m = {} \<and> capRange cap \<noteq> {} \<and>
                      capBits cap \<le> capBits parent
                    \<or> isArchIOPortCap cap \<and> isIOPortControlCap' parent \<and>
                      (\<forall>p n'. m p \<noteq> Some (CTE cap n')))"

definition
  "is_simple_cap' cap \<equiv>
  cap \<noteq> NullCap \<and>
  cap \<noteq> IRQControlCap \<and>
  \<not> isUntypedCap cap \<and>
  \<not> isReplyCap cap \<and>
  \<not> isEndpointCap cap \<and>
  \<not> isNotificationCap cap \<and>
  \<not> isThreadCap cap \<and>
  \<not> isCNodeCap cap \<and>
  \<not> isZombie cap \<and>
  \<not> isArchPageCap cap \<and>
  \<not> isIOPortControlCap' cap"
end

(* FIXME: duplicated *)
locale mdb_insert_simple = mdb_insert +
  assumes safe_parent: "safe_parent_for' m src c'"
  assumes simple: "is_simple_cap' c'"
  assumes arch_mdb_assert: "arch_mdb_assert m"
begin
interpretation Arch . (*FIXME: arch-split*)
lemma dest_no_parent_n:
  "n \<turnstile> dest \<rightarrow> p = False"
  using src simple safe_parent
  apply clarsimp
  apply (erule subtree.induct)
   prefer 2
   apply simp
  apply (clarsimp simp: parentOf_def mdb_next_unfold n_dest new_dest_def n)
  apply (cases "mdbNext src_node = dest")
   apply (subgoal_tac "m \<turnstile> src \<leadsto> dest")
    apply simp
   apply (subst mdb_next_unfold)
   apply (simp add: src)
  apply (clarsimp simp: isMDBParentOf_CTE)
  apply (clarsimp simp: is_simple_cap'_def Retype_H.isCapRevocable_def X64_H.isCapRevocable_def
                 split: capability.splits arch_capability.splits)
     apply (cases c', auto simp: isCap_simps)[1]
    apply (clarsimp simp add: sameRegionAs_def2)
    apply (clarsimp simp: isCap_simps)
    apply (clarsimp simp: safe_parent_for'_def isCap_simps)
   apply (cases c', auto simp: isCap_simps)[1]
  apply (clarsimp simp add: sameRegionAs_def2)
  apply (clarsimp simp: isCap_simps)
  apply (clarsimp simp: safe_parent_for'_def isCap_simps)
  done

lemma src_node_revokable [simp]:
  "mdbRevocable src_node"
  using safe_parent ut_rev src
  apply (clarsimp simp add: safe_parent_for'_def)
  apply (erule disjE)
   apply clarsimp
   apply (erule irq_revocable, rule irq_control)
  apply (erule disjE)
   apply (clarsimp simp: ut_revocable'_def)
  apply (clarsimp simp: isCap_simps)
  apply (erule ioport_revocable, rule arch_mdb_assert)
  done

lemma new_child [simp]:
  "isMDBParentOf new_src new_dest"
  using safe_parent ut_rev src
  apply (simp add: new_src_def new_dest_def isMDBParentOf_def)
  apply (clarsimp simp: safe_parent_for'_def)
  apply (auto simp: isCap_simps)
  done

lemma n_dest_child:
  "n \<turnstile> src \<rightarrow> dest"
  apply (rule subtree.direct_parent)
    apply (simp add: n_direct_eq)
   apply simp
  apply (clarsimp simp: parentOf_def src dest n)
  done

lemma parent_m_n:
  assumes "m \<turnstile> p \<rightarrow> p'"
  shows "if p' = src then n \<turnstile> p \<rightarrow> dest \<and> n \<turnstile> p \<rightarrow> p' else n \<turnstile> p \<rightarrow> p'" using assms
proof induct
  case (direct_parent c)
  thus ?case
    apply (cases "p = src")
     apply simp
     apply (rule conjI, clarsimp)
     apply clarsimp
     apply (rule subtree.trans_parent [where c'=dest])
        apply (rule n_dest_child)
       apply (simp add: n_direct_eq)
      apply simp
     apply (clarsimp simp: parentOf_def n)
     apply (clarsimp simp: new_src_def src)
    apply simp
    apply (subgoal_tac "n \<turnstile> p \<rightarrow> c")
     prefer 2
     apply (rule subtree.direct_parent)
       apply (clarsimp simp add: n_direct_eq)
      apply simp
     apply (clarsimp simp: parentOf_def n)
     apply (fastforce simp: new_src_def src)
    apply clarsimp
    apply (erule subtree_trans)
    apply (rule n_dest_child)
    done
next
  case (trans_parent c d)
  thus ?case
    apply -
    apply (cases "c = dest", simp)
    apply (cases "d = dest", simp)
    apply (cases "c = src")
     apply clarsimp
     apply (erule subtree.trans_parent [where c'=dest])
       apply (clarsimp simp add: n_direct_eq)
      apply simp
     apply (clarsimp simp: parentOf_def n)
     apply (rule conjI, clarsimp)
     apply (clarsimp simp: new_src_def src)
    apply clarsimp
    apply (subgoal_tac "n \<turnstile> p \<rightarrow> d")
     apply clarsimp
     apply (erule subtree_trans, rule n_dest_child)
    apply (erule subtree.trans_parent)
      apply (simp add: n_direct_eq)
     apply simp
    apply (clarsimp simp: parentOf_def n)
    apply (fastforce simp: src new_src_def)
    done
qed

lemma n_to_dest [simp]:
  "n \<turnstile> p \<leadsto> dest = (p = src)"
  by (simp add: n_direct_eq)

lemma parent_n_m:
  assumes "n \<turnstile> p \<rightarrow> p'"
  shows "if p' = dest then p \<noteq> src \<longrightarrow> m \<turnstile> p \<rightarrow> src else m \<turnstile> p \<rightarrow> p'"
proof -
  from assms have [simp]: "p \<noteq> dest" by (clarsimp simp: dest_no_parent_n)
  from assms
  show ?thesis
  proof induct
    case (direct_parent c)
    thus ?case
      apply simp
      apply (rule conjI)
       apply clarsimp
      apply clarsimp
      apply (rule subtree.direct_parent)
        apply (simp add: n_direct_eq split: if_split_asm)
       apply simp
      apply (clarsimp simp: parentOf_def n src new_src_def split: if_split_asm)
      done
  next
    case (trans_parent c d)
    thus ?case
      apply clarsimp
      apply (rule conjI, clarsimp)
      apply (clarsimp split: if_split_asm)
      apply (simp add: n_direct_eq)
      apply (cases "p=src")
       apply simp
       apply (rule subtree.direct_parent, assumption, assumption)
       apply (clarsimp simp: parentOf_def n src new_src_def split: if_split_asm)
      apply clarsimp
      apply (erule subtree.trans_parent, assumption, assumption)
      apply (clarsimp simp: parentOf_def n src new_src_def split: if_split_asm)
     apply (erule subtree.trans_parent)
       apply (simp add: n_direct_eq split: if_split_asm)
      apply assumption
     apply (clarsimp simp: parentOf_def n src new_src_def split: if_split_asm)
     done
 qed
qed


lemma descendants:
  "descendants_of' p n =
   (if src \<in> descendants_of' p m \<or> p = src
   then descendants_of' p m \<union> {dest} else descendants_of' p m)"
  apply (rule set_eqI)
  apply (simp add: descendants_of'_def)
  apply (fastforce dest!: parent_n_m dest: parent_m_n simp: n_dest_child split: if_split_asm)
  done

end

declare if_split [split del]

lemma setUntypedCapAsFull_safe_parent_for':
  "\<lbrace>\<lambda>s. safe_parent_for' (ctes_of s) slot a \<and> cte_wp_at' ((=) srcCTE) slot s\<rbrace>
   setUntypedCapAsFull (cteCap srcCTE) c' slot
   \<lbrace>\<lambda>rv s. safe_parent_for' (ctes_of s) slot a\<rbrace>"
  apply (clarsimp simp:safe_parent_for'_def setUntypedCapAsFull_def split:if_splits)
  apply (intro conjI impI)
   apply (wp updateCap_ctes_of_wp)
   apply (subgoal_tac "mdb_inv_preserve (ctes_of s)
     (modify_map (ctes_of s) slot
     (cteCap_update (\<lambda>_. capFreeIndex_update (\<lambda>_. max_free_index (capBlockSize c')) (cteCap srcCTE))))")
     apply (frule mdb_inv_preserve.descendants_of[where p = slot])
     apply (clarsimp simp: X64.isCap_simps modify_map_def cte_wp_at_ctes_of simp del: fun_upd_apply)
     apply (clarsimp cong:sameRegionAs_update_untyped)
   apply (rule mdb_inv_preserve_updateCap)
     apply (simp add:cte_wp_at_ctes_of)
   apply simp
 apply wp
 apply simp
done

lemma maskedAsFull_revokable_safe_parent:
  "\<lbrakk>is_simple_cap' c'; safe_parent_for' m p c'; m p = Some cte;
    cteCap cte = (maskedAsFull src_cap' a)\<rbrakk>
   \<Longrightarrow> isCapRevocable c' (maskedAsFull src_cap' a) = isCapRevocable c' src_cap'"
   apply (clarsimp simp:isCapRevocable_def X64_H.isCapRevocable_def maskedAsFull_def
                  split:if_splits capability.splits)
   apply (intro allI impI conjI)
     apply (clarsimp simp: X64.isCap_simps is_simple_cap'_def)+
   apply (rule conjI; clarsimp)
  done

context begin interpretation Arch . (*FIXME: arch-split*)

(* FIXME arch-split: generic statement, arch specific proof *)
lemma setUntypedCapAsFull_archMDBAssertions[wp]:
  "setUntypedCapAsFull src_cap cap p \<lbrace>archMDBAssertions\<rbrace>"
  unfolding setUntypedCapAsFull_def archMDBAssertions_def updateCap_def
  apply (wpsimp wp: getCTE_wp')
  apply (rename_tac cte, case_tac cte, rename_tac cte_cap node)
  apply (clarsimp simp: arch_mdb_assert_def cte_wp_at_ctes_of isCap_simps split: if_split_asm)
  done

lemma cteInsert_simple_corres:
  assumes "cap_relation c c'" "src' = cte_map src" "dest' = cte_map dest"
  notes trans_state_update'[symmetric,simp]
  shows "corres dc
        (valid_objs and pspace_distinct and pspace_aligned and
         valid_mdb and valid_list and K (src\<noteq>dest) and
         cte_wp_at (\<lambda>c. c=cap.NullCap) dest and
         K (is_simple_cap c) and
         (\<lambda>s. cte_wp_at (safe_parent_for (cdt s) src c) src s) and valid_arch_state)
        (pspace_distinct' and pspace_aligned' and valid_mdb' and valid_cap' c' and
         K (is_simple_cap' c') and
         cte_wp_at' (\<lambda>c. cteCap c=NullCap) dest' and
         (\<lambda>s. safe_parent_for' (ctes_of s) src' c'))
        (cap_insert c src dest)
        (cteInsert c' src' dest')"
  (is "corres _ (?P and (\<lambda>s. cte_wp_at _ _ s) and valid_arch_state) (?P' and cte_wp_at' _ _ and _) _ _")
  using assms
  unfolding cap_insert_def cteInsert_def
  supply subst_all [simp del]
  apply simp
  apply (rule corres_stateAssert_add_assertion[rotated])
   apply (rule archMDBAssertions_cross; simp add: valid_mdb_def)
  apply (rule corres_guard_imp)
    apply (rule corres_split[OF get_cap_corres])
      apply (rule corres_split[OF get_cap_corres])
        apply (rule_tac F="cteCap oldCTE = NullCap" in corres_gen_asm2)
        apply simp
        apply (rule_tac P="?P and cte_at dest and
                            (\<lambda>s. cte_wp_at (safe_parent_for (cdt s) src c) src s) and
                            cte_wp_at ((=) src_cap) src" and
                        Q="?P' and archMDBAssertions and
                           cte_wp_at' ((=) oldCTE) (cte_map dest) and
                           cte_wp_at' ((=) srcCTE) (cte_map src) and
                           (\<lambda>s. safe_parent_for' (ctes_of s) src' c')"
                        in corres_assert_assume)
         prefer 2
         apply (clarsimp simp: cte_wp_at_ctes_of valid_mdb'_def valid_mdb_ctes_def valid_nullcaps_def)
         apply (case_tac oldCTE)
         apply (simp add: initMDBNode_def)
         apply (erule allE)+
         apply (erule (1) impE)
         apply (simp add: nullPointer_def)
        apply (rule corres_guard_imp)
          apply (rule_tac R="\<lambda>r. ?P and cte_at dest and
                            (\<lambda>s. cte_wp_at (safe_parent_for (cdt s) src c) src s) and
                            cte_wp_at ((=) (masked_as_full src_cap c)) src" and
                        R'="\<lambda>r. ?P' and archMDBAssertions and cte_wp_at' ((=) oldCTE) (cte_map dest)
           and cte_wp_at' ((=) (CTE (maskedAsFull (cteCap srcCTE) c') (cteMDBNode srcCTE))) (cte_map src)
           and (\<lambda>s. safe_parent_for' (ctes_of s) src' c')"
                        in corres_split[where r'=dc])
             apply (rule setUntypedCapAsFull_corres)
                  apply simp+
            apply (rule corres_stronger_no_failI)
             apply (rule no_fail_pre, wp hoare_weak_lift_imp)
             apply (clarsimp simp: cte_wp_at_ctes_of valid_mdb'_def valid_mdb_ctes_def)
             apply (erule_tac valid_dlistEn[where p = "cte_map src"])
               apply (simp+)[3]
            apply (clarsimp simp: corres_underlying_def state_relation_def
                                  in_monad valid_mdb'_def valid_mdb_ctes_def)
            apply (drule (18) set_cap_not_quite_corres)
             apply (rule refl)
            apply (elim conjE exE)
            apply (rule bind_execI, assumption)
            apply (subgoal_tac "mdb_insert_abs (cdt a) src dest")
             prefer 2
             apply (clarsimp simp: cte_wp_at_caps_of_state valid_mdb_def2)
             apply (rule mdb_insert_abs.intro)
               apply clarsimp
              apply (erule (1) mdb_cte_at_Null_None)
             apply (erule (1) mdb_cte_at_Null_descendants)
            apply (subgoal_tac "no_mloop (cdt a)")
             prefer 2
             apply (simp add: valid_mdb_def)
            apply (clarsimp simp: exec_gets update_cdt_def bind_assoc set_cdt_def
                                  exec_get exec_put set_original_def modify_def
                        simp del: fun_upd_apply

                   | (rule bind_execI[where f="cap_insert_ext x y z x' y'" for x y z x' y'], clarsimp simp: mdb_insert_abs.cap_insert_ext_det_def2 update_cdt_list_def set_cdt_list_def put_def simp del: fun_upd_apply) | rule refl)+

            apply (clarsimp simp: put_def state_relation_def simp del: fun_upd_apply)
            apply (drule updateCap_stuff)
            apply clarsimp
            apply (drule (3) updateMDB_the_lot', simp only: no_0_modify_map, simp only:, elim conjE)
            apply (drule (3) updateMDB_the_lot', simp only: no_0_modify_map, simp only:, elim conjE)
            apply (drule (3) updateMDB_the_lot', simp only: no_0_modify_map, simp only:, elim conjE)
            apply clarsimp
            apply (thin_tac "gsCNodes t = p" for t p)+
            apply (thin_tac "ksMachineState t = p" for t p)+
            apply (thin_tac "ksCurThread t = p" for t p)+
            apply (thin_tac "ksWorkUnitsCompleted t = p" for t p)+
            apply (thin_tac "ksIdleThread t = p" for t p)+
            apply (thin_tac "ksReadyQueues t = p" for t p)+
            apply (thin_tac "ksSchedulerAction t = p" for t p)+
            apply (thin_tac "cur_thread t = p" for t p)+
            apply (thin_tac "domain_index t = p" for t p)+
            apply (thin_tac "domain_time t = p" for t p)+
            apply (thin_tac "cur_domain t = p" for t p)+
            apply (thin_tac "scheduler_action t = p" for t p)+
            apply (thin_tac "ready_queues t = p" for t p)+
            apply (thin_tac "idle_thread t = p" for t p)+
            apply (thin_tac "machine_state t = p" for t p)+
            apply (thin_tac "work_units_completed t = p" for t p)+
            apply (thin_tac "ksArchState t = p" for t p)+
            apply (thin_tac "gsUserPages t = p" for t p)+
            apply (thin_tac "ksCurDomain t = p" for t p)+
            apply (thin_tac "ksInterruptState t = p" for t p)+
            apply (thin_tac "ksDomScheduleIdx t = p" for t p)+
            apply (thin_tac "ksDomainTime t = p" for t p)+
            apply (thin_tac "ksDomSchedule t = p" for t p)+
            apply (thin_tac "ctes_of t = p" for t p)+
            apply (thin_tac "pspace_relation t p" for t p)+
            apply (thin_tac "interrupt_state_relation s t p" for s t p)+
            apply (thin_tac "sched_act_relation t p" for t p)+
            apply (thin_tac "ready_queues_relation t p" for t p)+
            apply (rule conjI)
             subgoal by (clarsimp simp: ghost_relation_typ_at set_cap_a_type_inv data_at_def)
            apply (clarsimp simp: cte_wp_at_ctes_of nullPointer_def prev_update_modify_mdb_relation)
            apply (subgoal_tac "cte_map dest \<noteq> 0")
             prefer 2
             apply (clarsimp simp: valid_mdb'_def
                                   valid_mdb_ctes_def no_0_def)
            apply (subgoal_tac "cte_map src \<noteq> 0")
             prefer 2
             apply (clarsimp simp: valid_mdb'_def valid_mdb_ctes_def no_0_def)
            apply (subgoal_tac "should_be_parent_of src_cap (is_original_cap a src) c (is_cap_revocable c src_cap) = True")
             prefer 2
             apply (subst should_be_parent_of_masked_as_full[symmetric])
             apply (subst safe_parent_is_parent)
                apply ((simp add: cte_wp_at_caps_of_state)+)[4]
            apply (subst conj_assoc[symmetric])
            apply (rule conjI)
             defer
             apply (clarsimp simp: modify_map_apply)
             apply (clarsimp simp: revokable_relation_def simp del: fun_upd_apply)
             apply (simp split: if_split)
             apply (rule conjI)
              apply clarsimp
              apply (subgoal_tac "mdbRevocable node = isCapRevocable c' (cteCap srcCTE)")
               prefer 2
               apply (case_tac oldCTE)
               apply (clarsimp simp add: const_def modify_map_def split: if_split_asm)
              apply clarsimp
              apply (rule is_cap_revocable_eq, assumption, assumption)
               apply (subst same_region_as_relation [symmetric])
                 prefer 3
                 apply (rule safe_parent_same_region)
                 apply (simp add: cte_wp_at_caps_of_state)
                apply assumption
               apply assumption
              apply (clarsimp simp: cte_wp_at_def is_simple_cap_def)
             apply clarsimp
             apply (case_tac srcCTE)
             apply (case_tac oldCTE)
             apply clarsimp
             apply (subgoal_tac "\<exists>cap' node'. ctes_of b (cte_map (aa,bb)) = Some (CTE cap' node')")
              prefer 2
              subgoal by (clarsimp simp: modify_map_def split: if_split_asm)
             apply clarsimp
             apply (drule set_cap_caps_of_state_monad)+
             apply (subgoal_tac "null_filter (caps_of_state a) (aa,bb) \<noteq> None")
              prefer 2
              subgoal by (clarsimp simp: cte_wp_at_caps_of_state null_filter_def split: if_splits)
             apply clarsimp
             apply (subgoal_tac "cte_at (aa,bb) a")
              prefer 2
              apply (drule null_filter_caps_of_stateD)
              apply (erule cte_wp_at_weakenE, rule TrueI)
             apply (subgoal_tac "mdbRevocable node = mdbRevocable node'")
              apply clarsimp
             apply (subgoal_tac "cte_map (aa,bb) \<noteq> cte_map dest")
              subgoal by (clarsimp simp: modify_map_def split: if_split_asm)
             apply (erule (5) cte_map_inj)
            apply (wp set_untyped_cap_full_valid_objs set_untyped_cap_as_full_valid_mdb set_untyped_cap_as_full_valid_list
                      set_untyped_cap_as_full_cte_wp_at setUntypedCapAsFull_valid_cap
                      setUntypedCapAsFull_cte_wp_at setUntypedCapAsFull_safe_parent_for' | clarsimp | wps)+
          apply (clarsimp simp:cte_wp_at_caps_of_state )
         apply (case_tac oldCTE,clarsimp simp:cte_wp_at_ctes_of maskedAsFull_def)
        apply (wp getCTE_wp' get_cap_wp)+
    apply clarsimp
    subgoal by (fastforce elim: cte_wp_at_weakenE)
   subgoal by (clarsimp simp: cte_wp_at'_def)
  apply (case_tac "srcCTE")
  apply (rename_tac src_cap' src_node)
  apply (case_tac "oldCTE")
  apply (rename_tac dest_node)
  apply (clarsimp simp: in_set_cap_cte_at_swp)
  apply (subgoal_tac "cte_at src a \<and> safe_parent_for (cdt a) src c src_cap")
   prefer 2
   subgoal by (fastforce simp: cte_wp_at_def)
  apply (erule conjE)
  apply (subgoal_tac "mdb_insert (ctes_of b) (cte_map src) (maskedAsFull src_cap' c') src_node
                                  (cte_map dest) NullCap dest_node")
   prefer 2
   apply (rule mdb_insert.intro)
     apply (rule mdb_ptr.intro)
      apply (rule vmdb.intro, simp add: valid_mdb_ctes_def)
     apply (erule mdb_ptr_axioms.intro)
    apply (rule mdb_ptr.intro)
     apply (rule vmdb.intro, simp add: valid_mdb_ctes_def)
    apply (erule mdb_ptr_axioms.intro; assumption)
   apply (rule mdb_insert_axioms.intro; assumption?)
    apply (rule refl)
   apply (erule (5) cte_map_inj)
  apply (rule conjI)
   apply (simp (no_asm_simp) add: cdt_relation_def split: if_split)
   apply (intro impI allI)
   apply (frule mdb_insert_simple_axioms.intro)
     apply(clarsimp simp:cte_wp_at_ctes_of)
    apply (simp add: archMDBAssertions_def)
   apply (drule (1) mdb_insert_simple.intro)
   apply (drule_tac src_cap' = src_cap' in maskedAsFull_revokable_safe_parent[symmetric])
      apply simp+
   apply (subst mdb_insert_simple.descendants)
    apply simp
   apply (subst mdb_insert_abs.descendants_child, assumption)
   apply (frule set_cap_caps_of_state_monad)
   apply (subgoal_tac "cte_at (aa,bb) a")
    prefer 2
    apply (clarsimp simp: cte_wp_at_caps_of_state split: if_split_asm)
   apply (simp add: descendants_of_eq' cdt_relation_def split: if_split del: split_paired_All)
   apply clarsimp
   apply (drule (5) cte_map_inj)+
   apply simp
  (* exact reproduction of proof in cteInsert_corres,
     as it does not used is_derived *)
  apply(simp add: cdt_list_relation_def del: split_paired_All split_paired_Ex)
  apply(subgoal_tac "no_mloop (cdt a) \<and> finite_depth (cdt a)")
   prefer 2
   apply(simp add: finite_depth valid_mdb_def)
  apply(intro impI allI)
  apply(simp add: fun_upd_twist)

  apply(subst next_slot_eq[OF mdb_insert_abs.next_slot])
        apply(simp_all del: fun_upd_apply)
   apply(simp split: option.splits del: fun_upd_apply add: fun_upd_twist)
   apply(intro allI impI)
   apply(subgoal_tac "src \<noteq> (aa, bb)")
    prefer 2
    apply(rule notI)
    apply(simp add: valid_mdb_def no_mloop_weaken)
   apply(subst fun_upd_twist, simp, simp)

  apply(case_tac "ca=src")
   apply(simp)
   apply(clarsimp simp: modify_map_def)
   subgoal by(fastforce split: if_split_asm)
  apply(case_tac "ca = dest")
   apply(simp)
   apply(case_tac "next_slot src (cdt_list (a)) (cdt a)")
    apply(simp)
   apply(simp)
   apply(clarsimp simp: modify_map_def const_def)
   apply(simp split: if_split_asm)
     apply(drule_tac p="cte_map src" in valid_mdbD1')
       apply(simp)
      apply(simp add: valid_mdb'_def valid_mdb_ctes_def)
     apply(clarsimp)
    subgoal by(drule cte_map_inj_eq; simp)
   apply(erule_tac x="fst src" in allE)
   apply(erule_tac x="snd src" in allE)
   apply(fastforce)
  apply(simp)
  apply(case_tac "next_slot ca (cdt_list (a)) (cdt a)")
   apply(simp)
  apply(simp)
  apply(subgoal_tac "cte_at ca a")
   prefer 2
   subgoal by (rule cte_at_next_slot; simp)
  apply(clarsimp simp: modify_map_def const_def)
  apply(simp split: if_split_asm)
        subgoal by (drule cte_map_inj_eq; simp)
       apply(drule_tac p="cte_map src" in valid_mdbD1')
         apply(simp)
        apply(simp add: valid_mdb'_def valid_mdb_ctes_def)
       apply(clarsimp)
      apply(clarsimp)
      apply(case_tac z)
      apply(erule_tac x=aa in allE)
      apply(erule_tac x=bb in allE)
      apply(fastforce)
     subgoal by (drule cte_map_inj_eq; simp)
    subgoal by (drule cte_map_inj_eq; simp)
   subgoal by (drule cte_map_inj_eq; simp)
  by(fastforce)

declare if_split [split]

lemma sameRegion_capRange_sub:
  "sameRegionAs cap cap' \<Longrightarrow> capRange cap' \<subseteq> capRange cap"
  apply (clarsimp simp: sameRegionAs_def2 gen_isCap_Master capRange_Master)
  apply (erule disjE)
   apply (clarsimp dest!: capMaster_capRange)
  apply (erule disjE)
   apply fastforce
  apply (erule disjE;
         clarsimp simp: isCap_simps capRange_def split: if_split_asm)+
  done

lemma safe_parent_for_capRange_capBits:
  "\<lbrakk> safe_parent_for' m p cap; m p = Some cte \<rbrakk> \<Longrightarrow> capRange cap \<subseteq> capRange (cteCap cte)
    \<and> capBits cap \<le> capBits (cteCap cte)"
  apply (clarsimp simp: safe_parent_for'_def)
  apply (erule disjE)
   apply (clarsimp simp: capRange_def)
  by (auto simp: sameRegionAs_def2 isCap_simps capRange_def
                    capMasterCap_def capRange_Master objBits_simps
         split:capability.splits arch_capability.splits)

lemma safe_parent_Null:
  "\<lbrakk> m src = Some (CTE NullCap n); safe_parent_for' m src c' \<rbrakk> \<Longrightarrow> False"
  by (simp add: safe_parent_for'_def)

lemma notUntypedRange:
  "\<not>isUntypedCap cap \<Longrightarrow> untypedRange cap = {}"
  by (cases cap) (auto simp: isCap_simps)

lemma safe_parent_for_untypedRange:
  "\<lbrakk> safe_parent_for' m p cap; m p = Some cte \<rbrakk> \<Longrightarrow> untypedRange cap \<subseteq> untypedRange (cteCap cte)"
  apply (clarsimp simp: safe_parent_for'_def)
  apply (erule disjE)
   apply clarsimp
  apply (erule disjE)
   apply clarsimp
   apply (simp add: sameRegionAs_def2)
   apply (erule disjE)
    apply clarsimp
    apply (drule capMaster_untypedRange)
    apply blast
   apply (erule disjE)
    apply (clarsimp simp: capRange_Master untypedCapRange)
    apply (cases "isUntypedCap cap")
     apply (clarsimp simp: capRange_Master untypedCapRange)
     apply blast
    apply (drule notUntypedRange)
    apply simp
   apply (clarsimp simp: gen_isCap_Master isCap_simps)
  apply (clarsimp simp: isCap_simps)
  done

lemma safe_parent_for_capUntypedRange:
  "\<lbrakk> safe_parent_for' m p cap; m p = Some cte \<rbrakk> \<Longrightarrow> capRange cap \<subseteq> untypedRange (cteCap cte)"
  apply (clarsimp simp: safe_parent_for'_def)
  apply (erule disjE)
   apply (clarsimp simp: capRange_def)
  apply (erule disjE)
   apply clarsimp
   apply (simp add: sameRegionAs_def2)
   apply (erule disjE)
    apply clarsimp
    apply (frule capMaster_capRange)
    apply (clarsimp simp: capRange_Master untypedCapRange)
   apply (erule disjE)
    apply (clarsimp simp: capRange_Master untypedCapRange)
    apply blast
   apply (clarsimp simp: gen_isCap_Master isCap_simps)
  apply (clarsimp simp: capRange_def isCap_simps)
  done

lemma safe_parent_for_descendants':
  "\<lbrakk> safe_parent_for' m p cap; m p = Some (CTE pcap n); isUntypedCap pcap \<rbrakk> \<Longrightarrow> descendants_of' p m = {}"
  by (auto simp: safe_parent_for'_def isCap_simps)

lemma safe_parent_not_ep':
  "\<lbrakk> safe_parent_for' m p cap; m p = Some (CTE src_cap n) \<rbrakk> \<Longrightarrow> \<not>isEndpointCap src_cap"
  by (auto simp: safe_parent_for'_def isCap_simps)

lemma safe_parent_not_ntfn':
  "\<lbrakk> safe_parent_for' m p cap; m p = Some (CTE src_cap n) \<rbrakk> \<Longrightarrow> \<not>isNotificationCap src_cap"
  by (auto simp: safe_parent_for'_def isCap_simps)

lemma safe_parent_capClass:
  "\<lbrakk> safe_parent_for' m p cap; m p = Some (CTE src_cap n) \<rbrakk> \<Longrightarrow> capClass cap = capClass src_cap"
  by (auto simp: safe_parent_for'_def isCap_simps sameRegionAs_def2 capRange_Master capRange_def
           capMasterCap_def
           split: capability.splits arch_capability.splits)
end
locale mdb_insert_simple' = mdb_insert_simple +
  fixes n'
  defines  "n' \<equiv> modify_map n (mdbNext src_node) (cteMDBNode_update (mdbPrev_update (\<lambda>_. dest)))"
begin
interpretation Arch . (*FIXME: arch-split*)
lemma no_0_n' [intro!]: "no_0 n'" by (auto simp: n'_def)
lemmas n_0_simps' [iff] = no_0_simps [OF no_0_n']

lemmas no_0_m_prev [iff] = no_0_prev [OF no_0]
lemmas no_0_n_prev [iff] = no_0_prev [OF no_0_n']

lemma chain_n': "mdb_chain_0 n'"
  unfolding n'_def
  by (rule mdb_chain_0_modify_map_prev) (rule chain_n)

lemma no_loops_n': "no_loops n'" using chain_n' no_0_n'
  by (rule mdb_chain_0_no_loops)

lemma n_direct_eq':
  "n' \<turnstile> p \<leadsto> p' = (if p = src then p' = dest else
                 if p = dest then m \<turnstile> src \<leadsto> p'
                 else m \<turnstile> p \<leadsto> p')"
  by (simp add: n'_def n_direct_eq)

lemma dest_no_next_p:
  "m p = Some cte \<Longrightarrow> mdbNext (cteMDBNode cte) \<noteq> dest"
  using dest dest_prev
  apply (cases cte)
  apply (rule notI)
  apply (rule dlistEn, assumption)
   apply clarsimp
  apply clarsimp
  done

lemma dest_no_src_next [iff]:
  "mdbNext src_node \<noteq> dest"
  using src by (clarsimp dest!: dest_no_next_p)

lemma n_dest':
  "n' dest = Some new_dest"
  by (simp add: n'_def n modify_map_if new_dest_def)

lemma n'_trancl_eq:
  "n' \<turnstile> p \<leadsto>\<^sup>+ p' =
  (if p' = dest then p = src \<or> m \<turnstile> p \<leadsto>\<^sup>+ src
   else if p = dest then m \<turnstile> src \<leadsto>\<^sup>+ p'
   else m \<turnstile> p \<leadsto>\<^sup>+ p')"
  unfolding n'_def trancl_prev_update
  by (simp add: n_trancl_eq)

lemma n_rtrancl_eq':
  "n' \<turnstile> p \<leadsto>\<^sup>* p' =
  (if p' = dest then p = dest \<or> p \<noteq> dest \<and> m \<turnstile> p \<leadsto>\<^sup>* src
   else if p = dest then p' \<noteq> src \<and> m \<turnstile> src \<leadsto>\<^sup>* p'
   else m \<turnstile> p \<leadsto>\<^sup>* p')"
  unfolding n'_def rtrancl_prev_update
  by (simp add: n_rtrancl_eq)

lemma n'_cap:
  "n' p = Some (CTE cap node) \<Longrightarrow>
  \<exists>node'. if p = dest then cap = c' \<and> m p = Some (CTE dest_cap node')
          else m p = Some (CTE cap node')"
  by (auto simp add: n'_def n src dest new_src_def new_dest_def modify_map_if split: if_split_asm)

lemma n'_rev:
  "n' p = Some (CTE cap node) \<Longrightarrow>
  \<exists>node'. if p = dest then mdbRevocable node = isCapRevocable c' src_cap \<and> m p = Some (CTE dest_cap node')
          else m p = Some (CTE cap node') \<and> mdbRevocable node = mdbRevocable node'"
  by (auto simp add: n'_def n src dest new_src_def new_dest_def modify_map_if split: if_split_asm)

lemma m_cap':
  "m p = Some (CTE cap node) \<Longrightarrow>
  \<exists>node'. if p = dest then cap = dest_cap \<and> n' p = Some (CTE c' node')
          else n' p = Some (CTE cap node')"
  apply (simp add: n'_def n new_src_def new_dest_def modify_map_if)
  apply (cases "p=dest")
   apply (auto simp: src dest)
  done

lemma descendants':
  "descendants_of' p n' =
   (if src \<in> descendants_of' p m \<or> p = src
   then descendants_of' p m \<union> {dest} else descendants_of' p m)"
  by (simp add: n'_def descendants descendants_of_prev_update)

lemma ut_revocable_n' [simp]:
  "ut_revocable' n'"
  using dest
  apply (clarsimp simp: ut_revocable'_def)
  apply (frule n'_cap)
  apply (drule n'_rev)
  apply clarsimp
  apply (clarsimp simp: n_dest' new_dest_def split: if_split_asm)
   apply (clarsimp simp: Retype_H.isCapRevocable_def isCap_simps)
  apply (drule_tac p=p and m=m in ut_revocableD', assumption)
   apply (rule ut_rev)
  apply simp
  done

lemma valid_nc' [simp]:
  "valid_nullcaps n'"
  unfolding valid_nullcaps_def
  using src dest dest_prev dest_next simple safe_parent
  apply (clarsimp simp: n'_def n_def modify_map_if)
  apply (rule conjI)
   apply (clarsimp simp: is_simple_cap'_def)
  apply clarsimp
  apply (rule conjI)
   apply (fastforce dest!: safe_parent_Null)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (drule (1) valid_nullcaps_next, rule no_0, rule dlist, rule nullcaps)
   apply simp
  apply clarsimp
  apply (erule nullcapsD', rule nullcaps)
  done

lemma n'_prev_eq:
  "n' \<turnstile> p \<leftarrow> p' =
  (if p' = mdbNext src_node \<and> p' \<noteq> 0 then p = dest
   else if p' = dest then p = src
   else m \<turnstile> p \<leftarrow> p')"
  using src dest dest_prev dest_next
  apply (cases "p' = 0", simp)
  apply (simp split del: if_split)
  apply (cases "p' = mdbNext src_node")
   apply (clarsimp simp: modify_map_apply n'_def n_def mdb_prev_def)
   apply (clarsimp simp: modify_map_if)
   apply (rule iffI, clarsimp)
   apply clarsimp
   apply (rule dlistEn, assumption, simp)
   apply clarsimp
   apply (case_tac cte')
   apply clarsimp
  apply (cases "p' = dest")
   apply (clarsimp simp: modify_map_if n'_def n_def mdb_prev_def)
  apply clarsimp
  apply (clarsimp simp: modify_map_if n'_def n_def mdb_prev_def)
  apply (cases "p' = src", simp)
  apply clarsimp
  apply (rule iffI, clarsimp)
  apply clarsimp
  apply (case_tac z)
  apply clarsimp
  done

lemma m_prev_of_next:
  "m \<turnstile> p \<leftarrow> mdbNext src_node = (p = src \<and> mdbNext src_node \<noteq> 0)"
  using src
  apply (clarsimp simp: mdb_prev_def)
  apply (rule iffI)
   apply clarsimp
   apply (rule dlistEn, assumption, clarsimp)
   apply clarsimp
  apply clarsimp
  apply (rule dlistEn, assumption, clarsimp)
  apply clarsimp
  done

lemma src_next_eq:
  "m \<turnstile> p \<leadsto> mdbNext src_node = (if mdbNext src_node \<noteq> 0 then p = src else m \<turnstile> p \<leadsto> 0)"
  using src
  apply -
  apply (rule iffI)
   prefer 2
   apply (clarsimp split: if_split_asm)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (frule (1) dlist_nextD0)
   apply (clarsimp simp: m_prev_of_next)
  apply clarsimp
  done

lemma src_next_eq':
  "m (mdbNext src_node) = Some cte \<Longrightarrow> m \<turnstile> p \<leadsto> mdbNext src_node = (p = src)"
  by (subst src_next_eq) auto

lemma dest_no_prev [iff]:
  "\<not> m \<turnstile> dest \<leftarrow> p"
  using dest dest_next
  apply (clarsimp simp: mdb_prev_def)
  apply (rule dlistEp [where p=p], assumption, clarsimp)
  apply clarsimp
  done

lemma src_prev [iff]:
  "m \<turnstile> src \<leftarrow> p = (p = mdbNext src_node \<and> p \<noteq> 0)"
  using src
  apply -
  apply (rule iffI)
   prefer 2
   apply (clarsimp simp: mdb_ptr_src.next_p_prev)
  apply (clarsimp simp: mdb_prev_def)
  apply (rule conjI)
   prefer 2
   apply clarsimp
  apply (rule dlistEp [where p=p], assumption, clarsimp)
  apply simp
  done

lemma dlist' [simp]:
  "valid_dlist n'"
  using src dest
  apply (unfold valid_dlist_def3 n_direct_eq' n'_prev_eq)
  apply (split if_split)
  apply (split if_split)
  apply (split if_split)
  apply (split if_split)
  apply (split if_split)
  apply (split if_split)
  apply (split if_split)
  apply simp
  apply (intro conjI impI allI notI)
         apply (fastforce simp: src_next_eq')
        apply (clarsimp simp: src_next_eq split: if_split_asm)
       apply (simp add: mdb_ptr_src.p_next)
      apply (erule (1) dlist_nextD0)
     apply clarsimp
    apply clarsimp
   apply clarsimp
  apply (erule (1) dlist_prevD0)
  done

lemma utRange_c':
  "untypedRange c' \<subseteq> untypedRange src_cap"
  using safe_parent src
  by - (drule (1) safe_parent_for_untypedRange, simp)

lemma capRange_c':
  "capRange c' \<subseteq> capRange src_cap"
  using safe_parent src
  by - (drule (1) safe_parent_for_capRange_capBits, simp)

lemma not_ut_c' [simp]:
  "\<not>isUntypedCap c'"
  using simple
  by (simp add: is_simple_cap'_def)

lemma utCapRange_c':
  "capRange c' \<subseteq> untypedRange src_cap"
  using safe_parent src
  by - (drule (1) safe_parent_for_capUntypedRange, simp)

lemma ut_descendants:
  "isUntypedCap src_cap \<Longrightarrow> descendants_of' src m = {}"
  using safe_parent src
  by (rule safe_parent_for_descendants')

lemma ut_mdb' [simp]:
  "untyped_mdb' n'"
  using src dest utRange_c' capRange_c' utCapRange_c'
  apply (clarsimp simp: untyped_mdb'_def)
  apply (drule n'_cap)+
  apply (clarsimp simp: descendants')
  apply (clarsimp split: if_split_asm)
   apply (cases "isUntypedCap src_cap")
    prefer 2
    apply (drule_tac p=p and p'=src and m=m in untyped_mdbD', assumption+)
      apply blast
     apply (rule untyped_mdb)
    apply simp
   apply (frule ut_descendants)
   apply (drule (3) untyped_incD', rule untyped_inc)
   apply clarsimp
   apply blast
  apply (fastforce elim: untyped_mdbD' intro!: untyped_mdb)
  done

lemma n'_badge:
  "n' p = Some (CTE cap node) \<Longrightarrow>
  \<exists>node'. if p = dest then mdbFirstBadged node = isCapRevocable c' src_cap \<and> m p = Some (CTE dest_cap node')
          else m p = Some (CTE cap node') \<and> mdbFirstBadged node = mdbFirstBadged node'"
  by (auto simp add: n'_def n src dest new_src_def new_dest_def modify_map_if split: if_split_asm)

lemma src_not_ep [simp]:
  "\<not>isEndpointCap src_cap"
  using safe_parent src by (rule safe_parent_not_ep')

lemma src_not_ntfn [simp]:
  "\<not>isNotificationCap src_cap"
  using safe_parent src by (rule safe_parent_not_ntfn')

lemma c_not_ep [simp]:
  "\<not>isEndpointCap c'"
  using simple by (simp add: is_simple_cap'_def)

lemma c_not_ntfn [simp]:
  "\<not>isNotificationCap c'"
  using simple by (simp add: is_simple_cap'_def)

lemma valid_badges' [simp]:
  "valid_badges n'"
  using simple src dest
  apply (clarsimp simp: valid_badges_def valid_arch_badges_def) (* FIXME arch-split; use AARCH64 version *)
  apply (simp add: n_direct_eq')
  apply (frule_tac p=p in n'_badge)
  apply (frule_tac p=p' in n'_badge)
  apply (drule n'_cap)+
  apply (clarsimp split: if_split_asm)
  apply (insert valid_badges)
  apply (simp add: valid_badges_def)
  apply blast
  done

lemma caps_contained' [simp]:
  "caps_contained' n'"
  using src dest capRange_c' utCapRange_c'
  apply (clarsimp simp: caps_contained'_def)
  apply (drule n'_cap)+
  apply clarsimp
  apply (clarsimp split: if_split_asm)
     apply (drule capRange_untyped)
     apply simp
    apply (drule capRange_untyped)
    apply clarsimp
   apply (cases "isUntypedCap src_cap")
    prefer 2
    apply (drule_tac p=p and p'=src in caps_containedD', assumption+)
      apply blast
     apply (rule caps_contained)
    apply blast
   apply (frule capRange_untyped)
   apply (drule (3) untyped_incD', rule untyped_inc)
   apply (clarsimp simp: ut_descendants)
   apply blast
  apply (drule (3) caps_containedD', rule caps_contained)
  apply blast
  done

lemma capClass_c' [simp]:
  "capClass c' = capClass src_cap"
  using safe_parent src by (rule safe_parent_capClass)

lemma class_links' [simp]:
  "class_links n'"
  using src dest
  apply (clarsimp simp: class_links_def)
  apply (simp add: n_direct_eq')
  apply (case_tac cte, case_tac cte')
  apply clarsimp
  apply (drule n'_cap)+
  apply clarsimp
  apply (clarsimp split: if_split_asm)
   apply (drule (2) class_linksD, rule class_links)
   apply simp
  apply (drule (2) class_linksD, rule class_links)
  apply simp
  done

lemma untyped_inc' [simp]:
  "untyped_inc' n'"
  using src dest
  apply (clarsimp simp: untyped_inc'_def)
  apply (drule n'_cap)+
  apply (clarsimp simp: descendants')
  apply (clarsimp split: if_split_asm)
  apply (rule conjI)
   apply clarsimp
   apply (drule (3) untyped_incD', rule untyped_inc)
   apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (frule_tac p=src and p'=p' in untyped_incD', assumption+, rule untyped_inc)
   apply (clarsimp simp: ut_descendants)
   apply (intro conjI, clarsimp+)
  apply (drule (3) untyped_incD', rule untyped_inc)
  apply clarsimp
  done

lemma sameRegion_src [simp]:
  "sameRegionAs src_cap c'"
  using safe_parent src
  apply (simp add: safe_parent_for'_def)
  done

lemma sameRegion_src_c':
  "sameRegionAs cap src_cap \<Longrightarrow> sameRegionAs cap c'"
  using safe_parent simple src capRange_c'
  apply (simp add: safe_parent_for'_def)
  apply (erule disjE)
   apply (clarsimp simp: sameRegionAs_def2 isCap_simps capRange_def)
  apply (erule disjE)
  apply clarsimp
   apply (simp add: sameRegionAs_def2 gen_isCap_Master capRange_Master)
   apply (erule disjE)
    prefer 2
    apply (clarsimp simp: isCap_simps)
   apply (elim conjE)
   apply (erule disjE)
    prefer 2
    apply (clarsimp simp: isCap_simps)
   apply simp
   apply blast
  apply (clarsimp simp: sameRegionAs_def2 isCap_simps capRange_def)
  done

lemma irq_c'_new:
  assumes irq_src: "isIRQControlCap src_cap"
  shows "m p = Some (CTE cap node) \<Longrightarrow> \<not> sameRegionAs c' cap"
  using safe_parent irq_src src
  apply (clarsimp simp: safe_parent_for'_def isCap_simps)
  apply (clarsimp simp: sameRegionAs_def2 isCap_simps)
  done

lemma ioport_c'_new:
  assumes ioport_src: "isIOPortControlCap' src_cap"
  shows "m p = Some (CTE cap node) \<Longrightarrow> \<not> sameRegionAs c' cap"
  using safe_parent ioport_src src
  apply (clarsimp simp: safe_parent_for'_def isCap_simps sameRegionAs_def2)
  done

lemma ut_capRange_non_empty:
  "isUntypedCap src_cap \<Longrightarrow> capRange c' \<noteq> {}"
  using safe_parent src unfolding safe_parent_for'_def
  by (clarsimp simp: isCap_simps)


lemma ut_sameRegion_non_empty:
  "\<lbrakk> isUntypedCap src_cap; sameRegionAs c' cap \<rbrakk> \<Longrightarrow> capRange cap \<noteq> {}"
  using simple safe_parent src
  by (clarsimp simp: is_simple_cap'_def sameRegionAs_def2 gen_isCap_Master)
     (force dest!: capMaster_capRange
            simp: safe_parent_for'_def isCap_simps capRange_def ut_capRange_non_empty)

lemma ut_c'_new:
  assumes ut_src: "isUntypedCap src_cap"
  shows "m p = Some (CTE cap node) \<Longrightarrow> \<not> sameRegionAs c' cap"
  using src simple
  apply clarsimp
  apply (drule untyped_mdbD', rule ut_src, assumption)
     apply (clarsimp simp: is_simple_cap'_def sameRegionAs_def2 gen_isCap_Master capRange_Master)
     apply (fastforce simp: isCap_simps)
    apply (frule sameRegion_capRange_sub)
    apply (drule ut_sameRegion_non_empty [OF ut_src])
    apply (insert utCapRange_c')
    apply blast
   apply (rule untyped_mdb)
  apply (simp add: ut_descendants [OF ut_src])
  done

lemma c'_new:
  "m p = Some (CTE cap node) \<Longrightarrow> \<not> sameRegionAs c' cap"
  using safe_parent src unfolding safe_parent_for'_def
  apply (elim exE conjE)
  apply (erule disjE)
   apply (erule irq_c'_new [rotated])
   apply (clarsimp simp: isCap_simps)
  apply (erule disjE)
   prefer 2
   apply (erule ioport_c'_new[rotated])
   apply (clarsimp simp: isCap_simps)
  apply clarsimp
  apply (drule (1) ut_c'_new)
  apply simp
  done

lemma irq_control_src:
  "\<lbrakk> isIRQControlCap src_cap;
     m p = Some (CTE cap node);
     sameRegionAs cap c' \<rbrakk> \<Longrightarrow> p = src"
  using safe_parent src unfolding safe_parent_for'_def
  apply (clarsimp simp: isCap_simps)
  apply (clarsimp simp: sameRegionAs_def2 gen_isCap_Master)
  apply (erule disjE, fastforce simp: isCap_simps)
  apply (erule disjE, clarsimp simp: isCap_simps capRange_def)
   apply (drule (1) irq_controlD, rule irq_control)
   apply simp
  apply (clarsimp simp: isCap_simps capRange_def)
  done

lemma ioport_control_src:
  "\<lbrakk> isIOPortControlCap' src_cap;
     m p = Some (CTE cap node);
     sameRegionAs cap c' \<rbrakk> \<Longrightarrow> p = src"
  using safe_parent src unfolding safe_parent_for'_def
  apply (clarsimp simp: isCap_simps)
  apply (clarsimp simp: sameRegionAs_def2 gen_isCap_Master)
  apply (erule disjE, clarsimp simp: isCap_simps)
  apply (erule disjE, clarsimp simp: isCap_simps)
  apply (erule disjE, clarsimp simp: isCap_simps capRange_def)
  apply (clarsimp simp: isCap_simps split: if_split_asm)
  apply (drule (1) arch_mdb_assertD, rule arch_mdb_assert)
  apply simp
  done

lemma not_irq_ioport_parentD:
  "\<not> isIRQControlCap src_cap \<Longrightarrow> \<not> isIOPortControlCap' src_cap \<Longrightarrow>
  isUntypedCap src_cap \<and> descendants_of' src m = {} \<and> capRange c' \<noteq> {}"
  using src safe_parent unfolding safe_parent_for'_def
  by (clarsimp simp: isCap_simps)

lemma ut_src_only_ut_c_parents:
  "\<lbrakk> isUntypedCap src_cap; sameRegionAs cap c'; m p = Some (CTE cap node) \<rbrakk> \<Longrightarrow> isUntypedCap cap"
  using safe_parent src unfolding safe_parent_for'_def
  apply clarsimp
  apply (erule disjE, clarsimp simp: isCap_simps)
  apply (erule disjE)
   prefer 2
   apply (clarsimp simp: isCap_simps)
  apply clarsimp
  apply (rule ccontr)
  apply (drule (3) untyped_mdbD')
    apply (frule sameRegion_capRange_sub)
    apply (insert utCapRange_c')[1]
    apply blast
   apply (rule untyped_mdb)
  apply simp
  done

lemma ut_src:
  "\<lbrakk> isUntypedCap src_cap; sameRegionAs cap c'; m p = Some (CTE cap node) \<rbrakk> \<Longrightarrow>
  isUntypedCap cap \<and> untypedRange cap \<inter> untypedRange src_cap \<noteq> {}"
  apply (frule (2) ut_src_only_ut_c_parents)
  apply simp
  apply (frule sameRegion_capRange_sub)
  apply (insert utCapRange_c')[1]
  apply (simp add: untypedCapRange)
  apply (drule ut_capRange_non_empty)
  apply blast
  done


lemma chunked' [simp]:
  "mdb_chunked n'"
  using src dest
  apply (clarsimp simp: mdb_chunked_def)
  apply (drule n'_cap)+
  apply (clarsimp simp: n'_trancl_eq)
  apply (clarsimp split: if_split_asm)
    prefer 3
    apply (frule (4) mdb_chunkedD, rule chunked)
    apply clarsimp
    apply (rule conjI, clarsimp)
     apply (clarsimp simp: is_chunk_def n'_trancl_eq n_rtrancl_eq' n_dest' new_dest_def)
     apply (rule conjI, clarsimp)
      apply (rule conjI, clarsimp)
      apply clarsimp
      apply (erule_tac x=src in allE)
      apply simp
      apply (erule sameRegion_src_c')
     apply clarsimp
     apply (erule_tac x=p'' in allE)
     apply clarsimp
     apply (frule_tac p=p'' in m_cap')
     apply clarsimp
    apply clarsimp
    apply (clarsimp simp: is_chunk_def n'_trancl_eq n_rtrancl_eq' n_dest' new_dest_def)
    apply (rule conjI, clarsimp)
     apply (rule conjI, clarsimp)
     apply clarsimp
     apply (erule_tac x=src in allE)
     apply simp
     apply (erule sameRegion_src_c')
    apply clarsimp
    apply (erule_tac x=p'' in allE)
    apply clarsimp
    apply (frule_tac p=p'' in m_cap')
    apply clarsimp
   apply (case_tac "p' = src")
    apply simp
    apply (clarsimp simp: is_chunk_def)
    apply (simp add: n'_trancl_eq n_rtrancl_eq')
    apply (erule disjE)
     apply (simp add: n_dest' new_dest_def)
    apply clarsimp
    apply (drule (1) trancl_rtrancl_trancl)
    apply simp
   apply clarsimp
   apply (drule c'_new)
   apply (erule (1) notE)
  apply (case_tac "p=src")
   apply clarsimp
   apply (clarsimp simp: is_chunk_def)
   apply (simp add: n'_trancl_eq n_rtrancl_eq')
   apply (erule disjE)
    apply (clarsimp simp: n_dest' new_dest_def)
   apply clarsimp
   apply (drule (1) trancl_rtrancl_trancl)
   apply simp
  apply (case_tac "isIRQControlCap src_cap")
   apply (drule (2) irq_control_src)
   apply simp
  apply (case_tac "isIOPortControlCap' src_cap")
   apply (drule (2) ioport_control_src)
   apply simp
  apply (drule (1) not_irq_ioport_parentD)
  apply clarsimp
  apply (frule (2) ut_src)
  apply clarsimp
  apply (subgoal_tac "src \<in> descendants_of' p m")
   prefer 2
   apply (drule (3) untyped_incD', rule untyped_inc)
   apply clarsimp
   apply fastforce
  apply (frule_tac m=m and p=p and p'=src in mdb_chunkedD, assumption+)
      apply (clarsimp simp: descendants_of'_def)
      apply (drule subtree_parent)
      apply (clarsimp simp: parentOf_def isMDBParentOf_def split: if_split_asm)
     apply simp
    apply (simp add: mdb_chunked_arch_assms_def)
   apply (rule chunked)
  apply clarsimp
  apply (erule disjE)
   apply clarsimp
   apply (rule conjI)
    prefer 2
    apply clarsimp
    apply (drule (1) trancl_trans, simp)
   apply (clarsimp simp: is_chunk_def)
   apply (simp add: n'_trancl_eq n_rtrancl_eq' split: if_split_asm)
    apply (clarsimp simp: n_dest' new_dest_def)
   apply (erule_tac x=p'' in allE)
   apply clarsimp
   apply (drule_tac p=p'' in m_cap')
   apply clarsimp
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (drule (1) trancl_trans, simp)
  apply (clarsimp simp: descendants_of'_def)
  apply (drule subtree_mdb_next)
  apply (drule (1) trancl_trans)
  apply simp
  done

lemma distinct_zombies_m:
  "distinct_zombies m"
  using valid by (simp add: valid_mdb_ctes_def)

lemma untyped_rangefree:
  "\<lbrakk> isUntypedCap src_cap; m x = Some cte; x \<noteq> src; \<not> isUntypedCap (cteCap cte) \<rbrakk>
          \<Longrightarrow> capRange (cteCap cte) \<noteq> capRange c'"
  apply (frule ut_descendants)
  apply (cases cte, clarsimp)
  apply (frule(2) untyped_mdbD' [OF src _ _ _ _ untyped_mdb])
   apply (simp add: untypedCapRange[symmetric])
   apply (frule ut_capRange_non_empty)
   apply (cut_tac capRange_c')
   apply blast
  apply simp
  done

lemma notZomb:
  "\<not> isZombie src_cap" "\<not> isZombie c'"
  using sameRegion_src simple
  by (auto simp: isCap_simps sameRegionAs_def3
       simp del: sameRegion_src,
      auto simp: is_simple_cap'_def isCap_simps)

lemma notArchPage:
  "\<not> isArchPageCap c'"
  using simple
  by (clarsimp simp: isCap_simps is_simple_cap'_def)

lemma distinct_zombies[simp]:
  "distinct_zombies n'"
  using distinct_zombies_m
  apply (simp add: n'_def distinct_zombies_nonCTE_modify_map)
  apply (simp add: n_def modify_map_apply src dest)
  apply (rule distinct_zombies_sameE[rotated])
        apply (simp add: src)
       apply simp+
  apply (cases "isUntypedCap src_cap")
   apply (erule distinct_zombies_seperateE)
   apply (case_tac "y = src")
    apply (clarsimp simp add: src)
   apply (frule(3) untyped_rangefree)
   apply (simp add: capRange_def)
  apply (rule sameRegionAsE [OF sameRegion_src], simp_all)
     apply (erule distinct_zombies_copyMasterE, rule src)
      apply simp
     apply (simp add: notZomb)
    apply (simp add: notArchPage)
   apply (clarsimp simp: isCap_simps)
   apply (erule distinct_zombies_sameMasterE, rule dest)
   apply (clarsimp simp: isCap_simps)
  apply (clarsimp simp: isCap_simps)
  apply (erule distinct_zombies_sameMasterE, rule dest)
  apply (clarsimp simp: isCap_simps)
  done

lemma irq' [simp]:
  "irq_control n'" using simple
  apply (clarsimp simp: irq_control_def)
  apply (frule n'_cap)
  apply (drule n'_rev)
  apply (clarsimp split: if_split_asm)
   apply (simp add: is_simple_cap'_def)
  apply (frule irq_revocable, rule irq_control)
  apply clarsimp
  apply (drule n'_cap)
  apply (clarsimp split: if_split_asm)
  apply (erule disjE)
   apply (clarsimp simp: is_simple_cap'_def)
  apply (erule (1) irq_controlD, rule irq_control)
  done

lemma reply_masters_rvk_fb:
  "reply_masters_rvk_fb m"
  using valid by (simp add: valid_mdb_ctes_def)

lemma reply_masters_rvk_fb' [simp]:
  "reply_masters_rvk_fb n'"
   using reply_masters_rvk_fb simple
   apply (simp add: reply_masters_rvk_fb_def n'_def
                    n_def ball_ran_modify_map_eq)
   apply (subst ball_ran_modify_map_eq)
    apply (clarsimp simp: modify_map_def m_p is_simple_cap'_def)
   apply (simp add: ball_ran_modify_map_eq m_p is_simple_cap'_def
                    dest_cap isCap_simps)
   done

lemma mdb:
  "valid_mdb_ctes n'"
  by (simp add: valid_mdb_ctes_def no_0_n' chain_n')

end

lemma updateCapFreeIndex_no_0:
  assumes preserve:"\<And>m m'.  mdb_inv_preserve m m'
  \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  shows
 "\<lbrace>\<lambda>s. P (no_0(Q (ctes_of s))) \<and> cte_wp_at' (\<lambda>c. c = srcCTE \<and> isUntypedCap (cteCap c)) src s\<rbrace>
  updateCap src (capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE))
 \<lbrace>\<lambda>r s. P (no_0 (Q (ctes_of s)))\<rbrace>"
  apply (wp updateCap_ctes_of_wp)
  apply (subgoal_tac "mdb_inv_preserve (Q (ctes_of s)) (Q (modify_map (ctes_of s) src
              (cteCap_update (\<lambda>_. capFreeIndex_update (\<lambda>_. index) (cteCap srcCTE)))))")
    apply (drule mdb_inv_preserve.by_products)
    apply simp
  apply (rule preserve)
  apply (simp add:cte_wp_at_ctes_of)+
  apply (rule mdb_inv_preserve_updateCap)
    apply (clarsimp simp:cte_wp_at_ctes_of)+
  done

context begin interpretation Arch . (*FIXME: arch-split*)

lemma cteInsert_simple_mdb':
  "\<lbrace>valid_mdb' and pspace_aligned' and pspace_distinct' and (\<lambda>s. src \<noteq> dest) and K (capAligned cap) and
    (\<lambda>s. safe_parent_for' (ctes_of s) src cap) and K (is_simple_cap' cap) \<rbrace>
  cteInsert cap src dest
  \<lbrace>\<lambda>_. valid_mdb'\<rbrace>"
  unfolding cteInsert_def valid_mdb'_def
  apply simp
  apply (rule hoare_name_pre_state)
  apply (rule hoare_pre)
   apply (wp updateCap_ctes_of_wp getCTE_wp' setUntypedCapAsFull_ctes
     mdb_inv_preserve_updateCap mdb_inv_preserve_modify_map | clarsimp)+
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (rule conjI)
   apply (clarsimp simp: valid_mdb_ctes_def)
  apply (case_tac cte)
  apply (rename_tac src_cap src_node)
  apply (case_tac ctea)
  apply (rename_tac dest_cap dest_node)
  apply clarsimp
  apply (subst modify_map_eq)
     apply simp+
   apply (clarsimp simp:maskedAsFull_def is_simple_cap'_def)
  apply (subgoal_tac "mdb_insert_simple'
    (ctes_of sa) src src_cap src_node dest NullCap dest_node cap")
   prefer 2
   apply (intro mdb_insert_simple'.intro
                mdb_insert_simple.intro mdb_insert_simple_axioms.intro
                mdb_ptr.intro mdb_insert.intro vmdb.intro
                mdb_ptr_axioms.intro mdb_insert_axioms.intro)
              apply (simp add:modify_map_def valid_mdb_ctes_maskedAsFull)+
         apply (clarsimp simp:nullPointer_def)+
       apply (clarsimp simp:valid_mdb_ctes_def archMDBAssertions_def)+
  apply (drule mdb_insert_simple'.mdb)
  apply (clarsimp simp:valid_mdb_ctes_def)
  done

lemma cteInsert_valid_globals_simple:
 "\<lbrace>valid_global_refs' and (\<lambda>s. safe_parent_for' (ctes_of s) src cap)\<rbrace>
  cteInsert cap src dest
  \<lbrace>\<lambda>rv. valid_global_refs'\<rbrace>"
  apply (simp add: cteInsert_def)
  apply (rule hoare_pre)
   apply (wp getCTE_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (drule (1) safe_parent_for_capRange_capBits)
  apply (drule (1) valid_global_refsD_with_objSize)
  apply (auto elim: order_trans[rotated])
  done

lemma cteInsert_simple_invs:
 "\<lbrace>invs' and cte_wp_at' (\<lambda>c. cteCap c=NullCap) dest and valid_cap' cap and
  (\<lambda>s. src \<noteq> dest) and (\<lambda>s. safe_parent_for' (ctes_of s) src cap)
  and (\<lambda>s. \<forall>irq. cap = IRQHandlerCap irq \<longrightarrow> irq_issued' irq s)
  and cte_at' src
  and ex_cte_cap_to' dest and K (is_simple_cap' cap)\<rbrace>
  cteInsert cap src dest
  \<lbrace>\<lambda>rv. invs'\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: invs'_def valid_state'_def valid_pspace'_def)
   apply (wp cur_tcb_lift sch_act_wf_lift valid_queues_lift tcb_in_cur_domain'_lift
             valid_irq_node_lift irqs_masked_lift sym_heap_sched_pointers_lift
             cteInsert_simple_mdb' cteInsert_valid_globals_simple
             cteInsert_norq | simp add: pred_tcb_at'_def)+
  apply (auto simp: invs'_def valid_state'_def valid_pspace'_def
                    is_simple_cap'_def untyped_derived_eq_def o_def
              elim: valid_capAligned)
  done

lemma ensureEmptySlot_stronger [wp]:
  "\<lbrace>\<lambda>s. cte_wp_at' (\<lambda>c. cteCap c = NullCap) p s \<longrightarrow> P s\<rbrace> ensureEmptySlot p \<lbrace>\<lambda>rv. P\<rbrace>, -"
  apply (simp add: ensureEmptySlot_def whenE_def unlessE_whenE)
  apply (wp getCTE_wp')
  apply (clarsimp simp: cte_wp_at'_def)
  done

lemma lookupSlotForCNodeOp_real_cte_at'[wp]:
  "\<lbrace>valid_objs' and valid_cap' rootCap\<rbrace>
     lookupSlotForCNodeOp isSrc rootCap cref depth
   \<lbrace>\<lambda>rv. real_cte_at' rv\<rbrace>,-"
  apply (simp add: lookupSlotForCNodeOp_def split_def unlessE_def
                     split del: if_split cong: if_cong)
  apply (rule hoare_pre)
   apply (wp resolveAddressBits_real_cte_at' | simp | wp (once) hoare_drop_imps)+
  done

lemma cte_refs_maskCapRights[simp]:
  "cte_refs' (maskCapRights rghts cap) = cte_refs' cap"
  by (rule ext, cases cap,
      simp_all add: maskCapRights_def isCap_defs Let_def
                    X64_H.maskCapRights_def
         split del: if_split
             split: arch_capability.split)

lemma getSlotCap_cap_to'[wp]:
  "\<lbrace>\<top>\<rbrace> getSlotCap cp \<lbrace>\<lambda>rv s. \<forall>r\<in>cte_refs' rv (irq_node' s). ex_cte_cap_to' r s\<rbrace>"
  apply (simp add: getSlotCap_def)
  apply (wp getCTE_wp)
  apply (fastforce simp: cte_wp_at_ctes_of ex_cte_cap_to'_def)
  done

lemma getSlotCap_cap_to2:
  "\<lbrace>\<top> and K (\<forall>cap. P cap \<longrightarrow> Q cap)\<rbrace>
     getSlotCap slot
   \<lbrace>\<lambda>rv s. P rv \<longrightarrow> (\<forall>x \<in> cte_refs' rv (irq_node' s). ex_cte_cap_wp_to' Q x s)\<rbrace>"
  apply (simp add: getSlotCap_def)
  apply (wp getCTE_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of ex_cte_cap_wp_to'_def)
  apply fastforce
  done

lemma locateSlot_cap_to'[wp]:
  "\<lbrace>\<lambda>s. isCNodeCap cap \<and> (\<forall>r \<in> cte_refs' cap (irq_node' s). ex_cte_cap_wp_to' P r s)\<rbrace>
     locateSlotCNode (capCNodePtr cap) n (v && mask (capCNodeBits cap))
   \<lbrace>ex_cte_cap_wp_to' P\<rbrace>"
  apply (simp add: locateSlot_conv shiftl_t2n')
  apply wp
  apply (clarsimp dest!: isCapDs valid_capAligned
                   simp: objBits_simps' mult.commute capAligned_def cte_level_bits_def shiftl_t2n')
  apply (erule bspec)
  apply (case_tac "bits < word_bits")
   apply (simp add: word_and_le1)
  apply (simp add: power_overflow word_bits_def word_and_le1)
  done

lemma rab_cap_to'':
  assumes P: "\<And>cap. isCNodeCap cap \<longrightarrow> P cap"
  shows
  "s \<turnstile> \<lbrace>\<lambda>s. isCNodeCap cap \<longrightarrow> (\<forall>r\<in>cte_refs' cap (irq_node' s). ex_cte_cap_wp_to' P r s)\<rbrace>
     resolveAddressBits cap cref depth
   \<lbrace>\<lambda>rv s. ex_cte_cap_wp_to' P (fst rv) s\<rbrace>,\<lbrace>\<top>\<top>\<rbrace>"
proof (induct arbitrary: s rule: resolveAddressBits.induct)
  case (1 cap fn cref depth)
  show ?case
    apply (subst resolveAddressBits.simps)
    apply (simp add: Let_def split_def cap_case_CNodeCap[unfolded isCap_simps]
               split del: if_split cong: if_cong)
    apply (rule hoare_pre_spec_validE)
     apply ((elim exE | wp (once) spec_strengthen_postE[OF "1.hyps"])+,
              (rule refl conjI | simp add: in_monad split del: if_split del: cte_refs'.simps)+)
            apply (wp getSlotCap_cap_to2
                     | simp    add: assertE_def split_def whenE_def locateSlotCap_def
                        split del: if_split | simp add: imp_conjL[symmetric]
                     | wp (once) hoare_drop_imps)+
    apply (clarsimp simp: P)
  done
qed

lemma rab_cap_to'[wp]:
  "\<lbrace>(\<lambda>s. isCNodeCap cap \<longrightarrow> (\<forall>r\<in>cte_refs' cap (irq_node' s). ex_cte_cap_wp_to' P r s))
              and K (\<forall>cap. isCNodeCap cap \<longrightarrow> P cap)\<rbrace>
     resolveAddressBits cap cref depth
   \<lbrace>\<lambda>rv s. ex_cte_cap_wp_to' P (fst rv) s\<rbrace>,-"
  apply (rule hoare_gen_asmE)
  apply (unfold validE_R_def)
  apply (rule use_spec, rule rab_cap_to'')
  apply simp
  done

lemma lookupCNode_cap_to'[wp]:
  "\<lbrace>\<lambda>s. \<forall>r\<in>cte_refs' rootCap (irq_node' s). ex_cte_cap_to' r s\<rbrace>
     lookupSlotForCNodeOp isSrc rootCap cref depth
   \<lbrace>\<lambda>p. ex_cte_cap_to' p\<rbrace>,-"
  apply (simp add: lookupSlotForCNodeOp_def Let_def split_def unlessE_def
             split del: if_split cong: if_cong)
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps | simp)+
  done

lemma badge_derived'_refl[simp]: "badge_derived' c c"
  by (simp add: badge_derived'_def)

lemma derived'_not_Null:
  "\<not> is_derived' m p c capability.NullCap"
  "\<not> is_derived' m p capability.NullCap c"
  by (clarsimp simp: is_derived'_def badge_derived'_def)+

lemma getSlotCap_wp:
  "\<lbrace>\<lambda>s.  (\<exists>cap. cte_wp_at' (\<lambda>c. cteCap c = cap) p s \<and> Q cap s)\<rbrace>
   getSlotCap p \<lbrace>Q\<rbrace>"
  apply (simp add: getSlotCap_def)
  apply (wp getCTE_wp)
  apply (clarsimp simp: cte_wp_at'_def)
  done

lemma storeWordUser_typ_at' :
  "\<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> storeWordUser v w \<lbrace>\<lambda>_ s. P (typ_at' T p s)\<rbrace>"
  unfolding storeWordUser_def by wpsimp

lemma arch_update_updateCap_invs:
  "\<lbrace>cte_wp_at' (is_arch_update' cap) p and invs' and valid_cap' cap\<rbrace>
  updateCap p cap
  \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: updateCap_def)
  apply (wp arch_update_setCTE_invs getCTE_wp')
  apply clarsimp
  done

lemma setCTE_set_cap_ready_queues_relation_valid_corres:
  assumes pre: "ready_queues_relation s s'"
  assumes step_abs: "(x, t) \<in> fst (set_cap cap slot s)"
  assumes step_conc: "(y, t') \<in> fst (setCTE slot' cap' s')"
  shows "ready_queues_relation t t'"
  apply (clarsimp simp: ready_queues_relation_def)
  apply (insert pre)
  apply (rule use_valid[OF step_abs set_cap_rqueues])
  apply (rule use_valid[OF step_conc setCTE_ksReadyQueues])
  apply (rule use_valid[OF step_conc setCTE_tcbSchedNexts_of])
  apply (rule use_valid[OF step_conc setCTE_tcbSchedPrevs_of])
  apply (clarsimp simp: ready_queues_relation_def Let_def)
  using use_valid[OF step_conc setCTE_inQ_opt_pred]
  by fast

lemma updateCap_same_master:
  "\<lbrakk> cap_relation cap cap' \<rbrakk> \<Longrightarrow>
   corres dc (valid_objs and pspace_aligned and pspace_distinct and
              cte_wp_at (\<lambda>c. cap_master_cap c = cap_master_cap cap \<and>
                             \<not>is_reply_cap c \<and> \<not>is_master_reply_cap c \<and>
                             \<not>is_ep_cap c \<and> \<not>is_ntfn_cap c) slot)
             (pspace_aligned' and pspace_distinct' and cte_at' (cte_map slot))
     (set_cap cap slot)
     (updateCap (cte_map slot) cap')" (is "_ \<Longrightarrow> corres _ ?P ?P' _ _")
  supply if_cong[cong]
  apply (unfold updateCap_def)
  apply (rule corres_guard_imp)
    apply (rule_tac Q="?P" and R'="\<lambda>cte. ?P' and (\<lambda>s. ctes_of s (cte_map slot) = Some cte)"
      in corres_symb_exec_r_conj)
       apply (rule corres_stronger_no_failI)
        apply (rule no_fail_pre, wp)
        apply (clarsimp simp: cte_wp_at_ctes_of)
       apply clarsimp
       apply (clarsimp simp add: state_relation_def)
       apply (frule (4) set_cap_not_quite_corres_prequel)
            apply (erule cte_wp_at_weakenE, rule TrueI)
           apply assumption
          apply assumption
         apply simp
        apply (rule refl)
       apply clarsimp
       apply (rule bexI)
        prefer 2
        apply assumption
       apply clarsimp
       apply (subst conj_assoc[symmetric])
       apply (extract_conjunct \<open>match conclusion in "ready_queues_relation a b" for a b \<Rightarrow> -\<close>)
        subgoal by (erule setCTE_set_cap_ready_queues_relation_valid_corres; assumption)
       apply (rule conjI)
        apply (frule setCTE_pspace_only)
        apply (clarsimp simp: set_cap_def in_monad split_def get_object_def set_object_def
                         split: if_split_asm Structures_A.kernel_object.splits)
       apply (rule conjI)
        apply (clarsimp simp: ghost_relation_typ_at set_cap_a_type_inv data_at_def)
        apply (intro allI conjI)
         apply (frule use_valid[OF _ setCTE_gsUserPages])
          prefer 2
          apply simp+
        apply (frule use_valid[OF _ setCTE_gsCNodes])
         prefer 2
         apply simp+
       apply (subst conj_assoc[symmetric])
       apply (rule conjI)
        prefer 2
        apply (rule conjI)
         prefer 2
         apply (frule setCTE_pspace_only)
         apply clarsimp
         apply (clarsimp simp: set_cap_def in_monad split_def get_object_def set_object_def
                         split: if_split_asm Structures_A.kernel_object.splits)
        apply (frule set_cap_caps_of_state_monad)
        apply (drule is_original_cap_set_cap)
        apply clarsimp
        apply (erule use_valid [OF _ setCTE_ctes_of_wp])
        apply (clarsimp simp: revokable_relation_def simp del: fun_upd_apply)
        apply (clarsimp split: if_split_asm)
        apply (drule cte_map_inj_eq)
              prefer 2
              apply (erule cte_wp_at_weakenE, rule TrueI)
             apply (simp add: null_filter_def split: if_split_asm)
              apply (erule cte_wp_at_weakenE, rule TrueI)
             apply (erule caps_of_state_cte_at)
            apply fastforce
           apply fastforce
          apply fastforce
         apply clarsimp
         apply (simp add: null_filter_def split: if_split_asm)
          apply (erule_tac x=aa in allE, erule_tac x=bb in allE)
         apply (clarsimp simp: cte_wp_at_caps_of_state)
         apply (erule disjE)
          apply (clarsimp simp: cap_master_cap_simps dest!: cap_master_cap_eqDs)
         apply (case_tac rv)
         apply clarsimp
        apply (subgoal_tac "(aa,bb) \<noteq> slot")
         prefer 2
         apply clarsimp
        apply (simp add: null_filter_def cte_wp_at_caps_of_state split: if_split_asm)
       apply (clarsimp simp: cdt_relation_def)
       apply (frule set_cap_caps_of_state_monad)
       apply (frule mdb_set_cap, frule exst_set_cap)
       apply clarsimp
       apply (erule use_valid [OF _ setCTE_ctes_of_wp])
       apply (frule cte_wp_at_norm)
       apply (clarsimp simp del: fun_upd_apply)
       apply (frule (1) pspace_relation_ctes_ofI)
         apply fastforce
        apply fastforce
       apply (clarsimp simp del: fun_upd_apply)
       apply (subst same_master_descendants)
            apply assumption
           apply (clarsimp simp: master_cap_relation)
          apply (frule_tac d=c in master_cap_relation [symmetric], assumption)
          apply (frule is_reply_cap_relation[symmetric],
                 drule is_reply_master_relation[symmetric])+
          apply simp
          apply (drule masterCap.intro)
          apply (drule masterCap.isReplyCap)
          apply simp
         apply (drule is_ep_cap_relation)+
         apply (drule master_cap_ep)
         apply simp
        apply (drule is_ntfn_cap_relation)+
        apply (drule master_cap_ntfn)
        apply simp
       apply (simp add: in_set_cap_cte_at)
       apply(simp add: cdt_list_relation_def split del: if_split)
       apply(intro allI impI)
       apply(erule_tac x=aa in allE)+
       apply(erule_tac x=bb in allE)+
       apply(clarsimp split: if_split_asm)
       apply(case_tac rv, clarsimp)
      apply (wp getCTE_wp')+
     apply clarsimp
    apply (rule no_fail_pre, wp)
    apply clarsimp
    apply assumption
   apply clarsimp
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemma updateCapFreeIndex_valid_mdb_ctes:
  assumes preserve:"\<And>m m'. mdb_inv_preserve m m' \<Longrightarrow> mdb_inv_preserve (Q m) (Q m')"
  and     coin  :"\<And>m cte. \<lbrakk>m src = Some cte\<rbrakk> \<Longrightarrow> (\<exists>cte'. (Q m) src = Some cte' \<and> cteCap cte = cteCap cte')"
  and     assoc :"\<And>m f. Q (modify_map m src (cteCap_update f)) = modify_map (Q m) src (cteCap_update f)"
  shows
 "\<lbrace>\<lambda>s. usableUntypedRange (capFreeIndex_update (\<lambda>_. index) cap) \<subseteq> usableUntypedRange cap \<and> isUntypedCap cap
       \<and>  valid_mdb_ctes (Q (ctes_of s)) \<and> cte_wp_at' (\<lambda>c. cteCap c = cap) src s\<rbrace>
  updateCap src (capFreeIndex_update (\<lambda>_. index) cap)
 \<lbrace>\<lambda>r s. (valid_mdb_ctes (Q (ctes_of s)))\<rbrace>"
  apply (wp updateCap_ctes_of_wp)
  apply (subgoal_tac "mdb_inv_preserve (Q (ctes_of s)) (Q (modify_map (ctes_of s) src
              (cteCap_update (\<lambda>_. capFreeIndex_update (\<lambda>_. index) cap))))")
   apply (clarsimp simp:valid_mdb_ctes_def)
   apply (intro conjI)
                apply ((simp add:mdb_inv_preserve.preserve_stuff mdb_inv_preserve.by_products)+)[7]
         apply (rule mdb_inv_preserve.untyped_inc')
           apply assumption
          apply (clarsimp simp:assoc cte_wp_at_ctes_of)
          apply (clarsimp simp:modify_map_def split:if_splits)
          apply (drule coin)
          apply clarsimp
          apply (erule(1) subsetD)
         apply simp
        apply (simp_all add:mdb_inv_preserve.preserve_stuff  mdb_inv_preserve.by_products)
  apply (rule preserve)
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (rule mdb_inv_preserve_updateCap)
   apply (clarsimp simp:cte_wp_at_ctes_of)+
  done

lemma usableUntypedRange_mono1:
  "is_aligned ptr sz \<Longrightarrow> idx \<le> 2 ^ sz \<Longrightarrow> idx' \<le> 2 ^ sz
    \<Longrightarrow> sz < word_bits
    \<Longrightarrow> idx \<ge> idx'
    \<Longrightarrow> usableUntypedRange (UntypedCap dev ptr sz idx)
      \<le> usableUntypedRange (UntypedCap dev' ptr sz idx')"
  apply clarsimp
  apply (rule word_plus_mono_right)
   apply (rule of_nat_mono_maybe_le[THEN iffD1])
     apply (subst word_bits_def[symmetric])
     apply (erule less_le_trans[OF _  power_increasing])
      apply simp
     apply simp
    apply (subst word_bits_def[symmetric])
    apply (erule le_less_trans)
    apply (erule less_le_trans[OF _ power_increasing])
     apply simp+
  apply (erule is_aligned_no_wrap')
  apply (rule word_of_nat_less)
  apply simp
  done

lemma usableUntypedRange_mono2:
  "isUntypedCap cap
    \<Longrightarrow> isUntypedCap cap'
    \<Longrightarrow> capAligned cap \<Longrightarrow> capFreeIndex cap \<le> 2 ^ capBlockSize cap
    \<Longrightarrow> capFreeIndex cap' \<le> 2 ^ capBlockSize cap'
    \<Longrightarrow> capFreeIndex cap \<ge> capFreeIndex cap'
    \<Longrightarrow> capPtr cap' = capPtr cap
    \<Longrightarrow> capBlockSize cap' = capBlockSize cap
    \<Longrightarrow> usableUntypedRange cap \<le> usableUntypedRange cap'"
  apply (clarsimp simp only: isCap_simps capability.sel del: subsetI)
  apply (rule usableUntypedRange_mono1, auto simp: capAligned_def)
  done

lemma ctes_of_cte_wpD:
  "ctes_of s p = Some cte \<Longrightarrow> cte_wp_at' ((=) cte) p s"
  by (simp add: cte_wp_at_ctes_of)

lemma updateFreeIndex_forward_valid_objs':
  "\<lbrace>\<lambda>s. valid_objs' s \<and> cte_wp_at' ((\<lambda>cap. isUntypedCap cap
          \<and> capFreeIndex cap \<le> idx \<and> idx \<le> 2 ^ capBlockSize cap
          \<and> is_aligned (of_nat idx :: machine_word) minUntypedSizeBits) o cteCap) src s\<rbrace>
   updateFreeIndex src idx
   \<lbrace>\<lambda>r s. valid_objs' s\<rbrace>"
  apply (simp add: updateFreeIndex_def updateTrackedFreeIndex_def updateCap_def getSlotCap_def)
  apply (wp getCTE_wp')
  apply clarsimp
  apply (frule(1) CSpace1_R.ctes_of_valid)
  apply (clarsimp simp: cte_wp_at_ctes_of isCap_simps capAligned_def
                        valid_cap_simps' is_aligned_weaken[OF is_aligned_triv])
  apply (clarsimp simp add: valid_untyped'_def
                  simp del: usableUntypedRange.simps)
  apply (erule allE, erule notE, erule ko_wp_at'_weakenE)
  apply (rule disjCI2, simp only: simp_thms)
  apply (rule notI, erule notE, erule disjoint_subset2[rotated])
  apply (rule usableUntypedRange_mono1, simp_all)
  done

crunch updateFreeIndex
  for pspace_aligned'[wp]: "pspace_aligned'"
crunch updateFreeIndex
  for pspace_distinct'[wp]: "pspace_distinct'"
crunch updateFreeIndex
  for no_0_obj[wp]: "no_0_obj'"

lemma updateFreeIndex_forward_valid_mdb':
  "\<lbrace>\<lambda>s. valid_mdb' s \<and> valid_objs' s \<and> cte_wp_at' ((\<lambda>cap. isUntypedCap cap
          \<and> capFreeIndex cap \<le> idx \<and> idx \<le> 2 ^ capBlockSize cap) o cteCap) src s\<rbrace>
   updateFreeIndex src idx
   \<lbrace>\<lambda>r s. valid_mdb' s\<rbrace>"
  apply (simp add: valid_mdb'_def updateFreeIndex_def
                   updateTrackedFreeIndex_def getSlotCap_def)
  apply (wp updateCapFreeIndex_valid_mdb_ctes getCTE_wp' | simp)+
  apply clarsimp
  apply (frule(1) CSpace1_R.ctes_of_valid)
  apply (clarsimp simp: cte_wp_at_ctes_of del: subsetI)
  apply (rule usableUntypedRange_mono2,
    auto simp add: isCap_simps valid_cap_simps' capAligned_def)
  done

crunch updateFreeIndex
  for pspace_canonical'[wp]: "pspace_canonical'"

crunch updateFreeIndex
  for pspace_in_kernel_mappings'[wp]: "pspace_in_kernel_mappings'"

lemma updateFreeIndex_forward_invs':
  "\<lbrace>\<lambda>s. invs' s \<and> cte_wp_at' ((\<lambda>cap. isUntypedCap cap
          \<and> capFreeIndex cap \<le> idx \<and> idx \<le> 2 ^ capBlockSize cap
          \<and> is_aligned (of_nat idx :: machine_word) minUntypedSizeBits) o cteCap) src s\<rbrace>
   updateFreeIndex src idx
   \<lbrace>\<lambda>r s. invs' s\<rbrace>"
  apply (clarsimp simp:invs'_def valid_state'_def)
  apply (rule hoare_pre)
   apply (rule hoare_vcg_conj_lift)
    apply (simp add: valid_pspace'_def, wp updateFreeIndex_forward_valid_objs'
             updateFreeIndex_forward_valid_mdb')
   apply (simp add: updateFreeIndex_def updateTrackedFreeIndex_def)
   apply (wp sch_act_wf_lift valid_queues_lift updateCap_iflive' tcb_in_cur_domain'_lift
            | simp add: pred_tcb_at'_def)+
      apply (rule hoare_vcg_conj_lift)
       apply (simp add: ifunsafe'_def3 cteInsert_def setUntypedCapAsFull_def
               split del: if_split)
       apply wp+
      apply (rule hoare_vcg_conj_lift)
       apply (simp add:updateCap_def)
       apply wp
      apply (wp valid_irq_node_lift)
      apply (rule hoare_vcg_conj_lift)
       apply (simp add:updateCap_def)
       apply (wp setCTE_irq_handlers' getCTE_wp)
      apply (simp add:updateCap_def)
      apply (wp irqs_masked_lift cur_tcb_lift ct_idle_or_in_cur_domain'_lift
                hoare_vcg_disj_lift untyped_ranges_zero_lift getCTE_wp
                sym_heap_sched_pointers_lift valid_bitmaps_lift
               | wp (once) hoare_use_eq[where f="gsUntypedZeroRanges"]
               | simp add: getSlotCap_def)+
  apply (clarsimp simp: cte_wp_at_ctes_of fun_upd_def[symmetric])
  apply (clarsimp simp: isCap_simps valid_pspace'_def)
  apply (frule(1) valid_global_refsD_with_objSize)
  apply clarsimp
  apply (intro conjI allI impI)
   apply (clarsimp simp: modify_map_def cteCaps_of_def ifunsafe'_def3 split:if_splits)
    apply (drule_tac x=src in spec)
    apply (clarsimp simp:isCap_simps)
    apply (rule_tac x = cref' in exI)
    apply clarsimp
   apply (drule_tac x = cref in spec)
   apply clarsimp
   apply (rule_tac x = cref' in exI)
   apply clarsimp
  apply (erule untyped_ranges_zero_fun_upd, simp_all)
  apply (clarsimp simp: untypedZeroRange_def cteCaps_of_def isCap_simps)
  done

lemma no_fail_getSlotCap:
  "no_fail (cte_at' p) (getSlotCap p)"
  apply (rule no_fail_pre)
  apply (simp add: getSlotCap_def | wp)+
  done

end
end
