(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Lemmas and automation for automatically cancelling shared parts of the heap predicate
 * in a sep_fold
 *)

theory Sep_Fold_Cancel
imports
  Sep_Algebra_L4v
  Sep_Forward
begin

lemma sep_fold_cong1: "(\<And>x s. P x s = P' x s) \<Longrightarrow> sep_fold P Q R xs s \<Longrightarrow> sep_fold P' Q R xs s"
  apply (induct xs arbitrary: s; clarsimp simp: sep_fold_def)
  apply (erule sep_conj_impl, fastforce)
  apply (sep_cancel, sep_mp)
  by (clarsimp)

lemma sep_fold_cong2: "(\<And>x s. Q x s = Q' x s) \<Longrightarrow> sep_fold P Q R xs s \<Longrightarrow> sep_fold P Q' R xs s"
  apply (induct xs arbitrary: s; clarsimp simp: sep_fold_def)
  apply (erule sep_conj_impl, fastforce)
  apply (sep_cancel)
  apply (sep_drule (direct) sep_mp_gen)
  by (clarsimp)

lemma sep_fold_cong3: "(\<And> s. R s = R' s) \<Longrightarrow> sep_fold P Q R xs s \<Longrightarrow> sep_fold P Q R' xs s"
  apply (induct xs arbitrary: s; clarsimp simp: sep_fold_def)
  apply (erule sep_conj_impl, fastforce)
  apply (sep_cancel)
  apply (sep_drule (direct) sep_mp_gen)
  by (clarsimp)

lemma sep_fold_strengthen_final:
  "\<lbrakk>\<And>s. R s \<Longrightarrow> R' s;
    \<lparr>{P} \<and>* {Q} \<longrightarrow>* {R}\<rparr> xs s\<rbrakk>
   \<Longrightarrow> \<lparr>{P} \<and>* {Q} \<longrightarrow>* {R'}\<rparr> xs s"
  apply (induct xs arbitrary: s)
   apply (clarsimp simp: sep_fold_def)
  apply (clarsimp simp: sep_fold_def)
  apply (sep_cancel)+
  apply (sep_mp)
  apply (clarsimp)
  done

lemma sep_factor_foldI__:
  "(\<And>* map P xs \<and>* foldr (\<lambda>x R. Q x \<longrightarrow>* R) xs R) s \<Longrightarrow> sep_fold P Q R xs s"
  apply (clarsimp simp: sep_fold_def)
  apply (induct xs arbitrary: s; clarsimp)
  apply sep_cancel+
  apply sep_mp
  apply (clarsimp simp: sep_conj_ac)
  done

lemma sep_factor_foldI_:
  "(\<And>* map (\<lambda>_. I) xs \<and>* sep_fold P Q R xs) s \<Longrightarrow> sep_fold (\<lambda>x. I \<and>* P x) Q R xs s"
  apply (induct xs arbitrary: s)
   apply (clarsimp simp: sep_fold_def)
  apply (clarsimp simp: sep_fold_def)
  apply (sep_cancel+, clarsimp, sep_mp)
  apply (clarsimp simp: sep_conj_ac)
  done

lemma sep_factor_foldI':
  "(I \<and>* (sep_fold P Q (I \<longrightarrow>* R) xs)) s \<Longrightarrow> sep_fold (\<lambda>x. I \<and>* P x) (\<lambda>x. I \<and>* Q x) R xs s"
  apply (induct xs arbitrary:s; clarsimp simp: sep_fold_def)
   apply (sep_solve)
  apply (sep_cancel)+
  apply (sep_mp)
  apply (clarsimp simp: sep_conj_ac)
  done

lemma sep_factor_foldI'':
  "(\<And>s. R s \<Longrightarrow> (R' \<and>* (R' \<longrightarrow>* R)) s) \<Longrightarrow>
   precise R' \<Longrightarrow>
   (R' \<and>* sep_fold P Q (R' -* R) xs) s \<Longrightarrow>
   sep_fold (\<lambda>x. R' \<and>* P x) (\<lambda>x. R' \<and>* Q x) R xs s"
  apply (induct xs arbitrary:s; clarsimp simp: sep_fold_def)
   apply (erule septract_mp[where R'=R'])
    apply (assumption)+
  apply (clarsimp simp: sep_conj_ac)
  apply (sep_cancel)+
  apply (sep_mp)
  by (clarsimp simp: sep_conj_ac)

ML \<open>
 fun sep_fold_tactic ctxt =
     rotator' ctxt (resolve_tac ctxt [@{thm sep_fold_cong2 }])
                   (resolve_tac ctxt [@{thm sep_factor_foldI' }]) |>
     rotator' ctxt (resolve_tac ctxt [@{thm sep_fold_cong1 }]);
\<close>

method_setup sep_fold_cancel_inner =
  \<open>Scan.succeed (SIMPLE_METHOD' o sep_fold_tactic)\<close> \<open>Simple elimination of conjuncts\<close>

(* Cancels out shared resources according to the rule sep_factor_foldI' *)

lemma sep_map_set_sep_foldI:
  "distinct xs \<Longrightarrow>
   (sep_map_set_conj P (set xs) \<and>* (sep_map_set_conj Q (set xs) \<longrightarrow>* R)) s \<Longrightarrow>
   \<lparr>{P} \<and>* {Q} \<longrightarrow>* {R}\<rparr> xs s"
  apply (induct xs arbitrary: s; clarsimp simp: sep_fold_def)
   apply (sep_solve)
  apply (sep_cancel)+
  apply (sep_mp)
  apply (clarsimp simp: sep_conj_ac)
  done

lemma sep_fold_pure: "P \<Longrightarrow> sep_fold P' Q R xs s \<Longrightarrow> sep_fold (\<lambda>x s. P \<and> P' x s) Q R xs s "
  by (clarsimp simp: sep_fold_def)

lemma sep_fold_pure':
  "sep_fold P' Q R xs s \<Longrightarrow>
   (\<And>x. x \<in> set xs \<Longrightarrow> P x) \<Longrightarrow>
   sep_fold (\<lambda>x s. P x \<and> P' x s) Q R xs s "
  apply (clarsimp simp: sep_fold_def)
  apply (induct xs arbitrary: s; clarsimp)
  apply (sep_cancel)+
  apply (sep_mp)
  apply (clarsimp)
  done

lemma sep_fold_pure'':
  "sep_fold P' Q R xs s \<Longrightarrow>
   (\<And>x. x \<in> set xs \<Longrightarrow> P x) \<Longrightarrow>
   sep_fold (\<lambda>x s. P' x s \<and> P x ) Q R xs s "
  apply (clarsimp simp: sep_fold_def)
  apply (induct xs arbitrary: s; clarsimp)
  apply (sep_cancel)+
  apply (sep_mp)
  apply (clarsimp)
  done

method sep_fold_cancel = (
  sep_flatten?,
  ((rule sep_fold_pure' sep_fold_pure'')+)?,
  (sep_fold_cancel_inner, sep_cancel, sep_flatten?)+
)

end
