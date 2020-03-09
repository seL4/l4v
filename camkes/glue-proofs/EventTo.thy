(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)
chapter \<open>Event Receive\<close>
(*<*)
theory EventTo imports
  "CParser.CTranslation"
  "AutoCorres.AutoCorres"
begin

(* THIS THEORY IS GENERATED. DO NOT EDIT. *)

declare [[allow_underscore_idents=true]]

external_file "EventTo.c"
install_C_file "EventTo.c"

autocorres [ts_rules = nondet, no_heap_abs = seL4_SetMR] "EventTo.c"

context EventTo begin

(* Repeated constants from C. *)
abbreviation "seL4_MsgMaxLength \<equiv> 120"

(* Introduce this definition here so we can refer to it in the locale extension below. *)
definition
  seL4_SetMR_lifted' :: "int \<Rightarrow> word32 \<Rightarrow> lifted_globals \<Rightarrow> (unit \<times> lifted_globals) set \<times> bool"
where
  "seL4_SetMR_lifted' i val \<equiv>
   do
     ret' \<leftarrow> seL4_GetIPCBuffer';
     guard (\<lambda>s. i < seL4_MsgMaxLength);
     guard (\<lambda>s. 0 \<le> i);
     modify (\<lambda>s. s \<lparr>heap_seL4_IPCBuffer__C :=
       (heap_seL4_IPCBuffer__C s)(ret' :=
          msg_C_update (\<lambda>a. Arrays.update a (nat i) val)
             (heap_seL4_IPCBuffer__C s ret'))
     \<rparr>)
  od"

end

locale EventTo_glue = EventTo +
  assumes seL4_SetMR_axiom: "exec_concrete lift_global_heap (seL4_SetMR' i val) = seL4_SetMR_lifted' i val"
  assumes swi_safe_to_ignore[simplified, simp]:
    "asm_semantics_ok_to_ignore TYPE(nat) true (''swi '' @ x)"
begin

definition
  globals_frame_intact :: "lifted_globals \<Rightarrow> bool"
where
  "globals_frame_intact s \<equiv> is_valid_seL4_IPCBuffer__C'ptr s (Ptr (scast seL4_GlobalsFrame))"

definition
  ipc_buffer_valid :: "lifted_globals \<Rightarrow> bool"
where
  "ipc_buffer_valid s \<equiv> is_valid_seL4_IPCBuffer__C s (heap_seL4_IPCBuffer__C'ptr s (Ptr (scast seL4_GlobalsFrame)))"

definition
  setMR :: "lifted_globals \<Rightarrow> nat \<Rightarrow> word32 \<Rightarrow> lifted_globals"
where
  "setMR s i v \<equiv>
      s\<lparr>heap_seL4_IPCBuffer__C := (heap_seL4_IPCBuffer__C s)
          (heap_seL4_IPCBuffer__C'ptr s (Ptr (scast seL4_GlobalsFrame)) :=
              msg_C_update (\<lambda>a. Arrays.update a i v)
                 (heap_seL4_IPCBuffer__C s (heap_seL4_IPCBuffer__C'ptr s (Ptr (scast seL4_GlobalsFrame)))))\<rparr>"

definition
  setMRs :: "lifted_globals \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow>
             word32 \<Rightarrow> word32 \<Rightarrow> lifted_globals"
where
  "setMRs s mr0 mr1 mr2 mr3 \<equiv> setMR (setMR (setMR (setMR s 0 mr0) 1 mr1) 2 mr2) 3 mr3"

lemma seL4_SetMR_wp[wp_unsafe]:
  notes seL4_SetMR_axiom[simp]
  shows
  "\<lbrace>\<lambda>s. globals_frame_intact s \<and>
        ipc_buffer_valid s \<and>
        i \<ge> 0 \<and>
        i < seL4_MsgMaxLength \<and>
        (\<forall>x. P x (setMR s (nat i) v))\<rbrace>
     exec_concrete lift_global_heap (seL4_SetMR' i v)
   \<lbrace>P\<rbrace>!"
  apply (simp add:seL4_SetMR_lifted'_def seL4_GetIPCBuffer'_def)
  apply wp
  apply (simp add:setMR_def globals_frame_intact_def ipc_buffer_valid_def)
  done

lemma seL4_GetIPCBuffer_wp[wp_unsafe]: "\<lbrace>\<lambda>s. \<forall>x. P x s\<rbrace> seL4_GetIPCBuffer' \<lbrace>P\<rbrace>"
  apply (unfold seL4_GetIPCBuffer'_def)
  apply wp
  apply clarsimp
  done

definition
  thread_count :: word32
where
  "thread_count \<equiv> 2"

definition
  tls_ptr :: "lifted_globals \<Rightarrow> camkes_tls_t_C ptr"
where
  "tls_ptr s \<equiv> Ptr (ptr_val (heap_seL4_IPCBuffer__C'ptr s
     (Ptr (scast seL4_GlobalsFrame))) && 0xFFFFF000)"
definition
  tls :: "lifted_globals \<Rightarrow> camkes_tls_t_C"
where
  "tls s \<equiv> heap_camkes_tls_t_C s (tls_ptr s)"
definition
  tls_valid :: "lifted_globals \<Rightarrow> bool"
where
  "tls_valid s \<equiv> is_valid_camkes_tls_t_C s (tls_ptr s)"

lemma camkes_get_tls_wp':
  "\<forall>s'. \<lbrace>\<lambda>s. tls_valid s \<and> globals_frame_intact s \<and> s = s'\<rbrace>
     camkes_get_tls'
   \<lbrace>\<lambda>r s. s = s' \<and> r = tls_ptr s\<rbrace>!"
  apply (rule allI)
  apply (simp add:camkes_get_tls'_def seL4_GetIPCBuffer'_def tls_valid_def)
  apply wp
  apply (clarsimp simp:globals_frame_intact_def tls_ptr_def)
  done

lemmas camkes_get_tls_wp[wp] =
  camkes_get_tls_wp'[THEN validNF_make_schematic_post, simplified]

lemma abort_wp[wp]:
  "\<lbrace>\<lambda>_. False\<rbrace> abort' \<lbrace>P\<rbrace>!"
  apply (rule validNF_false_pre)
  done

lemma seL4_Poll_wp[wp_unsafe]:
  "\<lbrace>\<lambda>s. globals_frame_intact s \<and>
        ipc_buffer_valid s \<and>
        (\<forall>x b v0 v1 v2 v3. P x (heap_w32_update (\<lambda>a. a(badge := b)) (setMRs s v0 v1 v2 v3))) \<and>
        badge \<noteq> NULL \<and>
        is_valid_w32 s badge \<rbrace>
     seL4_Poll' cap badge
   \<lbrace>P\<rbrace>!"
  apply (simp add:seL4_Poll'_def seL4_GetIPCBuffer'_def)
  apply (wp seL4_SetMR_wp)
  apply (simp add:globals_frame_intact_def ipc_buffer_valid_def setMRs_def setMR_def)
  done

lemma seL4_Wait_wp[wp_unsafe]:
  "\<lbrace>\<lambda>s. globals_frame_intact s \<and>
        ipc_buffer_valid s \<and>
        (\<forall>x v0 v1 v2 v3. P x (setMRs s v0 v1 v2 v3))\<rbrace>
     seL4_Wait' cap NULL
   \<lbrace>P\<rbrace>!"
  apply (simp add:seL4_Wait'_def seL4_GetIPCBuffer'_def)
  apply (wp seL4_SetMR_wp)
  apply (simp add:globals_frame_intact_def ipc_buffer_valid_def setMRs_def setMR_def)
  done
(*>*)

text \<open>
  The glue code for receiving an event provides two functions, poll and wait. These functions
  perform a non-blocking and blocking check for an incoming event, respectively. To show the safety
  of these two generated functions we make a number of assumptions. Namely, that the globals frame,
  IPC buffer and TLS regions have not been interfered with and that any necessary thread-local
  variables are still valid. Non-malicious user code should never touch any of these
  resources. The generated code for poll and its safety proof are as follows.
  \clisting{eventto-poll.c}
\<close>
lemma EventTo_poll_nf:
  notes seL4_SetMR_wp[wp]
  shows
  "\<lbrace>\<lambda>s. is_valid_w32 s (Ptr (symbol_table ''badge_1'')) \<and>
        Ptr (symbol_table ''badge_1'') \<noteq> NULL \<and>
        is_valid_w32 s (Ptr (symbol_table ''badge_2'')) \<and>
        Ptr (symbol_table ''badge_2'') \<noteq> NULL \<and>
        globals_frame_intact s \<and>
        ipc_buffer_valid s \<and>
        tls_valid s \<and>
        thread_index_C (tls s) \<in> {1..thread_count}\<rbrace>
   EventTo_poll'
  \<lbrace>\<lambda>r s. is_valid_w32 s (Ptr (symbol_table ''badge_1'')) \<and>
         Ptr (symbol_table ''badge_1'') \<noteq> NULL \<and>
         is_valid_w32 s (Ptr (symbol_table ''badge_2'')) \<and>
         Ptr (symbol_table ''badge_2'') \<noteq> NULL \<and>
         globals_frame_intact s \<and>
         ipc_buffer_valid s \<and>
         tls_valid s \<and>
         thread_index_C (tls s) \<in> {1..thread_count} \<and>
         (r = 0 \<or> r = 1)\<rbrace>!"
  apply (simp add:EventTo_poll'_def get_badge'_def)
  apply (wp seL4_Poll_wp)
  apply (clarsimp simp:globals_frame_intact_def seL4_GetIPCBuffer'_def
                       thread_count_def setMRs_def setMR_def
                       ipc_buffer_valid_def tls_valid_def tls_ptr_def
                       tls_def)
  apply unat_arith
  done

(*<*)
(* This function is invoked on startup of this connector and, while we can show its correctness as
 * below, it is not interesting for the purposes of this report.
 *)
lemma EventTo_run_nf: "\<lbrace>\<lambda>s. \<forall>r. P r s\<rbrace> EventTo__run' \<lbrace>P\<rbrace>!"
  apply (unfold EventTo__run'_def)
  apply wp
  apply simp
  done
(*>*)

text \<open>
  The code for wait is somewhat simpler as it is just a wrapper around the seL4 primitive.
  \clisting{eventto-wait.c}
\<close>
lemma EventTo_wait_nf:
  notes seL4_SetMR_wp[wp]
  shows
  "\<lbrace>\<lambda>s. globals_frame_intact s \<and> ipc_buffer_valid s\<rbrace>
    EventTo_wait'
   \<lbrace>\<lambda>_ s. globals_frame_intact s \<and> ipc_buffer_valid s\<rbrace>!"
  apply (simp add:EventTo_wait'_def)
  apply (wp seL4_Wait_wp)
  apply (simp add:globals_frame_intact_def ipc_buffer_valid_def setMRs_def
                  setMR_def)
  done

(*<*)
end

end
(*>*)
