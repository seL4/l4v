(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)
chapter \<open>RPC Receive\<close>
(*<*)
theory RPCTo imports
  "CParser.CTranslation"
  "AutoCorres.AutoCorres"
begin

(* THIS THEORY IS GENERATED. DO NOT EDIT. *)

(* ucast is type-polymorphic, but often appears in a visually indistinguishable form in proofs.
 * These abbreviations help you identify which type signature you're looking at. These
 * abbreviations need to exist outside the locale in order to be used in output.
 *)
abbreviation "ucast_32_to_32 \<equiv> ucast :: word32 \<Rightarrow> word32"
abbreviation "ucast_s32_to_32 \<equiv> ucast :: sword32 \<Rightarrow> word32"
abbreviation "ucast_32_to_s32 \<equiv> ucast :: word32 \<Rightarrow> sword32"
abbreviation "ucast_s32_to_s32 \<equiv> ucast :: sword32 \<Rightarrow> sword32"

(* As above for scast. *)
abbreviation "scast_32_to_32 \<equiv>   scast :: word32 \<Rightarrow> word32"
abbreviation "scast_s32_to_32 \<equiv>  scast :: sword32 \<Rightarrow> word32"
abbreviation "scast_32_to_s32 \<equiv>  scast :: word32 \<Rightarrow> sword32"
abbreviation "scast_s32_to_s32 \<equiv> scast :: sword32 \<Rightarrow> sword32"

declare [[allow_underscore_idents=true]]

external_file "RPCTo.c"
install_C_file "RPCTo.c"

(* Use non-determinism instead of the standard option monad type stregthening and do not heap
 * abstract seL4_SetMR.
 *)
autocorres [ts_rules = nondet, no_heap_abs = seL4_SetMR] "RPCTo.c"

context RPCTo begin

(* Repeated constants from C. *)
abbreviation "seL4_MsgMaxLength \<equiv> 120"

definition
  seL4_SetMR_lifted' :: "int \<Rightarrow> word32 \<Rightarrow> lifted_globals \<Rightarrow> (unit \<times> lifted_globals) set \<times> bool"
where
  "seL4_SetMR_lifted' i val \<equiv>
   do
     ret' \<leftarrow> seL4_GetIPCBuffer';
     guard (\<lambda>s. i < seL4_MsgMaxLength);
     guard (\<lambda>s. 0 \<le> i);
     modify (\<lambda>s. s \<lparr>heap_seL4_IPCBuffer__C := (heap_seL4_IPCBuffer__C s)(ret' :=
        msg_C_update  (
            \<lambda>a. Arrays.update a (nat i) val) (heap_seL4_IPCBuffer__C s ret')
          )  \<rparr>)
  od"

end

locale RPCTo_glue = RPCTo +
  assumes seL4_SetMR_axiom: "exec_concrete lift_global_heap (seL4_SetMR' i val) = seL4_SetMR_lifted' i val"
  assumes RPCTo_echo_int_wp: "\<lbrace>\<lambda>s0'. \<forall>r1'. P2' r1'
    s0'\<rbrace> RPCTo_echo_int' i3' \<lbrace>P2'\<rbrace>!"
  assumes RPCTo_echo_parameter_wp: "\<lbrace>\<lambda>s4'. \<forall>r5'. P6' r5'
    s4'\<rbrace> RPCTo_echo_parameter' pin7' pout8' \<lbrace>P6'\<rbrace>!"
  assumes RPCTo_echo_char_wp: "\<lbrace>\<lambda>s9'. \<forall>r10'. P11' r10'
    s9'\<rbrace> RPCTo_echo_char' i12' \<lbrace>P11'\<rbrace>!"
  assumes RPCTo_increment_char_wp: "\<lbrace>\<lambda>s13'. \<forall>r14'. P15'
    r14' s13'\<rbrace> RPCTo_increment_char' x16' \<lbrace>P15'\<rbrace>!"
  assumes RPCTo_increment_parameter_wp: "\<lbrace>\<lambda>s17'. \<forall>r18'.
    P19' r18' s17'\<rbrace> RPCTo_increment_parameter' x20'
    \<lbrace>P19'\<rbrace>!"
  assumes RPCTo_increment_64_wp: "\<lbrace>\<lambda>s21'. \<forall>r22'. P23'
    r22' s21'\<rbrace> RPCTo_increment_64' x24' \<lbrace>P23'\<rbrace>!"
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

lemma abort_wp[wp]:
  "\<lbrace>\<lambda>_. False\<rbrace> abort' \<lbrace>P\<rbrace>!"
  by (rule validNF_false_pre)

definition
  setMR :: "lifted_globals \<Rightarrow> nat \<Rightarrow> word32 \<Rightarrow> lifted_globals"
where
  "setMR s i v \<equiv>
      s\<lparr>heap_seL4_IPCBuffer__C := (heap_seL4_IPCBuffer__C s)
        (heap_seL4_IPCBuffer__C'ptr s (Ptr (scast seL4_GlobalsFrame)) :=
          msg_C_update (\<lambda>a. Arrays.update a i v)
            (heap_seL4_IPCBuffer__C s (heap_seL4_IPCBuffer__C'ptr s
              (Ptr (scast seL4_GlobalsFrame)))))\<rparr>"

definition
  setMRs :: "lifted_globals \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow>
             word32 \<Rightarrow> word32 \<Rightarrow> lifted_globals"
where
  "setMRs s mr0 mr1 mr2 mr3 \<equiv>
    setMR (setMR (setMR (setMR s 0 mr0) 1 mr1) 2 mr2) 3 mr3"

lemma seL4_GetIPCBuffer_wp':
  "\<forall>s'. \<lbrace>\<lambda>s. globals_frame_intact s \<and>
             s = s'\<rbrace>
     seL4_GetIPCBuffer'
   \<lbrace>\<lambda>r s. r = heap_seL4_IPCBuffer__C'ptr s (Ptr (scast seL4_GlobalsFrame)) \<and>
          s = s'\<rbrace>!"
  apply (rule allI)
  apply (simp add:seL4_GetIPCBuffer'_def)
  apply wp
  apply (clarsimp simp:globals_frame_intact_def)
  done

lemmas seL4_GetIPCBuffer_wp[wp_unsafe] =
  seL4_GetIPCBuffer_wp'[THEN validNF_make_schematic_post, simplified]

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
  apply (simp add:seL4_SetMR_lifted'_def)
  apply (wp seL4_GetIPCBuffer_wp)
  apply (simp add:setMR_def globals_frame_intact_def ipc_buffer_valid_def)
  done

lemma seL4_GetMR_wp[wp_unsafe]:
  "\<lbrace>\<lambda>s. \<forall>x. i \<ge> 0 \<and>
            i < seL4_MsgMaxLength \<and>
            globals_frame_intact s \<and>
            ipc_buffer_valid s \<and>
            P x s\<rbrace>
     seL4_GetMR' i
   \<lbrace>P\<rbrace>!"
  apply (simp add:seL4_GetMR'_def)
  apply (wp seL4_GetIPCBuffer_wp)
  apply (simp add:globals_frame_intact_def ipc_buffer_valid_def)
  done

lemma seL4_Wait_wp[wp_unsafe]:
  "\<lbrace>\<lambda>s. globals_frame_intact s \<and>
        ipc_buffer_valid s \<and>
        (\<forall>x v0 v1 v2 v3. P x (setMRs s v0 v1 v2 v3))\<rbrace>
     seL4_Wait' cap NULL
   \<lbrace>P\<rbrace>!"
  apply (simp add:seL4_Wait'_def)
  apply (wp seL4_SetMR_wp)
  apply (simp add:globals_frame_intact_def ipc_buffer_valid_def setMRs_def
                  setMR_def)
  done

lemma seL4_ReplyWait_wp[wp_unsafe]:
  "\<lbrace>\<lambda>s. globals_frame_intact s \<and>
        ipc_buffer_valid s \<and>
        (\<forall>x v0 v1 v2 v3. P x (setMRs s v0 v1 v2 v3))\<rbrace>
     seL4_ReplyWait' cap info NULL
   \<lbrace>P\<rbrace>!"
  apply (simp add:seL4_ReplyWait'_def seL4_GetMR'_def)
  apply (wp seL4_SetMR_wp seL4_GetIPCBuffer_wp)
  apply (simp add:globals_frame_intact_def ipc_buffer_valid_def setMRs_def
                  setMR_def)
  done

definition
  thread_count :: word32
where
  "thread_count \<equiv> 2"

(* Various definitions used in assumptions on the TLS region. *)
definition
  tls_ptr :: "lifted_globals \<Rightarrow> camkes_tls_t_C ptr"
where
  "tls_ptr s \<equiv> Ptr (ptr_val (heap_seL4_IPCBuffer__C'ptr s
     (Ptr (scast_s32_to_32 seL4_GlobalsFrame))) && 0xFFFFF000)"
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

lemmas camkes_get_tls'_wp[wp] =
  camkes_get_tls_wp'[THEN validNF_make_schematic_post, simplified]
(*>*)

text \<open>
  The generated definitions and lemmas in this chapter have been formed from the same procedure
  specification provided in the previous chapter. Again, to give some context to the proofs below,
  the generated receiving code for the \code{echo\_int} method is given here.
  \clisting{to-echo-int.c}

  The glue code receiving an RPC invocation from another component unmarshals arguments and then
  invokes the user's interface implementation. To show the safety of this glue code we assume that
  the user's implementation being invoked does not modify the state of the system. For example, for
  the \code{echo\_int} method, we assume the following property.

  @{term "\<lbrace>\<lambda>s. \<forall>r. P r s\<rbrace> RPCTo_echo_int' i \<lbrace>P\<rbrace>!"}

  The unbound variables in the above statement, @{term P} and @{term i}, unify
  with any suitably typed expression to allow use of the assumption in all contexts. This property
  states that the
  user's implementation, \code{RPCTo\_echo\_int}, only manipulates local variables and does not
  write to any global memory. The property we ultimately need from the user's implementation is
  weaker than this; that the function does not invalidate the TLS memory. In future the assumption
  above will be reduced to this, but for now we assume this stronger property.
\<close>

text \<open>
  For each thread-local variable, a function to retrieve a pointer to the relevant memory for the
  current thread is emitted. For each of these we generate a proof that it does not modify the
  state. This is uninteresting, in and of itself, but useful for reasoning about glue code that
  calls these.
\<close>
text \<open>\newpage\<close>

lemma get_echo_int_i_nf:
  "\<forall>s25'.
    \<lbrace>\<lambda>s26'. globals_frame_intact s26' \<and>
            ipc_buffer_valid s26' \<and>
            tls_valid s26' \<and>
            thread_index_C (tls s26') \<in> {1..thread_count} \<and>
            is_valid_w32 s26' (Ptr (symbol_table ''echo_int_i_1'')) \<and>
            is_valid_w32 s26' (Ptr (symbol_table ''echo_int_i_2'')) \<and>
            s26' = s25'\<rbrace>
     get_echo_int_i'
    \<lbrace>\<lambda>r27' s26'. r27' \<in> {Ptr (symbol_table
      ''echo_int_i_1''), Ptr (symbol_table ''echo_int_i_2'')} \<and>
      s26' = s25'\<rbrace>!"
  apply (rule allI)
  apply (simp add:get_echo_int_i'_def)
  apply (wp seL4_GetIPCBuffer_wp)
  apply (clarsimp simp:thread_count_def tls_valid_def tls_def)
  apply unat_arith
  done

    (*<*)

lemmas get_echo_int_i_wp[wp_unsafe] =
  get_echo_int_i_nf[THEN validNF_make_schematic_post, simplified]

definition
  update_global_w32 :: "char list \<Rightarrow> word32 \<Rightarrow> lifted_globals \<Rightarrow> lifted_globals"
where
  "update_global_w32 symbol v s \<equiv>
     heap_w32_update (\<lambda>c. c(Ptr (symbol_table symbol) := (ucast v))) s"

lemma get_echo_parameter_pin_nf:
  "\<forall>s28'.
    \<lbrace>\<lambda>s29'. globals_frame_intact s29' \<and>
            ipc_buffer_valid s29' \<and>
            tls_valid s29' \<and>
            thread_index_C (tls s29') \<in> {1..thread_count} \<and>
            is_valid_w32 s29' (Ptr (symbol_table ''echo_parameter_pin_1'')) \<and>
            is_valid_w32 s29' (Ptr (symbol_table ''echo_parameter_pin_2'')) \<and>
            s29' = s28'\<rbrace>
     get_echo_parameter_pin'
    \<lbrace>\<lambda>r30' s29'. r30' \<in> {Ptr (symbol_table
      ''echo_parameter_pin_1''), Ptr (symbol_table ''echo_parameter_pin_2'')}
      \<and>
      s29' = s28'\<rbrace>!"
  apply (rule allI)
  apply (simp add:get_echo_parameter_pin'_def)
  apply (wp seL4_GetIPCBuffer_wp)
  apply (clarsimp simp:thread_count_def tls_valid_def tls_def)
  apply unat_arith
  done

lemmas get_echo_parameter_pin_wp[wp_unsafe] =
  get_echo_parameter_pin_nf[THEN validNF_make_schematic_post, simplified]

lemma get_echo_parameter_pout_nf:
  "\<forall>s31'.
    \<lbrace>\<lambda>s32'. globals_frame_intact s32' \<and>
            ipc_buffer_valid s32' \<and>
            tls_valid s32' \<and>
            thread_index_C (tls s32') \<in> {1..thread_count} \<and>
            is_valid_w32 s32' (Ptr (symbol_table ''echo_parameter_pout_1'')) \<and>
            is_valid_w32 s32' (Ptr (symbol_table ''echo_parameter_pout_2'')) \<and>
            s32' = s31'\<rbrace>
     get_echo_parameter_pout'
    \<lbrace>\<lambda>r33' s32'. r33' \<in> {Ptr (symbol_table
      ''echo_parameter_pout_1''), Ptr (symbol_table ''echo_parameter_pout_2'')
      } \<and>
      s32' = s31'\<rbrace>!"
  apply (rule allI)
  apply (simp add:get_echo_parameter_pout'_def)
  apply (wp seL4_GetIPCBuffer_wp)
  apply (clarsimp simp:thread_count_def tls_valid_def tls_def)
  apply unat_arith
  done

lemmas get_echo_parameter_pout_wp[wp_unsafe] =
  get_echo_parameter_pout_nf[THEN validNF_make_schematic_post, simplified]

lemma get_echo_char_i_nf:
  "\<forall>s34'.
    \<lbrace>\<lambda>s35'. globals_frame_intact s35' \<and>
            ipc_buffer_valid s35' \<and>
            tls_valid s35' \<and>
            thread_index_C (tls s35') \<in> {1..thread_count} \<and>
            is_valid_w8 s35' (Ptr (symbol_table ''echo_char_i_1'')) \<and>
            is_valid_w8 s35' (Ptr (symbol_table ''echo_char_i_2'')) \<and>
            s35' = s34'\<rbrace>
     get_echo_char_i'
    \<lbrace>\<lambda>r36' s35'. r36' \<in> {Ptr (symbol_table
      ''echo_char_i_1''), Ptr (symbol_table ''echo_char_i_2'')} \<and>
      s35' = s34'\<rbrace>!"
  apply (rule allI)
  apply (simp add:get_echo_char_i'_def)
  apply (wp seL4_GetIPCBuffer_wp)
  apply (clarsimp simp:thread_count_def tls_valid_def tls_def)
  apply unat_arith
  done

lemmas get_echo_char_i_wp[wp_unsafe] =
  get_echo_char_i_nf[THEN validNF_make_schematic_post, simplified]

definition
  update_global_w8 :: "char list \<Rightarrow> word32 \<Rightarrow> lifted_globals \<Rightarrow> lifted_globals"
where
  "update_global_w8 symbol v s \<equiv>
     heap_w8_update (\<lambda>c. c(Ptr (symbol_table symbol) := (ucast v))) s"

lemma get_increment_char_x_nf:
  "\<forall>s37'.
    \<lbrace>\<lambda>s38'. globals_frame_intact s38' \<and>
            ipc_buffer_valid s38' \<and>
            tls_valid s38' \<and>
            thread_index_C (tls s38') \<in> {1..thread_count} \<and>
            is_valid_w8 s38' (Ptr (symbol_table ''increment_char_x_1'')) \<and>
            is_valid_w8 s38' (Ptr (symbol_table ''increment_char_x_2'')) \<and>
            s38' = s37'\<rbrace>
     get_increment_char_x'
    \<lbrace>\<lambda>r39' s38'. r39' \<in> {Ptr (symbol_table
      ''increment_char_x_1''), Ptr (symbol_table ''increment_char_x_2'')}
      \<and>
      s38' = s37'\<rbrace>!"
  apply (rule allI)
  apply (simp add:get_increment_char_x'_def)
  apply (wp seL4_GetIPCBuffer_wp)
  apply (clarsimp simp:thread_count_def tls_valid_def tls_def)
  apply unat_arith
  done

lemmas get_increment_char_x_wp[wp_unsafe] =
  get_increment_char_x_nf[THEN validNF_make_schematic_post, simplified]

lemma get_increment_parameter_x_nf:
  "\<forall>s40'.
    \<lbrace>\<lambda>s41'. globals_frame_intact s41' \<and>
            ipc_buffer_valid s41' \<and>
            tls_valid s41' \<and>
            thread_index_C (tls s41') \<in> {1..thread_count} \<and>
            is_valid_w32 s41' (Ptr (symbol_table ''increment_parameter_x_1'')) \<and>
            is_valid_w32 s41' (Ptr (symbol_table ''increment_parameter_x_2'')) \<and>
            s41' = s40'\<rbrace>
     get_increment_parameter_x'
    \<lbrace>\<lambda>r42' s41'. r42' \<in> {Ptr (symbol_table
      ''increment_parameter_x_1''), Ptr (symbol_table
      ''increment_parameter_x_2'')} \<and>
      s41' = s40'\<rbrace>!"
  apply (rule allI)
  apply (simp add:get_increment_parameter_x'_def)
  apply (wp seL4_GetIPCBuffer_wp)
  apply (clarsimp simp:thread_count_def tls_valid_def tls_def)
  apply unat_arith
  done

lemmas get_increment_parameter_x_wp[wp_unsafe] =
  get_increment_parameter_x_nf[THEN validNF_make_schematic_post, simplified]

lemma get_increment_64_x_nf:
  "\<forall>s43'.
    \<lbrace>\<lambda>s44'. globals_frame_intact s44' \<and>
            ipc_buffer_valid s44' \<and>
            tls_valid s44' \<and>
            thread_index_C (tls s44') \<in> {1..thread_count} \<and>
            is_valid_w64 s44' (Ptr (symbol_table ''increment_64_x_1'')) \<and>
            is_valid_w64 s44' (Ptr (symbol_table ''increment_64_x_2'')) \<and>
            s44' = s43'\<rbrace>
     get_increment_64_x'
    \<lbrace>\<lambda>r45' s44'. r45' \<in> {Ptr (symbol_table
      ''increment_64_x_1''), Ptr (symbol_table ''increment_64_x_2'')} \<and>
      s44' = s43'\<rbrace>!"
  apply (rule allI)
  apply (simp add:get_increment_64_x'_def)
  apply (wp seL4_GetIPCBuffer_wp)
  apply (clarsimp simp:thread_count_def tls_valid_def tls_def)
  apply unat_arith
  done

lemmas get_increment_64_x_wp[wp_unsafe] =
  get_increment_64_x_nf[THEN validNF_make_schematic_post, simplified]

definition
  update_global_w64 :: "char list \<Rightarrow> word32 \<Rightarrow> lifted_globals \<Rightarrow> lifted_globals"
where
  "update_global_w64 symbol v s \<equiv>
     heap_w64_update (\<lambda>c. c(Ptr (symbol_table symbol) := (ucast v))) s"

definition
  update_global_w64_high :: "char list \<Rightarrow> word32 \<Rightarrow> lifted_globals \<Rightarrow> lifted_globals"
where
  "update_global_w64_high symbol high s \<equiv>
     heap_w64_update (\<lambda>c. c(Ptr (symbol_table symbol) :=
       (heap_w64 s (Ptr (symbol_table symbol))) || (ucast high << 32))) s"

(*>*)
text \<open>
  For each method in the procedure we generate a function for specifically handling receiving of a
  call to that method. A top-level dispatch function is generated that selects the appropriate
  handler to invoke after receiving an RPC invocation. The handler function for the first method is
  the code given at the start of this chapter. We generate proofs that the handler
  functions do not fail, as given below.
\<close>

lemma echo_int_internal_wp[wp_unsafe]:
  notes seL4_GetMR_wp[wp] seL4_SetMR_wp[wp]
  shows
  "\<lbrace>\<lambda>s46'. globals_frame_intact s46' \<and>
           ipc_buffer_valid s46' \<and>
           tls_valid s46' \<and>
           thread_index_C (tls s46') \<in> {1..thread_count} \<and>
           is_valid_w32 s46' (Ptr (symbol_table ''echo_int_i_1'')) \<and>
           is_valid_w32 s46' (Ptr (symbol_table ''echo_int_i_2'')) \<and>
           (\<forall>x r47' i_in_value .
           \<forall> i_symbol \<in> {''echo_int_i_1'', ''echo_int_i_2''}.
           P48' x
           (setMR (update_global_w32 i_symbol i_in_value s46') 0 r47')
           )\<rbrace>
    echo_int_internal'
   \<lbrace>P48'\<rbrace>!"
  apply (simp add:echo_int_internal'_def)
  apply wp
       apply (wp RPCTo_echo_int_wp)+
     apply (wp get_echo_int_i_wp)+
  apply (clarsimp simp:globals_frame_intact_def ipc_buffer_valid_def
    tls_valid_def tls_def tls_ptr_def thread_count_def setMR_def ucast_id
    update_global_w32_def)
  apply force?
  done

lemma echo_parameter_internal_wp[wp_unsafe]:
  notes seL4_GetMR_wp[wp] seL4_SetMR_wp[wp]
  shows
  "\<lbrace>\<lambda>s49'. globals_frame_intact s49' \<and>
           ipc_buffer_valid s49' \<and>
           tls_valid s49' \<and>
           thread_index_C (tls s49') \<in> {1..thread_count} \<and>
           is_valid_w32 s49' (Ptr (symbol_table ''echo_parameter_pin_1'')) \<and>
           is_valid_w32 s49' (Ptr (symbol_table ''echo_parameter_pin_2'')) \<and>
           is_valid_w32 s49' (Ptr (symbol_table ''echo_parameter_pout_1'')) \<and>
           is_valid_w32 s49' (Ptr (symbol_table ''echo_parameter_pout_2'')) \<and>
           (\<forall>x r50' pin_in_value pout_out_value .
           \<forall> pin_symbol \<in> {''echo_parameter_pin_1'',
           ''echo_parameter_pin_2''}.
           \<forall> pout_symbol \<in> {''echo_parameter_pout_1'',
           ''echo_parameter_pout_2''}.
           P51' x
           (setMR (setMR (update_global_w32 pin_symbol pin_in_value s49') 0
           r50') 1 pout_out_value))\<rbrace>
    echo_parameter_internal'
   \<lbrace>P51'\<rbrace>!"
  apply (simp add:echo_parameter_internal'_def)
  apply wp
       apply (wp RPCTo_echo_parameter_wp)+
     apply (wp get_echo_parameter_pout_wp)
     apply (wp get_echo_parameter_pin_wp)+
  apply (clarsimp simp:globals_frame_intact_def ipc_buffer_valid_def
    tls_valid_def tls_def tls_ptr_def thread_count_def setMR_def ucast_id
    update_global_w32_def)
  apply force?
  done

lemma echo_char_internal_wp[wp_unsafe]:
  notes seL4_GetMR_wp[wp] seL4_SetMR_wp[wp]
  shows
  "\<lbrace>\<lambda>s52'. globals_frame_intact s52' \<and>
           ipc_buffer_valid s52' \<and>
           tls_valid s52' \<and>
           thread_index_C (tls s52') \<in> {1..thread_count} \<and>
           is_valid_w8 s52' (Ptr (symbol_table ''echo_char_i_1'')) \<and>
           is_valid_w8 s52' (Ptr (symbol_table ''echo_char_i_2'')) \<and>
           (\<forall>x r53' i_in_value .
           \<forall> i_symbol \<in> {''echo_char_i_1'', ''echo_char_i_2''}.
           P54' x
           (setMR (update_global_w8 i_symbol i_in_value s52') 0 r53')
           )\<rbrace>
    echo_char_internal'
   \<lbrace>P54'\<rbrace>!"
  apply (simp add:echo_char_internal'_def)
  apply wp
       apply (wp RPCTo_echo_char_wp)+
     apply (wp get_echo_char_i_wp)+
  apply (clarsimp simp:globals_frame_intact_def ipc_buffer_valid_def
    tls_valid_def tls_def tls_ptr_def thread_count_def setMR_def ucast_id
    update_global_w8_def)
  apply force?
  done

lemma increment_char_internal_wp[wp_unsafe]:
  notes seL4_GetMR_wp[wp] seL4_SetMR_wp[wp]
  shows
  "\<lbrace>\<lambda>s55'. globals_frame_intact s55' \<and>
           ipc_buffer_valid s55' \<and>
           tls_valid s55' \<and>
           thread_index_C (tls s55') \<in> {1..thread_count} \<and>
           is_valid_w8 s55' (Ptr (symbol_table ''increment_char_x_1'')) \<and>
           is_valid_w8 s55' (Ptr (symbol_table ''increment_char_x_2'')) \<and>
           (\<forall>x x_in_value x_out_value .
           \<forall> x_symbol \<in> {''increment_char_x_1'',
           ''increment_char_x_2''}.
           P57' x
           (setMR (update_global_w8 x_symbol x_in_value s55') 0 x_out_value)
           )\<rbrace>
    increment_char_internal'
   \<lbrace>P57'\<rbrace>!"
  apply (simp add:increment_char_internal'_def)
  apply wp
       apply (wp RPCTo_increment_char_wp)+
     apply (wp get_increment_char_x_wp)+
  apply (clarsimp simp:globals_frame_intact_def ipc_buffer_valid_def
    tls_valid_def tls_def tls_ptr_def thread_count_def setMR_def ucast_id
    update_global_w8_def)
  apply force?
  done

lemma increment_parameter_internal_wp[wp_unsafe]:
  notes seL4_GetMR_wp[wp] seL4_SetMR_wp[wp]
  shows
  "\<lbrace>\<lambda>s58'. globals_frame_intact s58' \<and>
           ipc_buffer_valid s58' \<and>
           tls_valid s58' \<and>
           thread_index_C (tls s58') \<in> {1..thread_count} \<and>
           is_valid_w32 s58' (Ptr (symbol_table ''increment_parameter_x_1'')) \<and>
           is_valid_w32 s58' (Ptr (symbol_table ''increment_parameter_x_2'')) \<and>
           (\<forall>x x_in_value x_out_value .
           \<forall> x_symbol \<in> {''increment_parameter_x_1'',
           ''increment_parameter_x_2''}.
           P60' x
           (setMR (update_global_w32 x_symbol x_in_value s58') 0 x_out_value)
           )\<rbrace>
    increment_parameter_internal'
   \<lbrace>P60'\<rbrace>!"
  apply (simp add:increment_parameter_internal'_def)
  apply wp
       apply (wp RPCTo_increment_parameter_wp)+
     apply (wp get_increment_parameter_x_wp)+
  apply (clarsimp simp:globals_frame_intact_def ipc_buffer_valid_def
    tls_valid_def tls_def tls_ptr_def thread_count_def setMR_def ucast_id
    update_global_w32_def)
  apply force?
  done

lemma increment_64_internal_wp[wp_unsafe]:
  notes seL4_GetMR_wp[wp] seL4_SetMR_wp[wp]
  shows
  "\<lbrace>\<lambda>s61'. globals_frame_intact s61' \<and>
           ipc_buffer_valid s61' \<and>
           tls_valid s61' \<and>
           thread_index_C (tls s61') \<in> {1..thread_count} \<and>
           is_valid_w64 s61' (Ptr (symbol_table ''increment_64_x_1'')) \<and>
           is_valid_w64 s61' (Ptr (symbol_table ''increment_64_x_2'')) \<and>
           (\<forall>x x_in_value x_in_value_high x_out_value x_out_value_high .
           \<forall> x_symbol \<in> {''increment_64_x_1'',
           ''increment_64_x_2''}.
           P63' x
           (setMR (setMR (update_global_w64_high x_symbol x_in_value_high
           (update_global_w64 x_symbol x_in_value s61') ) 0 x_out_value) 1
           x_out_value_high))\<rbrace>
    increment_64_internal'
   \<lbrace>P63'\<rbrace>!"
  apply (simp add:increment_64_internal'_def)
  apply wp
       apply (wp RPCTo_increment_64_wp)+
     apply (wp get_increment_64_x_wp)+
  apply (clarsimp simp:globals_frame_intact_def ipc_buffer_valid_def
    tls_valid_def tls_def tls_ptr_def thread_count_def setMR_def ucast_id
    update_global_w64_def update_global_w64_high_def)
  apply force?
  done

text \<open>
  \newpage
  With proofs that the handler functions do not fail, the proof of the same for the top-level
  dispatch function can be generated by composing these. Note that we accumulate the pre- and
  post-conditions from the leaf functions.
\<close>

lemma RPCTo_run_internal_wp[wp_unsafe]:
  notes seL4_SetMR_axiom[simp] seL4_SetMR_wp[wp] seL4_GetMR_wp[wp]
  shows
  "\<lbrace>\<lambda>s64'. globals_frame_intact s64' \<and>
           tls_valid s64' \<and>
           thread_index_C (tls s64') \<in> {1..thread_count} \<and>
           is_valid_w32 s64' (Ptr (symbol_table ''echo_int_i_1'')) \<and>
           is_valid_w32 s64' (Ptr (symbol_table ''echo_int_i_2'')) \<and>
           is_valid_w32 s64' (Ptr (symbol_table ''echo_parameter_pin_1'')) \<and>
           is_valid_w32 s64' (Ptr (symbol_table ''echo_parameter_pin_2'')) \<and>
           is_valid_w32 s64' (Ptr (symbol_table ''echo_parameter_pout_1'')) \<and>
           is_valid_w32 s64' (Ptr (symbol_table ''echo_parameter_pout_2'')) \<and>
           is_valid_w8 s64' (Ptr (symbol_table ''echo_char_i_1'')) \<and>
           is_valid_w8 s64' (Ptr (symbol_table ''echo_char_i_2'')) \<and>
           is_valid_w8 s64' (Ptr (symbol_table ''increment_char_x_1'')) \<and>
           is_valid_w8 s64' (Ptr (symbol_table ''increment_char_x_2'')) \<and>
           is_valid_w32 s64' (Ptr (symbol_table ''increment_parameter_x_1'')) \<and>
           is_valid_w32 s64' (Ptr (symbol_table ''increment_parameter_x_2'')) \<and>
           is_valid_w64 s64' (Ptr (symbol_table ''increment_64_x_1'')) \<and>
           is_valid_w64 s64' (Ptr (symbol_table ''increment_64_x_2'')) \<and>
           ipc_buffer_valid s64'\<rbrace>
    RPCTo__run_internal' first65' info66'
  \<lbrace>\<lambda>_ s64'. globals_frame_intact s64' \<and>
           tls_valid s64' \<and>
           thread_index_C (tls s64') \<in> {1..thread_count} \<and>
           is_valid_w32 s64' (Ptr (symbol_table ''echo_int_i_1'')) \<and>
           is_valid_w32 s64' (Ptr (symbol_table ''echo_int_i_2'')) \<and>
           is_valid_w32 s64' (Ptr (symbol_table ''echo_parameter_pin_1'')) \<and>
           is_valid_w32 s64' (Ptr (symbol_table ''echo_parameter_pin_2'')) \<and>
           is_valid_w32 s64' (Ptr (symbol_table ''echo_parameter_pout_1'')) \<and>
           is_valid_w32 s64' (Ptr (symbol_table ''echo_parameter_pout_2'')) \<and>
           is_valid_w8 s64' (Ptr (symbol_table ''echo_char_i_1'')) \<and>
           is_valid_w8 s64' (Ptr (symbol_table ''echo_char_i_2'')) \<and>
           is_valid_w8 s64' (Ptr (symbol_table ''increment_char_x_1'')) \<and>
           is_valid_w8 s64' (Ptr (symbol_table ''increment_char_x_2'')) \<and>
           is_valid_w32 s64' (Ptr (symbol_table ''increment_parameter_x_1'')) \<and>
           is_valid_w32 s64' (Ptr (symbol_table ''increment_parameter_x_2'')) \<and>
           is_valid_w64 s64' (Ptr (symbol_table ''increment_64_x_1'')) \<and>
           is_valid_w64 s64' (Ptr (symbol_table ''increment_64_x_2'')) \<and>
           ipc_buffer_valid s64'\<rbrace>!"
  apply (simp add:RPCTo__run_internal'_def)
  apply wp
       apply (wp seL4_ReplyWait_wp)
      apply (simp add:seL4_MessageInfo_new'_def)
      apply wp
     apply (wp echo_int_internal_wp)
       apply (wp seL4_ReplyWait_wp)
      apply (simp add:seL4_MessageInfo_new'_def)
      apply wp
     apply (wp echo_parameter_internal_wp)
       apply (wp seL4_ReplyWait_wp)
      apply (simp add:seL4_MessageInfo_new'_def)
      apply wp
     apply (wp echo_char_internal_wp)
       apply (wp seL4_ReplyWait_wp)
      apply (simp add:seL4_MessageInfo_new'_def)
      apply wp
     apply (wp increment_char_internal_wp)
       apply (wp seL4_ReplyWait_wp)
      apply (simp add:seL4_MessageInfo_new'_def)
      apply wp
     apply (wp increment_parameter_internal_wp)
       apply (wp seL4_ReplyWait_wp)
      apply (simp add:seL4_MessageInfo_new'_def)
      apply wp
     apply (wp increment_64_internal_wp)
    apply (wp seL4_Wait_wp)+
  apply (clarsimp simp:globals_frame_intact_def ipc_buffer_valid_def
    tls_valid_def tls_def tls_ptr_def ucast_id seL4_GetIPCBuffer'_def
    thread_count_def setMR_def setMRs_def update_global_w32_def
    update_global_w8_def update_global_w64_def update_global_w64_high_def)
  done

(*<*)
end

end
(*>*)
