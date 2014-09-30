theory SetMR imports
  "../../tools/c-parser/CTranslation"
  "../../tools/autocorres/AutoCorres"
  "../../tools/autocorres/NonDetMonadEx"
begin

(* This theory contains some lemmas about libsel4 that are useful for CAmkES systems, but are likely
 * useful for other user-level reasoning on seL4 as well.
 *)

(* Load the fragment of libsel4 we need for reasoning about seL4_GetMR and seL4_SetMR. *)
install_C_file "mr.c"

autocorres [ts_rules=nondet, no_heap_abs=seL4_SetMR] "mr.c"

context mr begin

abbreviation "seL4_MsgMaxLength \<equiv> 120"

lemma le_step_down:"\<lbrakk>(i::int) < n; i = n - 1 \<Longrightarrow> P; i < n - 1 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  apply arith
  done

(* Avoid having to hold Isabelle's hand with "unat (of_int x)". *)
lemma unat_nat[simp]:"\<lbrakk>(i::int) \<ge> 0; i < seL4_MsgMaxLength\<rbrakk> \<Longrightarrow> unat ((of_int i)::sword32) = nat i"
  apply (erule le_step_down, simp, simp)+
  done

(* A manually abstracted version of seL4_SetMR. A future version of AutoCorres should translate
 * seL4_SetMR to this automatically.
 *)
definition
  seL4_SetMR_lifted' :: "int \<Rightarrow> word32 \<Rightarrow> (lifted_globals, unit) nondet_monad"
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

definition
  globals_frame_intact :: "lifted_globals \<Rightarrow> bool"
where
  "globals_frame_intact s \<equiv> is_valid_seL4_IPCBuffer__C'ptr s (Ptr (scast seL4_GlobalsFrame))"
definition
  ipc_buffer_valid :: "lifted_globals \<Rightarrow> bool"
where
  "ipc_buffer_valid s \<equiv> is_valid_seL4_IPCBuffer__C s
      (heap_seL4_IPCBuffer__C'ptr s (Ptr (scast seL4_GlobalsFrame)))"

(* seL4_GetMR and seL4_SetMR call seL4_GetIPCBuffer, so we're going to need a WP lemma about it. *)
lemma seL4_GetIPCBuffer_wp[THEN validNF_make_schematic_post, simplified]:
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

(* Functional versions of seL4_SetMR and seL4_GetMR. See how these are used below for stating
 * transformations on states.
 *)
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
  getMR :: "lifted_globals \<Rightarrow> nat \<Rightarrow> word32"
where
  "getMR s i \<equiv>
       index (msg_C (heap_seL4_IPCBuffer__C s
            (heap_seL4_IPCBuffer__C'ptr s (Ptr (scast seL4_GlobalsFrame))))) i"

lemma getMR_setMR:
  "\<lbrakk>i < seL4_MsgMaxLength\<rbrakk> \<Longrightarrow> getMR (setMR s j v) i = (if i = j then v else getMR s i)"
  apply (simp add:getMR_def setMR_def fun_upd_def)
  done

lemma seL4_GetMR_wp[wp_unsafe]:
  "\<lbrace>\<lambda>s. (i::int) \<ge> 0 \<and>
            i < seL4_MsgMaxLength \<and>
            globals_frame_intact s \<and>
            ipc_buffer_valid s \<and>
            P (getMR s (nat i)) s\<rbrace>
     seL4_GetMR' i
   \<lbrace>P\<rbrace>!"
  apply (simp add:seL4_GetMR'_def)
  apply (wp seL4_GetIPCBuffer_wp)
  apply (simp add:globals_frame_intact_def ipc_buffer_valid_def getMR_def)
  done

end

locale SetMR = mr +
  (* This assumption should go away in future when the abstraction is performed automatically. *)
  assumes seL4_SetMR_axiom:"exec_concrete lift_global_heap (seL4_SetMR' i val) =
                                seL4_SetMR_lifted' i val"
begin

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

(* When you write to a message register and then read back from the same register, you get the value
 * you wrote and the only state you have affected is that register.
 *)
lemma "\<forall>(i::int) x. \<lbrace>\<lambda>s. i \<ge> 0 \<and> i < seL4_MsgMaxLength \<and>
                         globals_frame_intact s \<and>
                         ipc_buffer_valid s \<and>
                         P (setMR s (nat i) x)\<rbrace>
         do exec_concrete lift_global_heap (seL4_SetMR' i x);
            seL4_GetMR' i
         od
             \<lbrace>\<lambda>r s. globals_frame_intact s \<and>
                    ipc_buffer_valid s \<and>
                    r = x \<and>
                    P s\<rbrace>!"
  apply (rule allI)+
  apply (wp seL4_GetMR_wp seL4_SetMR_wp)
  apply clarsimp
  apply (subst getMR_setMR)
   apply (erule le_step_down, simp, simp)+
  apply (simp add:setMR_def getMR_def globals_frame_intact_def ipc_buffer_valid_def)
  done

end

end
