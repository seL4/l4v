(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)
chapter {* Shared Memory *}
(*<*)
theory DataIn imports
  "../../tools/c-parser/CTranslation"
  "../../tools/autocorres/AutoCorres"
begin

(* THIS THEORY IS GENERATED. DO NOT EDIT. *)

declare [[allow_underscore_idents=true]]

install_C_file "DataIn.c"

autocorres [ts_rules = nondet] "DataIn.c"

locale DataIn_glue = DataIn
  + assumes swi_safe_to_ignore[simplified, simp]:
    "asm_semantics_ok_to_ignore TYPE(nat) true (''swi '' @ x)"
begin

lemma DataIn__run_nf: "\<lbrace>\<lambda>s. \<forall>r. P r s\<rbrace> DataIn__run' \<lbrace>P\<rbrace>!"
  apply (simp add:DataIn__run'_def)
  apply wp
  apply simp
  done
(*>*)

text {*
  The CAmkES glue code for dataports (shared memory regions) involves no system calls, but we can
  show safety of the utility functions provided to the user code. These functions for ``wrapping''
  and ``unwrapping'' a pointer to a dataport are designed to convert a local pointer to and from a
  global reference to a dataport. A dataport pointer can be ``wrapped,'' passed over an RPC
  interface, and then ``unwrapped'' on the other side for access. This requires the sender and the
  receiver to both have access to the given dataport. The following two proofs characterise the
  safety of such functions.
*}
lemma DataIn_wrap_ptr_nf:
  "\<lbrace>\<lambda>s. (\<forall>x\<in>set (array_addrs (Ptr (symbol_table ''DataIn_data'')) 4096).
          is_valid_w8 s x) \<and>
         is_valid_dataport_ptr__C s x\<rbrace>
    DataIn_wrap_ptr' x y
   \<lbrace>\<lambda>_ s. (\<forall>x\<in>set (array_addrs (Ptr (symbol_table ''DataIn_data'')) 4096).
           is_valid_w8 s x) \<and>
          is_valid_dataport_ptr__C s x\<rbrace>!"
  apply (simp add:DataIn_wrap_ptr'_def)
  apply wp
  apply simp
  done

lemma DataIn_unwrap_ptr_nf:
  "\<lbrace>\<lambda>s. (\<forall>x\<in>set (array_addrs (Ptr (symbol_table ''DataIn_data'')) 4096).
          is_valid_w8 s x) \<and>
         is_valid_dataport_ptr__C s x\<rbrace>
    DataIn_unwrap_ptr' x
   \<lbrace>\<lambda>_ s. (\<forall>x\<in>set (array_addrs (Ptr (symbol_table ''DataIn_data'')) 4096).
           is_valid_w8 s x) \<and>
          is_valid_dataport_ptr__C s x\<rbrace>!"
  apply (simp add:DataIn_unwrap_ptr'_def)
  apply wp
  apply simp
  done

(*<*)
end

end
(*>*)
