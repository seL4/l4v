(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

theory IpcDet_AI
imports "./$L4V_ARCH/ArchIpc_AI"
begin

lemma send_ipc_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>
   send_ipc block call badge can_grant can_donate thread epptr \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"

  sorry
(*
crunch typ_at[wp]: send_ipc "\<lambda>(s::det_ext state). P (typ_at T p s)"
  (wp: hoare_drop_imps mapM_wp_inv maybeM_inv simp: crunch_simps)
*)

lemma si_tcb_at [wp]:
  "\<And>t' call bl w d cd t ep.
    \<lbrace>tcb_at t' :: det_ext state \<Rightarrow> bool\<rbrace>
      send_ipc call bl w d cd t ep
    \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (simp add: tcb_at_typ) wp

lemma handle_fault_typ_at [wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> handle_fault t f \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  by (wpsimp simp: handle_fault_def unless_def handle_no_fault_def send_fault_ipc_def)

lemma hf_tcb_at [wp]:
  "\<And>t' t x.
    \<lbrace>tcb_at t' :: det_ext state \<Rightarrow> bool\<rbrace>
      handle_fault t x
    \<lbrace>\<lambda>rv. tcb_at t'\<rbrace>"
  by (simp add: tcb_at_typ, wp)

lemma sfi_tcb_at [wp]:
  "\<And>t tptr handler_cap fault can_donate.
    \<lbrace>tcb_at t :: det_ext state \<Rightarrow> bool\<rbrace>
      send_fault_ipc tptr handler_cap fault can_donate
    \<lbrace>\<lambda>_. tcb_at t\<rbrace>"
  by (wpsimp simp: send_fault_ipc_def)



end