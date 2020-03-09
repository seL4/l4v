(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Decoding system calls
*)

chapter "Decoding System Calls"

theory Decode_SA
imports    "Ipc_SA"

begin

section "IRQ"

section "Toplevel invocation decode."

text \<open>This definition is the toplevel decoding definition; it dispatches
to the above definitions, after checking, in some cases, whether the
invocation is allowed.
\<close>

definition
  decode_invocation ::
  "data \<Rightarrow> data list \<Rightarrow> cap_ref \<Rightarrow> cslot_ptr \<Rightarrow> cap \<Rightarrow> (cap \<times> cslot_ptr) list \<Rightarrow> (invocation,'z::state_ext) se_monad"
where
  "decode_invocation label args cap_index slot cap excaps \<equiv>
  case cap of
    NotificationCap ptr badge rights \<Rightarrow>
      if AllowSend \<in> rights then
        returnOk $ InvokeNotification ptr badge
      else throwError $ InvalidCapability 0
  | _ \<Rightarrow>
      throwError $ InvalidCapability 0"

end
