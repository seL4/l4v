(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Operations on endpoints.  *)

theory Endpoint_D
  imports
    Tcb_D
begin

definition get_ipc_buffer :: "cdl_object_id \<Rightarrow> bool \<Rightarrow> cdl_object_id option k_monad" where
  "get_ipc_buffer oid in_receive \<equiv> do
     frame_cap \<leftarrow> get_cap (oid, tcb_ipcbuffer_slot);
     case frame_cap of
        FrameCap _ a rights _ _ _ \<Rightarrow>
          if (Write \<in> rights \<and> Read \<in> rights) \<or> (Read \<in> rights \<and> \<not>in_receive)
          then return (Some a)
          else return None
        | _ \<Rightarrow> return None
   od"

definition corrupt_ipc_buffer :: "cdl_object_id \<Rightarrow> bool \<Rightarrow> unit k_monad" where
  "corrupt_ipc_buffer oid in_receive \<equiv> do
     buffer \<leftarrow> get_ipc_buffer oid in_receive;
     case buffer of
       Some a \<Rightarrow> corrupt_frame a
     | None \<Rightarrow> corrupt_tcb_intent oid
   od"

definition lookup_extra_caps ::
  "cdl_object_id \<Rightarrow> cdl_cptr list \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) list fault_monad"
  where
  "lookup_extra_caps thread cptrs \<equiv> mapME (\<lambda>cptr. lookup_cap_and_slot thread cptr) cptrs"

end
