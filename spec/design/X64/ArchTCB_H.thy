(* THIS FILE WAS AUTOMATICALLY GENERATED. DO NOT EDIT. *)
(* instead, see the skeleton file ArchTCB_H.thy *)
(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchTCB_H
imports "../TCBDecls_H"
begin

context Arch begin global_naming X64_H

definition
decodeTransfer :: "word8 \<Rightarrow> ( syscall_error , copy_register_sets ) kernel_f"
where
"decodeTransfer arg1 \<equiv> returnOk X64NoExtraRegisters"

definition
performTransfer :: "copy_register_sets \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> unit kernel"
where
"performTransfer arg1 arg2 arg3 \<equiv> return ()"

definition
sanitiseOrFlags :: "machine_word"
where
"sanitiseOrFlags \<equiv> (1 << 1) || bit 9"

definition
sanitiseAndFlags :: "machine_word"
where
"sanitiseAndFlags\<equiv> ((1 << 12) - 1) && (complement (bit 3)) && (complement (bit 5)) && (complement (bit 8))"

definition
sanitiseRegister :: "tcb \<Rightarrow> register \<Rightarrow> machine_word \<Rightarrow> machine_word"
where
"sanitiseRegister arg1 r v \<equiv>
    let val = if r = FaultIP \<or> r = NextIP then
                 if v > 0x00007fffffffffff \<and> v < 0xffff800000000000 then 0 else v
              else v;
        val' = if r = TLS_BASE then if val > 0x00007fffffffffff then 0x00007fffffffffff else val else val
    in
        if r = FLAGS then
            (val' || sanitiseOrFlags) && sanitiseAndFlags
        else val'"


definition
archThreadGet :: "(arch_tcb \<Rightarrow> 'a) \<Rightarrow> machine_word \<Rightarrow> 'a kernel"
where
"archThreadGet f tptr\<equiv> liftM (f \<circ> tcbArch) $ getObject tptr"

definition
archThreadSet :: "(arch_tcb \<Rightarrow> arch_tcb) \<Rightarrow> machine_word \<Rightarrow> unit kernel"
where
"archThreadSet f tptr\<equiv> (do
        tcb \<leftarrow> getObject tptr;
        setObject tptr $ tcb \<lparr> tcbArch := f (tcbArch tcb) \<rparr>
od)"


end
end
