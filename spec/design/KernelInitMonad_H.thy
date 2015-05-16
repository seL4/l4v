(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Kernel Init Monad"

theory KernelInitMonad_H
imports KernelStateData_H
begin

text {* This is a similar way of getting around StateT as with the kernel
state, we add an extra field to the record that Haskell expects to store the
inner monad state. *}

record init_data =
  initFreeSlotsL1   :: "(cptr * machine_word) list"
  initFreeSlotsL2   :: "(cptr * machine_word) list"
  initFreeMemory    :: "(machine_word * machine_word) list"
  initBootMemory    :: "(machine_word * machine_word) list"
  initRegions       :: "boot_region list"
  initKernelState   :: kernel_state

type_synonym 'a kernel_init = "(init_data, 'a) nondet_monad"

translations
  (type) "'c kernel_init" <= (type) "(init_data, 'c) nondet_monad"

definition
  doKernelOp :: "'a kernel \<Rightarrow> 'a kernel_init"
where
 "doKernelOp kop \<equiv> do
    ms \<leftarrow> gets initKernelState;
    (r, ms') \<leftarrow> select_f (kop ms);
    modify (\<lambda>ks. ks \<lparr> initKernelState := ms' \<rparr>);
    return r
  od"

definition
  runInit :: "(machine_word * machine_word) list
              \<Rightarrow> (machine_word * machine_word) list
              \<Rightarrow> (vptr * (vptr * machine_word) * capability) kernel_init
              \<Rightarrow> (boot_info * vptr * machine_word * capability) kernel"
where
 "runInit freeMem bootMem doInit \<equiv> do
    ks \<leftarrow> get;
    initData \<leftarrow> return \<lparr> initFreeSlotsL1 = [],
                   initFreeSlotsL2 = [],
                   initFreeMemory = freeMem,
                   initBootMemory = bootMem,
                   initRegions = [],
                   initKernelState = ks \<rparr>;
    ((bufferPtr, (infoVPtr, infoPPtr), tcbCap), initData') \<leftarrow> select_f (doInit initData);
    put (initKernelState initData');
    return ((BootInfo bufferPtr (initRegions initData')), infoVPtr, infoPPtr, tcbCap)
  od"


end
