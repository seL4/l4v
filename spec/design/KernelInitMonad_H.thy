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
imports KernelStateData_H Types_H Fault_H
begin

text {* This is a similar way of getting around StateT as with the kernel
state, we add an extra field to the record that Haskell expects to store the
inner monad state. *}

record init_data =
  initFreeMemory   :: "region list"
  initSlotPosCur :: "machine_word"
  initSlotPosMax   :: "machine_word"
  initBootInfo    :: "biframe_data"
  initBootInfoFrame       :: paddr
  initKernelState :: kernel_state

type_synonym 'a kernel_init_state = "(init_data, 'a) nondet_monad"

translations
  (type) "'c kernel_init_state" <= (type) "(init_data, 'c) nondet_monad"

type_synonym 'a kernel_init = "(init_failure + 'a) kernel_init_state"

translations
  (type) "'a kernel_init" <= (type) "(init_failure + 'a) kernel_init"

definition
  noInitFailure :: "'a kernel_init_state \<Rightarrow> 'a kernel_init"
where
  noInitFailure_def[simp]:
  "noInitFailure \<equiv> liftE"



definition
  doKernelOp :: "'a kernel \<Rightarrow> 'a kernel_init"
where
 "doKernelOp kop \<equiv> doE
    ms \<leftarrow> liftE $ gets initKernelState;
    (r, ms') \<leftarrow> liftE $ select_f (kop ms);
    liftE $ modify (\<lambda>ks. ks \<lparr> initKernelState := ms' \<rparr>);
    returnOk r
  odE"

consts 
  itASID :: asid
  biCapNull :: word32
  biCapITTCB :: word32
  biCapITCNode :: word32
  biCapITPD :: word32
  biCapIRQControl :: word32
  biCapASIDControl :: word32
  biCapITASIDPool :: word32
  biCapIOPort :: word32
  biCapIOSpace :: word32
  biCapBIFrame :: word32
  biCapITIPCBuf :: word32
  biCapDynStart :: word32
  biFrameSizeBits :: nat
  nopBIFrameData :: biframe_data

definition
  runInit :: "'a kernel_init \<Rightarrow> 'b kernel"
where
  "runInit doInit \<equiv> do
    ks \<leftarrow> get;
    initData \<leftarrow> return \<lparr> initFreeMemory = [],
                   initSlotPosCur = 0,
                   initSlotPosMax = bit (pageBits),
                   initBootInfo = nopBIFrameData,
                   initBootInfoFrame = 0,
                   initKernelState = ks \<rparr>;
    (ret, initData') \<leftarrow> select_f (doInit initData);
    (case ret of
      Inr a \<Rightarrow> fail
    | Inl _ \<Rightarrow> fail)
  od"

end
