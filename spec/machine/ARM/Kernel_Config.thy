(*
 * Copyright 2022, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Kernel Configuration"

theory Kernel_Config
imports Word_Lib.WordSetup
begin

(*
  GENERATED -- DO NOT EDIT! Changes will be overwritten.

  This file was generated from /home/sbuckley/repos/verification_timeprot/l4v/spec/cspec/c/config-build/ARM/gen_config/kernel/gen_config.h
  by the script /home/sbuckley/repos/verification_timeprot/l4v/spec/cspec/c/gen-config-thy.py.
*)

definition CONFIG_ARM_HIKEY_OUTSTANDING_PREFETCHERS :: bool where
  "CONFIG_ARM_HIKEY_OUTSTANDING_PREFETCHERS \<equiv> False"

definition CONFIG_ARM_HIKEY_PREFETCHER_STRIDE :: bool where
  "CONFIG_ARM_HIKEY_PREFETCHER_STRIDE \<equiv> False"

definition CONFIG_ARM_HIKEY_PREFETCHER_NPFSTRM :: bool where
  "CONFIG_ARM_HIKEY_PREFETCHER_NPFSTRM \<equiv> False"

definition CONFIG_PLAT_SABRE :: bool where
  "CONFIG_PLAT_SABRE \<equiv> True"

definition CONFIG_PLAT_IMX6DQ :: bool where
  "CONFIG_PLAT_IMX6DQ \<equiv> True"

definition CONFIG_ARCH_AARCH32 :: bool where
  "CONFIG_ARCH_AARCH32 \<equiv> True"

definition CONFIG_ARCH_ARM :: bool where
  "CONFIG_ARCH_ARM \<equiv> True"

definition CONFIG_WORD_SIZE :: nat where
  "CONFIG_WORD_SIZE \<equiv> 32"

definition CONFIG_USER_TOP :: machine_word where
  "CONFIG_USER_TOP \<equiv> 0xa0000000"

definition CONFIG_PLAT_IMX6 :: bool where
  "CONFIG_PLAT_IMX6 \<equiv> True"

definition CONFIG_ARM_CORTEX_A9 :: bool where
  "CONFIG_ARM_CORTEX_A9 \<equiv> True"

definition CONFIG_ARCH_ARM_V7A :: bool where
  "CONFIG_ARCH_ARM_V7A \<equiv> True"

definition CONFIG_ARM_ICACHE_VIPT :: bool where
  "CONFIG_ARM_ICACHE_VIPT \<equiv> False"

definition CONFIG_L1_CACHE_LINE_SIZE_BITS :: nat where
  "CONFIG_L1_CACHE_LINE_SIZE_BITS \<equiv> 5"

definition CONFIG_VTIMER_UPDATE_VOFFSET :: bool where
  "CONFIG_VTIMER_UPDATE_VOFFSET \<equiv> True"

definition CONFIG_PADDR_USER_DEVICE_TOP :: machine_word where
  "CONFIG_PADDR_USER_DEVICE_TOP \<equiv> 4294967295"

definition CONFIG_ROOT_CNODE_SIZE_BITS :: nat where
  "CONFIG_ROOT_CNODE_SIZE_BITS \<equiv> 12"

definition CONFIG_TIMER_TICK_MS :: machine_word where
  "CONFIG_TIMER_TICK_MS \<equiv> 2"

definition timeSlice :: nat where
  "timeSlice \<equiv> 5"  (* CONFIG_TIME_SLICE *)

definition retypeFanOutLimit :: machine_word where
  "retypeFanOutLimit \<equiv> 256"  (* CONFIG_RETYPE_FAN_OUT_LIMIT *)

definition workUnitsLimit :: nat where
  "workUnitsLimit \<equiv> 100"  (* CONFIG_MAX_NUM_WORK_UNITS_PER_PREEMPTION *)

definition resetChunkBits :: nat where
  "resetChunkBits \<equiv> 8"  (* CONFIG_RESET_CHUNK_BITS *)

definition CONFIG_MAX_NUM_BOOTINFO_UNTYPED_CAPS :: nat where
  "CONFIG_MAX_NUM_BOOTINFO_UNTYPED_CAPS \<equiv> 230"

definition CONFIG_FASTPATH :: bool where
  "CONFIG_FASTPATH \<equiv> True"

definition numDomains :: nat where
  "numDomains \<equiv> 16"  (* CONFIG_NUM_DOMAINS *)

definition numPriorities :: nat where
  "numPriorities \<equiv> 256"  (* CONFIG_NUM_PRIORITIES *)

definition CONFIG_MAX_NUM_NODES :: nat where
  "CONFIG_MAX_NUM_NODES \<equiv> 1"

definition CONFIG_KERNEL_STACK_BITS :: nat where
  "CONFIG_KERNEL_STACK_BITS \<equiv> 12"

definition CONFIG_VERIFICATION_BUILD :: bool where
  "CONFIG_VERIFICATION_BUILD \<equiv> True"

definition CONFIG_NO_BENCHMARKS :: bool where
  "CONFIG_NO_BENCHMARKS \<equiv> True"

definition CONFIG_MAX_NUM_TRACE_POINTS :: nat where
  "CONFIG_MAX_NUM_TRACE_POINTS \<equiv> 0"

definition CONFIG_USER_STACK_TRACE_LENGTH :: nat where
  "CONFIG_USER_STACK_TRACE_LENGTH \<equiv> 0"

definition CONFIG_KERNEL_OPT_LEVEL_O2 :: bool where
  "CONFIG_KERNEL_OPT_LEVEL_O2 \<equiv> True"

definition config_ARM_PA_SIZE_BITS_40 :: bool where
  "config_ARM_PA_SIZE_BITS_40 \<equiv> False"  (* CONFIG_ARM_PA_SIZE_BITS_40 *)

definition config_ARM_PA_SIZE_BITS_44 :: bool where
  "config_ARM_PA_SIZE_BITS_44 \<equiv> False"  (* CONFIG_ARM_PA_SIZE_BITS_44 *)


(* These definitions should only be unfolded consciously and carefully: *)
hide_fact (open) CONFIG_ARM_HIKEY_OUTSTANDING_PREFETCHERS_def
hide_fact (open) CONFIG_ARM_HIKEY_PREFETCHER_STRIDE_def
hide_fact (open) CONFIG_ARM_HIKEY_PREFETCHER_NPFSTRM_def
hide_fact (open) CONFIG_PLAT_SABRE_def
hide_fact (open) CONFIG_PLAT_IMX6DQ_def
hide_fact (open) CONFIG_ARCH_AARCH32_def
hide_fact (open) CONFIG_ARCH_ARM_def
hide_fact (open) CONFIG_WORD_SIZE_def
hide_fact (open) CONFIG_USER_TOP_def
hide_fact (open) CONFIG_PLAT_IMX6_def
hide_fact (open) CONFIG_ARM_CORTEX_A9_def
hide_fact (open) CONFIG_ARCH_ARM_V7A_def
hide_fact (open) CONFIG_ARM_ICACHE_VIPT_def
hide_fact (open) CONFIG_L1_CACHE_LINE_SIZE_BITS_def
hide_fact (open) CONFIG_VTIMER_UPDATE_VOFFSET_def
hide_fact (open) CONFIG_PADDR_USER_DEVICE_TOP_def
hide_fact (open) CONFIG_ROOT_CNODE_SIZE_BITS_def
hide_fact (open) CONFIG_TIMER_TICK_MS_def
hide_fact (open) timeSlice_def
hide_fact (open) retypeFanOutLimit_def
hide_fact (open) workUnitsLimit_def
hide_fact (open) resetChunkBits_def
hide_fact (open) CONFIG_MAX_NUM_BOOTINFO_UNTYPED_CAPS_def
hide_fact (open) CONFIG_FASTPATH_def
hide_fact (open) numDomains_def
hide_fact (open) numPriorities_def
hide_fact (open) CONFIG_MAX_NUM_NODES_def
hide_fact (open) CONFIG_KERNEL_STACK_BITS_def
hide_fact (open) CONFIG_VERIFICATION_BUILD_def
hide_fact (open) CONFIG_NO_BENCHMARKS_def
hide_fact (open) CONFIG_MAX_NUM_TRACE_POINTS_def
hide_fact (open) CONFIG_USER_STACK_TRACE_LENGTH_def
hide_fact (open) CONFIG_KERNEL_OPT_LEVEL_O2_def
hide_fact (open) config_ARM_PA_SIZE_BITS_40_def
hide_fact (open) config_ARM_PA_SIZE_BITS_44_def

end
