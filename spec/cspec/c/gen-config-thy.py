#!/usr/bin/env python3
#
# Copyright 2021, Proofcraft Pty Ltd
#
# SPDX-License-Identifier: BSD-2-Clause
#

#
# This script generates a theory Kernel_Config.thy from the file gen_config.h,
# which in turn is produced by the kernel build system, containing kernel
# configuration options.
#
# The script makes the following assumptions about gen_config.h:
#
#   - only lines that start with "#define" are config options that are used
#   - the value of the config option is separated from its name by two spaces
#   - there is an optional comment after the value, separated by two spaces
#   - values are numbers, booleans or strings
#
# Example excerpt from gen_config.h:
#
#     #define CONFIG_FASTPATH  1  /* KernelFastpath=ON */
#     #define CONFIG_NUM_DOMAINS  16
#     #define CONFIG_NUM_PRIORITIES  256
#     #define CONFIG_MAX_NUM_NODES  1
#     /* disabled: CONFIG_ENABLE_SMP_SUPPORT */
#

import re

from datetime import date
from os import path, getenv
from typing import Dict

# Isabelle types for config keys
bool = 'boolean'
string = 'string'
nat = 'nat'
word = 'machine_word'

# All known config keys that could be set in a gen_config.h file. The dict maps
# config key to (type, definition name)
#
# This table duplicates some information from the kernel build system, but only
# which keys exist, not their values.
#
# If they are used in Haskell, the translated config key names have to start
# with a lower case letter, because Haskell enforces that only datatype
# constructores start with upper case. For new names, we tend to use `config_`
# as prefix and potentially shorten the C name a bit.
known_config_keys = {
    'CONFIG_ARM_HIKEY_OUTSTANDING_PREFETCHERS': (bool, None),
    'CONFIG_ARM_HIKEY_PREFETCHER_STRIDE': (bool, None),
    'CONFIG_ARM_HIKEY_PREFETCHER_NPFSTRM': (bool, None),
    'CONFIG_ARM_HIKEY_PREFETCHER_STBPFDIS': (bool, None),
    'CONFIG_ARM_HIKEY_PREFETCHER_STBPFRS': (bool, None),
    'CONFIG_PLAT_SABRE': (bool, None),
    'CONFIG_PLAT_IMX6DQ': (bool, None),
    'CONFIG_ARM_PLAT': (string, None),
    'CONFIG_ARCH_AARCH32': (bool, None),
    'CONFIG_ARCH_AARCH64': (bool, None),
    'CONFIG_ARCH_ARM_HYP': (bool, None),
    'CONFIG_ARCH_RISCV32': (bool, None),
    'CONFIG_ARCH_RISCV64': (bool, None),
    'CONFIG_ARCH_X86_64': (bool, None),
    'CONFIG_ARCH_IA32': (bool, None),
    'CONFIG_SEL4_ARCH': (string, None),
    'CONFIG_ARCH': (string, None),
    'CONFIG_ARCH_ARM': (bool, None),
    'CONFIG_WORD_SIZE': (nat, None),
    'CONFIG_PLAT_IMX7': (bool, None),
    'CONFIG_USER_TOP': (word, None),
    'CONFIG_PLAT_ALLWINNERA20': (bool, None),
    'CONFIG_PLAT_AM335X': (bool, None),
    'CONFIG_PLAT_APQ8064': (bool, None),
    'CONFIG_PLAT_BCM2711': (bool, None),
    'CONFIG_PLAT_BCM2837': (bool, None),
    'CONFIG_PLAT_EXYNOS4': (bool, None),
    'CONFIG_PLAT_EXYNOS5': (bool, None),
    'CONFIG_PLAT_HIKEY': (bool, None),
    'CONFIG_PLAT_IMX6': (bool, None),
    'CONFIG_PLAT_IMX7_SABRE': (bool, None),
    'CONFIG_PLAT_IMX8MQ_EVK': (bool, None),
    'CONFIG_PLAT_IMX8MM_EVK': (bool, None),
    'CONFIG_PLAT_OMAP3': (bool, None),
    'CONFIG_PLAT_QEMU_ARM_VIRT': (bool, None),
    'CONFIG_PLAT_TK1': (bool, None),
    'CONFIG_PLAT_TQMA8XQP1GB': (bool, None),
    'CONFIG_PLAT_ZYNQ7000': (bool, None),
    'CONFIG_PLAT_ZYNQMP': (bool, None),
    'CONFIG_PLAT': (string, None),
    'CONFIG_ARM_CORTEX_A7': (bool, None),
    'CONFIG_ARM_CORTEX_A8': (bool, None),
    'CONFIG_ARM_CORTEX_A9': (bool, None),
    'CONFIG_ARM_CORTEX_A15': (bool, None),
    'CONFIG_ARM_CORTEX_A35': (bool, None),
    'CONFIG_ARM_CORTEX_A53': (bool, None),
    'CONFIG_ARM_CORTEX_A55': (bool, None),
    'CONFIG_ARM_CORTEX_A57': (bool, None),
    'CONFIG_ARM_CORTEX_A72': (bool, None),
    'CONFIG_ARCH_ARM_V7A': (bool, None),
    'CONFIG_ARCH_ARM_V7VE': (bool, None),
    'CONFIG_ARCH_ARM_V8A': (bool, None),
    'CONFIG_ARM_SMMU': (bool, None),
    'CONFIG_AARCH64_SERROR_IGNORE': (bool, None),
    'CONFIG_ARM_MACH': (string, None),
    'CONFIG_KERNEL_MCS': (bool, None),
    'CONFIG_ARM_PA_SIZE_BITS_40': (bool, 'config_ARM_PA_SIZE_BITS_40'),
    'CONFIG_ARM_PA_SIZE_BITS_44': (bool, 'config_ARM_PA_SIZE_BITS_44'),
    'CONFIG_ARM_ICACHE_VIPT': (bool, None),
    'CONFIG_DEBUG_DISABLE_L2_CACHE': (bool, None),
    'CONFIG_DEBUG_DISABLE_L1_ICACHE': (bool, None),
    'CONFIG_DEBUG_DISABLE_L1_DCACHE': (bool, None),
    'CONFIG_DEBUG_DISABLE_BRANCH_PREDICTION': (bool, None),
    'CONFIG_ARM_HYPERVISOR_SUPPORT': (bool, None),
    'CONFIG_ARM_GIC_V3_SUPPORT': (bool, 'config_ARM_GIC_V3'),
    'CONFIG_AARCH64_VSPACE_S2_START_L1': (bool, None),
    'CONFIG_ARM_HYP_ENABLE_VCPU_CP14_SAVE_AND_RESTORE': (bool, None),
    'CONFIG_ARM_ERRATA_430973': (bool, None),
    'CONFIG_ARM_ERRATA_773022': (bool, None),
    'CONFIG_TK1_SMMU': (bool, None),
    'CONFIG_ENABLE_A9_PREFETCHER': (bool, None),
    'CONFIG_EXPORT_PMU_USER': (bool, None),
    'CONFIG_DISABLE_WFI_WFE_TRAPS': (bool, 'config_DISABLE_WFI_WFE_TRAPS'),
    'CONFIG_SMMU_INTERRUPT_ENABLE': (bool, None),
    'CONFIG_AARCH32_FPU_ENABLE_CONTEXT_SWITCH': (bool, None),
    'CONFIG_L1_CACHE_LINE_SIZE_BITS': (nat, None),
    'CONFIG_EXPORT_PCNT_USER': (bool, None),
    'CONFIG_EXPORT_VCNT_USER': (bool, None),
    'CONFIG_EXPORT_PTMR_USER': (bool, None),
    'CONFIG_EXPORT_VTMR_USER': (bool, None),
    'CONFIG_VTIMER_UPDATE_VOFFSET': (bool, None),
    'CONFIG_HAVE_FPU': (bool, 'config_HAVE_FPU'),
    'CONFIG_PADDR_USER_DEVICE_TOP': (word, None),
    'CONFIG_ROOT_CNODE_SIZE_BITS': (nat, None),
    'CONFIG_TIMER_TICK_MS': (word, None),
    'CONFIG_TIME_SLICE': (nat, 'timeSlice'),
    'CONFIG_RETYPE_FAN_OUT_LIMIT': (word, 'retypeFanOutLimit'),
    'CONFIG_MAX_NUM_WORK_UNITS_PER_PREEMPTION': (word, 'workUnitsLimit'),
    'CONFIG_RESET_CHUNK_BITS': (nat, 'resetChunkBits'),
    'CONFIG_MAX_NUM_BOOTINFO_UNTYPED_CAPS': (nat, None),
    'CONFIG_FASTPATH': (bool, None),
    'CONFIG_NUM_DOMAINS': (nat, 'numDomains'),
    'CONFIG_NUM_PRIORITIES': (nat, 'numPriorities'),
    'CONFIG_MAX_NUM_NODES': (nat, None),
    'CONFIG_ENABLE_SMP_SUPPORT': (bool, None),
    'CONFIG_KERNEL_STACK_BITS': (nat, None),
    'CONFIG_VERIFICATION_BUILD': (bool, None),
    'CONFIG_DEBUG_BUILD': (bool, None),
    'CONFIG_HARDWARE_DEBUG_API': (bool, None),
    'CONFIG_PRINTING': (bool, None),
    'CONFIG_KERNEL_INVOCATION_REPORT_ERROR_IPC': (bool, None),
    'CONFIG_NO_BENCHMARKS': (bool, None),
    'CONFIG_ENABLE_BENCHMARKS': (bool, None),
    'CONFIG_KERNEL_LOG_BUFFER': (bool, None),
    'CONFIG_MAX_NUM_TRACE_POINTS': (nat, None),
    'CONFIG_IRQ_REPORTING': (bool, None),
    'CONFIG_COLOUR_PRINTING': (bool, None),
    'CONFIG_USER_STACK_TRACE_LENGTH': (nat, None),
    'CONFIG_KERNEL_OPT_LEVEL_O2': (bool, None),
    'CONFIG_KERNEL_OPT_LEVEL_OS': (bool, None),
    'CONFIG_KERNEL_OPT_LEVEL_O0': (bool, None),
    'CONFIG_KERNEL_OPT_LEVEL_O1': (bool, None),
    'CONFIG_KERNEL_OPT_LEVEL_O3': (bool, None),
    'CONFIG_KERNEL_OPT_LEVEL': (string, None),
    'CONFIG_KERNEL_FWHOLE_PROGRAM': (bool, None),
    'CONFIG_DANGEROUS_CODE_INJECTION': (bool, None),
    'CONFIG_DEBUG_DISABLE_PREFETCHERS': (bool, None),
    'CONFIG_SET_TLS_BASE_SELF': (bool, None),
    'CONFIG_CLZ_32': (bool, None),
    'CONFIG_CLZ_64': (bool, None),
    'CONFIG_CTZ_32': (bool, None),
    'CONFIG_CTZ_64': (bool, None),
    'CONFIG_CLZ_NO_BUILTIN': (bool, None),
    'CONFIG_CTZ_NO_BUILTIN': (bool, None),
    'CONFIG_MAX_NUM_IOAPIC': (nat, 'maxNumIOAPIC'),
}


def type_of(config_key: str) -> str:
    """
    Return the Isabelle type of the given config key.
    """

    return known_config_keys.get(config_key, (None, None))[0]


def name_of(config_key: str) -> str:
    """
    Return the name of the Isabelle constant for the given config key.
    """
    name = known_config_keys.get(config_key, (None, None))[1]
    return name or config_key


def parse_gen_config(gen_config_file: str) -> Dict[str, str]:
    """
    Parse gen_config.h and return a dictionary of the values.
    """
    end_comment_re = re.compile(r'/\*.*\*/')

    config = {}
    with open(gen_config_file, 'r') as f:
        for line in f:
            line = line.strip()
            if not line.startswith('#define '):
                continue
            line = line[len('#define '):]
            line = re.sub(end_comment_re, '', line)
            key, value = line.split('  ')
            config[key] = value
    return config


def parse_physBase(l4v_arch: str, devices_gen_h_file: str) -> str:
    """
    Parse devices_gen.h and return the physBase value as string in hex or
    decimal form. Return None for architectures that don't use physBase.
    """
    if l4v_arch == 'X64':
        return None

    physBase_re = re.compile(r'#define PHYS_BASE_RAW (0x[0-9a-fA-F]+|[0-9]+)')
    with open(devices_gen_h_file, 'r') as f:
        for line in f:
            line = line.strip()
            m = physBase_re.match(line)
            if m:
                return m.group(1)
    raise Exception(f'Could not find PHYS_BASE_RAW in {devices_gen_h_file}')


def parse_maxIRQ(l4v_arch: str, platform_gen_h_file: str) -> str:
    """
    Parse platform_gen.h for Arm platforms to extract the value of maxIRQ.
    This value is expected to be set to a number literal in an enum.
    """
    # fixed value on X64, and different way of setting the value on RISCV64
    if l4v_arch == 'X64' or l4v_arch == 'RISCV64':
        return None

    maxIRQ_re = re.compile(r'maxIRQ[\t ]+= ([0-9]+)')

    with open(platform_gen_h_file, 'r') as f:
        for line in f:
            line = line.strip()
            m = maxIRQ_re.match(line)
            if m:
                return m.group(1)

    raise Exception(f'Could not find maxIRQ in {platform_gen_h_file}')


def parse_irqBits(l4v_arch: str, platform_gen_h_file: str) -> str:
    """
    Parse platform_gen.h for the value of IRQ_CNODE_SLOT_BITS, which becomes
    the width of the irq type in ASpec and ExecSpec. It is expected to be
    of the form #define IRQ_CNODE_SLOT_BITS (<number literal>)
    """

    # fixed value on X64
    if l4v_arch == 'X64':
        return None

    irqBits_re = re.compile(r'#define[\t ]+IRQ_CNODE_SLOT_BITS[\t ]+\(?([0-9]+)\)?')

    with open(platform_gen_h_file, 'r') as f:
        for line in f:
            line = line.strip()
            m = irqBits_re.match(line)
            if m:
                return m.group(1)

    raise Exception(f'Could not find IRQ_CNODE_SLOT_BITS in {platform_gen_h_file}')


def add_defaults(config: Dict[str, str]):
    """
    Defaults are boolean config keys that are mentioned in known_config_keys
    with a custom name. These are set to `false` if not present in the input
    config file.
    """
    for key, (_, name) in known_config_keys.items():
        if key not in config and name is not None:
            config[key] = 0


theory_header = """(*
 * Copyright {}, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Kernel Configuration"

theory Kernel_Config
imports Word_Lib.WordSetup
begin

(*
  GENERATED -- DO NOT EDIT! Changes will be overwritten.

  This file was generated from the following files:
  {}
  {}
  {}
  by the script {}.
*)

"""


def write_config_thy(header, config_thy_path, config: Dict[str, str],
                     physBase=None, maxIRQ=None, irqBits=None):
    """
    Write a Kernel_Config.thy file for a given configuration dict.
    """
    file_name = path.realpath(path.join(config_thy_path, 'Kernel_Config.thy'))
    with open(file_name, 'w') as f:
        f.write(header)

        names = []

        if physBase:
            f.write('(* This value is PHYS_BASE_RAW in the devices_gen.h header listed above. *)\n')
            f.write('definition physBase :: machine_word where\n')
            f.write(f'  "physBase \\<equiv> {physBase}"\n\n')
            names.append('physBase')

        if maxIRQ:
            # type is left unspecified to get the most general numeral type
            f.write('definition maxIRQ where (* from platform_gen.h. *)\n')
            f.write(f'  "maxIRQ \\<equiv> {maxIRQ}"\n\n')
            names.append('maxIRQ')

        if irqBits:
            f.write('(* IRQ_CNODE_SLOT_BITS from platform_gen.h. *)\n')
            f.write('definition irqBits :: nat where\n')
            f.write(f'  "irqBits \\<equiv> {irqBits}"\n\n')
            names.append('irqBits')

        for key, value in config.items():
            type = type_of(key)
            if type is nat or type is word:
                name = name_of(key)
                names.append(name)
                f.write(f'definition {name} :: {type} where\n')
                f.write(f'  "{name} \\<equiv> {value}"')
                if name != key:
                    f.write(f'  (* {key} *)')
                f.write('\n\n')
            if type is bool:
                name = name_of(key)
                names.append(name)
                f.write(f'definition {name} :: bool where\n')
                val = 'True' if value == '1' else 'False'
                f.write(f'  "{name} \\<equiv> {val}"')
                if name != key:
                    f.write(f'  (* {key} *)')
                f.write('\n\n')
            else:
                # currently ignoring string configs
                pass

        f.write('\n(* These definitions should only be unfolded consciously and carefully: *)\n')
        for name in names:
            f.write(f'hide_fact (open) {name}_def\n')

        f.write('\nend\n')

    print(f'Wrote {file_name}')


if __name__ == '__main__':
    l4v_arch = getenv('L4V_ARCH')
    if not l4v_arch:
        print('L4V_ARCH environment variable not set')
        exit(1)

    this_dir = path.dirname(path.realpath(__file__))
    build_dir = path.join(this_dir, f"config-build/{l4v_arch}")

    config_path = path.join(build_dir, "gen_config/kernel/gen_config.h")
    devices_gen_path = path.join(build_dir, "gen_headers/plat/machine/devices_gen.h")
    platform_gen_path = path.join(build_dir, "gen_headers/plat/platform_gen.h")

    thy_path = path.join(this_dir, f'../../machine/{l4v_arch}')

    config = parse_gen_config(config_path)
    physBase = parse_physBase(l4v_arch, devices_gen_path)
    maxIRQ = parse_maxIRQ(l4v_arch, platform_gen_path)
    irqBits = parse_irqBits(l4v_arch, platform_gen_path)
    add_defaults(config)

    header = theory_header.format(
        date.today().year,
        config_path,
        devices_gen_path,
        platform_gen_path,
        path.realpath(__file__)
    )
    write_config_thy(header, thy_path, config, physBase, maxIRQ, irqBits)
