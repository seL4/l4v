/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 */

#pragma once

#include <config.h>

#define TIMER_CLOCK_HZ ULL_CONST(498000000)
#define CLK_MAGIC 4415709349llu
#define CLK_SHIFT 41llu
#define TIMER_PRECISION 2u

enum IRQConstants {
    maxIRQ                      = 159
} platform_interrupt_t;

#define IRQ_CNODE_SLOT_BITS (8)

#include <arch/machine/gic_v2.h>
#include <drivers/timer/arm_priv.h>

/* #undef CONFIGURE_SMMU */
#if (defined(CONFIGURE_SMMU) && defined(CONFIG_TK1_SMMU))
#include CONFIGURE_SMMU
#endif

/* #undef CONFIGURE_SMMU */
#if (defined(CONFIGURE_SMMU) && defined(CONFIG_ARM_SMMU))
#include CONFIGURE_SMMU

#define SMMU_MAX_SID  
#define SMMU_MAX_CB  

#endif

#ifdef CONFIG_KERNEL_MCS
static inline CONST time_t getKernelWcetUs(void)
{
    return 10llu;
}
#endif
