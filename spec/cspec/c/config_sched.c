/*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 */

#include <object/structures.h>
#include <model/statedata.h>

/* Random schedule clagged from Tim's original example. */
const dschedule_t ksDomSchedule[] = {
    { .domain = 0, .length = 15 },
    { .domain = 2, .length = 42 },
    { .domain = 1, .length = 73 },
};

const word_t ksDomScheduleLength = sizeof(ksDomSchedule) / sizeof(dschedule_t);
