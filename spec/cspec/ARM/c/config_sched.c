/*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
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
