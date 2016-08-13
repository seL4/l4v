/*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 */

#include <stdint.h>
/* Memory map for MCT */
typedef struct mp_priv_timer {
    uint32_t load;
    uint32_t count;
    uint32_t ctrl;
    uint32_t ints;
}priv_timer;
