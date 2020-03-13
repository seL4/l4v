#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

FREQ_AVAIL=/sys/devices/system/cpu/cpu0/cpufreq/scaling_available_frequencies
FREQ_CONTROL=/sys/devices/system/cpu/cpu0/cpufreq/scaling_setspeed
FREQ_GOV=/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor
FREQ_CUR=/sys/devices/system/cpu/cpu0/cpufreq/scaling_cur_freq

FREQ_LIST=`cat ${FREQ_AVAIL}`

OLD_GOV=`cat ${FREQ_GOV}`
OLD_SPEED=`cat ${FREQ_CUR}`

echo userspace > ${FREQ_GOV}
echo -n "cpufreq governor is now "
cat ${FREQ_GOV}

for f in ${FREQ_LIST}
do
    echo $f > ${FREQ_CONTROL}
    echo -n "CPU frequency is now "
    cat ${FREQ_CUR}
    sleep 1
done

echo ${OLD_SPEED} > ${FREQ_CONTROL}
echo ${OLD_GOV} > ${FREQ_GOV}
echo -n "Restored CPU frequency to "
cat ${FREQ_CUR}
echo -n "Restored cpufreq governor to "
cat ${FREQ_GOV}
