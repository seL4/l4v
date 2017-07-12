#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
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
