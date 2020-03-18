#!/usr/bin/env python
#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

import os
import sys
import re
import locale

locale.setlocale(locale.LC_ALL, 'en_US.UTF8')


def fetch_match(str, r):
    m = re.search(r, str)
    assert m != None
    return m.group(1)


for i in sys.argv[1:]:
    with open(i) as f:
        data = "\n".join(f.readlines())

    def intc(v):
        return "{:,}".format(int(v), grouping=True).replace(",", "\\,")

    project = i.split(".")[0]
    functions = intc(fetch_match(data, "([0-9]+) function.s"))
    loc = intc(fetch_match(data, "([0-9]+) input line"))

    c_time = fetch_match(data, "C Parser CPU Time : ([0-9]+) ms")
    ac_time = fetch_match(data, "AutoCorres CPU Time : ([0-9]+) ms")
    c_secs = int(c_time) / 1000.0
    ac_secs = int(ac_time) / 1000.0

    c_los = intc(fetch_match(data, "CParser +([0-9]+)"))
    ac_los = intc(fetch_match(data, "polish +([0-9]+)"))

    c_termsize = intc(fetch_match(data, "CParser +[0-9]+ +([0-9]+)"))
    ac_termsize = intc(fetch_match(data, "polish +[0-9]+ +([0-9]+)"))

    project = {
        "rtos": "eChronos",
        "schorr_waite": "Schorr-Waite",
        "sel4": "seL4 kernel",
        "sysinit": "CapDL SysInit",
        "piccolo": "Piccolo kernel",
    }[project]

    print("    {project:<20} & {loc:>7} & {functions:>4} & "
          + "{c_secs:8.1f} & {ac_secs:8.1f} & "
          + "{c_los:>8} &  {ac_los:>8} & "
            + "{c_termsize:>5} & {ac_termsize:>5} \\\\").format(grouping=True, **locals())

    c_los_raw = int(fetch_match(data, "CParser +([0-9]+)"))
    ac_los_raw = int(fetch_match(data, "polish +([0-9]+)"))

    c_termsize_raw = int(fetch_match(data, "CParser +[0-9]+ +([0-9]+)"))
    ac_termsize_raw = int(fetch_match(data, "polish +[0-9]+ +([0-9]+)"))

    print(" % percent : LoS: {:%}  TS: {:%}".format(
        float(c_los_raw - ac_los_raw) / c_los_raw, float(c_termsize_raw - ac_termsize_raw) / c_termsize_raw))
