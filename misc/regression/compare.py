#!/usr/bin/env python3
#
# Copyright 2022, Proofcraft Pty Ltd
#
# SPDX-License-Identifier: BSD-2-Clause
#

'''
Compare two run_tests.py log files for timing and memory differences.
'''

import argparse
import re


session_re = r'[A-Za-z0-9_-]+'
time_re = r'[0-9]+:[0-9][0-9]:[0-9][0-9]'
mem_re = r'[0-9]+[.][0-9]+'

line_re = re.compile(
    f'.*Finished ({session_re}).*\([ ]*({time_re}) real,[ ]*({time_re}) cpu,[ ]*({mem_re})GB\)')


def to_sec(time: str) -> int:
    '''
    Convert a time string to seconds
    '''
    h, m, s = time.split(':')
    return int(h) * 3600 + int(m) * 60 + int(s)


def parse_log(filename: str) -> dict:
    '''
    Parse a run_tests log file for lines of the form
    `Finished <session> (<time> real,  <time> cpu,  <number>GB)`
    '''
    session_data = {}

    with open(filename, 'r') as f:
        for line in f:
            match = re.match(line_re, line)
            if match:
                session = match[1]
                real, cpu, mem = to_sec(match[2]), to_sec(match[3]), float(match[4])
                session_data[session] = (real, cpu, mem)

    return session_data


def diff(sessions1: dict, sessions2: dict) -> dict:
    '''
    Return a dictionary of session names and differences between the times
    '''
    diffs = {}
    for session in sessions1:
        if session in sessions2:
            session1 = sessions1[session]
            session2 = sessions2[session]
            diff = (session2[0] - session1[0],
                    session2[1] - session1[1],
                    session2[2] - session1[2])
            perc = (diff[0] * 100 / session1[0] if session1[0] else 0,
                    diff[1] * 100 / session1[1] if session1[1] else 0,
                    diff[2] * 100 / session1[2] if session1[2] else 0)
            diffs[session] = diff, perc
        else:
            diffs[session] = None

    return diffs


def signed_time(seconds: int) -> str:
    '''
    Convert a time in seconds to a signed time string in [+-]m:ss format
    '''
    minutes = seconds // 60
    sec = seconds % 60
    return f'{minutes:+}:{sec:02}'


def main():
    parser = argparse.ArgumentParser(description="Compare regression log times")
    parser.add_argument('log1', help='First log file')
    parser.add_argument('log2', help='Second log file')

    args = parser.parse_args()

    sessions1 = parse_log(args.log1)
    sessions2 = parse_log(args.log2)

    diffs = diff(sessions1, sessions2)
    for session in diffs:
        if diffs[session] is None:
            print(f'{session} not in {args.log2}')
        else:
            real, cpu, mem = diffs[session][0]
            realh = signed_time(real)
            cpuh = signed_time(cpu)
            realp, cpup, memp = diffs[session][1]

        print(f'{session:22} '
              f'{realh:>6} ({realp:+6.1f}%) real, '
              f'{cpuh:>6} ({cpup:+6.1f}%) cpu, '
              f'{mem:+6.2f}GB ({memp:+6.1f}%)')


if __name__ == "__main__":
    main()
