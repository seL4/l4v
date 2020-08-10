#!/usr/bin/env python3
#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

import argparse
import os
import sys
import re
from datetime import timedelta, date
from dateutil.parser import isoparse

DESCRIPTION = 'Run sorry count statistics on repository'


def cmd(c):
    return os.popen(c).read()


def log_lines(start, end, path):
    """
    git log -p for the specified date period
    """
    git_cmd = 'git log --date=local -p --since "%s" --before "%s" -- %s'
    return cmd(git_cmd % (start, end, path)).splitlines()


def sorries_current(path):
    """
    git grep
    """
    git_cmd = 'git grep sorry %s | wc -l' % path
    return int(cmd(git_cmd).strip())


def repo_root():
    git_cmd = 'git rev-parse --show-toplevel'
    return cmd(git_cmd)[:-1]


def print_stats(deadline, delta, end, path):
    start = end - delta

    cur_path = os.getcwd()
    os.chdir(repo_root())
    difflog = log_lines(start, end, path)
    current = sorries_current(path)
    os.chdir(cur_path)

    sorry_added = re.compile("^\+.*sorry")
    sorry_removed = re.compile("^-.*sorry")
    lemma_added = re.compile("^\+.*lemma")
    lemma_removed = re.compile("^-.*lemma")
    author_line = re.compile("^Author:")
    patch_line = re.compile("(^\+)|(^-)")

    sorries_added = 0
    sorries_removed = 0
    lemmas_added = 0
    lines = 0

    authors = {}

    for line in difflog:
        if patch_line.match(line):
            lines += 1
        if sorry_added.match(line):
            sorries_added += 1
        if sorry_removed.match(line):
            sorries_removed += 1
        if lemma_added.match(line):
            lemmas_added += 1
        if lemma_removed.match(line):
            lemmas_added -= 1
        if author_line.match(line):
            authors[line] = 1

    balance = sorries_added-sorries_removed

    removed_per_day = sorries_removed / delta.days
    balance_per_day = balance / delta.days

    if removed_per_day != 0:
        projected_days = current / removed_per_day
    else:
        projected_days = -1

    today = date.today()
    projected_end = today + timedelta(days=projected_days)

    days_left = deadline - today
    needed_rate = current / days_left.days

    days_diff = projected_days-days_left.days
    if days_diff == 0:
        over_under = 'precisely on target'
    elif days_diff < 0:
        over_under = '%d days early' % (-days_diff)
    else:
        over_under = '%d days late' % days_diff

    print("Date range: {} to {} ({:.0f} weeks)".format(start, end, delta.days/7))
    print()
    print("Patch lines:     {:6d}".format(lines))
    print("Lemmas added:    {:6d}".format(lemmas_added))
    print("Sorries added:   {:6d}".format(sorries_added))
    print("Sorries removed: {:6d}".format(sorries_removed))
    print("Sorry balance:   {:+6d}".format(balance))
    print("Active authors:  {:6d}".format(len(list(authors))))
    print()
    print("Sorries current: {:6d}".format(current))
    print()
    print("Rate removed:    {:6.1f} sorries per week".format(removed_per_day * 7))
    print("Rate balance:    {:+6.1f} sorries per week".format(balance_per_day * 7))
    print("Rate needed:     {:6.1f} sorries per week ({:+.1f} s/w)".format(
        needed_rate * 7, (needed_rate-removed_per_day)*7))
    print()
    print("Target end date: {0} (in {1} days)".format(deadline, days_left.days))
    if projected_days >= 0:
        print("Projected date:  {0} ({1})".format(projected_end, over_under))
    else:
        print("Projected date:  inf")


if __name__ == '__main__':
    # Setup the command line parser.
    parser = argparse.ArgumentParser(description=DESCRIPTION)
    parser.add_argument('-w', "--weeks", help="Number of weeks to look back",
                        type=int, default=4)
    parser.add_argument('-e', "--end", help="End of the stats time period",
                        default=date.today().isoformat())
    parser.add_argument('-p', "--path", help="Restrict statistic to this path",
                        default=".")
    parser.add_argument("deadline", help="Project deadline (yyyy-mm-dd)")

    args = parser.parse_args()

    delta = timedelta(weeks=args.weeks)
    end = isoparse(args.end).date()
    deadline = isoparse(args.deadline).date()

    print_stats(deadline, delta, end, args.path)
    sys.exit(0)
