#
# Copyright 2022, Proofcraft Pty Ltd
#
# SPDX-License-Identifier: BSD-2-Clause
#

"""Error, warning, and status message handling."""

import os
import sys

ANSI_RESET = "\033[0m"
ANSI_RED = "\033[31;1m"
ANSI_YELLOW = "\033[33m"

tty_status_line = [""]


def running_on_github():
    """Return True if we're running on GitHub Actions."""
    return os.environ.get("GITHUB_REPOSITORY") != None


def output_color(color, s, github=running_on_github()):
    """Wrap the given string in the given colour."""
    if sys.stderr.isatty() or github:
        return color + s + ANSI_RESET
    return s


def wipe_tty_status():
    """Clear the tty status line if it exists."""
    if sys.stdout.isatty() and tty_status_line[0]:
        print(" " * len(tty_status_line[0]) + "\r", end="")
        sys.stdout.flush()
        tty_status_line[0] = ""


def status(msg: str):
    """Print a status message to a tty status line or stdout."""
    wipe_tty_status()
    tty_status_line[0] = msg
    end = "\r" if sys.stdout.isatty() else "\n"
    print(tty_status_line[0], end=end)
    sys.stdout.flush()


def pos_str(file, line):
    """Return a string indicating a file position."""
    if file is None:
        return ""
    if line is None:
        return f" [{file}]"
    return f" [{file}:{line}]"


def warning(msg: str, file=None, line=None):
    """Print a warning message to stderr."""
    wipe_tty_status()
    w = output_color(ANSI_YELLOW, 'Warning:')
    sys.stderr.write(f'{w} {msg}{pos_str(file,line)}\n')


def error(msg: str, file=None, line=None):
    """Print an error message to stderr."""
    wipe_tty_status()
    e = output_color(ANSI_RED, 'Fatal error:')
    sys.stderr.write(f'{e} {msg}{pos_str(file,line)}\n')
