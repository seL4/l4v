#
# Copyright 2021, Proofcraft Pty Ltd
#
# SPDX-License-Identifier: GPL-2.0-only
#

# This toolchain file is used for config file generation and is attempting
# to remove all compiler and tool chain checking that CMake does by default.
#
# This comes with the caveat that some internal CMake values will not be set,
# but it's fine to be fast and loose here, because the config values will
# eventually be checked against the real values the C compiler will use.

set(CMAKE_C_COMPILER_FORCED TRUE)
set(CMAKE_C_COMPILER_WORKS TRUE)

# This setting would remove the compiler ID check as well, but it doesn't seem
# to be working under Ubuntu, presumably because some other CMake variable isn't
# being set. So we're leaving it alone. Uncomment if you want fewer checks on
# e.g. MacOS.

# set(CMAKE_C_COMPILER_ID_RUN TRUE)
