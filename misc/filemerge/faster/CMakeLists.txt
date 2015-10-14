#
# Copyright 2015, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
#

cmake_minimum_required (VERSION 2.6)
project (isa-translator CXX)

set (CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -W -Wall -Wextra -std=c++11")

if (NOT CMAKE_BUILD_TYPE)
  set (CMAKE_BUILD_TYPE Release)
endif (NOT CMAKE_BUILD_TYPE)

add_executable(isa-translator translate.cpp
    ${CMAKE_CURRENT_BINARY_DIR}/tables.hpp)

add_custom_command(
    OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/tables.hpp
    COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/make_tables.py --output ${CMAKE_CURRENT_BINARY_DIR}/tables.hpp
    DEPENDS make_tables.py)
