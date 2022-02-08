# Install script for directory: /home/sbuckley/repos/verification_timeprot/seL4

# Set the install prefix
if(NOT DEFINED CMAKE_INSTALL_PREFIX)
  set(CMAKE_INSTALL_PREFIX "/usr/local")
endif()
string(REGEX REPLACE "/$" "" CMAKE_INSTALL_PREFIX "${CMAKE_INSTALL_PREFIX}")

# Set the install configuration name.
if(NOT DEFINED CMAKE_INSTALL_CONFIG_NAME)
  if(BUILD_TYPE)
    string(REGEX REPLACE "^[^A-Za-z0-9_]+" ""
           CMAKE_INSTALL_CONFIG_NAME "${BUILD_TYPE}")
  else()
    set(CMAKE_INSTALL_CONFIG_NAME "Release")
  endif()
  message(STATUS "Install configuration: \"${CMAKE_INSTALL_CONFIG_NAME}\"")
endif()

# Set the component getting installed.
if(NOT CMAKE_INSTALL_COMPONENT)
  if(COMPONENT)
    message(STATUS "Install component: \"${COMPONENT}\"")
    set(CMAKE_INSTALL_COMPONENT "${COMPONENT}")
  else()
    set(CMAKE_INSTALL_COMPONENT)
  endif()
endif()

# Install shared libraries without execute permission?
if(NOT DEFINED CMAKE_INSTALL_SO_NO_EXE)
  set(CMAKE_INSTALL_SO_NO_EXE "1")
endif()

# Is this installation the result of a crosscompile?
if(NOT DEFINED CMAKE_CROSSCOMPILING)
  set(CMAKE_CROSSCOMPILING "FALSE")
endif()

# Set default install directory permissions.
if(NOT DEFINED CMAKE_OBJDUMP)
  set(CMAKE_OBJDUMP "/usr/bin/objdump")
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  if(EXISTS "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/bin/kernel.elf" AND
     NOT IS_SYMLINK "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/bin/kernel.elf")
    file(RPATH_CHECK
         FILE "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/bin/kernel.elf"
         RPATH "")
  endif()
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/bin" TYPE EXECUTABLE FILES "/home/sbuckley/repos/verification_timeprot/l4v/spec/cspec/c/config-build/ARM/kernel.elf")
  if(EXISTS "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/bin/kernel.elf" AND
     NOT IS_SYMLINK "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/bin/kernel.elf")
    if(CMAKE_INSTALL_DO_STRIP)
      execute_process(COMMAND "/usr/bin/strip" "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/bin/kernel.elf")
    endif()
  endif()
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/libsel4/include" TYPE DIRECTORY FILES
    "/home/sbuckley/repos/verification_timeprot/seL4/libsel4/include/"
    "/home/sbuckley/repos/verification_timeprot/seL4/libsel4/arch_include/arm/"
    "/home/sbuckley/repos/verification_timeprot/seL4/libsel4/sel4_arch_include/aarch32/"
    "/home/sbuckley/repos/verification_timeprot/seL4/libsel4/sel4_plat_include/imx6/"
    "/home/sbuckley/repos/verification_timeprot/seL4/libsel4/mode_include/32/"
    "/home/sbuckley/repos/verification_timeprot/l4v/spec/cspec/c/config-build/ARM/libsel4/include/"
    "/home/sbuckley/repos/verification_timeprot/l4v/spec/cspec/c/config-build/ARM/libsel4/arch_include/arm/"
    "/home/sbuckley/repos/verification_timeprot/l4v/spec/cspec/c/config-build/ARM/libsel4/sel4_arch_include/aarch32/"
    "/home/sbuckley/repos/verification_timeprot/l4v/spec/cspec/c/config-build/ARM/gen_config/"
    "/home/sbuckley/repos/verification_timeprot/l4v/spec/cspec/c/config-build/ARM/libsel4/gen_config/"
    "/home/sbuckley/repos/verification_timeprot/l4v/spec/cspec/c/config-build/ARM/libsel4/autoconf/"
    FILES_MATCHING REGEX "/[^/]*\\.h$")
endif()

if("x${CMAKE_INSTALL_COMPONENT}x" STREQUAL "xUnspecifiedx" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/libsel4/src" TYPE DIRECTORY FILES "/home/sbuckley/repos/verification_timeprot/seL4/libsel4/src/")
endif()

if(NOT CMAKE_INSTALL_LOCAL_ONLY)
  # Include the install script for each subdirectory.
  include("/home/sbuckley/repos/verification_timeprot/l4v/spec/cspec/c/config-build/ARM/libsel4/cmake_install.cmake")

endif()

if(CMAKE_INSTALL_COMPONENT)
  set(CMAKE_INSTALL_MANIFEST "install_manifest_${CMAKE_INSTALL_COMPONENT}.txt")
else()
  set(CMAKE_INSTALL_MANIFEST "install_manifest.txt")
endif()

string(REPLACE ";" "\n" CMAKE_INSTALL_MANIFEST_CONTENT
       "${CMAKE_INSTALL_MANIFEST_FILES}")
file(WRITE "/home/sbuckley/repos/verification_timeprot/l4v/spec/cspec/c/config-build/ARM/${CMAKE_INSTALL_MANIFEST}"
     "${CMAKE_INSTALL_MANIFEST_CONTENT}")
