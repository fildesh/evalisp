
# Just a guess, can probably go older.
cmake_minimum_required (VERSION 2.8)

project (PipeLisp)

set (srcs main.c)

#set (CMAKE_C_COMPILER "clang")

if (UNIX)
  set (install_dir "$ENV{HOME}/.wireshark/plugins")
  if (NOT CMAKE_BUILD_TYPE)
    set (CMAKE_BUILD_TYPE DEBUG)
  else ()
    set (install_dir "${CMAKE_INSTALL_PREFIX}/share/wireshark/plugins")
  endif ()
  set (CMAKE_C_FLAGS "-Wall -Wextra")
  set (CMAKE_C_FLAGS_DEBUG "${CMAKE_C_FLAGS_DEBUG} -g3 -ansi -pedantic")
endif ()

add_executable (pipelisp ${srcs})

