
cmake_minimum_required (VERSION 2.8)

project (eva)

set (CxPath ../cx)
set (BinPath ../bin)
set (BldPath eva)

list (APPEND CFiles eva.c pipelisp.c sxpn.c)
list (APPEND HFiles sxpn.h)

include (${CxPath}/include.cmake)

set (CMAKE_RUNTIME_OUTPUT_DIRECTORY ${BinPath})

addbinexe (eva eva.c)
addbinexe (pipelisp pipelisp.c)

