
cmake_minimum_required (VERSION 2.8)

project (eva)

set (CxPath ../cx)
set (BinPath ../bin)
set (BldPath eva)

list (APPEND CFiles eva.c pipelisp.c)

include (${CxPath}/include.cmake)

set (RUNTIME_OUTPUT_DIRECTORY ${BinPath})

add_executable (eva ${BldPath}/eva.c ${CxFullCFiles})
add_executable (pipelisp ${BldPath}/pipelisp.c ${CxFullCFiles})

