
cmake_minimum_required (VERSION 2.8.12)
set(CMAKE_DISABLE_SOURCE_CHANGES ON)
set(CMAKE_DISABLE_IN_SOURCE_BUILD ON)

project (evalisp)

include(ExternalProject)

ExternalProject_Add(fildesh_project
  #URL "https://github.com/fildesh/fildesh/archive/v0.1.5.tar.gz"
  #URL_HASH "SHA256=43be71eccda7254fed9b027db8f750d0ce744bd12375c3e560a584fb83889f90"
  GIT_REPOSITORY "https://github.com/fildesh/fildesh.git"
  #GIT_TAG "1bddffb7c521c54b4d6a49cf6533b2c75b06f1f0"
  GIT_TAG "trunk"

  CMAKE_ARGS "-DCMAKE_INSTALL_PREFIX:PATH=<INSTALL_DIR>"
  )
add_executable(fildesh IMPORTED)
add_library (fildesh_lib STATIC IMPORTED)
ExternalProject_Get_Property(fildesh_project INSTALL_DIR)
set_target_properties(fildesh PROPERTIES IMPORTED_LOCATION "${INSTALL_DIR}/bin/fildesh")
set_target_properties(fildesh_lib PROPERTIES IMPORTED_LOCATION "${INSTALL_DIR}/lib/libfildesh.a")
add_dependencies (fildesh fildesh_project)
add_dependencies (fildesh_lib fildesh_project)
set(FILDESH_INCLUDE_DIR "${INSALL_DIR}/include")

add_subdirectory(src)
