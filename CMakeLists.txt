
cmake_minimum_required (VERSION 3.8)

#set(CMAKE_C_COMPILER "clang-cl")

project ("MIR")

set(CMAKE_BUILD_TYPE "RelWithDebInfo")

#set(CMAKE_VERBOSE_MAKEFILE ON)

if(NOT WIN32)
  add_compile_options(
    $<$<CONFIG:RELEASE>:-O3>
    $<$<CONFIG:RelWithDebInfo>:-O3>
  )
  add_compile_options(-std=gnu11 -Wno-abi -fsigned-char)
endif()

include(CheckCCompilerFlag)
if(CMAKE_COMPILER_IS_GNUCC)
  check_c_compiler_flag(-fno-tree-sra NO_TREE_SRA)
  if (NO_TREE_SRA)
    add_compile_options(-fno-tree-sra)
  endif()
  check_c_compiler_flag(-fno-ipa-cp-clone NO_IPA_CP_CLONE)
  if (NO_IPA_CP_CLONE)
    add_compile_options(-fno-ipa-cp-clone)
  endif()
endif()

include(FindThreads)
if(Threads_FOUND)
  link_libraries(${CMAKE_THREAD_LIBS_INIT})
endif()

message("C compiler flags: ${CMAKE_C_FLAGS}")

option(BUILD_TESTING "" ON)
include(CTest)

# ------------------ LIBMIR -----------------------
add_library(mir STATIC mir.c mir-gen.c c2mir/c2mir.c mir.h mir-gen.h c2mir/c2mir.h)
target_include_directories(mir PRIVATE ${PROJECT_SOURCE_DIR})
if(Threads_FOUND)
  target_compile_definitions(mir PUBLIC "MIR_PARALLEL_GEN")
endif()

# ------------------ C2M --------------------------
add_executable (c2m "c2mir/c2mir-driver.c")
target_include_directories(c2m PRIVATE ${PROJECT_SOURCE_DIR})
target_link_libraries(c2m mir ${CMAKE_DL_LIBS} )

# ------------------ MIR utils --------------------
add_executable (m2b "mir-utils/m2b.c")
target_include_directories(m2b PRIVATE ${PROJECT_SOURCE_DIR})
target_link_libraries(m2b mir)

add_executable (b2m "mir-utils/b2m.c")
target_include_directories(b2m PRIVATE ${PROJECT_SOURCE_DIR})
target_link_libraries(b2m mir)

add_executable (b2ctab "mir-utils/b2ctab.c")
target_include_directories(b2ctab PRIVATE ${PROJECT_SOURCE_DIR})
target_link_libraries(b2ctab mir)

# ------------------ ADT tests --------------------------
add_executable (varr_test "adt-tests/mir-varr-test.c")
target_include_directories(varr_test PRIVATE ${PROJECT_SOURCE_DIR})

add_executable (dlist_test "adt-tests/mir-dlist-test.c")
target_include_directories(dlist_test PRIVATE ${PROJECT_SOURCE_DIR})

add_executable (bitmap_test "adt-tests/mir-bitmap-test.c")
target_include_directories(bitmap_test PRIVATE ${PROJECT_SOURCE_DIR})

add_executable (htab_test "adt-tests/mir-htab-test.c")
target_include_directories(htab_test PRIVATE ${PROJECT_SOURCE_DIR})

add_executable (reduce_test "adt-tests/mir-reduce-test.c")
target_include_directories(reduce_test PRIVATE ${PROJECT_SOURCE_DIR})

add_test(varr-test varr_test)
add_test(dlist-test dlist_test)
add_test(bitmap-test bitmap_test)
add_test(htab-test htab_test)
add_test(reduce-test reduce_test ${PROJECT_SOURCE_DIR}/c2mir/c2mir.c)

# ------------------ MIR utility tests ------------------------
add_executable (simplify_test "mir-tests/simplify.c")
target_link_libraries(simplify_test mir)

add_executable (scan_test "mir-tests/scan-test.c")
target_link_libraries(scan_test mir)

add_executable (io_test "mir-tests/io.c")
target_link_libraries(io_test mir)

add_test(simplify-test simplify_test)
add_test(scan-test scan_test)
add_test(io-test io_test)

# ------------------ Common for MIR tests ----------------------
add_executable (run_test "mir-tests/run-test.c")
target_include_directories(run_test PRIVATE ${PROJECT_SOURCE_DIR})
target_link_libraries(run_test mir)

# ------------------ MIR interp tests --------------------------
add_executable (interp_loop "mir-tests/loop-interp.c")
target_include_directories(interp_loop PRIVATE ${PROJECT_SOURCE_DIR})
target_compile_definitions(interp_loop PRIVATE MIR_INTERP_DEBUG=1)
target_link_libraries(interp_loop mir)

add_executable (interp_loop_c "mir-tests/loop-interp.c")
target_include_directories(interp_loop_c PRIVATE ${PROJECT_SOURCE_DIR})
target_compile_definitions(interp_loop_c PRIVATE MIR_INTERP_DEBUG=1 MIR_C_INTERFACE=1)
target_link_libraries(interp_loop_c mir)

add_executable (interp_sieve "mir-tests/sieve-interp.c")
target_include_directories(interp_sieve PRIVATE ${PROJECT_SOURCE_DIR})
target_compile_definitions(interp_sieve PRIVATE MIR_INTERP_DEBUG=1)
target_link_libraries(interp_sieve mir)

add_executable (interp_sieve_c "mir-tests/sieve-interp.c")
target_include_directories(interp_sieve_c PRIVATE ${PROJECT_SOURCE_DIR})
target_compile_definitions(interp_sieve_c PRIVATE MIR_INTERP_DEBUG=1 MIR_C_INTERFACE=1)
target_link_libraries(interp_sieve_c mir)

add_executable (interp_hi "mir-tests/hi-interp.c")
target_include_directories(interp_hi PRIVATE ${PROJECT_SOURCE_DIR})
target_compile_definitions(interp_hi PRIVATE MIR_INTERP_DEBUG=1)
target_link_libraries(interp_hi mir)

add_executable (interp_args "mir-tests/args-interp.c")
target_include_directories(interp_args PRIVATE ${PROJECT_SOURCE_DIR})
target_link_libraries(interp_args mir)

add_executable (interp_args_c "mir-tests/args-interp.c")
target_include_directories(interp_args_c PRIVATE ${PROJECT_SOURCE_DIR})
target_compile_definitions(interp_args_c PRIVATE MIR_C_INTERFACE=1)
target_link_libraries(interp_args_c mir)

add_executable (run_test_d "mir-tests/run-test.c")
target_include_directories(run_test_d PRIVATE ${PROJECT_SOURCE_DIR})
target_compile_definitions(run_test_d PRIVATE TEST_GEN_DEBUG=1)
target_link_libraries(run_test_d mir)

add_test(interp-test1 interp_loop)
add_test(interp-test2 interp_loop_c)
add_test(interp-test3 interp_sieve)
add_test(interp-test4 interp_sieve_c)
add_test(interp-test5 interp_hi)
add_test(interp-test6 interp_args)
add_test(interp-test7 interp_args_c)

foreach (num 8 9 10)
  add_test(interp-test${num} run_test -i ${PROJECT_SOURCE_DIR}/mir-tests/test${num}.mir)
endforeach()

if(NOT WIN32)
  add_test(interp-test11 run_test -i ${PROJECT_SOURCE_DIR}/mir-tests/test11.mir) # for long double >= 10 bytes
  add_test(interp-test12 run_test -i ${PROJECT_SOURCE_DIR}/mir-tests/test12.mir) # multiple return values
endif()

foreach (num 13 14 15 16)
  add_test(interp-test${num} run_test -i ${PROJECT_SOURCE_DIR}/mir-tests/test${num}.mir)
endforeach()

# ------------------ MIR gen tests --------------------------

foreach (num 1 2 3 4 5 6 7)
  add_test(gen-test${num} run_test -d ${PROJECT_SOURCE_DIR}/mir-tests/test${num}.mir)
endforeach()

foreach (num 8 9 10)
  add_test(gen-test${num} run_test -g ${PROJECT_SOURCE_DIR}/mir-tests/test${num}.mir)
endforeach()

if(NOT WIN32)
  add_test(gen-test11 run_test -g ${PROJECT_SOURCE_DIR}/mir-tests/test11.mir) # for long double >= 10 bytes
  add_test(gen-test12 run_test -g ${PROJECT_SOURCE_DIR}/mir-tests/test12.mir) # multiple return values
endif()

foreach (num 13 14 15 16)
  add_test(gen-test${num} run_test -g ${PROJECT_SOURCE_DIR}/mir-tests/test${num}.mir)
endforeach()

add_executable (gen_loop "mir-tests/loop-sieve-gen.c")
target_include_directories(gen_loop PRIVATE ${PROJECT_SOURCE_DIR})
target_compile_definitions(gen_loop PRIVATE TEST_GEN_DEBUG=1 TEST_GEN_LOOP)
target_link_libraries(gen_loop mir)

add_executable (gen_sieve "mir-tests/loop-sieve-gen.c")
target_include_directories(gen_sieve PRIVATE ${PROJECT_SOURCE_DIR})
target_compile_definitions(gen_sieve PRIVATE TEST_GEN_DEBUG=1 TEST_GEN_SIEVE)
target_link_libraries(gen_sieve mir)

add_test(gen-test-loop gen_loop)
add_test(gen-test-sieve gen_sieve)

# ------------------ readme example test ----------------

add_executable (readme_example "mir-tests/readme-example.c")
target_include_directories(readme_example PRIVATE ${PROJECT_SOURCE_DIR})
target_link_libraries(readme_example mir)

add_test(readme-example-test readme_example)

# ------------------ mir2c test -------------------------

add_executable (mir2c_test "mir2c/mir2c.c")
target_include_directories(mir2c_test PRIVATE ${PROJECT_SOURCE_DIR})
target_compile_definitions(mir2c_test PRIVATE TEST_MIR2C)
target_link_libraries(mir2c_test mir)

add_test(mir2c-test mir2c_test)

# ------------------ c2m tests --------------------------

add_test(c2mir-simple-test c2m -v ${PROJECT_SOURCE_DIR}/sieve.c -ei)

