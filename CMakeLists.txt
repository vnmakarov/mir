
cmake_minimum_required (VERSION 3.8)

project ("MIR")

option(BUILD_TESTING "" OFF)
include(CTest)

find_package(LLVM)

add_library(mir STATIC mir.c "mir.h")
add_library(mir_gen STATIC mir-gen.c "mir.h")

if(NOT BUILD_TESTING)

add_executable (c2m "c2mir/c2mir.c" "c2mir/c2mir.h" "c2mir/c2mir-driver.c" "mir-gen.h")
target_include_directories(c2m PRIVATE ./)
target_link_libraries(c2m mir mir_gen)

add_executable (m2b "mir-utils/m2b.c")
target_include_directories(m2b PRIVATE ./)
target_link_libraries(m2b mir)

add_executable (b2m "mir-utils/b2m.c")
target_include_directories(b2m PRIVATE ./)
target_link_libraries(b2m mir)

add_executable (b2ctab "mir-utils/b2ctab.c")
target_include_directories(b2ctab PRIVATE ./)
target_link_libraries(b2ctab mir)

if(LLVM_FOUND)
add_library(llvm2mir STATIC llvm2mir/llvm2mir.c)
add_executable (l2m "llvm2mir/llvm2mir-driver.c" "llvm2mir/llvm2mir.h")
target_include_directories(l2m PRIVATE ./ ${LLVM_INCLUDE_DIRS})
target_link_libraries(l2m mir mir_gen llvm2mir)
endif()

else()

add_executable (interp_loop "mir-tests/loop-interp.c")
target_include_directories(interp_loop PRIVATE ./)
target_compile_definitions(interp_loop PRIVATE MIR_INTERP_DEBUG=1)
target_link_libraries(interp_loop mir)

add_executable (interp_loop_c "mir-tests/loop-interp.c")
target_include_directories(interp_loop_c PRIVATE ./)
target_compile_definitions(interp_loop_c PRIVATE MIR_INTERP_DEBUG=1 MIR_C_INTERFACE=1)
target_link_libraries(interp_loop_c mir)

add_executable (interp_sieve "mir-tests/sieve-interp.c")
target_include_directories(interp_sieve PRIVATE ./)
target_compile_definitions(interp_sieve PRIVATE MIR_INTERP_DEBUG=1)
target_link_libraries(interp_sieve mir)

add_executable (interp_sieve_c "mir-tests/sieve-interp.c")
target_include_directories(interp_sieve_c PRIVATE ./)
target_compile_definitions(interp_sieve_c PRIVATE MIR_INTERP_DEBUG=1 MIR_C_INTERFACE=1)
target_link_libraries(interp_sieve_c mir)

add_executable (interp_hi "mir-tests/hi-interp.c")
target_include_directories(interp_hi PRIVATE ./)
target_compile_definitions(interp_hi PRIVATE MIR_INTERP_DEBUG=1)
target_link_libraries(interp_hi mir)

add_executable (interp_args "mir-tests/args-interp.c")
target_include_directories(interp_args PRIVATE ./)
target_link_libraries(interp_args mir)

add_executable (interp_args_c "mir-tests/args-interp.c")
target_include_directories(interp_args_c PRIVATE ./)
target_compile_definitions(interp_args_c PRIVATE MIR_C_INTERFACE=1)
target_link_libraries(interp_args_c mir)

add_executable (mir_test "mir-tests/simplify.c")
target_include_directories(mir_test PRIVATE ./)
target_link_libraries(mir_test mir)

add_executable (scan_test "mir-tests/scan-test.c")
target_include_directories(scan_test PRIVATE ./)
target_link_libraries(scan_test mir)

add_executable (io_test "mir-tests/io.c")
target_include_directories(io_test PRIVATE ./)
target_link_libraries(io_test mir)

add_executable (gen_loop "mir-tests/loop-sieve-gen.c")
target_include_directories(gen_loop PRIVATE ./)
target_compile_definitions(gen_loop PRIVATE TEST_GEN_DEBUG=1 TEST_GEN_LOOP)
target_link_libraries(gen_loop mir mir_gen)

add_executable (gen_sieve "mir-tests/loop-sieve-gen.c")
target_include_directories(gen_sieve PRIVATE ./)
target_compile_definitions(gen_sieve PRIVATE TEST_GEN_DEBUG=1 TEST_GEN_SIEVE)
target_link_libraries(gen_sieve mir mir_gen)

add_executable (gen_test_d "mir-tests/test-gen.c")
target_include_directories(gen_test_d PRIVATE ./)
target_compile_definitions(gen_test_d PRIVATE TEST_GEN_DEBUG=1)
target_link_libraries(gen_test_d mir mir_gen)

add_executable (run_test_d "mir-tests/run-test.c")
target_include_directories(run_test_d PRIVATE ./)
target_compile_definitions(run_test_d PRIVATE TEST_GEN_DEBUG=1)
target_link_libraries(run_test_d mir mir_gen)

add_executable (run_test "mir-tests/run-test.c")
target_include_directories(run_test PRIVATE ./)
target_link_libraries(run_test mir mir_gen)

add_executable (varr_test "adt-tests/mir-varr-test.c")
target_include_directories(varr_test PRIVATE ./)

add_executable (dlist_test "adt-tests/mir-dlist-test.c")
target_include_directories(dlist_test PRIVATE ./)

add_executable (bitmap_test "adt-tests/mir-bitmap-test.c")
target_include_directories(bitmap_test PRIVATE ./)

add_executable (htab_test "adt-tests/mir-htab-test.c")
target_include_directories(htab_test PRIVATE ./)

add_executable (reduce_test "adt-tests/mir-reduce-test.c")
target_include_directories(reduce_test PRIVATE ./)

add_test(interp-test1 interp_loop)
add_test(interp-test2 interp_loop_c)
add_test(interp-test3 interp_sieve)
add_test(interp-test4 interp_sieve_c)
add_test(interp-test5 interp_hi)
add_test(interp-test6 interp_args)
add_test(interp-test7 interp_args_c)

add_test(interp-test8 run_test -i ./mir-tests/test8.mir)
add_test(interp-test9 run_test -i ./mir-tests/test9.mir)
add_test(interp-test10 run_test -i ./mir-tests/test10.mir)
add_test(interp-test11 run_test -i ./mir-tests/test11.mir)
#add_test(interp-test12 run_test -i ./mir-tests/test12.mir) multiple return values
add_test(interp-test13 run_test -i ./mir-tests/test13.mir)
add_test(interp-test14 run_test -i ./mir-tests/test14.mir)
add_test(interp-test15 run_test -i ./mir-tests/test15.mir)
add_test(interp-test16 run_test -i ./mir-tests/test16.mir)

add_test(mir-test mir_test)
add_test(scan-test scan_test)
add_test(io-test io_test)
add_test(loop-test gen_loop)
add_test(sieve-test gen_sieve)

add_test(gen-test1 gen_test_d ./mir-tests/test1.mir)
add_test(gen-test2 gen_test_d ./mir-tests/test2.mir)
add_test(gen-test3 gen_test_d ./mir-tests/test3.mir)
add_test(gen-test4 gen_test_d ./mir-tests/test4.mir)
add_test(gen-test5 gen_test_d ./mir-tests/test5.mir)
add_test(gen-test6 gen_test_d ./mir-tests/test6.mir)
add_test(gen-test7 gen_test_d ./mir-tests/test7.mir)
add_test(gen-test8 run_test_d ./mir-tests/test8.mir)
add_test(gen-test9 run_test_d ./mir-tests/test9.mir)
add_test(gen-test10 run_test ./mir-tests/test10.mir)
add_test(gen-test11 run_test_d ./mir-tests/test11.mir)
#add_test(gen-test12 run_test_d ./mir-tests/test12.mir)  multiple return values
#add_test(gen-test13 run_test ./mir-tests/test13.mir) SEGFAULT
add_test(gen-test14 run_test ./mir-tests/test14.mir)
add_test(gen-test15 run_test ./mir-tests/test15.mir)
add_test(gen-test16 run_test ./mir-tests/test16.mir)

add_test(varr-test varr_test)
add_test(dlist-test dlist_test)
add_test(bitmap-test bitmap_test)
add_test(htab-test htab_test)
add_test(reduce-test reduce_test)

endif()
