SHELL=sh
#
CC=gcc -fno-tree-sra -std=gnu11 -Wno-abi # latest versions of gcc has a buggy SRA
# 2nd alternative:
# CC=clang -std=gnu11 -Wno-abi
CFLAGS=-O3 -g -DNDEBUG 
TARGET=x86_64
MIR_DEPS=mir.h mir-varr.h mir-dlist.h mir-htab.h mir-hash.h mir-interp.c mir-x86_64.c
MIR_GEN_DEPS=$(MIR_DEPS) mir-bitmap.h mir-gen-$(TARGET).c
OBJS=mir.o mir-gen.o c2m l2m m2b b2m b2ctab
Q=@

all: $(OBJS)

mir.o: mir.c $(MIR_DEPS)
	$(CC) -c $(CFLAGS) -o $@ $<

mir-gen.o: mir-gen.c $(MIR_GEN_DEPS)
	$(CC) -c $(CFLAGS) -D$(TARGET) -o $@ $<

c2m: mir.o mir-gen.o c2mir/c2mir.h c2mir/c2mir.c c2mir/c2mir-driver.c
	$(CC) $(CFLAGS) -D$(TARGET) -I. mir-gen.o c2mir/c2mir.c c2mir/c2mir-driver.c mir.o -ldl -o $@

llvm2mir.o: llvm2mir/llvm2mir.c $(MIR_DEPS) mir.c mir-gen.h mir-gen.c
	$(CC) -I. -c $(CFLAGS) -o $@ $<

l2m: llvm2mir.o $(MIR_DEPS) llvm2mir/llvm2mir.h llvm2mir/llvm2mir-driver.c mir-gen.c mir-gen.h 
	$(CC) -I. $(CFLAGS) mir.c mir-gen.c llvm2mir.o llvm2mir/llvm2mir-driver.c -lLLVM -lm -ldl -o l2m

m2b: mir.o mir-utils/m2b.c
	$(CC) -I. $(CFLAGS) -o $@ mir.o mir-utils/m2b.c
	
b2m: mir.o mir-utils/b2m.c
	$(CC) -I. $(CFLAGS) -o $@ mir.o mir-utils/b2m.c
	
b2ctab: mir.o mir-utils/b2ctab.c
	$(CC) -I. $(CFLAGS) -o $@ mir.o mir-utils/b2ctab.c
	
test: adt-test mir-test io-test scan-test interp-test gen-test readme-example-test mir2c-test c2mir-test l2m-test
	@echo ==============================Test is done
      
l2m-test: l2m-simple-test # l2m-full-test

l2m-simple-test: l2m-test1 l2m-test2

l2m-full-test: l2m-interp-test l2m-gen-test

l2m-interp-test: l2m
	$(SHELL) c-tests/runtests.sh c-tests/use-l2m-interp
l2m-gen-test: l2m
	$(SHELL) c-tests/runtests.sh c-tests/use-l2m-gen

l2m-test1: l2m
	@echo +++++ LLVM to MIR translator test '(-O0)' +++++++
	clang -O0 -fno-vectorize -w -c -emit-llvm sieve.c
	@echo +++++ Interpreter +++++++ && ./l2m -i sieve.bc
	@echo +++++ Generator +++++++ && ./l2m -g sieve.bc
	
l2m-test2: l2m
	@echo +++++ LLVM to MIR translator test '(-O2)' +++++++
	clang -O2 -fno-vectorize -w -c -emit-llvm sieve.c
	@echo +++++ Interpreter +++++++ && ./l2m -i sieve.bc
	@echo +++++ Generator +++++++ && ./l2m -g sieve.bc
	
bench: interp-bench gen-bench io-bench mir2c-bench c2mir-sieve-bench gen-speed c2mir-bench
	@echo ==============================Bench is done

mir-test:
	$(CC) -g mir.c mir-tests/simplify.c && ./a.out

scan-test:
	$(CC) -g mir.c mir-tests/scan-test.c && ./a.out

io-test:
	$(CC) -g mir.c mir-tests/io.c && ./a.out

io-bench:
	@echo ========io-bench can take upto 2 min===============
	$(CC) $(CFLAGS) mir.c mir-tests/io-bench.c && ./a.out

interp-loop:
	$(CC) -g -D$(TARGET) -DMIR_INTERP_DEBUG=1 mir.c mir-tests/loop-interp.c && ./a.out
interp-loop-c:
	$(CC) -g -D$(TARGET) -DMIR_INTERP_DEBUG=1 -DMIR_C_INTERFACE=1 mir.c mir-tests/loop-interp.c && ./a.out
interp-sieve:
	$(CC) -g -D$(TARGET) -DMIR_INTERP_DEBUG=1 mir.c mir-tests/sieve-interp.c && ./a.out
interp-sieve-c:
	$(CC) -g -D$(TARGET) -DMIR_INTERP_DEBUG=1 -DMIR_C_INTERFACE=1 mir.c mir-tests/sieve-interp.c && ./a.out
interp-hi:
	$(CC) -g -D$(TARGET) -DMIR_INTERP_DEBUG=1 mir.c mir-tests/hi-interp.c && ./a.out
interp-args:
	$(CC) -g -D$(TARGET) mir.c mir-tests/args-interp.c && ./a.out
interp-args-c:
	$(CC) -g -D$(TARGET) -DMIR_C_INTERFACE=1 mir.c mir-tests/args-interp.c && ./a.out
interp-test8:
	$(CC) -g -D$(TARGET) mir.c mir-gen.c mir-tests/run-test.c && ./a.out -i mir-tests/test8.mir
interp-test9:
	$(CC) -g -D$(TARGET) mir.c mir-gen.c mir-tests/run-test.c && ./a.out -i mir-tests/test9.mir

interp-test10:
	$(CC) -g -D$(TARGET) mir.c mir-gen.c mir-tests/run-test.c && ./a.out -i mir-tests/test10.mir

interp-test11:
	$(CC) -g -D$(TARGET) mir.c mir-gen.c mir-tests/run-test.c && ./a.out -i mir-tests/test11.mir

interp-test12:
	$(CC) -g -D$(TARGET) mir.c mir-gen.c mir-tests/run-test.c && ./a.out -i mir-tests/test12.mir

interp-test13:
	$(CC) -g -D$(TARGET) mir.c mir-gen.c mir-tests/run-test.c && ./a.out -i mir-tests/test13.mir

interp-test14:
	$(CC) -g -D$(TARGET) mir.c mir-gen.c mir-tests/run-test.c && ./a.out -i mir-tests/test14.mir

interp-test: interp-loop interp-loop-c interp-sieve interp-sieve-c interp-hi interp-args interp-args-c interp-test8\
             interp-test9 interp-test10 interp-test11 interp-test12 interp-test13 interp-test14

interp-bench:
	$(CC) $(CFLAGS) -D$(TARGET) mir.c mir-tests/loop-interp.c && ./a.out && size ./a.out
	$(CC) $(CFLAGS) -D$(TARGET) -DMIR_C_INTERFACE=1 mir.c mir-tests/loop-interp.c && ./a.out && size ./a.out
	$(CC) $(CFLAGS) -D$(TARGET) mir.c mir-tests/sieve-interp.c && ./a.out && size ./a.out

gen-test1:
	$(CC) -g -D$(TARGET) -DMIR_GEN_DEBUG=1 mir.c mir-gen.c mir-tests/test-gen.c && ./a.out mir-tests/test1.mir
gen-test2:
	$(CC) -g -D$(TARGET) -DMIR_GEN_DEBUG=1 mir.c mir-gen.c mir-tests/test-gen.c && ./a.out mir-tests/test2.mir
gen-test3:
	$(CC) -g -D$(TARGET) -DMIR_GEN_DEBUG=1 mir.c mir-gen.c mir-tests/test-gen.c && ./a.out mir-tests/test3.mir
gen-test4:
	$(CC) -g -D$(TARGET) -DMIR_GEN_DEBUG=1 mir.c mir-gen.c mir-tests/test-gen.c && ./a.out mir-tests/test4.mir
gen-test5:
	$(CC) -g -D$(TARGET) -DMIR_GEN_DEBUG=1 mir.c mir-gen.c mir-tests/test-gen.c && ./a.out mir-tests/test5.mir
gen-test6:
	$(CC) -g -D$(TARGET) -DMIR_GEN_DEBUG=1 mir.c mir-gen.c mir-tests/test-gen.c && ./a.out mir-tests/test6.mir
gen-test7:
	$(CC) -g -D$(TARGET) -DMIR_GEN_DEBUG=1 mir.c mir-gen.c mir-tests/test-gen.c && ./a.out mir-tests/test7.mir

gen-test8:
	$(CC) -g -D$(TARGET) -DMIR_GEN_DEBUG=1 mir.c mir-gen.c mir-tests/run-test.c && ./a.out -g mir-tests/test8.mir

gen-test9:
	$(CC) -g -D$(TARGET) -DMIR_GEN_DEBUG=1 mir.c mir-gen.c mir-tests/run-test.c && ./a.out -g mir-tests/test9.mir

gen-test10:
	$(CC) -g -D$(TARGET) mir.c mir-gen.c mir-tests/run-test.c && ./a.out -g mir-tests/test10.mir

gen-test11:
	$(CC) -g -D$(TARGET) mir.c mir-gen.c mir-tests/run-test.c -DMIR_GEN_DEBUG=1 && ./a.out -g mir-tests/test11.mir

gen-test12:
	$(CC) -g -D$(TARGET) mir.c mir-gen.c mir-tests/run-test.c -DMIR_GEN_DEBUG=1 && ./a.out -g mir-tests/test12.mir

gen-test13:
	$(CC) -g -D$(TARGET) mir.c mir-gen.c mir-tests/run-test.c && ./a.out -g mir-tests/test13.mir

gen-test14:
	$(CC) -g -D$(TARGET) mir.c mir-gen.c mir-tests/run-test.c && ./a.out -g mir-tests/test14.mir

gen-test: gen-test1 gen-test2 gen-test3 gen-test4 gen-test5 gen-test6 gen-test7 gen-test8 gen-test9 gen-test10 gen-test11 gen-test12 gen-test13 gen-test14
	$(CC) -g -D$(TARGET) -DTEST_GEN_LOOP -DMIR_GEN_DEBUG=1 mir.c mir-gen.c mir-tests/loop-sieve-gen.c && ./a.out
	$(CC) -g -D$(TARGET) -DTEST_GEN_SIEVE -DMIR_GEN_DEBUG=1 mir.c mir-gen.c mir-tests/loop-sieve-gen.c && ./a.out

gen-bench:
	$(CC) $(CFLAGS) -D$(TARGET) -DTEST_GEN_LOOP mir.c mir-gen.c mir-tests/loop-sieve-gen.c && ./a.out && size ./a.out
	$(CC) $(CFLAGS) -D$(TARGET) -DTEST_GEN_SIEVE mir.c mir-gen.c mir-tests/loop-sieve-gen.c && ./a.out && size ./a.out

gen-speed:
	if type valgrind  > /dev/null 2>&1; then \
	  $(CC) $(CFLAGS) -D$(TARGET) -DTEST_GEN_SIEVE -DTEST_GENERATION_ONLY mir.c mir-gen.c mir-tests/loop-sieve-gen.c && valgrind --tool=lackey ./a.out; \
	fi

readme-example-test:
	$(CC) -g -D$(TARGET) mir.c mir-gen.c mir-tests/readme-example.c && ./a.out

c2mir-test: c2mir-simple-test c2mir-full-test

c2mir-simple-test:
	$(CC) -g -D$(TARGET) -I. mir.c mir-gen.c c2mir/c2mir.c c2mir/c2mir-driver.c -ldl && ./a.out -v sieve.c -ei

c2mir-full-test: c2mir-interp-test c2mir-gen-test c2mir-bootstrap-test

c2mir-interp-test: c2m
	$(SHELL) c-tests/runtests.sh c-tests/use-c2m-interp
c2mir-gen-test: c2m
	$(SHELL) c-tests/runtests.sh c-tests/use-c2m-gen

c2mir-bootstrap-test: c2m
	$(Q) echo -n +++++++ C2MIR Bootstrap Test '... '
	$(Q) ./c2m -D$(TARGET) -I. mir-gen.c c2mir/c2mir.c c2mir/c2mir-driver.c mir.c && mv a.bmir 1.bmir
	$(Q) ./c2m -D$(TARGET) -I. mir-gen.c c2mir/c2mir.c c2mir/c2mir-driver.c mir.c -el -D$(TARGET) -I. mir-gen.c c2mir/c2mir.c c2mir/c2mir-driver.c mir.c 
	$(Q) cmp 1.bmir a.bmir && echo Passed || echo FAIL
	$(Q) rm -rf 1.bmir a.bmir

c2mir-bootstrap-test2: c2m b2ctab
	$(Q) echo -n +++++++ C2MIR Bootstrap Test 2 '(usually it takes about 10-20 sec) ... '
	$(Q) ./c2m -D$(TARGET) -I. mir-gen.c c2mir/c2mir.c c2mir/c2mir-driver.c mir.c && mv a.bmir 1.bmir
	$(Q) ./b2ctab <1.bmir >mir-ctab
	$(Q) $(CC) $(CFLAGS) -D$(TARGET) -w -fno-tree-sra mir.c mir-gen.c mir-bin-driver.c -ldl
	$(Q) ./a.out -D$(TARGET) -I. mir-gen.c c2mir/c2mir.c c2mir/c2mir-driver.c mir.c
	$(Q) cmp 1.bmir a.bmir && echo Passed || echo FAIL
	$(Q) rm -rf 1.bmir a.bmir mir-ctab

c2mir-sieve-bench:
	$(CC) $(CFLAGS) -D$(TARGET) -I. mir-gen.c c2mir/c2mir.c c2mir/c2mir-driver.c mir.c -ldl && ./a.out -v sieve.c -eg && size ./a.out

c2mir-bench: c2m
	$(SHELL) c-benchmarks/run-benchmarks.sh

# c2mir-bin-test is very slow
c2mir-bin-test: c2mir-bin-interp-test c2mir-bin-gen-test

c2mir-bin-interp-test: c2m mir.o mir-gen.o b2ctab
	$(SHELL) c-tests/runtests.sh c-tests/use-c2m-bin-interp

c2mir-bin-gen-test: c2m mir.o mir-gen.o b2ctab
	$(SHELL) c-tests/runtests.sh c-tests/use-c2m-bin-gen

mir2c-test:
	$(CC) -g -DTEST_MIR2C -I. mir.c mir2c/mir2c.c && ./a.out

mir2c-bench:
	$(CC) $(CFLAGS) -DTEST_MIR2C -I. mir2c/mir2c.c mir.c && ./a.out -v && size ./a.out

adt-test: varr-test dlist-test bitmap-test htab-test reduce-test

varr-test:
	$(CC) -g -I. adt-tests/mir-varr-test.c && ./a.out

dlist-test:
	$(CC) -g -I. adt-tests/mir-dlist-test.c && ./a.out

bitmap-test:
	$(CC) -g -I. adt-tests/mir-bitmap-test.c && ./a.out

htab-test:
	$(CC) -g -I. adt-tests/mir-htab-test.c && ./a.out

reduce-test:
	$(CC) -g -I. -O3 -DNDEBUG adt-tests/mir-reduce-test.c && ./a.out < c2mir/c2mir.c

clean:
	rm -f $(OBJS) ./a.out
	rm -f llvm2mir.o ./l2m

realclean: clean

sloc:
	@echo -n 'C2MIR: ' && wc -l c2mir/c2mir.c | awk '{last=$$1} END {print last}'
	@echo -n 'ADT: ' && wc -l mir-dlist.h mir-hash.h mir-htab.h mir-varr.h mir-reduce.h mir-bitmap.h mir-mp.h | awk '{last=$$1} END {print last}'
	@echo -n 'MIR API: ' && wc -l mir.[ch] | awk '{last=$$1} END {print last}'
	@echo -n 'MIR Interpreter: ' && wc -l mir-interp.c | awk '{last=$$1} END {print last}'
	@echo -n 'MIR Generator: ' && wc -l mir-gen.[ch] | awk '{last=$$1} END {print last}'
	@echo -n 'Machine dependent code: ' && wc -l mir-x86_64.c mir-gen-x86_64.c | awk '{last=$$1} END {print last}'
	@echo -n 'Overall: ' && wc -l c2mir/c2mir.c mir-dlist.h mir-hash.h mir-htab.h mir-varr.h mir-reduce.h mir-bitmap.h mir-mp.h mir.[ch] mir-interp.c mir-gen.[ch] mir-x86_64.c mir-gen-x86_64.c | awk '{last=$$1} END {print last}'

gcc-test:
	$(SHELL) c-tests/runtests.sh c-tests/use-gcc

clang-test:
	$(SHELL) c-tests/runtests.sh c-tests/use-clang
