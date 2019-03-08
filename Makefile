CC=gcc -std=gnu11
CFLAGS=-Os -g
TARGET=x86_64
DEPS=mir.h mir-varr.h mir-dlist.h
OBJS=mir.o mir-interp.o mir-gen.o
all: $(OBJS)

mir.o: mir.c $(DEPS)
	$(CC) -c $(CFLAGS) -DMIR_IO -DMIR_SCAN -o $@ $<

mir-interp.o: mir-interp.c $(DEPS) mir-interp.h
	$(CC) -c -Os -g -o $@ $<

mir-gen.o: mir-gen.c $(DEPS) mir-bitmap.h $(TARGET)-target.c
	$(CC) -c $(CFLAGS) -D$(TARGET) -o $@ $<

test: util-test mir-test io-test scan-test interp-test gen-test c-test
	@echo ==============================Test is done
      
bench: interp-bench gen-bench io-bench c-bench
	@echo ==============================Bench is done

mir-test:
	$(CC) -g mir.c mir-tests/simplify.c && ./a.out

scan-test:
	$(CC) -g -DMIR_SCAN mir.c mir-tests/scan-test.c && ./a.out

io-test:
	$(CC) -g -DMIR_SCAN -DMIR_IO mir.c mir-tests/io.c && ./a.out

io-bench:
	$(CC) $(CFLAGS) -DNDEBUG -DMIR_SCAN -DMIR_IO mir.c mir-tests/io-bench.c && ./a.out

interp-test:
	$(CC) -g -D$(TARGET) -DMIR_INTERP_DEBUG=1 mir.c mir-interp.c mir-tests/loop-interp.c -lffi && ./a.out
	$(CC) -g -D$(TARGET) -DMIR_INTERP_DEBUG=1 -DMIR_C_INTERFACE=1 mir.c mir-interp.c mir-tests/loop-interp.c -lffi && ./a.out
	$(CC) -g -D$(TARGET) -DMIR_SCAN -DMIR_INTERP_DEBUG=1 mir.c mir-interp.c mir-tests/sieve-interp.c -lffi && ./a.out
	$(CC) -g -D$(TARGET) -DMIR_SCAN -DMIR_INTERP_DEBUG=1 -DMIR_C_INTERFACE=1 mir.c mir-interp.c mir-tests/sieve-interp.c -lffi && ./a.out
	$(CC) -g -D$(TARGET) -DMIR_SCAN -DMIR_INTERP_DEBUG=1 mir.c mir-interp.c mir-tests/hi-interp.c -lffi && ./a.out
	$(CC) -g -D$(TARGET) -DMIR_SCAN mir.c mir-interp.c mir-tests/args-interp.c -lffi && ./a.out
	$(CC) -g -D$(TARGET) -DMIR_SCAN -DMIR_C_INTERFACE=1 mir.c mir-interp.c mir-tests/args-interp.c -lffi && ./a.out

interp-bench:
	$(CC) $(CFLAGS) -DNDEBUG -D$(TARGET) mir.c mir-interp.c mir-tests/loop-interp.c -lffi && ./a.out && size ./a.out
	$(CC) $(CFLAGS) -DNDEBUG -D$(TARGET) -DMIR_C_INTERFACE=1 mir.c mir-interp.c mir-tests/loop-interp.c -lffi && ./a.out && size ./a.out
	$(CC) $(CFLAGS) -DNDEBUG -D$(TARGET) -DMIR_SCAN mir.c mir-interp.c mir-tests/sieve-interp.c -lffi && ./a.out && size ./a.out

gen-test:
	$(CC) -g -D$(TARGET) -DTEST_GEN_LOOP -DMIR_GEN_DEBUG=1 mir.c mir-gen.c mir-tests/loop-sieve-gen.c && ./a.out
	$(CC) -g -D$(TARGET) -DMIR_SCAN -DTEST_GEN_SIEVE -DMIR_GEN_DEBUG=1 mir.c mir-gen.c mir-tests/loop-sieve-gen.c && ./a.out
	$(CC) -g -D$(TARGET) -DMIR_SCAN -DMIR_GEN_DEBUG=1 mir.c mir-gen.c mir-tests/test-gen.c && ./a.out mir-tests/test1.mir && ./a.out mir-tests/test2.mir && ./a.out mir-tests/test3.mir

gen-bench:
	$(CC) $(CFLAGS) -DNDEBUG -D$(TARGET) -DTEST_GEN_LOOP mir.c mir-gen.c mir-tests/loop-sieve-gen.c && ./a.out && size ./a.out
	$(CC) $(CFLAGS) -DNDEBUG -D$(TARGET) -DMIR_SCAN -DTEST_GEN_SIEVE mir.c mir-gen.c mir-tests/loop-sieve-gen.c && ./a.out && size ./a.out

c-test:
	$(CC) -g -D$(TARGET) -DTEST_MIR_C -I. mir.c mir-c/mir-c.c && ./a.out -v

c-bench:
	$(CC) $(CFLAGS) -DNDEBUG -D$(TARGET) -DTEST_MIR_C -I. mir-c/mir-c.c mir.c && ./a.out -v && size ./a.out

util-test: varr-test dlist-test bitmap-test htab-test

varr-test:
	$(CC) -g -I. tests/mir-varr-test.c && ./a.out

dlist-test:
	$(CC) -g -I. tests/mir-dlist-test.c && ./a.out

bitmap-test:
	$(CC) -g -I. tests/mir-bitmap-test.c && ./a.out

htab-test:
	$(CC) -g -I. tests/mir-htab-test.c && ./a.out

clean:
	rm -f $(OBJS) ./a.out

realclean: clean
