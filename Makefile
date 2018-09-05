CC=gcc
CFLAGS=-Os -g
TARGET=x86_64
DEPS=mir.h mir-varr.h mir-dlist.h
OBJS=mir.o mir-interp.o mir-gen.o
all: $(OBJS)

mir.o: mir.c $(DEPS)
	$(CC) -c $(CFLAGS) -DMIR_IO -DMIR_SCAN -o $@ $<
mir-interp.o: mir-interp.c $(DEPS) mir-interp.h
	$(CC) -c -O2 -g -o $@ $<
mir-gen.o: mir-gen.c $(DEPS) mir-bitmap.h $(TARGET)-target.c
	$(CC) -c $(CFLAGS) -D$(TARGET) -o $@ $<

test: util-test mir-test io-test scan-test interp-test gen-test c-test

bench: interp-bench gen-bench c-bench

mir-test:
	$(CC) -g -DTEST_MIR mir.c && ./a.out

scan-test:
	$(CC) -g -DMIR_SCAN -DTEST_MIR_SCAN mir.c && ./a.out

io-test:
	$(CC) -g -DMIR_SCAN -DMIR_IO -DTEST_MIR_IO mir.c && ./a.out

io-bench:
	$(CC) $(CFLAGS) -DNDEBUG -DMIR_SCAN -DMIR_IO -DBENCH_MIR_IO mir.c && ./a.out

interp-test:
	$(CC) -g -D$(TARGET) -DTEST_MIR_INTERP -DMIR_INTERP_DEBUG=1 mir.c mir-interp.c && ./a.out
	$(CC) -g -D$(TARGET) -DMIR_SCAN -DTEST_MIR_INTERP2 -DMIR_INTERP_DEBUG=1 mir.c mir-interp.c && ./a.out

interp-bench:
	$(CC) $(CFLAGS) -DNDEBUG -D$(TARGET) -DTEST_MIR_INTERP mir.c mir-interp.c && ./a.out && size ./a.out
	$(CC) $(CFLAGS) -DNDEBUG -D$(TARGET) -DMIR_SCAN -DTEST_MIR_INTERP2 mir.c mir-interp.c \
	  && ./a.out && size ./a.out

gen-test:
	$(CC) -g -D$(TARGET) -DTEST_MIR_GEN -DMIR_GEN_DEBUG=1 mir.c mir-gen.c && ./a.out
	$(CC) -g -D$(TARGET) -DMIR_SCAN -DTEST_MIR_GEN2 -DMIR_GEN_DEBUG=1 mir.c mir-gen.c && ./a.out

gen-bench:
	$(CC) $(CFLAGS) -DNDEBUG -D$(TARGET) -DTEST_MIR_GEN mir.c mir-gen.c && ./a.out && size ./a.out
	$(CC) $(CFLAGS) -DNDEBUG -D$(TARGET) -DMIR_SCAN -DTEST_MIR_GEN2 mir.c mir-gen.c && ./a.out && size ./a.out

c-test:
	$(CC) -g -D$(TARGET) -DTEST_MIR_C mir-c.c && ./a.out

c-bench:
	$(CC) $(CFLAGS) -DNDEBUG -D$(TARGET) -DTEST_MIR_C mir-c.c && ./a.out && size ./a.out

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
