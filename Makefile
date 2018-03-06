CC=gcc
CFLAGS=-Ofast -g
TARGET=x86_64
DEPS=mir.h mir-varr.h mir-dlist.h
OBJS=mir.o mir-interp.o mir-gen.o
all: $(OBJS)

mir.o: mir.c $(DEPS)
	$(CC) -c $(CFLAGS) -o $@ $<
mir-interp.o: mir-interp.c $(DEPS) mir-interp.h
	$(CC) -c $(CFLAGS) -o $@ $<
mir-gen.o: mir-gen.c $(DEPS) mir-bitmap.h $(TARGET)-target.c
	$(CC) -c $(CFLAGS) -D$(TARGET) -o $@ $<

gen-bench:
	$(CC) $(CFLAGS) -D$(TARGET) -DTEST_MIR_GEN mir.c mir-gen.c && ./a.out

interp-test:
	$(CC) -g -D$(TARGET) -DTEST_MIR_INTERP -DMIR_INTERP_DEBUG=1 mir.c mir-interp.c && ./a.out

interp-bench:
	$(CC) $(CFLAGS) -D$(TARGET) -DTEST_MIR_INTERP mir.c mir-interp.c && ./a.out

gen-test:
	$(CC) -g -D$(TARGET) -DTEST_MIR_GEN -DMIR_GEN_DEBUG=1 mir.c mir-gen.c && ./a.out

clean:
	rm -f $(OBJS) ./a.out

realclean: clean
