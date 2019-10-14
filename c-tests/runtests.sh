#!/bin/sh
# Run runtests.sh execution_program
#

outf=c-tests/__temp.out
errf=c-tests/__temp.err
all=0
ok=0
execution_program=$1

runtest () {
	t=$1
	add_main=$2
	all=`expr $all + 1`
	if test -f $t.expectrc; then expect_code=`cat $t.expectrc`; else expect_code=0; fi
	if test -f $t.expect; then expect_out=$t.expect; else expect_out=; fi
	another_expect=`dirname $t`/`basename $t .c`.expect
	if test x$expect_out = x && test -f $another_expect; then expect_out=$another_expect; else expect_out=; fi
	echo -n $t:
	timeout 30s $execution_program $t $add_main 2>$errf >$outf
	code=$?
	if test $code = $expect_code; then
	    if test x$expect_out != x && ! cmp $outf $expect_out;then
	            echo Output mismatch
		    diff -up $expect_out $outf
		else
		    ok=`expr $ok + 1`
	            echo -ne "OK\r"
		fi
	elif test $expect_code = 0; then
	        cat $errf
	        echo FAIL "(code = $code)"
	else
	        cat $errf
		echo $FAIL "(code = $code, expected code = $expect_code)"
	fi
}

for dir in andrewchambers_c gcc lacc # $8cc avltree helloworld *lcc nano ^netlib %picoc set1 $-but-c2m *-but-l2m/c2m ^-but-l2m-gen %-but-clang-l2m
do
	echo ++++++++++++++Running tests in $dir+++++++++++++
	if test -f c-tests/$dir/main.c;then
	   runtest c-tests/$dir/main.c
	   continue;
	fi
	if test -f c-tests/$dir/add-main.c;then add_main=c-tests/$dir/add-main.c;else add_main=;fi
	for t in c-tests/$dir/*.c;do
	    if test x$t = x$add_main;then continue;fi
	    runtest $t $add_main
	done
done

echo Tests $all, Success tests $ok
rm -f $outf $errf
