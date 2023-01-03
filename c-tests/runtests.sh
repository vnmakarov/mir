#!/bin/sh
# Run runtests.sh execution_program
#

outf=__c-tests-temp.out
errf=__c-tests-temp.err
all=0
ok=0
ctest_dir=`dirname $0`
execution_program=$1
compiler=$2

EGREP=egrep

ECHO=echo
if test x$BASH_VERSION != x;then
  set +o posix
elif test -x /bin/echo;then
  ECHO=/bin/echo
fi

if type timeout >/dev/null 2>&1;then
    TIMEOUT="timeout 30s"
elif type gtimeout >/dev/null 2>&1;then
    TIMEOUT="gtimeout 30s"
else
    TIMEOUT=
fi

runtest () {
	t=$1
	add_main=$2
	all=`expr $all + 1`
	if test -f $t.expectrc; then expect_code=`cat $t.expectrc`; else expect_code=0; fi
	if test -f $t.expect; then expect_out=$t.expect; else expect_out=; fi
	another_expect=`dirname $t`/`basename $t .c`.expect
	if test x$expect_out = x && test -f $another_expect; then expect_out=$another_expect; else expect_out=; fi
	$ECHO -n $t:
	$TIMEOUT $execution_program $compiler $t $add_main 2>$errf >$outf
	code=$?
	if test $code = $expect_code; then
	    if test x$expect_out != x && ! diff --strip-trailing-cr -up $expect_out $outf >$errf;then
	            $ECHO Output mismatch
		    cat $errf
		else
		    ok=`expr $ok + 1`
	            $ECHO -ne "OK               \r"
		fi
	elif test $expect_code = 0; then
	        cat $errf
	        $ECHO FAIL "(code = $code)"
	else
	        cat $errf
		$ECHO $FAIL "(code = $code, expected code = $expect_code)"
	fi
}

for dir in mir
do
	$ECHO ++++++++++++++Running tests in $dir+++++++++++++
	for t in $ctest_dir/$dir/*.mir;do
	    runtest $t
	done
done

for dir in havoc new andrewchambers_c gcc lacc # $8cc avltree helloworld *lcc nano ^netlib %picoc set1 $-but-c2m *-but-l2m/c2m ^-but-l2m-gen %-but-clang-l2m
do
	$ECHO ++++++++++++++Running tests in $dir+++++++++++++
	if test -f $ctest_dir/$dir/main.c;then
	   runtest $ctest_dir/$dir/main.c
	   continue;
	fi
	for t in $ctest_dir/$dir/*.c;do
	    if $ECHO $t|$EGREP '/add-[a-zA-Z0-9]+.c$' >/dev/null; then continue; fi
	    if test -f $ctest_dir/$dir/add-`basename $t`;then add_main=$ctest_dir/$dir/add-`basename $t`
	    elif test -f $ctest_dir/$dir/add-`basename $t .c`.mir;then
		add_main=$ctest_dir/$dir/add-`basename $t .c`.mir
	    else
		add_main=
	    fi
	    runtest $t $add_main
	done
done

$ECHO Tests $all, Success tests $ok
rm -f $outf $errf
