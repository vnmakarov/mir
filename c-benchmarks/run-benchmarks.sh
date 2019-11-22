#!/bin/sh
# Run run-benchmarks.sh
#

CC=gcc
temp=c-benchmarks/__temp.out
temp2=c-benchmarks/__temp2.out
errf=c-benchmarks/__temp.err

if test x`echo -n` != "x-n";then NECHO="echo -n"; else NECHO=printf; fi

percent () {
  echo `awk "BEGIN {if ($2==0) print \"Inf\"; else printf \"%.2fx\n\", $1/$2;}"`
}

print_time() {
    title="$1"
    secs=$2
    if test "x$NECHO" = x; then
	echo $title:
	echo "   " $secs
    else
	n=$title:
	$NECHO "$n"
	l=${#n}
	while test $l -le 40; do $NECHO " "; l=`expr $l + 1`; done
	$NECHO "$secs"
	l=${#secs}
	while test $l -le 10; do $NECHO " "; l=`expr $l + 1`; done
        echo " " `percent $base_time $secs`
    fi
}

run () {
  title=$1
  preparation=$2
  program=$3
  expect_out=$4
  inputf=$5
  flag=$6
  ok=
  if test x"$preparation" != x; then
    $preparation 2>$errf
    if test $? != 0; then echo "$2": FAIL; cat $errf; return 1; fi
  fi
  if test x$inputf == x; then inputf=/dev/null;fi
  if (time -p $program < $inputf) >$temp 2>$temp2; then ok=y;fi
  if test x$ok == x;then echo $program: FAILED; return 1; fi
  if test x$expect_out != x && ! cmp $expect_out $temp; then
    echo Unexpected output:
    diff -up $expect_out $temp
    return 1
  fi
  secs=`egrep 'user[ 	]*[0-9]' $temp2 | sed s/.*user// | sed s/\\t//`
  if test x$flag != x;then base_time=$secs;fi
  print_time "$title" $secs
}

runbench () {
  bench=$1
  arg=$2
  base_time=0.01
  inputf=
  if test -f $bench.expect; then expect_out=$bench.expect; else expect_out=; fi
  run "$CC -O2" "$CC -O2 -Ic-benchmarks -I. $bench.c -lm" "./a.out $arg" "$expect_out" "$inputf" first
  if type clang >/dev/null 2>&1; then
     run "clang -O2" "clang -O2 -Ic-benchmarks -I. $bench.c -lm" "./a.out $arg" "$expect_out" "$inputf"
  fi
#  run "$CC -O0" "$CC -O0 -Ic-benchmarks -I. $bench.c -lm" "./a.out $arg" "$expect_out" "$inputf"
  run "c2m -eg" "" "./c2m -Ic-benchmarks -I. $bench.c -eg $arg" "$expect_out" "$inputf"
}

for bench in array binary-trees except funnkuch-reduce hash hash2 heapsort lists matrix method-call mandelbrot nbody sieve spectral-norm strcat  # ackermann fib random 
do
    b=c-benchmarks/$bench
    if test -f $b.arg; then arg=`cat $b.arg`; else arg=; fi
    echo "+++++ $bench $arg +++++"
    runbench $b $arg
done

rm -f $temp $temp2 $errf
