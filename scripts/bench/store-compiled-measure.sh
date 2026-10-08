#!/bin/bash
# run-measure.sh N : every mode x 3 runs; append modes on a fresh copy of the store each run.
cd /srv/lanes/bench-store; ulimit -s unlimited; umask 022
N=$1; B=src/.lake/build/bin/bench-store-compiled; H=data/store-helper
OUT=logs/measure-$N.txt; : > $OUT
for mode in full-open light-open full-append light-append past-image past-full-reader past-light-reader since-image since-full-reader since-light-reader profile-light; do
  for run in 1 2 3; do
    D=data/n$N
    case $mode in *append) rm -rf data/tmp-$N; cp -r data/n$N data/tmp-$N; D=data/tmp-$N;; esac
    echo "### N=$N mode=$mode run=$run" >> $OUT
    MINI_OPEN_TIMING=$([ $mode = light-open ] && [ $run = 1 ] && echo 1 || echo 0) /usr/bin/time -f "WALL_S=%e MAXRSS_KB=%M" $B $H $D $mode >> $OUT 2>&1
    echo "EXIT=$?" >> $OUT
    rm -rf data/tmp-$N
  done
done
echo DONE >> $OUT
