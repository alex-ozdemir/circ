#!/usr/bin/env zsh

set -e

echo lib,trial,n,threads,s_xgcd,us_per_n_interp,cpu_time
for lib in flint ntl
do
  for trial in $(seq 0 2)
  do
    for n in $(seq 10 14)
    do
      for threads in 1 2 4 8
      do
        /usr/bin/time -v ./xgcd-$lib $n $threads &> temp.out
        s_xgcd=$(cat temp.out | rg 'XGCD *time = ([0-9.]+)s' -o -r '$1')
        us_per_n_interp=$(cat temp.out | rg 'interp time' | rg '([0-9.]+)' -o)
        cpu_time=$(cat temp.out | rg 'User time' | rg '([0-9.]+)' -o)
        echo $lib,$trial,$n,$threads,$s_xgcd,$us_per_n_interp,$cpu_time
      done
    done
  done
done
rm -rf temp.out
