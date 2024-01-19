#!/usr/bin/env zsh

set -e

echo lib,trial,n,threads,us_per_n,cpu_time,real_time
for lib in flint-feea ntl-feea ntl-interp
do
  for trial in $(seq 0 2)
  do
    for n in $(seq 10 14)
    do
      for threads in 1 2 4 8 16
      do
        /usr/bin/time -v ./xgcd $lib $n $threads &> temp.out
        us_per_n=$(cat temp.out | rg 'total *time .*= ([0-9.]+)$' -o -r '$1')
        cpu_time=$(cat temp.out | rg 'User time' | rg '([0-9.]+)' -o)
        real_time=$(cat temp.out | rg 'Elapsed' | rg ':([1-9][0-9]?.[0-9][0-9])' -o -r '$1')
        echo $lib,$trial,$n,$threads,$us_per_n,$cpu_time,$real_time
      done
    done
  done
done
rm -rf temp.out
