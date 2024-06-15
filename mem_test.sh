#!/usr/bin/env bash

echo "threads;expr_size;memory" > $1

for len in 10 100 1000 10000 100000; do
    for th in 1 2 3 4 5 6 7 8 10 12 14 16 20 24 28 32; do
        for seed in 1 2 3 4 5; do
            export PE_SEQ=false
            export PE_THREADS=$th
            export PE_LEN=$len
            export PE_SEED=1

            mem=$(/usr/bin/time --format=%M $2 parallel_mem --nocapture 2>&1 | tail -n1)
            echo "$th;$len;$mem" >> $1
        done
    done
done

for len in 10 100 1000 10000 100000; do
    for seed in 1 2 3 4 5; do
        export PE_SEQ=true
        export PE_LEN=$len
        export PE_SEED=$seed

        mem=$(/usr/bin/time --format=%M $2 parallel_mem --nocapture 2>&1 | tail -n1)
        echo "0;$len;$mem" >> $1
    done
done
