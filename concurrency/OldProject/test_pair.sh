#!/bin/bash
for run in {1..2000}; do
  ./pair_conc >> pair.txt
done
