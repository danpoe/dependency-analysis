#!/bin/bash

set -e

rm -f *.log

for f in *
do
  if [ -d "$f" ]; then
    cd $f
    rm -f *.out
    cd ..
  fi
done
