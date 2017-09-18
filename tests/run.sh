#!/bin/bash

FLAGS=
TESTPL=test.pl
MAIN=../../main

if [ ! -z "$1" ]; then
  FLAGS=-T
fi

$TESTPL $FLAGS -c $MAIN $1

