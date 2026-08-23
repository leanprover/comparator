#!/bin/sh
set -eu

log=$1
shift
test "$1" = "--phase"
phase=$2
shift 2
test "$1" = "--"
shift
printf '%s\n' "$phase" >> "$log"
exec "$@"
