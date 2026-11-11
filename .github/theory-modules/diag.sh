#!/bin/bash
# diag.sh <hol dir>: what configure sees, and the theory_modules test log.
d=$(cd "$1" && pwd)
here=$(cd "$(dirname "$0")" && pwd)
echo "== diagnostics for $d"
[ -x "$d/bin/hol" ] && (cd "$d" && bin/hol run --noconfig "$here/diag.sml")
find "$d" -name theory-modules-selftest.log -path '*theory_modules*' |
  while read -r f; do echo "== $f"; tail -40 "$f"; done
true
