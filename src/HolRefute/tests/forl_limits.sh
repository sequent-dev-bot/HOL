#!/bin/sh
set -eu
if [ -z "${HOL4_KODKODI:-}${HOL4_KODKODI_EXEC:-}" ] ||
   [ ! -x "${MINISAT_HOME:-}/minisat" ]; then
  echo "skipped: Kodkodi file-limit regression needs Kodkodi and external MiniSat"
  exit 0
fi
"$HOLDIR/bin/hol" --gcthreads=1 run forl_limits
scratch=$(mktemp -d)
trap 'rm -f "$scratch/launcher"; rmdir "$scratch"' EXIT HUP INT TERM
cat > "$scratch/launcher" <<'LAUNCHER'
#!/bin/sh
set -eu
cat > /dev/null
first() { printf '*** PROBLEM 1 ***\n---OUTCOME---\nUNSATISFIABLE\n\n'; }
sat() { printf '*** PROBLEM 2 ***\n---OUTCOME---\nSATISFIABLE\n\n'; }
pad() {
  bytes=$1
  {
    dd if=/dev/zero bs=65536 count=$((bytes / 65536)) 2>/dev/null
    if [ $((bytes % 65536)) -gt 0 ]; then
      dd if=/dev/zero bs=$((bytes % 65536)) count=1 2>/dev/null
    fi
  } | tr '\000' ' '
}
first
if [ "$FORL_LIMIT_CASE" = stdout ]; then
  pad 16777216
  printf '*** PROBLEM 2 ***\n---OUTCOME---\nUNSATISFIABLE\n\n'
elif [ "$FORL_LIMIT_CASE" = stdout_marker ]; then
  # The 16 MiB prefix ends in ---INST of a later satisfiable problem.
  pad $((16777216 - $(first | wc -c) - $(sat | wc -c) - 7))
  sat
  printf '%s\n' '---INSTANCE---' 'relations:{}' ''
else
  dd if=/dev/zero bs=65536 count=256 2>/dev/null | tr '\000' ' ' >&2
  printf 'AFTER_LIMIT\n' >&2
fi
LAUNCHER
chmod +x "$scratch/launcher"
for mode in stdout stdout_marker stderr; do
  FORL_LIMIT_CASE="$mode" HOL4_KODKODI_EXEC="$scratch/launcher" \
    "$HOLDIR/bin/hol" --gcthreads=1 run forl_limits
done
