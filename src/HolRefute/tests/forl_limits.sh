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
printf '*** PROBLEM 1 ***\n---OUTCOME---\nUNSATISFIABLE\n\n'
if [ "$FORL_LIMIT_CASE" = stdout ]; then
  dd if=/dev/zero bs=65536 count=256 2>/dev/null | tr '\000' ' '
  printf '*** PROBLEM 2 ***\n---OUTCOME---\nUNSATISFIABLE\n\n'
else
  dd if=/dev/zero bs=65536 count=256 2>/dev/null | tr '\000' ' ' >&2
  printf 'AFTER_LIMIT\n' >&2
fi
LAUNCHER
chmod +x "$scratch/launcher"
for mode in stdout stderr; do
  FORL_LIMIT_CASE="$mode" HOL4_KODKODI_EXEC="$scratch/launcher" \
    "$HOLDIR/bin/hol" --gcthreads=1 run forl_limits
done
