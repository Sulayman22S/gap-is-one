#!/usr/bin/env bash
# Build the project one module at a time, then run the audit.
#
# Plain `lake build` compiles independent modules in parallel, and every Lean process loads all
# of Mathlib (several GB). On a machine that is short of free memory that fails with
# "failed to read file ... .olean". Building sequentially avoids it.
#
# Usage:   bash build.sh          (add `clean` to rebuild from scratch)
#
# `lake` must be on PATH. If it is not, the script reads a file that puts it there: the one
# named by the variable CONJ2_LEAN_ENV, or `lean-env.sh` in the folder above this one.
set -u
cd "$(dirname "$0")"
if ! command -v lake > /dev/null 2>&1; then
  env_file="${CONJ2_LEAN_ENV:-../lean-env.sh}"
  if [ -f "$env_file" ]; then source "$env_file"; fi
fi
if ! command -v lake > /dev/null 2>&1; then
  echo "lake not found: install Lean (https://lean-lang.org) or set CONJ2_LEAN_ENV" >&2
  exit 1
fi
if [ "${1:-}" = "clean" ]; then rm -rf .lake/build; fi
status=0
# Challenge and Solution are the two modules that `lake comparator` judges (comparator.json).
for m in Conj2.Rayleigh Conj2.Graph Conj2.PathLemmas Conj2.SharpLemmas Conj2.Main Conj2.Family Conj2.Transfer Conj2.Sharp Conj2.BestConstant Conj2 Challenge Solution; do
  if lake build "$m" > .build-step.log 2>&1; then
    echo "built  $m"
  else
    echo "FAILED $m"
    grep -v "designed for use with the module system" .build-step.log | tail -30
    status=1
    break
  fi
done
rm -f .build-step.log
echo "build status: $status"
if [ "$status" = 0 ]; then
  echo "=== audit (lake env lean Check.lean) ==="
  lake env lean Check.lean
  echo "audit status: $?"
  echo "=== placeholders (sorry / admit / native_decide) ==="
  # Challenge.lean is not counted: it states the theorems and leaves each one as `sorry` on purpose.
  grep -c "sorry\|admit\|native_decide" Conj2/*.lean Solution.lean
fi
exit $status
