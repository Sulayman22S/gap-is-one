#!/usr/bin/env bash
# Build paper.pdf from paper.tex.
#
# Uses Tectonic (https://tectonic-typesetting.github.io): the program named by the variable
# TECTONIC, or `tectonic` on PATH, or a copy unpacked in ../../tools/tectonic.
# Any LaTeX distribution works as well:  pdflatex paper.tex  (twice).
set -u
cd "$(dirname "$0")"
local_tools=../../tools
if [ -z "${TECTONIC:-}" ]; then
  if command -v tectonic > /dev/null 2>&1; then
    TECTONIC=tectonic
  elif [ -x "$local_tools/tectonic/tectonic.exe" ]; then
    TECTONIC="$local_tools/tectonic/tectonic.exe"
    # keep the TeX packages Tectonic downloads next to it
    if [ -z "${TECTONIC_CACHE_DIR:-}" ] && [ -d "$local_tools/tectonic-cache" ]; then
      cache="$(cd "$local_tools/tectonic-cache" && pwd)"
      if command -v cygpath > /dev/null 2>&1; then cache="$(cygpath -w "$cache")"; fi
      export TECTONIC_CACHE_DIR="$cache"
    fi
  else
    echo "Tectonic not found: install it, or run  pdflatex paper.tex  twice" >&2
    exit 1
  fi
fi
"$TECTONIC" --keep-logs paper.tex 2>&1 | grep -v "^note: downloading" | grep -v "Fontconfig error"
status=${PIPESTATUS[0]}
echo "tectonic status: $status"
echo "overfull boxes: $(grep -c Overfull paper.log 2>/dev/null; true)"
echo "undefined references: $(grep -c 'undefined' paper.log 2>/dev/null; true)"
rm -f paper.aux paper.out paper.log
exit $status
