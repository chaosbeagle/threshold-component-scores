#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export MATHLIB_CACHE_DIR="${MATHLIB_CACHE_DIR:-$PWD/.cache/mathlib}"
mapfile -t modules < <(grep -h '^import Mathlib' ThresholdComponentScores/*.lean | awk '{print $2}' | sort -u)
lake exe cache get "${modules[@]}"
lake build
lake env lean AxiomAudit.lean

lake env lean KernelAudit.lean
