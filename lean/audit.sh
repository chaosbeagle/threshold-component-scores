#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
lake env lean AxiomAudit.lean
lake env lean KernelAudit.lean
