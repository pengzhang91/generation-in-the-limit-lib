#!/usr/bin/env bash
set -euo pipefail

script_directory="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repository_root="$(cd "${script_directory}/.." && pwd)"

cd "${repository_root}/GenLimitLean"

echo "==> Checking every registry-linked Lean declaration"
lake env lean RegistryAudit.lean

echo "==> Running curated logical-dependency regression probes"
lake env lean Audit.lean

echo "==> Lean machine-audit checks passed"
