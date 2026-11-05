#!/usr/bin/env bash
# Prints the public API of Inkproof.Core, one line per declaration; CI compares it with API.lock.
# Regenerate with: scripts/api-lock.sh > API.lock
set -euo pipefail
cd "$(dirname "$0")/.."
lake build InkproofCore >&2
lake exe api-lock Inkproof.Core
