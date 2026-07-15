#!/usr/bin/env bash
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

lake build
lake env lean mathlib/NBMellinTools/Audit.lean
