#!/usr/bin/env bash
set -euo pipefail

lake build
lake env lean NBMellinTools/Audit.lean

