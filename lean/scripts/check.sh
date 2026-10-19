#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
lake build
lake env lean Audit.lean
python3 ../tools/check_lean_map.py
