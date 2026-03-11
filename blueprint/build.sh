#!/bin/bash
# Build GIFT blueprint with dark theme customizations.
# Usage: bash blueprint/build.sh
set -eu

cd "$(dirname "$0")/.."

echo "=== Building blueprint ==="
leanblueprint web

echo ""
echo "=== Applying GIFT theme ==="
python3 blueprint/src/postprocess.py

echo ""
echo "Done. Open blueprint/web/dep_graph_document.html"
