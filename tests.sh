#!/bin/bash

set -eo pipefail

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$SCRIPT_DIR"

sbt assembly

for f in tests/timer.truth ; do
    echo "TESTING $f"
    java -cp electronics.jar mccluskey.Main "$f" > "${f%.*}.minsums.json"
    netlist="${f%.*}.netlist"
    java -cp electronics.jar logic.Main "$f" > "$netlist"
    tmp="${f%.*}.tmp"
    netlistsvg "$netlist" -o "$tmp"
    xmllint --format "$tmp" > "${f%.*}.svg"
    rm "$tmp"
done
