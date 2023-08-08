#!/bin/bash

set -eo pipefail

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$SCRIPT_DIR"

sbt assembly

for f in tests/*.truth ; do
  java -cp electronics.jar mccluskey.Main "$f" > "${f%.*}.minsums"
done
