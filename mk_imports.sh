#!/bin/bash
set -e
find GroupComp -name "*.lean" | env LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > GroupComp.lean
