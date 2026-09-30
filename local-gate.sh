#!/bin/bash
# Local replication of the Hodge Conjecture Final Integration Gate
cd /home/z/hc-proof
export PATH="$HOME/.elan/bin:$PATH"
echo "=== [1/5] elan install ==="
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain leanprover/lean4:v4.33.0-rc2 2>&1
echo "=== [2/5] lake update ==="
lake update 2>&1 | tail -20
echo "=== [3/5] cache get ==="
lake exe cache get 2>&1 | tail -30
echo "=== [4/5] lake build HodgePureMath ==="
lake build HodgePureMath 2>&1
echo "=== [5/5] lane + landing ==="
lake env lean GSTClassicalHodgeDirectOrbitWordSaturation.lean 2>&1
lake env lean HodgeConjecture.lean 2>&1
echo "=== GATE COMPLETE ==="
