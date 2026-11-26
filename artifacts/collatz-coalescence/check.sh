#!/bin/sh
# Rebuild the Lean development and print the axioms of the headline theorems.
# Usage: sh check.sh        (from this directory; needs elan and the Mathlib cache: `lake exe cache get`)
set -e
cd "$(dirname "$0")"
if grep -n -E '\bsorry\b|^[[:space:]]*axiom\b|native_decide|implemented_by|\bunsafe\b|set_option' CollatzCoalescence/*.lean CollatzCoalescence.lean; then
  echo "FORBIDDEN CONSTRUCT FOUND"; exit 1
fi
lake build
tmp=$(mktemp -d)
cat > "$tmp/Audit.lean" <<'LEAN'
import CollatzCoalescence
open Coalescence
#print Tn
#print Coalescence.Cn
#check @gao_conjecture
#check @coalescence_density_one
#print axioms gao_conjecture
#print axioms coalescence_density_one_log
#print axioms coalescence_density_one
#print axioms offset_classes
#print axioms every_offset_merges
#check @neighbour_merge_rate
#print axioms neighbour_merge_rate
#print axioms survival_lower
#check @unmerged_density_rate
#print axioms unmerged_density_rate
#check @offset_merge_rate
#print axioms offset_merge_rate
LEAN
lake env lean "$tmp/Audit.lean" | tee "$tmp/out.txt"
if grep -q -E 'sorryAx|ofReduceBool' "$tmp/out.txt"; then echo "NON-STANDARD AXIOM"; exit 1; fi
n=$(grep -c 'depends on axioms: \[propext, Classical.choice, Quot.sound\]' "$tmp/out.txt")
[ "$n" = 9 ] && echo "OK: 9 headline theorems, standard axioms only" || { echo "UNEXPECTED AXIOM OUTPUT"; exit 1; }
