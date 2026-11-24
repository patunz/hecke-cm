#!/bin/sh
# Builds the part of anthropics/fermats-last-theorem that is needed (Lean 4.33.1),
# then this library on top of it.
# Needs: git, elan. Usage: scripts/build.sh [workdir]   (default: ./_flt)
set -eu
HERE="$(cd "$(dirname "$0")/.." && pwd)"
WORK="${1:-$(pwd)/_flt}"
sh "$HERE/scripts/build_flt_subset.sh" "$WORK"
cd "$WORK"
rm -rf HeckeCM
cp -r "$HERE/HeckeCM" HeckeCM
grep -q 'lean_lib HeckeCM' lakefile.lean || printf '\nlean_lib HeckeCM where\n  globs := #[.submodules `HeckeCM]\n' >> lakefile.lean
lake build HeckeCM
cat > AxiomCheck.lean <<'EOF'
import HeckeCM.BsdInstances
import HeckeCM.FunctionalEqStrip
import HeckeCM.BsdFive
#print axioms CMPoints.entire_lseries_curveD_of_ne_zero
#print axioms CMPoints.functional_equation_curveD_odd
#print axioms CMPoints.functional_equation_curveD_two_mul
#print axioms CMPoints.vanishing_curveD_all
#print axioms CMPoints.functional_equation_strip_five
#print axioms CMPoints.not_isOfFinAddOrder_of_ne_zero
#print axioms CMPoints.exists_not_isOfFinAddOrder_iff_isCongruent
#print axioms CMPoints.vanishing_and_rank
#print axioms CMPoints.positiveRanks_five
#print axioms CMPoints.positiveRanks_six
#print axioms CMPoints.positiveRanks_seven
#print axioms CMPoints.thetaCurve_inversion
#print axioms CMPoints.deriv_ne_zero_curve_five
#print axioms BSD.exists_generator_curve_five
#print axioms CMPoints.ranks_curve_five
EOF
lake env lean AxiomCheck.lean
