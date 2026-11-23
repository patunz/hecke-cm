#!/bin/sh
# Like build_flt_subset.sh, but with Lean 4.35.0 and Mathlib v4.35.0: applies the
# patch in port-435/ to the Fermat repository and builds the same 7 root modules.
# Needs: git, elan. Usage: scripts/build_flt_subset_435.sh [dir]   (default: ./_flt35)
# After the build: copy HeckeCM/ into the directory, apply port-435/heckecm-435.patch
# and add `lean_lib HeckeCM where globs := #[.submodules `HeckeCM]` to the lakefile.
set -eu
FLT_COMMIT=6e837e75355538c7f80bab5b956861e86c4eacc2
MATHLIB_PIN=db584cd6d46c92f209a44c0f1c829460d327499d
PORT="${PORT_DIR:-$(cd "$(dirname "$0")/.." && pwd)/port-435}"
WORK="${1:-$(pwd)/_flt35}"

if [ ! -d "$WORK/.git" ]; then
  git clone --filter=blob:none --no-checkout https://github.com/anthropics/fermats-last-theorem.git "$WORK"
  cd "$WORK"
  git sparse-checkout init --no-cone
  printf '/*\n!/html/\n' > .git/info/sparse-checkout
  git checkout "$FLT_COMMIT"
fi
cd "$WORK"
echo "leanprover/lean4:v4.35.0" > lean-toolchain
sed -i "s/$MATHLIB_PIN/v4.35.0/g" lakefile.lean
rm -f lake-manifest.json
git apply "$PORT/fermat-435.patch"
cp "$PORT/Compat435.lean" Definitions/Compat435.lean
# Mathlib v4.35.0 has fewer transitive imports: every file imports all of Mathlib.
find Definitions Theorems P2M -name '*.lean' | while read -r f; do
  grep -q '^import Mathlib$' "$f" || sed -i '0,/^import /s//import Mathlib\nimport /' "$f"
done
lake update
lake exe cache get
P=Theorems.Thm
lake build \
  ${P}_NumberField_TateGlobal_exists_entire_zetaIntegral_eq_mul_prod_Gamma_mul_eulerProduct_and_one_sub_eq_root_mul_cpow_of_archLocalChar_eq \
  ${P}_NumberField_TateGlobal_differentiableOn_tprod_eulerFactor_of_norm_le_rpow \
  ${P}_NumberField_TateGlobal_exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar \
  ${P}_HeckeCharacter_eq_of_forall_apply_localUnit_uniformizerUnit_eq \
  ${P}_ArtinL_Abelian_hasProd_primes_inv_eval_prod_placesOver \
  ${P}_DirichletCharacter_isFiniteOrderHeckeChar_dirichletIdeleChar \
  ${P}_DirichletCharacter_admitsModulus_dirichletIdeleChar
