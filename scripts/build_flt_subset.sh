#!/bin/sh
# Builds the part of anthropics/fermats-last-theorem needed for Tate's theorem on
# Hecke characters: 7 root modules, about 325 modules of that project in all.
# Needs: git, elan. Usage: scripts/build_flt_subset.sh [dir]   (default: ./_flt)
# About 9 GB of disk at peak.
set -eu
FLT_COMMIT=6e837e75355538c7f80bab5b956861e86c4eacc2
# Mathlib: the project pins db584cd6, which has no cache for Lean 4.33.1.
# 0df444a3 is the next commit and only changes `lean-toolchain` (4.33.0 to
# 4.33.1): same sources, and a cache exists for it.
MATHLIB_PIN=db584cd6d46c92f209a44c0f1c829460d327499d
MATHLIB_CACHED=0df444a360eaa60ab8c11dca51a86af692955474
WORK="${1:-$(pwd)/_flt}"

if [ ! -d "$WORK/.git" ]; then
  git clone --filter=blob:none --no-checkout https://github.com/anthropics/fermats-last-theorem.git "$WORK"
  cd "$WORK"
  git sparse-checkout init --no-cone
  printf '/*\n!/html/\n' > .git/info/sparse-checkout   # without the web pages (390 MB)
  git checkout "$FLT_COMMIT"
fi
cd "$WORK"
sed -i "s/$MATHLIB_PIN/$MATHLIB_CACHED/g" lakefile.lean lake-manifest.json
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
