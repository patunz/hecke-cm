# Port to Lean 4.35.0 / Mathlib v4.35.0

The proof in `HeckeCM/` is written and checked with Lean 4.33.1, the version of
`anthropics/fermats-last-theorem` it depends on. This folder contains what is
needed to compile it with Lean 4.35.0 and Mathlib `v4.35.0` (commit `56a00585`)
as well.

| File | What |
|---|---|
| `fermat-435.patch` | changes to 32 files of the Fermat repository (commit `6e837e75`), out of about 330 compiled modules |
| `Compat435.lean` | one compatibility lemma: the previous statement of `WithZeroMulInt.toNNReal_neg_apply` |
| `heckecm-435.patch` | the only change to our own files: in `CurveModel.lean` the `UIntegral` section is removed, since Mathlib has it at that version |
| `../scripts/build_flt_subset_435.sh` | the recipe: clone, apply the patch, add `import Mathlib` to every file, build |

## What changed between the two Mathlib versions

- fewer transitive imports: every Fermat file now imports all of Mathlib;
- induction on tensor products no longer has a `zero` case
  (`TensorProduct.inductionOn`);
- the rank-one structure on completions needs `Ring.HasFiniteQuotients` and
  `Infinite`: two instances added in `Def_NumberField_AdelicHaar.lean`;
- `WithZeroMulInt.toNNReal_neg_apply` is now stated with `WithZero.log`;
- renames: `continuous_add_right` → `continuous_add_const` and the like,
  `Finset.prod_le_prod` → `prod_le_prod₀`, `finprod_le_finprod` → `…₀`,
  `measurable_pi_lambda` without its first argument;
- `exists_subset_nhds_of_isCompact'` takes its hypothesis with `𝓝ˢ`;
- a few instances have to be named by hand (`BorelSpace`, dot notation on
  `QuasiMeasurePreserving.mono_left`).

No theorem statement or definition of the Fermat repository is changed: 68 lines
removed and 90 added, in proofs and imports. The only declarations touched are
two added instances (`Infinite R`, `Ring.HasFiniteQuotients R`) and the body of
one local rank-one instance, now taken from Mathlib.

## Check (2026-11-23)

The recipe was run from scratch on a clean machine: Fermat subset 9,374 jobs,
then `HeckeCM` (the 66 files present at the time, with `heckecm-435.patch`
applied) 9,415 jobs, no errors. The files added after that (`FunctionalEqStrip`,
the theta and rank files, `Descent/`) have not been compiled with Lean 4.35.
