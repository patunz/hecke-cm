# Port to Lean 4.35.0 / Mathlib v4.35.0

The proof in `HeckeCM/` is written and checked with Lean 4.33.1, the version of
`anthropics/fermats-last-theorem` it depends on. This folder contains what is
needed to compile it with Lean 4.35.0 and Mathlib `v4.35.0` (commit `56a00585`)
as well.

| File | What |
|---|---|
| `fermat-435.patch` | changes to 35 files of the Fermat repository (commit `6e837e75`), out of about 330 compiled modules |
| `Compat435.lean` | one compatibility lemma: the previous statement of `WithZeroMulInt.toNNReal_neg_apply` |
| `heckecm-435.patch` | the only changes to our own files: in `CurveModel.lean` the `UIntegral` section is removed, since Mathlib has it at that version; in `Descent/NaiveHeight.lean` one name is written in full, since Mathlib now has a lemma with the same short name |
| `ZInQContrib.lean` | the two premises of `elliotglazer/diophantine-z-q` proved from this library; see below |
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

No theorem statement or definition of the Fermat repository is changed: 78 lines
removed and 97 added, in proofs and imports. The only declarations touched are
two added instances (`Infinite R`, `Ring.HasFiniteQuotients R`) and the body of
one local rank-one instance, now taken from Mathlib.

## Check (2026-11-25)

The recipe was run from scratch on a clean machine, from a fresh clone of this
repository at commit `760e238`: Fermat subset 9,374 jobs, then `HeckeCM` (all 91
files, with `heckecm-435.patch` applied) 9,450 jobs, no errors. Three of the 35
patched Fermat files are not among the seven root modules of the script; they
are built with `HeckeCM`, which imports them.

The patches in this folder were extracted from that machine after the build.
Applied to the published sources they reproduce the compiled files exactly; the
recipe has not been run again from the patches as committed.

## The premises of `diophantine-z-q`

`ZInQContrib.lean` states `ZInQ.Contrib.heckeContinuation` and
`ZInQ.Contrib.functionalEquation5` with the types
`ZInQ.Literature.HeckeContinuation` and `ZInQ.Literature.FunctionalEquation5`
of [`elliotglazer/diophantine-z-q`](https://github.com/elliotglazer/diophantine-z-q),
and proves them from `CMPoints.entire_lseries_curveD_of_ne_zero` and
`CMPoints.functional_equation_strip_five`. It imports that repository's
`ZInQKernel.Hypotheses.CR3Literature` and copies nothing from it.

Checked on 2026-11-25 in the Lean 4.35 build above, with that repository added
as a Lake dependency at commit `964d7dd7`: the file compiles and both theorems
depend on `propext`, `Classical.choice`, `Quot.sound` only. The file is not part
of the `HeckeCM` library and is not built by the scripts. It has not been
submitted to that project, and their CI has not run on it.
