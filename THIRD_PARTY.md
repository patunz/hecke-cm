# Third-party code

Four files in `HeckeCM/` contain code copied, with modifications, from three
projects released under the Apache License 2.0. The licence text is in
[`LICENSE`](LICENSE) (the same text is also at `LICENSE-APACHE-2.0`, the name
the file headers refer to). None of them ships a `NOTICE` file (checked on
2026-11-23).

| File | Origin | Commit | What |
|---|---|---|---|
| `HeckeCM/CurveModel.lean` | Mathlib, `Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean` | `31ce06ea` | the `UIntegral` section |
| `HeckeCM/CurveModel.lean` | Tau Ceti (`TauCetiProject/TauCeti`), `TauCeti/AlgebraicGeometry/EllipticCurve/`: `Affine/Formula/VariableChange.lean`, `PointCount.lean`, `IntegralModel.lean`, `MinimalModel/Basic.lean`, `CurveX3SubX.lean` | `b608709b` | the rest of the file |
| `HeckeCM/JacobiQuartic.lean` | Tau Ceti, `TauCeti/NumberTheory/JacobiSum/Quartic.lean`, `NumberTheory/NumberField/Cyclotomic/Four/Basic.lean`, `NumberTheory/MulChar/Basic.lean` | `b608709b` | the three main theorems and their helper lemmas |
| `HeckeCM/CurveLSeries.lean` | Tau Ceti, `TauCeti/AlgebraicGeometry/EllipticCurve/LFunction/Basic.lean` | `b608709b` | the two theorems `isMultiplicative_localEulerFactor` and `isMultiplicative_LFunction` |
| `HeckeCM/Places.lean` | `anthropics/fermats-last-theorem`, `P2M/Sol/S_ArtinL_Abelian_hasProd_primes_inv_eval_prod_placesOver.lean` | `6e837e75` | the lemmas `charOf`, `charOf_prime`, `natCast_mem_iff`, `under`, `under_eq_iff`, `liesOver_of_mem`, `finite_fibre` (private there) |

Original copyright notices, reproduced at the top of those files:

* Mathlib, `Reduction.lean`: "Copyright (c) 2025 Bryan Wang. All rights
  reserved. Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Bryan Wang".
* Tau Ceti, all the files listed: "Copyright (c) 2026 The Tau Ceti
  contributors. All rights reserved. Released under Apache 2.0 license as
  described in the file LICENSE. Authors: The Tau Ceti contributors".
* Fermat repository: "Copyright 2026 Anthropic, PBC", Apache License 2.0, as stated
  in the docstring of `Places.lean`.

Changes made to the originals: ported to Lean 4.33.1 and Mathlib `0df444a3`;
module-system keywords removed (`module`, `public`, `@[expose]`); names adapted
where Mathlib changed; several files merged into one; the curve lives in the
namespace `CMPoints.CurveX3SubX` instead of `TauCeti.CurveX3SubX`.

## Patch to third-party code

`port-435/fermat-435.patch` modifies 32 files of
`anthropics/fermats-last-theorem` (Apache 2.0, commit `6e837e75`) so that they
compile with Lean 4.35.0. It therefore contains context lines and modified
lines of that code. The changes are described in `port-435/README.md`.

## Dependencies that are not copied

`anthropics/fermats-last-theorem` (Apache 2.0) and Mathlib are dependencies
downloaded by the build scripts. Their code is not in this repository.
