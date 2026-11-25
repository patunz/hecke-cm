# The L-function of `y² = x³ − d²x`: continuation, functional equation, and vanishing at `s = 1`

A Lean 4 proof, downstream of the Hecke-character part of
[`anthropics/fermats-last-theorem`](https://github.com/anthropics/fermats-last-theorem), that
Mathlib's L-series of the congruent-number curves `C_d : y² = x³ − d²x` over `ℚ` has an entire
continuation satisfying a functional equation with an explicit sign and conductor, and that it
vanishes at `s = 1` when `d ≡ 5, 6, 7 (mod 8)` is squarefree. On the algebraic side: the torsion of
`C_d(ℚ)` is its 2-torsion, so `C_d` has a rational point of infinite order exactly when `d` is a
congruent number. For `C_5 : y² = x³ − 25x` both ranks are proved to be one: `C_5(ℚ)` is
`ℤ P ⊕ (2-torsion)`, and the L-series vanishes to order exactly one at `s = 1`.

```lean
theorem CMPoints.ranks_curve_five :
    (∃ P : (⟨0, 0, 0, -((5 : ℕ) : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ).toAffine.Point,
      ¬ IsOfFinAddOrder P ∧ ∀ Q, ∃ m : ℤ, ∃ T, 2 • T = 0 ∧ Q = m • P + T) ∧
    (∃ F : ℂ → ℂ, CMPoints.IsEntireContinuation ⟨0, 0, 0, -((5 : ℕ) : ℚ) ^ 2, 0⟩ F) ∧
    ∀ F : ℂ → ℂ, CMPoints.IsEntireContinuation ⟨0, 0, 0, -((5 : ℕ) : ℚ) ^ 2, 0⟩ F →
      analyticOrderAt F 1 = 1

theorem CMPoints.entire_lseries_curveD_of_ne_zero {d : ℕ} (hd : d ≠ 0) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ s : ℂ, 3 / 2 < s.re →
      F s = (⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ).LSeries s

theorem CMPoints.functional_equation_curveD_odd {d : ℕ} (hodd : d % 2 = 1) (hsq : Squarefree d) :
    ∃ F Λ : ℂ → ℂ, Differentiable ℂ F ∧ Differentiable ℂ Λ ∧
      (∀ s : ℂ, 3 / 2 < s.re →
        F s = (⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ).LSeries s) ∧
      (∀ s : ℂ, F s = (Complex.Gammaℂ s)⁻¹ * Λ s) ∧
      (∀ s : ℂ, Λ s = ((ZMod.χ₈ (d : ZMod 8) * ZMod.χ₄ (d : ZMod 4) : ℤ) : ℂ) *
        (32 * (d : ℂ) ^ 2) ^ (1 - s) * Λ (2 - s))

theorem CMPoints.vanishing_curveD_all {d : ℕ} (hsq : Squarefree d)
    (h8 : d % 8 = 5 ∨ d % 8 = 6 ∨ d % 8 = 7) (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hFval : ∀ s : ℂ, 3 / 2 < s.re →
      F s = (⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ).LSeries s) :
    F 1 = 0

theorem CMPoints.not_isOfFinAddOrder_of_ne_zero {d : ℕ} (hd4 : ¬ 4 ∣ d) {x y : ℚ}
    (h : (congCurve d).Nonsingular x y) (hy : y ≠ 0) :
    ¬ IsOfFinAddOrder (Point.some x y h : (congCurve d).Point)

theorem CMPoints.vanishing_and_rank {d : ℕ} (hsq : Squarefree d)
    (h8 : d % 8 = 5 ∨ d % 8 = 6 ∨ d % 8 = 7) :
    (∀ F : ℂ → ℂ,
        IsEntireContinuation (⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ) F → F 1 = 0) ∧
      ((∃ P : (congCurve d).Point, ¬ IsOfFinAddOrder P) ↔ IsCongruent d)
```

Here `congCurve d` is the same curve in affine form, `IsEntireContinuation E F` means "`F` is
entire and equals `E.LSeries` for `Re s > 3/2`", and

```lean
def CMPoints.IsCongruent (d : ℕ) : Prop :=
  ∃ a b c : ℚ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ a * b / 2 = d
```

No `sorry`, no `native_decide`; `#print axioms` on these theorems gives
`[propext, Classical.choice, Quot.sound]`.

## What is proved

| Statement | Scope |
|---|---|
| Entire continuation of the L-series | every `d ≠ 0` |
| Functional equation `Λ(s) = w · N^{1−s} · Λ(2−s)`, `Λ = Γ_ℂ · L` | `d` squarefree, and `d·m²` with the sign and conductor of `d` |
| Sign and conductor, `d` odd | `w = χ₈(d)·χ₄(d) = (−2/d)`, `N = 32 d²` |
| Sign and conductor, `d = 2e`, `e` odd | `w = χ₄(e)`, `N = 64 e² = 16 d²` |
| `d = 1` | `Λ(s) = 32^{1−s} Λ(2−s)` |
| Classical form `Λ*(s) = N^{s/2}(2π)^{−s}Γ(s)F(s)`, `Λ*(s) = w·Λ*(2−s)`, for every entire continuation `F` and `0 < Re s < 2` | `d` odd squarefree; `w = −1` for `d ≡ 5 (mod 8)` |
| Vanishing at `s = 1` of every entire continuation | `d ≡ 5, 6, 7 (mod 8)` squarefree, and `d·m²` |
| Every rational point with `y ≠ 0` has infinite order; a point is torsion iff `2P = 0` | `4 ∤ d` (in particular `d` squarefree) |
| A point of infinite order exists iff `d` is a congruent number | `4 ∤ d` |
| A point of infinite order, together with the vanishing (`PositiveRanks d`) | `d = 5, 6, 7`, from the points `(−4, 6)`, `(−3, 9)`, `(25, 120)` |
| Theta relation `θ(y) = w·N⁻¹·y⁻²·θ(1/(Ny))` for `θ(y) = Σ aₙ e^{−2πny}`, `N = 32d²` | `d` odd squarefree |
| `L(C_d, 1) = 0` and `L'(C_d, 1) = 4π·∫_A^∞ log(t/A) θ(t) dt`, `A = 1/√N` | `d = 5` (the formula is proved in general for sign `−1`, stated for `d = 5`) |
| `L'(C_5, 1) ≠ 0`: order of vanishing exactly one | `d = 5` |
| `2.22 < L'(C_5, 1) < 2.23` (`deriv_curve_five_bounds`) | `d = 5` |
| `C_5(ℚ) = ℤ P ⊕ C_5(ℚ)[2]` for a point `P` of infinite order | `d = 5` |

## Status and caveats

- **For `C_5` the rank part of BSD is proved, and nothing more of it.** Algebraic rank one and
  analytic rank one. The formula for the leading coefficient (regulator, period, Ш) is not
  addressed, `L'(C_5, 1)` is only located in the interval `(2.22, 2.23)`, and the
  generator `P` is not exhibited: the statement is an existence statement. For `d = 6, 7` only a
  point of infinite order and the vanishing of `L` at `s = 1` are proved.
- **`L'(1) ≠ 0` is proved for `d = 5` only.** The reduction to an integral is general; the
  numerical step uses `a₁ = 1`, `a₂ = … = a₈ = 0` and `|aₙ| ≤ (7/6)n`, and has to be redone for
  another `d`. The numerical margin is `0.0186 < 0.0276`.
- **Positive rank is not proved for general `d ≡ 5, 6, 7 (mod 8)`.** That is the open half of the
  congruent number problem, known only assuming BSD. What is proved is the reduction: for such
  `d`, positive rank is equivalent to `d` being a congruent number. Outside `d = 5`, "rank" is used
  informally for "there is a point of infinite order".
- **Pinned** to `anthropics/fermats-last-theorem` commit `6e837e75` (Lean `v4.33.1`, Mathlib
  `0df444a3`). Tate's thesis for Hecke characters and the local root-number theorems come from
  there; this repository builds the Hecke character of `ℚ(i)`, identifies its L-function with
  Mathlib's, and computes the local root numbers.
- **Lean 4.35.** `port-435/` contains a patch that makes the Fermat subset and this library compile
  with Lean `v4.35.0` / Mathlib `v4.35.0`; see [`port-435/README.md`](port-435/README.md).
  The files added after 23 November 2026 (`FunctionalEqStrip`, the theta and rank files,
  `Descent/`) have not been compiled there.
- **Third-party code.** About 630 lines in four files are copied, with changes, from Mathlib, Tau
  Ceti and the Fermat repository (all Apache 2.0), and `port-435/fermat-435.patch` is a patch to
  the Fermat repository. See [`THIRD_PARTY.md`](THIRD_PARTY.md).
- **Not Mathlib style.** The files do not use the module system, most of them `import Mathlib`
  wholesale, and the comments were translated from Italian. A few Lean identifiers and section
  names are still Italian words.
- **Verification.** On 24 November 2026 the whole library was built on a clean machine on top of
  the Fermat subset (9,102 jobs; 9,108 on 25 November with the six files on the value of
  `L'(C_5, 1)`), with `#print axioms` on the main theorems; the sources contain
  none of `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `implemented_by`. `scripts/build.sh`
  was last run end to end, from a fresh clone of this repository, on the version of 24 November
  (9,102 jobs), not on the current one. All runs were the
  author's; an independent rebuild is welcome.
- **AI assistance.** The Lean code was written with Claude (Anthropic).

## Relation to other work

Checked on 22–24 November 2026; I may have missed something.

- I did not find these statements proved in Mathlib, in Tau Ceti, in the Fermat repository, or in
  `formal-conjectures`. Tau Ceti has Grössencharakter L-functions whose continuation is defined
  "if it exists".
- [`elliotglazer/diophantine-z-q`](https://github.com/elliotglazer/diophantine-z-q) states three
  hypotheses about these curves, `ZInQ.Literature.HeckeContinuation`,
  `ZInQ.Literature.RootNumberVanishing` and `ZInQ.Literature.FunctionalEquation5` (the last two
  for `d ≡ 5 (mod 8)`); the first and the third are open problems on Prove2Me. On a scratch
  machine, with their definitions copied into a temporary file (Lean `v4.33.1`),
  `entire_lseries_curveD_of_ne_zero`, `vanishing_curveD_all` and `functional_equation_strip_five`
  prove all three as stated there. That check is not reproduced by this repository, which contains
  none of their code, and nothing has been submitted to Prove2Me.
- The algebraic side for `C_5` is not new. `diophantine-z-q` has a complete 2-descent for the
  curves `C_d` over `ℚ` (2-Selmer group, the bound on `C_d(ℚ)/2C_d(ℚ)`), and Michael Stoll's
  `EllipticCurves` has Mordell–Weil and 2-Selmer groups in general. The descent here was written
  independently and is much more special: three bits and one 5-adic fact for `d = 5`.
- I did not find the theta relation, the formula for `L'(1)`, `L'(C_5, 1) ≠ 0` or bounds for
  `L'(C_5, 1)` formalised
  elsewhere. In `diophantine-z-q` the general statement "order of vanishing at most one"
  (`TYZRow5b`) is a hypothesis; the result here is the single case `d = 5` and does not prove it.
- That the torsion of `C_d(ℚ)` is `ℤ/2 × ℤ/2` is classical. The argument here is elementary
  (duplication formula and parity); it uses no reduction modulo primes. Tau Ceti and Michael
  Stoll's [`EllipticCurves`](https://github.com/MichaelStollBayreuth/EllipticCurves) have a general
  two-prime reduction certificate for infinite order; I did not find it applied to these curves.
  I did not search specifically for an earlier formalisation of this torsion statement.
- On Prove2Me, the card `congruent_number_problem` formalises the elementary equivalence between
  rational right triangles of area `n` and points with `y ≠ 0`, which overlaps with
  `isCongruent_of_point` and `exists_point_of_isCongruent` here; I searched one keyword only.

## How it goes

1. **The Hecke character.** `𝓞 ℚ(i) ≃ ℤ[i]`; every ideal prime to 2 has a unique primary
   generator; an idèle is normalised by the product of these generators, and the character is
   `cmChar x = (θ/|θ|)⁻¹ · σ(root of unity congruent to the 2-adic unit mod (1+i)³)`.
2. **Twists.** For `d` odd squarefree the quadratic twist `(N α / d)`; for `d = 2e` an extra
   character `χ₈(N α)` defined modulo 8.
3. **Identification.** The local values of the character give the Euler factors of Mathlib's
   `WeierstrassCurve.LFunction`; point counts on `y² = x³ − d²x` over `𝔽_p` via a quartic Jacobi
   sum.
4. **Continuation and functional equation** from Tate's theorem in the Fermat repository.
5. **The sign.** Local root numbers: above 2 by an explicit Gauss sum over the 4 (resp. 8) classes
   of units modulo `(1+i)³` (resp. 4), giving `−i`; at inert primes dividing `d`, a Gauss sum over
   `(ℤ/p)[i]` equal to `p`; at split primes the two places have the same root number, whose square
   is `(−1/p) = 1`. The sign of the quadratic Gauss sum is never needed.
6. **Infinite order.** For `y(P) ≠ 0`, `x(2P) = (x² + d²)² / (4x(x² − d²))`. Writing `x = m/n` in
   lowest terms and checking parities (this is where `4 ∤ d` is used), `v₂(x(2P)) < 0`. And if
   `v₂(x(Q)) < 0` then `v₂(x(2Q)) = v₂(x(Q)) − 2`, so the points `2ᵏP`, `k ≥ 1`, are pairwise
   distinct.
7. **From the functional equation to the theta series.** Hecke's argument read backwards. The
   Fermat repository gives polynomial growth of `L` in vertical strips; `Γ` decays on vertical
   lines by `Γ(s+1) = sΓ(s)` alone; Mellin inversion and a shift of the line of integration
   (Cauchy on rectangles) give `θ(y) = w N⁻¹ y⁻² θ(1/(Ny))`. No Phragmén–Lindelöf.
8. **The derivative.** With the theta relation the Mellin transform of `θ` is holomorphic near
   `s = 1`, and the substitution `t ↦ 1/(Nt)`, done through Mathlib's Mellin identities, gives
   `Λ'(1) = 4 ∫_A^∞ log(t/A) θ(t) dt` when the sign is `−1`.
9. **Non-vanishing for `d = 5`.** Term-by-term integration; the first term is at least
   `log 2·(e^{−2x} + e^{−4x})/(2π)` and the rest at most `(7/54)/(A(2π)²)·e^{−9x}/(1 − e^{−x})`,
   `x = 2πA ≈ 0.2221`.
10. **Rank one for `C_5`.** Mordell–Weil by naive heights and 2-descent. The descent invariant of
    a point with `y ≠ 0` depends on three bits (the sign of `x`, the parities of `v₂(x+5)` and
    `v₅(x+5)`), because `v₂(x+5)` is even iff `v₅(x)` is even; this follows from `±2` not being
    squares modulo 5. So `C_5(ℚ)/2C_5(ℚ)` has at most 8 elements, while rank `≥ 2` would give 16.
11. **The interval for `L'(C_5, 1)`.** `L'(1) = 2·Σ aₙ E₁(nx)/n`, `x = 2π/√800`, with `E₁` the
    exponential integral. Exact coefficients for `n < 49` (nonzero only at 1, 9, 13, 17, 29, 37,
    41), `|aₙ| ≤ (7/6)n` beyond. For `z ≥ 2`, `E₁(z)` lies between `e^{−z}` times two convergents
    of its continued fraction, each proved by comparing derivatives; `E₁(x) = ∫_x^{9x} e^{−t}/t dt +
    E₁(9x)` and the integral is `log 9` plus a polynomial, so neither Euler's constant nor `log π`
    is needed. `e^{−t}` is bracketed by Taylor polynomials, evaluated in exact rational arithmetic
    by `norm_num`. A floating-point evaluation gives `2.22737`; that value is not proved.

## Files

91 files, 18,008 lines in `HeckeCM/`. Twenty of the files added last use Mathlib only
(`Theta*` except `ThetaCurve`, `HeckeConverse`, `ExpLogIntegral`, `ExpIntegral*`,
`DerivativeValue`, `GenCoeffBounds`, `CoeffFive`, `InfiniteOrder`, `Descent/`). The main entry points:

| File | Content |
|---|---|
| `Character.lean`, `Values.lean`, `Final.lean` | the Hecke character of `ℚ(i)` and its local values |
| `GenEuler.lean`, `GenPlaces.lean`, `GenConditional.lean` | from an Euler product over the places of `ℚ(i)` to a Dirichlet series over `ℕ`, and its continuation |
| `TwistChar.lean`, `TwistEight.lean`, `TwistFinal.lean`, `TwistEven.lean` | the twists and the continuation for every `d ≠ 0` |
| `CurveLSeries.lean`, `CurveGlobalD.lean`, `CurveEven.lean`, `CurveSquare.lean` | Mathlib's L-function of `C_d` in closed form |
| `FunctionalEq*.lean` | the functional equation with sign `±1` |
| `RootPsi.lean` … `RootGlobal.lean` | the sign and conductor for `d = 1` |
| `GaussLocal.lean`, `TwistLocal.lean`, `RootInert.lean`, `RootSplit.lean`, `RootPair.lean`, `RootTwist.lean` | the sign for `d` odd squarefree |
| `GaussLocalN.lean`, `RootEvenTwo.lean`, `RootEvenChar.lean`, `RootEven.lean` | the sign for `d = 2e` |
| `RootAll.lean`, `Bridge.lean` | conductors, explicit functional equations, final statements |
| `FunctionalEqStrip.lean` | the functional equation in classical form on the strip |
| `InfiniteOrder.lean` | torsion, points of infinite order, congruent numbers (Mathlib only) |
| `BsdInstances.lean` | `vanishing_and_rank`; `PositiveRanks 5, 6, 7` |
| `ThetaSeries.lean`, `ThetaInversion.lean`, `HeckeConverse.lean` | theta series, Mellin transform, the theta relation from a functional equation (Mathlib only) |
| `GrowthStrip.lean`, `ThetaCurve.lean` | polynomial growth in vertical strips; the theta relation for `C_d` |
| `ThetaDerivative.lean`, `ExpLogIntegral.lean`, `ThetaNumerics.lean` | the derivative at `s = 1` as an integral, and its non-vanishing (Mathlib only) |
| `AnalyticRankFive.lean` | `L(C_5, s)` vanishes to order exactly one at `s = 1` |
| `ExpIntegral.lean`, `ExpIntegralNumerics.lean`, `DerivativeValue.lean` | the exponential integral with explicit bounds; the interval, abstractly (Mathlib only) |
| `GenCoeffBounds.lean`, `CoeffFive.lean` | `|aₙ| ≤ (7/6)n`; the coefficients of `C_5` for `n < 49` (Mathlib only) |
| `ValueFive.lean` | `2.22 < L'(C_5, 1) < 2.23` |
| `Descent/AddSubMap.lean`, `NaiveHeight.lean`, `TwoDescent.lean`, `SquareClass.lean`, `WeakMordellWeil.lean` | Mordell–Weil for `y² = (x−e₁)(x−e₂)(x−e₃)` over `ℚ` (Mathlib only) |
| `Descent/RankAux.lean`, `LocalFive.lean`, `RankFive.lean` | `C_5(ℚ)/2C_5(ℚ)` has at most 8 elements; the generator |
| `BsdFive.lean` | `ranks_curve_five` |

## Building

```sh
scripts/build.sh        # needs git and elan; about 9 GB of disk and 25 minutes on 8 cores
```

It clones the Fermat repository at the pinned commit, builds the roughly 325 modules that are
needed, copies `HeckeCM/` in, builds it and prints the axioms of the main theorems.
`scripts/build_flt_subset_435.sh` does the first step with Lean 4.35.0 using `port-435/`.

## Licence

Apache License 2.0, see [`LICENSE`](LICENSE).
