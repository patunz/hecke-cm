import HeckeCM.Final
import HeckeCM.CurveLSeries

/-!
# The L-series of `y² = x³ − x` has an entire continuation

In a single environment (Lean 4.33.1, Mathlib `0df444a3`, the Fermat repository):

* `CMPoints.LFunction_curve_eq_cmCoeff` (`CurveLSeries.lean`): the Mathlib L-series of
  the curve is the sequence `cmCoeff`;
* `CMPoints.entire_lseries_cmCoeff` (`Final.lean`): the Dirichlet series of
  `cmCoeff` has an entire continuation.

Together they give `entire_lseries_curve`. The second form,
`entire_lseries_weierstrass`, uses none of our own definitions
in its statement.
-/

/-- **The Mathlib L-series of the curve `y² = x³ − x` over `ℚ` has an
entire continuation.** -/
theorem CMPoints.entire_lseries_curve :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      ∀ s : ℂ, 3 / 2 < s.re → F s = (CMPoints.CurveX3SubX.curve ℚ).LSeries s := by
  obtain ⟨F, hF, h⟩ := CMPoints.entire_lseries_cmCoeff
  refine ⟨F, hF, fun s hs => ?_⟩
  rw [h s hs, WeierstrassCurve.LSeries]
  congr 1
  funext n
  simp [CMPoints.LFunction_curve_eq_cmCoeff]

/-- The same statement, with the curve written by its coefficients
`(a₁, a₂, a₃, a₄, a₆) = (0, 0, 0, −1, 0)`. -/
theorem CMPoints.entire_lseries_weierstrass :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      ∀ s : ℂ, 3 / 2 < s.re → F s = (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).LSeries s :=
  CMPoints.entire_lseries_curve
