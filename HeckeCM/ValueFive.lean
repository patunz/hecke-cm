import HeckeCM.AnalyticRankFive
import HeckeCM.CoeffFive

/-!
# `2.22 < L'(C_5, 1) < 2.23`

For `C_5 : y² = x³ − 25x`, the derivative at `s = 1` of every entire
continuation of the Mathlib L-series is a real number between `2.22` and
`2.23` (`deriv_curve_five_bounds`). A floating-point evaluation of the same
series gives `2.22737…`; that value is not proved here.

The proof puts together `hasDerivAt_curve_five` (the derivative as an
integral), `gFive_table` (the coefficients up to `n = 48`) and
`integral_value_bounds` (the numerical estimate).
-/

set_option autoImplicit false

noncomputable section

open Real Complex MeasureTheory Set

namespace CMPoints

lemma curveCoeff_five_eq_gFive (n : ℕ) : curveCoeff 5 n = (((gFive n : ℤ) : ℝ) : ℂ) := by
  rw [curveCoeff_five n, Complex.ofReal_intCast]
  rfl

/-- `0.22214 ≤ 2π / √800 ≤ 0.22215`, for the lower limit of integration. -/
lemma two_pi_mul_fiveA_bounds' :
    (0.22214 : ℝ) ≤ 2 * π * fiveA ∧ 2 * π * fiveA ≤ 0.22215 := by
  have h800 : (32 : ℝ) * ((5 : ℕ) : ℝ) ^ 2 = 800 := by norm_num
  rw [fiveA, h800]
  exact two_pi_div_sqrt_bounds

/-- **`2.22 < L'(C_5, 1) < 2.23`**: for every entire continuation `F` of the
Mathlib L-series of `y² = x³ − 25x`, `F'(1)` is a real number in `(2.22, 2.23)`. -/
theorem deriv_curve_five_bounds (F : ℂ → ℂ)
    (hF : IsEntireContinuation (⟨0, 0, 0, -((5 : ℕ) : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ) F) :
    ∃ r : ℝ, 2.22 < r ∧ r < 2.23 ∧ deriv F 1 = (r : ℂ) := by
  obtain ⟨-, hder⟩ := hasDerivAt_curve_five F hF
  obtain ⟨hb1, hb2⟩ := two_pi_mul_fiveA_bounds'
  obtain ⟨r, h1, h2, hr⟩ := integral_value_bounds (a := curveCoeff 5)
    (α := fun n => ((gFive n : ℤ) : ℝ)) curveCoeff_five_eq_gFive
    (curveCoeff_zero (by norm_num) Nat.prime_five.squarefree) (fun n hn => gFive_table n hn)
    norm_curveCoeff_five_le fiveA_pos hb1 hb2
  refine ⟨r, h1, h2, ?_⟩
  rw [hder.deriv]
  exact hr

end CMPoints
