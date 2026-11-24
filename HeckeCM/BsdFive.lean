import HeckeCM.AnalyticRankFive
import HeckeCM.Descent.RankFive

/-!
# Both ranks of `y² = x³ − 25x` are equal to one

* algebraic side (`BSD.exists_generator_curve_five`): `C_5(ℚ) = ℤ P ⊕ C_5(ℚ)[2]`
  for a point `P` of infinite order;
* analytic side (`CMPoints.analyticOrderAt_curve_five`): the Mathlib L-series of
  `C_5` has an entire continuation, and every entire continuation vanishes to
  order exactly one at `s = 1`.

This is the rank part of the Birch and Swinnerton-Dyer conjecture for `C_5`.
The formula for the leading coefficient is not addressed.
-/

set_option autoImplicit false

/-- **Algebraic rank one and analytic rank one for `y² = x³ − 25x`.** -/
theorem CMPoints.ranks_curve_five :
    (∃ P : (⟨0, 0, 0, -((5 : ℕ) : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ).toAffine.Point,
      ¬ IsOfFinAddOrder P ∧
      ∀ Q : (⟨0, 0, 0, -((5 : ℕ) : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ).toAffine.Point,
        ∃ m : ℤ, ∃ T : (⟨0, 0, 0, -((5 : ℕ) : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ).toAffine.Point,
          2 • T = 0 ∧ Q = m • P + T) ∧
    (∃ F : ℂ → ℂ, CMPoints.IsEntireContinuation
      (⟨0, 0, 0, -((5 : ℕ) : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ) F) ∧
    ∀ F : ℂ → ℂ, CMPoints.IsEntireContinuation
      (⟨0, 0, 0, -((5 : ℕ) : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ) F → analyticOrderAt F 1 = 1 :=
  ⟨BSD.exists_generator_curve_five, CMPoints.heckeContinuation 5 (by norm_num),
    CMPoints.analyticOrderAt_curve_five⟩
