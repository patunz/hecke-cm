import Mathlib

/-!
# The sum-difference map does what it should

Mathlib defines `WeierstrassCurve.addSubMap`, the map of `ℙ²` sending
`(x(P)·x(Q) : x(P)+x(Q) : 1)` to `(x(P+Q)·x(P-Q) : x(P+Q)+x(P-Q) : 1)`, and leaves
as a TODO the proof that it really does so. Here it is proved, in all
cases: points at infinity, `P = ±Q`, points of order 2.
-/

open WeierstrassCurve MvPolynomial

namespace BSD

section Identita

variable {F : Type*} [CommRing F] (a1 a2 a3 a4 a6 : F) {x X y Y : F}

/-- Sum of the `x`-coordinates of `P+Q` and `P-Q`, numerator. -/
lemma addSub_I1 (hE : y ^ 2 + a1 * x * y + a3 * y = x ^ 3 + a2 * x ^ 2 + a4 * x + a6)
    (hE' : Y ^ 2 + a1 * X * Y + a3 * Y = X ^ 3 + a2 * X ^ 2 + a4 * X + a6) :
    ((y - Y) ^ 2 + a1 * (y - Y) * (x - X) - (a2 + x + X) * (x - X) ^ 2) +
      ((y + Y + a1 * X + a3) ^ 2 + a1 * (y + Y + a1 * X + a3) * (x - X)
        - (a2 + x + X) * (x - X) ^ 2) =
      2 * (x + X) * (x * X) + (a1 ^ 2 + 4 * a2) * (x * X) + (2 * a4 + a1 * a3) * (x + X)
        + (a3 ^ 2 + 4 * a6) := by
  linear_combination (2) * hE + (2) * hE'

/-- Product of the `x`-coordinates of `P+Q` and `P-Q`, numerator. -/
lemma addSub_I2 (hE : y ^ 2 + a1 * x * y + a3 * y = x ^ 3 + a2 * x ^ 2 + a4 * x + a6)
    (hE' : Y ^ 2 + a1 * X * Y + a3 * Y = X ^ 3 + a2 * X ^ 2 + a4 * X + a6) :
    ((y - Y) ^ 2 + a1 * (y - Y) * (x - X) - (a2 + x + X) * (x - X) ^ 2) *
      ((y + Y + a1 * X + a3) ^ 2 + a1 * (y + Y + a1 * X + a3) * (x - X)
        - (a2 + x + X) * (x - X) ^ 2) =
      ((x * X) ^ 2 - (2 * a4 + a1 * a3) * (x * X) - (a3 ^ 2 + 4 * a6) * (x + X)
        - (a1 ^ 2 * a6 + 4 * a2 * a6 - a1 * a3 * a4 + a2 * a3 ^ 2 - a4 ^ 2)) * (x - X) ^ 2 := by
  linear_combination (-2*X^3 - X^2*a1^2 - 2*X^2*a2 + 2*X^2*x - 2*X*Y*a1 + X*a1^2*x - X*a1*a3
    + 4*X*a2*x + 2*X*x^2 - 2*Y^2 - 2*Y*a3 + a1*a3*x + a1*x*y - a2*x^2 + a3*y + a4*x + a6 - x^3
    + y^2) * hE + (-X^3 - X^2*a2 + 2*X^2*x + X*Y*a1 + X*a1^2*x + X*a1*a3 + 4*X*a2*x + X*a4
    + 2*X*x^2 + Y^2 + Y*a3 - a1^2*x^2 - a1*a3*x - 4*a2*x^2 - 2*a4*x - a6 - 4*x^3) * hE'

/-- Doubling: the denominator. -/
lemma addSub_I3 (hE : y ^ 2 + a1 * x * y + a3 * y = x ^ 3 + a2 * x ^ 2 + a4 * x + a6) :
    (2 * y + a1 * x + a3) ^ 2 =
      2 * (x + x) * (x * x) + (a1 ^ 2 + 4 * a2) * (x * x) + (2 * a4 + a1 * a3) * (x + x)
        + (a3 ^ 2 + 4 * a6) := by
  linear_combination (4) * hE

/-- Doubling: the numerator. -/
lemma addSub_I4 (hE : y ^ 2 + a1 * x * y + a3 * y = x ^ 3 + a2 * x ^ 2 + a4 * x + a6) :
    (3 * x ^ 2 + 2 * a2 * x + a4 - a1 * y) ^ 2
      + a1 * (3 * x ^ 2 + 2 * a2 * x + a4 - a1 * y) * (2 * y + a1 * x + a3)
      - (a2 + 2 * x) * (2 * y + a1 * x + a3) ^ 2 =
      (x * x) ^ 2 - (2 * a4 + a1 * a3) * (x * x) - (a3 ^ 2 + 4 * a6) * (x + x)
        - (a1 ^ 2 * a6 + 4 * a2 * a6 - a1 * a3 * a4 + a2 * a3 ^ 2 - a4 ^ 2) := by
  linear_combination (-a1^2 - 4*a2 - 8*x) * hE

end Identita

section Valutazione

variable {F : Type*} [CommRing F] (W : WeierstrassCurve F)

/-- The sum-difference map evaluated at a vector. -/
lemma addSubMap_eval (s t u : F) :
    (fun i => (W.addSubMap i).eval ![s, t, u]) =
      ![s ^ 2 - W.b₄ * s * u - W.b₆ * t * u - W.b₈ * u ^ 2,
        2 * t * s + W.b₂ * s * u + W.b₄ * t * u + W.b₆ * u ^ 2,
        t ^ 2 - 4 * s * u] := by
  ext i
  fin_cases i <;> simp [addSubMap]

end Valutazione

section Punti

open Affine Affine.Point

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]

/-- The statement: the sum-difference map sends `sym2x P Q` to a nonzero
multiple of `sym2x (P+Q) (P-Q)`. -/
def AddSubSpec (P Q : W.toAffine.Point) : Prop :=
  ∃ c : F, c ≠ 0 ∧ (fun i => (W.addSubMap i).eval (P.sym2x Q)) = c • (P + Q).sym2x (P - Q)

variable {W}

/-- Replacing `Q` by `-Q` swaps `P+Q` and `P-Q`. -/
lemma AddSubSpec.of_neg {P Q : W.toAffine.Point} (h : AddSubSpec W P (-Q)) : AddSubSpec W P Q := by
  obtain ⟨c, hc, h⟩ := h
  refine ⟨c, hc, ?_⟩
  rw [sym2x_neg_right] at h
  rw [h, sub_neg_eq_add, ← sub_eq_add_neg, sym2x_comm]

omit [DecidableEq F] [W.IsElliptic] in
/-- The `x`-coordinate of the sum, cleared of the denominator. -/
lemma sq_mul_addX (x x' n ψ : F) (hψ : ψ ≠ 0) :
    ψ ^ 2 * W.toAffine.addX x x' (n / ψ) = n ^ 2 + W.a₁ * n * ψ - (W.a₂ + x + x') * ψ ^ 2 := by
  simp only [Affine.addX]
  field_simp
  ring

/-- The case `Q = P`. -/
lemma addSubSpec_self {x y : F} (h : W.toAffine.Nonsingular x y) :
    AddSubSpec W (some x y h) (some x y h) := by
  have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
    (Affine.equation_iff _ _).1 h.1
  have hψ : y - W.toAffine.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
    simp only [Affine.negY]; ring
  have I3 := addSub_I3 W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ hE
  have I4 := addSub_I4 W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ hE
  have h1 : 2 * (x + x) * (x * x) + W.b₂ * (x * x) * 1 + W.b₄ * (x + x) * 1 + W.b₆ * 1 ^ 2 =
      (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    linear_combination -I3
  have h2 : (x + x) ^ 2 - 4 * (x * x) * 1 = 0 := by ring
  by_cases hy : y = W.toAffine.negY x y
  · -- point of order 2: `P + P = 0`
    have hψ0 : 2 * y + W.a₁ * x + W.a₃ = 0 := by rw [← hψ, sub_eq_zero]; exact hy
    rw [hψ0, zero_pow two_ne_zero] at h1
    have hne := W.addSubMap_ne_zero (sym2x_ne_zero (some x y h) (some x y h))
    rw [sym2x_some_some, addSubMap_eval] at hne
    refine ⟨(x * x) ^ 2 - W.b₄ * (x * x) * 1 - W.b₆ * (x + x) * 1 - W.b₈ * 1 ^ 2, ?_, ?_⟩
    · intro h0
      apply hne
      rw [h0, h1, h2]
      ext i; fin_cases i <;> rfl
    · rw [add_self_of_Y_eq hy, sub_self, sym2x_zero_zero, sym2x_some_some, addSubMap_eval, h1, h2]
      ext i; fin_cases i <;> simp
  · -- doubling
    have hψ0 : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by rw [← hψ, sub_ne_zero]; exact hy
    have hX := sq_mul_addX (W := W) x x (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) _ hψ0
    refine ⟨(2 * y + W.a₁ * x + W.a₃) ^ 2, pow_ne_zero _ hψ0, ?_⟩
    rw [add_self_of_Y_ne hy, sub_self, sym2x_some_zero, sym2x_some_some, addSubMap_eval,
      slope_of_Y_ne rfl hy, hψ, h1, h2]
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul]
      rw [hX]
      simp only [WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      linear_combination -I4
    · simp
    · simp

/-- The generic case: `x(P) ≠ x(Q)`. -/
lemma addSubSpec_of_X_ne {x y x' y' : F} (h : W.toAffine.Nonsingular x y)
    (h' : W.toAffine.Nonsingular x' y') (hx : x ≠ x') :
    AddSubSpec W (some x y h) (some x' y' h') := by
  have hE : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
    (Affine.equation_iff _ _).1 h.1
  have hE' : y' ^ 2 + W.a₁ * x' * y' + W.a₃ * y' = x' ^ 3 + W.a₂ * x' ^ 2 + W.a₄ * x' + W.a₆ :=
    (Affine.equation_iff _ _).1 h'.1
  have hD : x - x' ≠ 0 := sub_ne_zero.2 hx
  have hD2 : (x - x') ^ 2 ≠ 0 := pow_ne_zero _ hD
  have I1 := addSub_I1 W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ hE hE'
  have I2 := addSub_I2 W.a₁ W.a₂ W.a₃ W.a₄ W.a₆ hE hE'
  have hp := sq_mul_addX (W := W) x x' (y - y') _ hD
  have hm := sq_mul_addX (W := W) x x' (y - W.toAffine.negY x' y') _ hD
  have hneg : y - W.toAffine.negY x' y' = y + y' + W.a₁ * x' + W.a₃ := by
    simp only [Affine.negY]; ring
  rw [hneg] at hm
  refine ⟨(x - x') ^ 2, hD2, ?_⟩
  rw [sub_eq_add_neg (some x y h) (some x' y' h'), neg_some, add_of_X_ne hx, add_of_X_ne hx,
    sym2x_some_some, sym2x_some_some, addSubMap_eval, slope_of_X_ne hx, slope_of_X_ne hx, hneg]
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul]
    apply mul_left_cancel₀ hD2
    have e : (x - x') ^ 2 * ((x - x') ^ 2 * (W.toAffine.addX x x' ((y - y') / (x - x')) *
        W.toAffine.addX x x' ((y + y' + W.a₁ * x' + W.a₃) / (x - x')))) =
        ((x - x') ^ 2 * W.toAffine.addX x x' ((y - y') / (x - x'))) *
        ((x - x') ^ 2 * W.toAffine.addX x x' ((y + y' + W.a₁ * x' + W.a₃) / (x - x'))) := by ring
    rw [e, hp, hm]
    simp only [WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    linear_combination -I2
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.smul_apply,
      smul_eq_mul]
    rw [mul_add ((x - x') ^ 2), hp, hm]
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    linear_combination -I1
  · simp
    ring

variable (W)

/-- **The sum-difference map does what it should**, for every pair of points. -/
theorem addSubSpec (P Q : W.toAffine.Point) : AddSubSpec W P Q := by
  rcases P with _ | ⟨x, y, h⟩ <;> rcases Q with _ | ⟨x', y', h'⟩
  · refine ⟨1, one_ne_zero, ?_⟩
    simp only [← zero_def]
    rw [add_zero, sub_zero, sym2x_zero_zero, addSubMap_eval, one_smul]
    ext i; fin_cases i <;> simp
  · refine ⟨1, one_ne_zero, ?_⟩
    simp only [← zero_def]
    rw [zero_add, zero_sub, sym2x_neg_right, sym2x_zero_some, sym2x_some_some, addSubMap_eval,
      one_smul]
    ext i; fin_cases i <;> simp <;> ring
  · refine ⟨1, one_ne_zero, ?_⟩
    simp only [← zero_def]
    rw [add_zero, sub_zero, sym2x_some_zero, sym2x_some_some, addSubMap_eval, one_smul]
    ext i; fin_cases i <;> simp <;> ring
  · by_cases hx : x = x'
    · subst hx
      rcases Affine.Y_eq_of_X_eq h.1 h'.1 rfl with hy | hy
      · subst hy
        exact addSubSpec_self h
      · apply AddSubSpec.of_neg
        have : -(some x y' h') = some x y h := by
          rw [neg_some]
          congr 1
          exact hy.symm
        rw [this]
        exact addSubSpec_self h
    · exact addSubSpec_of_X_ne h h' hx

end Punti

end BSD
