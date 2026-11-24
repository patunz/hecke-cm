import Mathlib
import HeckeCM.Descent.AddSubMap

/-!
# 2-descent on `y² = (x - e₁)(x - e₂)(x - e₃)`: the algebraic part

Over a field `K` in which `2 ≠ 0`, with `e₁`, `e₂`, `e₃` distinct:

* **halving**: if `x(P) - eᵢ` is a square for `i = 1, 2, 3`, then `P` is
  twice a point;
* **chord**: if `x(P) ≠ x(Q)`, then `(x(P) - e)(x(Q) - e)(x(P+Q) - e)` is a
  square for every root `e`.
-/

open WeierstrassCurve Affine Affine.Point

namespace BSD

variable {K : Type*} [Field K]

/-- The curve `y² = (x - e₁)(x - e₂)(x - e₃)`. -/
def twoTorsionCurve (e₁ e₂ e₃ : K) : WeierstrassCurve K :=
  ⟨0, -(e₁ + e₂ + e₃), 0, e₁ * e₂ + e₁ * e₃ + e₂ * e₃, -(e₁ * e₂ * e₃)⟩

lemma twoTorsionCurve_equation (e₁ e₂ e₃ x y : K) :
    (twoTorsionCurve e₁ e₂ e₃).toAffine.Equation x y ↔
      y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃) := by
  rw [Affine.equation_iff]
  simp only [twoTorsionCurve]
  constructor <;> intro h <;> linear_combination h

lemma twoTorsionCurve_negY (e₁ e₂ e₃ x y : K) :
    (twoTorsionCurve e₁ e₂ e₃).toAffine.negY x y = -y := by
  simp [Affine.negY, twoTorsionCurve]

/-- A point of the curve with `y ≠ 0` is nonsingular. -/
lemma twoTorsionCurve_nonsingular (h2 : (2 : K) ≠ 0) {e₁ e₂ e₃ x y : K}
    (h : y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃)) (hy : y ≠ 0) :
    (twoTorsionCurve e₁ e₂ e₃).toAffine.Nonsingular x y := by
  rw [Affine.nonsingular_iff]
  refine ⟨(twoTorsionCurve_equation ..).2 h, Or.inr ?_⟩
  simp only [twoTorsionCurve]
  intro h'
  have : 2 * y = 0 := by linear_combination h'
  exact hy ((mul_eq_zero.1 this).resolve_left h2)

section Dimezzamento

variable [DecidableEq K]

/-- **Halving.** If `x - eᵢ = αᵢ²` for every `i`, the point `(x, y)` is, up to
sign, twice a point. -/
theorem exists_two_nsmul_eq_or_eq_neg (h2 : (2 : K) ≠ 0) {e₁ e₂ e₃ : K} (h12 : e₁ ≠ e₂)
    (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃) {x y : K}
    (h : (twoTorsionCurve e₁ e₂ e₃).toAffine.Nonsingular x y) {α₁ α₂ α₃ : K}
    (h₁ : α₁ ^ 2 = x - e₁) (h₂ : α₂ ^ 2 = x - e₂) (h₃ : α₃ ^ 2 = x - e₃) :
    ∃ Q : (twoTorsionCurve e₁ e₂ e₃).toAffine.Point,
      2 • Q = some x y h ∨ 2 • Q = -some x y h := by
  have s12 : α₁ + α₂ ≠ 0 := by
    intro h0
    apply h12
    have : α₁ ^ 2 = α₂ ^ 2 := by
      have : α₁ = -α₂ := eq_neg_of_add_eq_zero_left h0
      rw [this]; ring
    rw [h₁, h₂] at this
    linear_combination -this
  have s13 : α₁ + α₃ ≠ 0 := by
    intro h0
    apply h13
    have : α₁ ^ 2 = α₃ ^ 2 := by
      have : α₁ = -α₃ := eq_neg_of_add_eq_zero_left h0
      rw [this]; ring
    rw [h₁, h₃] at this
    linear_combination -this
  have s23 : α₂ + α₃ ≠ 0 := by
    intro h0
    apply h23
    have : α₂ ^ 2 = α₃ ^ 2 := by
      have : α₂ = -α₃ := eq_neg_of_add_eq_zero_left h0
      rw [this]; ring
    rw [h₂, h₃] at this
    linear_combination -this
  have he₁ : e₁ = x - α₁ ^ 2 := by linear_combination h₁
  have he₂ : e₂ = x - α₂ ^ 2 := by linear_combination h₂
  have he₃ : e₃ = x - α₃ ^ 2 := by linear_combination h₃
  set X := x + (α₁ * α₂ + α₁ * α₃ + α₂ * α₃) with hX
  set Y := (α₁ + α₂) * (α₁ + α₃) * (α₂ + α₃) with hY
  have hY0 : Y ≠ 0 := mul_ne_zero (mul_ne_zero s12 s13) s23
  have hEq : Y ^ 2 = (X - e₁) * (X - e₂) * (X - e₃) := by
    rw [he₁, he₂, he₃, hX, hY]; ring
  have hns := twoTorsionCurve_nonsingular h2 hEq hY0
  have hYneg : Y ≠ (twoTorsionCurve e₁ e₂ e₃).toAffine.negY X Y := by
    rw [twoTorsionCurve_negY]
    intro h'
    have : 2 * Y = 0 := by linear_combination h'
    exact hY0 ((mul_eq_zero.1 this).resolve_left h2)
  refine ⟨some X Y hns, ?_⟩
  have hψ : Y - (twoTorsionCurve e₁ e₂ e₃).toAffine.negY X Y = 2 * Y := by
    rw [twoTorsionCurve_negY]; ring
  have hψ0 : 2 * Y ≠ 0 := mul_ne_zero h2 hY0
  have hmul := sq_mul_addX (W := twoTorsionCurve e₁ e₂ e₃) X X
    (3 * X ^ 2 + 2 * (twoTorsionCurve e₁ e₂ e₃).a₂ * X + (twoTorsionCurve e₁ e₂ e₃).a₄
      - (twoTorsionCurve e₁ e₂ e₃).a₁ * Y) (2 * Y) hψ0
  have hx : (twoTorsionCurve e₁ e₂ e₃).toAffine.addX X X
      ((twoTorsionCurve e₁ e₂ e₃).toAffine.slope X X Y Y) = x := by
    rw [slope_of_Y_ne rfl hYneg, hψ]
    apply mul_left_cancel₀ (pow_ne_zero 2 hψ0)
    rw [hmul]
    simp only [twoTorsionCurve]
    rw [he₁, he₂, he₃, hX, hY]
    ring
  rw [two_nsmul, add_self_of_Y_ne hYneg]
  apply eq_or_eq_neg_of_xRep_eq_xRep
  rw [xRep_some, xRep_some, hx]

end Dimezzamento

section Corda

variable {x1 y1 x2 y2 f1 f2 f3 : K}

/-- The line through two points of the curve, evaluated at a root. -/
lemma chord_identity (hE1 : y1 ^ 2 = (x1 - f1) * (x1 - f2) * (x1 - f3))
    (hE2 : y2 ^ 2 = (x2 - f1) * (x2 - f2) * (x2 - f3)) :
    (x1 - f1) * (x2 - f1) *
        (((y1 - y2) ^ 2 - (-(f1 + f2 + f3) + x1 + x2) * (x1 - x2) ^ 2) - f1 * (x1 - x2) ^ 2) =
      (y1 * (x1 - x2) + (y1 - y2) * (f1 - x1)) ^ 2 := by
  linear_combination (-f1*x1 + f1*x2 + x1*x2 - x2^2) * hE1
    + (f1*x1 - f1*x2 - x1^2 + x1*x2) * hE2

/-- If `x3` is the `x` of the third point on the line, `(x1 - f1)(x2 - f1)(x3 - f1)` is a square. -/
lemma isSquare_chord (hE1 : y1 ^ 2 = (x1 - f1) * (x1 - f2) * (x1 - f3))
    (hE2 : y2 ^ 2 = (x2 - f1) * (x2 - f2) * (x2 - f3)) (hD : x1 ≠ x2) {x3 : K}
    (hx3 : (x1 - x2) ^ 2 * x3 =
      (y1 - y2) ^ 2 - (-(f1 + f2 + f3) + x1 + x2) * (x1 - x2) ^ 2) :
    IsSquare ((x1 - f1) * (x2 - f1) * (x3 - f1)) := by
  have hD' : x1 - x2 ≠ 0 := sub_ne_zero.2 hD
  refine ⟨(y1 * (x1 - x2) + (y1 - y2) * (f1 - x1)) / (x1 - x2), ?_⟩
  rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hD' hD')]
  linear_combination chord_identity hE1 hE2 + (x1 - f1) * (x2 - f1) * hx3

end Corda

section Differenza

variable [DecidableEq K] {e₁ e₂ e₃ : K}

/-- **Chord.** If `x(P) ≠ x(Q)`, the difference `P - Q` is an affine point and for
every root `e` the product `(x(P) - e)(x(Q) - e)(x(P - Q) - e)` is a square. -/
theorem exists_sub_eq_some_and_isSquare {x1 y1 x2 y2 : K}
    (h1 : (twoTorsionCurve e₁ e₂ e₃).toAffine.Nonsingular x1 y1)
    (h2 : (twoTorsionCurve e₁ e₂ e₃).toAffine.Nonsingular x2 y2) (hx : x1 ≠ x2) :
    ∃ (x3 y3 : K) (h3 : (twoTorsionCurve e₁ e₂ e₃).toAffine.Nonsingular x3 y3),
      some x1 y1 h1 - some x2 y2 h2 = some x3 y3 h3 ∧
      IsSquare ((x1 - e₁) * (x2 - e₁) * (x3 - e₁)) ∧
      IsSquare ((x1 - e₂) * (x2 - e₂) * (x3 - e₂)) ∧
      IsSquare ((x1 - e₃) * (x2 - e₃) * (x3 - e₃)) := by
  have hE1 := (twoTorsionCurve_equation ..).1 h1.1
  have hE2 := (twoTorsionCurve_equation ..).1 h2.1
  have hE2' : (-y2) ^ 2 = (x2 - e₁) * (x2 - e₂) * (x2 - e₃) := by rw [neg_sq]; exact hE2
  have hD : x1 - x2 ≠ 0 := sub_ne_zero.2 hx
  have hmul := sq_mul_addX (W := twoTorsionCurve e₁ e₂ e₃) x1 x2 (y1 - -y2) (x1 - x2) hD
  have hx3 : (x1 - x2) ^ 2 * (twoTorsionCurve e₁ e₂ e₃).toAffine.addX x1 x2
      ((y1 - -y2) / (x1 - x2)) =
      (y1 - -y2) ^ 2 - (-(e₁ + e₂ + e₃) + x1 + x2) * (x1 - x2) ^ 2 := by
    rw [hmul]; simp only [twoTorsionCurve]; ring
  have key : ∃ (y3 : K) (h3 : (twoTorsionCurve e₁ e₂ e₃).toAffine.Nonsingular
      ((twoTorsionCurve e₁ e₂ e₃).toAffine.addX x1 x2 ((twoTorsionCurve e₁ e₂ e₃).toAffine.slope
        x1 x2 y1 ((twoTorsionCurve e₁ e₂ e₃).toAffine.negY x2 y2))) y3),
      some x1 y1 h1 - some x2 y2 h2 = some _ y3 h3 := by
    rw [sub_eq_add_neg, neg_some, add_of_X_ne hx]
    exact ⟨_, _, rfl⟩
  obtain ⟨y3, h3, hsub⟩ := key
  refine ⟨_, y3, h3, hsub, ?_, ?_, ?_⟩
  · rw [slope_of_X_ne hx, twoTorsionCurve_negY]
    exact isSquare_chord hE1 hE2' hx hx3
  · rw [slope_of_X_ne hx, twoTorsionCurve_negY]
    refine isSquare_chord (f1 := e₂) (f2 := e₁) (f3 := e₃) (by rw [hE1]; ring) (by rw [hE2']; ring)
      hx (by rw [hx3]; ring)
  · rw [slope_of_X_ne hx, twoTorsionCurve_negY]
    refine isSquare_chord (f1 := e₃) (f2 := e₁) (f3 := e₂) (by rw [hE1]; ring) (by rw [hE2']; ring)
      hx (by rw [hx3]; ring)

end Differenza

end BSD
