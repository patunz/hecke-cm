import HeckeCM.CurvePointCount

/-!
# The curve `y² = x³ − d²x` over a finite field

`frobeniusTrace_curveD`: over a finite field of characteristic different from 2,
for `d ≠ 0` the Frobenius trace of `y² = x³ − d²x` is that of
`y² = x³ − x` multiplied by the quadratic character of `d`. This is the quadratic
twist: the substitution `x = d t` takes `x³ − d²x` to `d³ (t³ − t)`.
-/

open Finset

namespace CMPoints

/-- The curve `y² = x³ − d²x`. -/
def curveD (R : Type*) [CommRing R] (d : R) : WeierstrassCurve R := ⟨0, 0, 0, -d ^ 2, 0⟩

lemma curveD_one (R : Type*) [CommRing R] : curveD R 1 = CurveX3SubX.curve R := by
  simp [curveD, CurveX3SubX.curve]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The number of affine solutions of `y² = x³ − d²x`. -/
lemma card_affine_curveD (hF : ringChar F ≠ 2) (d : F) :
    (Nat.card {p : F × F // (curveD F d).toAffine.Equation p.1 p.2} : ℤ) =
      Fintype.card F + ∑ x : F, quadraticChar F (x ^ 3 - d ^ 2 * x) := by
  have hiff : ∀ p : F × F, (curveD F d).toAffine.Equation p.1 p.2 ↔
      p.2 ^ 2 = p.1 ^ 3 - d ^ 2 * p.1 := by
    intro p
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [curveD]
    constructor <;> intro h <;> linear_combination h
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff), Nat.card_eq_fintype_card,
    Fintype.card_congr
      (Equiv.subtypeProdEquivSigmaSubtype fun x y : F => y ^ 2 = x ^ 3 - d ^ 2 * x),
    Fintype.card_sigma]
  push_cast
  rw [Finset.sum_congr rfl fun x _ => by
    rw [Fintype.card_subtype, card_filter_sq hF (x ^ 3 - d ^ 2 * x)], Finset.sum_add_distrib]
  simp
  ring

/-- The Frobenius trace of `y² = x³ − d²x` as a character sum. -/
theorem frobeniusTrace_curveD_eq_sum (hF : ringChar F ≠ 2) (d : F) :
    (curveD F d).frobeniusTrace = -∑ x : F, quadraticChar F (x ^ 3 - d ^ 2 * x) := by
  rw [WeierstrassCurve.frobeniusTrace_def, WeierstrassCurve.pointCount_def,
    Nat.card_eq_fintype_card]
  have := card_affine_curveD hF d
  push_cast
  rw [this]
  ring

/-- **The quadratic twist**: the trace of `y² = x³ − d²x` is `χ₂(d)` times
that of `y² = x³ − x`. -/
theorem frobeniusTrace_curveD (hF : ringChar F ≠ 2) {d : F} (hd : d ≠ 0) :
    (curveD F d).frobeniusTrace =
      quadraticChar F d * (CurveX3SubX.curve F).frobeniusTrace := by
  rw [frobeniusTrace_curveD_eq_sum hF, frobeniusTrace_curve hF]
  have hsum : ∑ x : F, quadraticChar F (x ^ 3 - d ^ 2 * x) =
      quadraticChar F d * ∑ t : F, quadraticChar F (t ^ 3 - t) := by
    rw [← Fintype.sum_equiv (Equiv.mulLeft₀ d hd)
      (fun t => quadraticChar F ((d * t) ^ 3 - d ^ 2 * (d * t)))
      (fun x => quadraticChar F (x ^ 3 - d ^ 2 * x)) (fun t => rfl), Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h3 : (d * t) ^ 3 - d ^ 2 * (d * t) = d ^ 2 * d * (t ^ 3 - t) := by ring
    rw [h3, map_mul, map_mul, map_pow, quadraticChar_sq_one hd, one_mul]
  rw [hsum]
  ring

end CMPoints
