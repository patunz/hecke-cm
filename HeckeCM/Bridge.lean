import HeckeCM.RootAll

/-!
# Statements with squares, and in the form "every entire continuation"

* `CMPoints.functional_equation_curveD_odd_sq_mul`, `…_two_mul_sq_mul`:
  explicit functional equation for `y² = x³ − (d m²)² x`; the sign and conductor
  are those of `d`, because the two L-series coincide;
* `CMPoints.IsEntireContinuation`: `F` is entire and agrees with the Mathlib
  L-series for `Re s > 3/2`;
* `CMPoints.heckeContinuation`: for every `d ≠ 0` there exists an entire
  continuation of the L-series of `y² = x³ − d²x`;
* `CMPoints.rootNumberVanishing`: for `d ≡ 5, 6, 7 (mod 8)` squarefree,
  every entire continuation vanishes at `s = 1`.
-/

set_option autoImplicit false

noncomputable section

namespace CMPoints

/-- The L-series of `y² = x³ − (d m²)² x` is that of `y² = x³ − d² x`, `d` odd
and squarefree. -/
theorem LSeries_curveD_sq_mul_odd {d m : ℕ} (hodd : d % 2 = 1) (hsq : Squarefree d) (hm : m ≠ 0)
    (s : ℂ) :
    (⟨0, 0, 0, -((d * m ^ 2 : ℕ) : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ).LSeries s =
      (⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ).LSeries s := by
  have hmZ : (m : ℤ) ≠ 0 := by exact_mod_cast hm
  have hoddZ : Odd (d : ℤ) := by exact_mod_cast Nat.odd_iff.2 hodd
  have hsqZ : Squarefree (d : ℤ) := Int.squarefree_natCast.2 hsq
  rw [curve_eq (y := ((((d : ℤ) * (m : ℤ) ^ 2 : ℤ)) : ℚ)) (by push_cast; ring),
    curve_eq (Int.cast_natCast d).symm, WeierstrassCurve.LSeries,
    WeierstrassCurve.LSeries, LFunction_curveD_mul_sq hoddZ hsqZ hmZ]

/-- The L-series of `y² = x³ − (2e m²)² x` is that of `y² = x³ − (2e)² x`, `e`
odd and squarefree. -/
theorem LSeries_curveD_sq_mul_two_mul {e m : ℕ} (hodd : e % 2 = 1) (hsq : Squarefree e)
    (hm : m ≠ 0) (s : ℂ) :
    (⟨0, 0, 0, -((2 * e * m ^ 2 : ℕ) : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ).LSeries s =
      (⟨0, 0, 0, -((2 * e : ℕ) : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ).LSeries s := by
  have hmZ : (m : ℤ) ≠ 0 := by exact_mod_cast hm
  have hoddZ : Odd (e : ℤ) := by exact_mod_cast Nat.odd_iff.2 hodd
  have hsqZ : Squarefree (e : ℤ) := Int.squarefree_natCast.2 hsq
  rw [curve_eq (y := (((2 * (e : ℤ) * (m : ℤ) ^ 2 : ℤ)) : ℚ)) (by push_cast; ring),
    curve_eq (x := ((2 * e : ℕ) : ℚ)) (y := (((2 * (e : ℤ) : ℤ)) : ℚ)) (by push_cast; ring),
    WeierstrassCurve.LSeries, WeierstrassCurve.LSeries,
    LFunction_curveD_two_mul_sq hoddZ hsqZ hmZ]

/-- **Explicit functional equation for `d m²`, `d` odd and squarefree.** -/
theorem functional_equation_curveD_odd_sq_mul {d m : ℕ} (hodd : d % 2 = 1) (hsq : Squarefree d)
    (hm : m ≠ 0) :
    ∃ F Λ : ℂ → ℂ, Differentiable ℂ F ∧ Differentiable ℂ Λ ∧
      (∀ s : ℂ, 3 / 2 < s.re →
        F s = (⟨0, 0, 0, -((d * m ^ 2 : ℕ) : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ).LSeries s) ∧
      (∀ s : ℂ, F s = (Complex.Gammaℂ s)⁻¹ * Λ s) ∧
      (∀ s : ℂ, Λ s = ((ZMod.χ₈ (d : ZMod 8) * ZMod.χ₄ (d : ZMod 4) : ℤ) : ℂ) *
        (32 * (d : ℂ) ^ 2) ^ (1 - s) * Λ (2 - s)) := by
  obtain ⟨F, Λ, hF, hΛ, hval, hrel, hfe⟩ := functional_equation_curveD_odd hodd hsq
  exact ⟨F, Λ, hF, hΛ, fun s hs => by rw [hval s hs, LSeries_curveD_sq_mul_odd hodd hsq hm],
    hrel, hfe⟩

/-- **Explicit functional equation for `2e m²`, `e` odd and squarefree.** -/
theorem functional_equation_curveD_two_mul_sq_mul {e m : ℕ} (hodd : e % 2 = 1)
    (hsq : Squarefree e) (hm : m ≠ 0) :
    ∃ F Λ : ℂ → ℂ, Differentiable ℂ F ∧ Differentiable ℂ Λ ∧
      (∀ s : ℂ, 3 / 2 < s.re →
        F s = (⟨0, 0, 0, -((2 * e * m ^ 2 : ℕ) : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ).LSeries s) ∧
      (∀ s : ℂ, F s = (Complex.Gammaℂ s)⁻¹ * Λ s) ∧
      (∀ s : ℂ, Λ s = ((ZMod.χ₄ (e : ZMod 4) : ℤ) : ℂ) *
        (64 * (e : ℂ) ^ 2) ^ (1 - s) * Λ (2 - s)) := by
  obtain ⟨F, Λ, hF, hΛ, hval, hrel, hfe⟩ := functional_equation_curveD_two_mul hodd hsq
  exact ⟨F, Λ, hF, hΛ, fun s hs => by rw [hval s hs, LSeries_curveD_sq_mul_two_mul hodd hsq hm],
    hrel, hfe⟩

/-- `F` is an entire continuation of the Mathlib L-series of `E`, starting
from the half-plane `Re s > 3/2`. -/
def IsEntireContinuation (E : WeierstrassCurve ℚ) (F : ℂ → ℂ) : Prop :=
  Differentiable ℂ F ∧ ∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s

/-- **Entire continuation** of the L-series of `y² = x³ − d²x`, for every `d ≠ 0`. -/
theorem heckeContinuation : ∀ d : ℕ, d ≠ 0 →
    ∃ F : ℂ → ℂ, IsEntireContinuation (⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ) F :=
  fun _ hd => entire_lseries_curveD_of_ne_zero hd

/-- **Vanishing at `s = 1`** for `d ≡ 5, 6, 7 (mod 8)` squarefree. -/
theorem rootNumberVanishing : ∀ d : ℕ, d % 8 = 5 ∨ d % 8 = 6 ∨ d % 8 = 7 → Squarefree d →
    ∀ F : ℂ → ℂ, IsEntireContinuation (⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ) F →
      F 1 = 0 :=
  fun _ h8 hsq F hF => vanishing_curveD_all hsq h8 F hF.1 hF.2

end CMPoints
