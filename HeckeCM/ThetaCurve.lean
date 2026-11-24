import HeckeCM.HeckeConverse
import HeckeCM.GrowthStrip

/-!
# The theta series of `y² = x³ − d²x`

For `d` odd and squarefree, let `aₙ` be the coefficients of the Mathlib
L-series of `C_d : y² = x³ − d²x` and `θ_d(y) = ∑ aₙ e^{−2π n y}`. Then

`θ_d(y) = w · N⁻¹ · y⁻² · θ_d(1 / (N y))`,  `N = 32 d²`,  `w = χ₈(d) χ₄(d)`.

This is the transformation of the weight 2 CM form of `C_d` under the Fricke
involution, restricted to the imaginary axis. It is obtained from the
functional equation of the L-function (`functional_equation_curveD_odd`) and
the polynomial growth in vertical strips (`growth_curveD_odd`).
-/

set_option autoImplicit false

noncomputable section

namespace CMPoints

/-- The coefficients of the Mathlib L-series of `y² = x³ − d²x`, as complex numbers. -/
def curveCoeff (d : ℕ) (n : ℕ) : ℂ :=
  (((⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ).LFunction n : ℤ) : ℂ)

/-- `θ_d(y) = ∑ aₙ e^{−2π n y}`. -/
def thetaCurve (d : ℕ) (y : ℝ) : ℂ := thetaSeries (curveCoeff d) y

lemma curveCoeff_eq {d : ℕ} (hodd : d % 2 = 1) (hsq : Squarefree d) (n : ℕ) :
    curveCoeff d n = ((cmCoeffTw (d : ℤ) n : ℤ) : ℂ) := by
  have hoddZ : Odd (d : ℤ) := by exact_mod_cast Nat.odd_iff.2 hodd
  have hsqZ : Squarefree (d : ℤ) := Int.squarefree_natCast.2 hsq
  rw [curveCoeff, curve_eq (Int.cast_natCast d).symm,
    LFunction_curveD_eq_cmCoeffTw_of_odd_squarefree hoddZ hsqZ n]

lemma curveCoeff_zero {d : ℕ} (hodd : d % 2 = 1) (hsq : Squarefree d) : curveCoeff d 0 = 0 := by
  rw [curveCoeff_eq hodd hsq, cmCoeffTw_eq_gCoeff, gCoeff_zero, Int.cast_zero]

lemma LSeries_curveCoeff (d : ℕ) (s : ℂ) :
    LSeries (curveCoeff d) s = (⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ).LSeries s :=
  rfl

/-- `∑ ‖aₙ‖ / n^c < ∞` for `c > 3/2`. -/
lemma summable_curveCoeff {d : ℕ} (hodd : d % 2 = 1) (hsq : Squarefree d) {c : ℝ}
    (hc : 3 / 2 < c) : Summable fun n : ℕ => ‖curveCoeff d n‖ / (n : ℝ) ^ c := by
  have h := (lseriesSummable_gCoeff (B := fun p : ℕ => (p : ℤ) ∣ 2 * (d : ℤ))
    (a := fun p => jacobiSym (d : ℤ) p * cmPrime p) (twCoeff_sq_le _) (s := (c : ℂ))
    (by simpa using hc)).norm
  refine h.congr fun n => ?_
  rw [LSeries.norm_term_eq, curveCoeff_eq hodd hsq, cmCoeffTw_eq_gCoeff]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [gCoeff_zero]
  · rw [if_neg hn.ne']
    simp

/-- **The theta relation for `C_d`, `d` odd and squarefree.** -/
theorem thetaCurve_inversion {d : ℕ} (hodd : d % 2 = 1) (hsq : Squarefree d) {y : ℝ}
    (hy : 0 < y) :
    thetaCurve d y = ((ZMod.χ₈ (d : ZMod 8) * ZMod.χ₄ (d : ZMod 4) : ℤ) : ℂ) *
      ((32 * (d : ℝ) ^ 2 : ℝ) : ℂ)⁻¹ * ((y : ℂ) ^ 2)⁻¹ *
        thetaCurve d (1 / (32 * (d : ℝ) ^ 2 * y)) := by
  have hd : (0 : ℝ) < d := by
    have : d ≠ 0 := by
      rintro rfl
      omega
    exact_mod_cast Nat.pos_of_ne_zero this
  obtain ⟨F, Λ, hF, hΛ, hval, hrel, hfe⟩ := functional_equation_curveD_odd hodd hsq
  obtain ⟨A, M, hgrow⟩ := growth_curveD_odd hodd hsq F ⟨hF, hval⟩ (2 - 7 / 4) (7 / 4)
  refine thetaSeries_inversion_of_growth (c := 13 / 8) (σ := 7 / 4) (N := 32 * (d : ℝ) ^ 2)
    (curveCoeff_zero hodd hsq) (by norm_num) (summable_curveCoeff hodd hsq (by norm_num))
    (by positivity) hΛ (by norm_num) (by norm_num) (by norm_num) (fun s hs => ?_)
    (fun s hs => ?_) (fun s => ?_) hgrow hy
  · rw [hrel s, mul_inv_cancel_left₀ (Gammaℂ_ne_zero_of_re_pos hs)]
  · rw [LSeries_curveCoeff]
    exact hval s (by linarith)
  · rw [hfe s]
    push_cast
    ring

end CMPoints
