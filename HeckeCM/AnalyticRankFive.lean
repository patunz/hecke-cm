import HeckeCM.ThetaCurve
import HeckeCM.ThetaDerivative
import HeckeCM.ThetaNumerics
import HeckeCM.GenCoeffBounds

/-!
# `L(C_5, s)` vanishes to order exactly one at `s = 1`

For `C_5 : y² = x³ − 25x`, every entire continuation `F` of the Mathlib
L-series satisfies `F(1) = 0` and `F'(1) ≠ 0`.

* `gCoeff_eq_zero_of_bad`, `gCoeff_prime`: values of a sequence of CM type at
  multiples of a bad prime and at good primes;
* `norm_gCoeff_le`: `‖aₙ‖ ≤ (7/6) n` when `2` is bad (Hasse on prime powers and
  multiplicativity; the factor `7/6` is only needed at `n = 3`);
* `hasDerivAt_curve_five`: `F'(1) = 4π · ∫_A^∞ log(t / A) θ₅(t) dt`,
  `A = 1 / √800`;
* `deriv_ne_zero_curve_five`, `analyticOrderAt_curve_five`: the statement.

The numerical input is small: `a₁ = 1`, `a₂ = … = a₈ = 0` and the bound above.
-/

set_option autoImplicit false

noncomputable section

open Real Complex MeasureTheory Set

namespace CMPoints

/-! ## The coefficients of `C_5` -/

lemma curveCoeff_five (n : ℕ) :
    curveCoeff 5 n = ((gCoeff (fun p : ℕ => (p : ℤ) ∣ 2 * ((5 : ℕ) : ℤ))
      (fun p => jacobiSym ((5 : ℕ) : ℤ) p * cmPrime p) n : ℤ) : ℂ) := by
  rw [curveCoeff_eq (by norm_num) Nat.prime_five.squarefree, cmCoeffTw_eq_gCoeff]

lemma curveCoeff_five_one : curveCoeff 5 1 = 1 := by
  rw [curveCoeff_five, gCoeff_one, Int.cast_one]

lemma curveCoeff_five_eq_zero {n : ℕ} (h2 : 2 ≤ n) (h8 : n ≤ 8) : curveCoeff 5 n = 0 := by
  rw [curveCoeff_five]
  have hB2 : ((2 : ℕ) : ℤ) ∣ 2 * ((5 : ℕ) : ℤ) := by norm_num
  have hB5 : ((5 : ℕ) : ℤ) ∣ 2 * ((5 : ℕ) : ℤ) := by norm_num
  have hodd : ∀ p : ℕ, p.Prime → p % 4 = 3 → ¬ ((p : ℤ) ∣ 2 * ((5 : ℕ) : ℤ)) →
      gCoeff (fun p : ℕ => (p : ℤ) ∣ 2 * ((5 : ℕ) : ℤ))
        (fun p => jacobiSym ((5 : ℕ) : ℤ) p * cmPrime p) p = 0 := by
    intro p hp h4 hB
    rw [gCoeff_prime hp hB]
    exact twCoeff_eq_zero _ p h4
  have heven : ∀ m : ℕ, 2 ∣ m → gCoeff (fun p : ℕ => (p : ℤ) ∣ 2 * ((5 : ℕ) : ℤ))
      (fun p => jacobiSym ((5 : ℕ) : ℤ) p * cmPrime p) m = 0 :=
    fun m hm => gCoeff_eq_zero_of_bad Nat.prime_two hB2 hm
  interval_cases n
  · rw [heven 2 (by norm_num), Int.cast_zero]
  · rw [hodd 3 Nat.prime_three (by norm_num) (by norm_num), Int.cast_zero]
  · rw [heven 4 (by norm_num), Int.cast_zero]
  · rw [gCoeff_eq_zero_of_bad Nat.prime_five hB5 (dvd_refl 5), Int.cast_zero]
  · rw [heven 6 (by norm_num), Int.cast_zero]
  · rw [hodd 7 (by norm_num) (by norm_num) (by norm_num), Int.cast_zero]
  · rw [heven 8 (by norm_num), Int.cast_zero]

lemma norm_curveCoeff_five_le (n : ℕ) : ‖curveCoeff 5 n‖ ≤ 7 / 6 * n := by
  rw [curveCoeff_five]
  exact norm_gCoeff_le (by norm_num) (twCoeff_sq_le _) n

/-! ## The derivative at `s = 1` -/

/-- The lower limit of integration, `A = 1 / √800`. -/
def fiveA : ℝ := (Real.sqrt (32 * ((5 : ℕ) : ℝ) ^ 2))⁻¹

lemma fiveA_pos : 0 < fiveA := by
  rw [fiveA]
  positivity

lemma fiveA_sq : 32 * ((5 : ℕ) : ℝ) ^ 2 * fiveA ^ 2 = 1 := by
  have h0 : (0 : ℝ) ≤ 32 * ((5 : ℕ) : ℝ) ^ 2 := by positivity
  have hpos : (0 : ℝ) < 32 * ((5 : ℕ) : ℝ) ^ 2 := by positivity
  rw [fiveA, inv_pow, Real.sq_sqrt h0, mul_inv_cancel₀ hpos.ne']

/-- `0.2221 ≤ 2π / √800 ≤ 0.2222`. -/
lemma two_pi_mul_fiveA_bounds : 0.2221 ≤ 2 * π * fiveA ∧ 2 * π * fiveA ≤ 0.2222 := by
  have h800 : (32 : ℝ) * ((5 : ℕ) : ℝ) ^ 2 = 800 := by norm_num
  have hs1 : Real.sqrt 800 ≤ 28.2843 :=
    (Real.sqrt_le_sqrt (by norm_num : (800 : ℝ) ≤ 28.2843 ^ 2)).trans_eq
      (Real.sqrt_sq (by norm_num))
  have hs2 : (28.2842 : ℝ) ≤ Real.sqrt 800 :=
    (Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 28.2842)).symm.le.trans
      (Real.sqrt_le_sqrt (by norm_num : (28.2842 : ℝ) ^ 2 ≤ 800))
  have hpos : (0 : ℝ) < Real.sqrt 800 := by linarith
  have hπ1 := Real.pi_gt_d6
  have hπ2 := Real.pi_lt_d6
  rw [fiveA, h800, ← div_eq_mul_inv]
  constructor
  · rw [le_div_iff₀ hpos]
    nlinarith
  · rw [div_le_iff₀ hpos]
    nlinarith

/-- **`F'(1) = 4π · ∫_A^∞ log(t / A) θ₅(t) dt`** for every entire continuation `F`. -/
theorem hasDerivAt_curve_five (F : ℂ → ℂ)
    (hF : IsEntireContinuation (⟨0, 0, 0, -((5 : ℕ) : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ) F) :
    F 1 = 0 ∧ HasDerivAt F
      (π * (4 * ∫ t in Ioi fiveA, (Real.log (t / fiveA) : ℂ) * thetaCurve 5 t)) 1 := by
  have hodd : (5 : ℕ) % 2 = 1 := by norm_num
  have hsq : Squarefree (5 : ℕ) := Nat.prime_five.squarefree
  obtain ⟨F₀, Λ, hF₀, hΛ, hval, hrel, hfe⟩ := functional_equation_curveD_odd hodd hsq
  -- `F = F₀`
  have hopen : IsOpen {t : ℂ | 3 / 2 < t.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : F₀ =ᶠ[nhds (2 : ℂ)] F :=
    Filter.eventually_of_mem (hopen.mem_nhds (by norm_num : (3 / 2 : ℝ) < (2 : ℂ).re))
      fun t ht => (hval t ht).trans (hF.2 t ht).symm
  have heq := (hF₀.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
    (hF.1.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (Set.mem_univ 2) hev
  have hFF : F = F₀ := funext fun s => (heq (Set.mem_univ s)).symm
  have hsign : ZMod.χ₈ ((5 : ℕ) : ZMod 8) * ZMod.χ₄ ((5 : ℕ) : ZMod 4) = -1 := by
    rw [ZMod.χ₈_nat_eq_if_mod_eight, ZMod.χ₄_nat_eq_if_mod_four]
    norm_num
  have ha0 := curveCoeff_zero hodd hsq
  have hsum := summable_curveCoeff hodd hsq (c := 13 / 8) (by norm_num)
  have hθ : ∀ y : ℝ, 0 < y → thetaSeries (curveCoeff 5) y =
      (-1 : ℂ) * ((32 * ((5 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)⁻¹ * ((y : ℂ) ^ 2)⁻¹ *
        thetaSeries (curveCoeff 5) (1 / (32 * ((5 : ℕ) : ℝ) ^ 2 * y)) := by
    intro y hy
    have h := thetaCurve_inversion hodd hsq hy
    rw [hsign] at h
    simpa [thetaCurve] using h
  have hΛθ : ∀ s : ℂ, (13 / 8 : ℝ) < s.re → Λ s = 2 * mellin (thetaSeries (curveCoeff 5)) s := by
    intro s hs
    have hs0 : 0 < s.re := by linarith
    have hΛs : Λ s = Complex.Gammaℂ s * F₀ s := by
      rw [hrel s, mul_inv_cancel_left₀ (Gammaℂ_ne_zero_of_re_pos hs0)]
    rw [hΛs, hval s (by linarith), mellin_thetaSeries ha0 (by norm_num) hsum hs.le,
      LSeries_curveCoeff, Complex.Gammaℂ_def]
    ring
  obtain ⟨hΛ1, hΛder⟩ := hasDerivAt_of_thetaSeries_inversion ha0 (by norm_num) hsum
    (N := 32 * ((5 : ℕ) : ℝ) ^ 2) (by positivity) fiveA_pos fiveA_sq hθ hΛ hΛθ
  have hinv : HasDerivAt (fun s : ℂ => (Complex.Gammaℂ s)⁻¹)
      (deriv (fun s : ℂ => (Complex.Gammaℂ s)⁻¹) 1) 1 :=
    (Complex.differentiable_Gammaℂ_inv 1).hasDerivAt
  have hprod := hinv.mul hΛder
  have hfun : F = fun s => (Complex.Gammaℂ s)⁻¹ * Λ s := by
    rw [hFF]
    exact funext hrel
  refine ⟨?_, ?_⟩
  · rw [hfun]
    show (Complex.Gammaℂ 1)⁻¹ * Λ 1 = 0
    rw [hΛ1, mul_zero]
  · show HasDerivAt F
      (π * (4 * ∫ t in Ioi fiveA, (Real.log (t / fiveA) : ℂ) * thetaSeries (curveCoeff 5) t)) 1
    have hv : (π : ℂ) * (4 * ∫ t in Ioi fiveA,
        (Real.log (t / fiveA) : ℂ) * thetaSeries (curveCoeff 5) t) =
        deriv (fun s : ℂ => (Complex.Gammaℂ s)⁻¹) 1 * Λ 1 + (Complex.Gammaℂ 1)⁻¹ *
          (4 * ∫ t in Ioi fiveA, (Real.log (t / fiveA) : ℂ) * thetaSeries (curveCoeff 5) t) := by
      rw [hΛ1, mul_zero, zero_add, Complex.Gammaℂ_one, one_div, inv_inv]
    rw [hfun, hv]
    exact hprod

/-- **`L'(C_5, 1) ≠ 0`**: for every entire continuation `F` of the Mathlib L-series
of `y² = x³ − 25x`, `F(1) = 0` and `F'(1) ≠ 0`. -/
theorem deriv_ne_zero_curve_five (F : ℂ → ℂ)
    (hF : IsEntireContinuation (⟨0, 0, 0, -((5 : ℕ) : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ) F) :
    F 1 = 0 ∧ deriv F 1 ≠ 0 := by
  obtain ⟨h1, hder⟩ := hasDerivAt_curve_five F hF
  refine ⟨h1, ?_⟩
  rw [hder.deriv]
  have hx := two_pi_mul_fiveA_bounds
  have hnum := numeric_ineq hx.1 hx.2
  have hI := integral_log_mul_thetaSeries_ne_zero (a := curveCoeff 5)
    (curveCoeff_zero (by norm_num) Nat.prime_five.squarefree) curveCoeff_five_one
    (fun n h2 h8 => curveCoeff_five_eq_zero h2 h8) norm_curveCoeff_five_le fiveA_pos hnum
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  exact mul_ne_zero hπ (mul_ne_zero (by norm_num) hI)

/-- **The order of vanishing of `L(C_5, s)` at `s = 1` is exactly one.** -/
theorem analyticOrderAt_curve_five (F : ℂ → ℂ)
    (hF : IsEntireContinuation (⟨0, 0, 0, -((5 : ℕ) : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ) F) :
    analyticOrderAt F 1 = 1 := by
  obtain ⟨h1, hd⟩ := deriv_ne_zero_curve_five F hF
  have h := (hF.1.analyticAt 1).analyticOrderAt_sub_eq_one_of_deriv_ne_zero hd
  simpa [h1] using h

end CMPoints
