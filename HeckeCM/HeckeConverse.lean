import HeckeCM.ThetaInversion

/-!
# The theta relation for an L-function with functional equation

Mathlib only. Let `a : ℕ → ℂ` with `a 0 = 0` and `∑ ‖a n‖ / n^c < ∞`, and let
`F` be an entire continuation of `L(a, s)` such that `Λ = Γ_ℂ · F` is entire,
`Λ(s) = w · N^{1−s} · Λ(2 − s)`, and `F` has polynomial growth on a vertical
strip `2 − σ ≤ Re s ≤ σ` with `c < σ < 2`. Then

`θ(y) = w · N⁻¹ · y⁻² · θ(1 / (N y))`,  `θ(y) = ∑ a n e^{−2π n y}`.

* `norm_two_pi_cpow_mul_Gamma_mul_le`: polynomial growth of `F` and the decay
  of `Γ` give `‖(2π)^{−s} Γ(s) F(s)‖ ≤ C / (1 + (Im s)²)` on the strip;
* `thetaSeries_inversion_of_growth`: the theta relation.
-/

set_option autoImplicit false

noncomputable section

open Real Complex MeasureTheory Set Filter
open scoped Topology

namespace CMPoints

/-- `(1 + u)^m ≤ 2^m (1 + u^m)` for `u ≥ 0`. -/
lemma one_add_pow_le (m : ℕ) {u : ℝ} (hu : 0 ≤ u) : (1 + u) ^ m ≤ 2 ^ m * (1 + u ^ m) := by
  rcases le_total u 1 with h | h
  · calc (1 + u) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ ≤ 2 ^ m * (1 + u ^ m) := by
          have : (0 : ℝ) ≤ u ^ m := by positivity
          nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) m]
  · calc (1 + u) ^ m ≤ (2 * u) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ = 2 ^ m * u ^ m := mul_pow _ _ _
      _ ≤ 2 ^ m * (1 + u ^ m) := by
          have : (0 : ℝ) < 2 ^ m := by positivity
          nlinarith

/-- `Γ` is bounded on a compact interval of positive reals. -/
lemma exists_Gamma_le {σ₁ σ₂ : ℝ} (h1 : 0 < σ₁) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ x : ℝ, σ₁ ≤ x → x ≤ σ₂ → Real.Gamma x ≤ G := by
  have hcont : ContinuousOn Real.Gamma (Icc σ₁ σ₂) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono fun x hx => lt_of_lt_of_le h1 hx.1
  obtain ⟨G, hG⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max G 0, le_max_right _ _, fun x hx1 hx2 => ?_⟩
  exact ((le_abs_self _).trans (hG x ⟨hx1, hx2⟩)).trans (le_max_left _ _)

/-- **Decay on a vertical strip.** If `‖F(s)‖ ≤ A (1 + |Im s|)^M` on
`σ₁ ≤ Re s ≤ σ₂` with `σ₁ > 0`, then `(2π)^{−s} Γ(s) F(s)` is
`O(1 / (1 + (Im s)²))` there. -/
theorem norm_two_pi_cpow_mul_Gamma_mul_le {F : ℂ → ℂ} {σ₁ σ₂ A : ℝ} {M : ℕ} (h1 : 0 < σ₁)
    (hF : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖F s‖ ≤ A * (1 + |s.im|) ^ M) :
    ∃ C : ℝ, ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ‖(2 * π : ℂ) ^ (-s) * Complex.Gamma s * F s‖ ≤ C / (1 + s.im ^ 2) := by
  obtain ⟨G, hG0, hG⟩ := exists_Gamma_le (σ₁ := σ₁) (σ₂ := σ₂ + (M + 2 : ℕ)) h1
  set P : ℝ := (2 * π) ^ (-σ₁) + (2 * π) ^ (-σ₂) with hP
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hP0 : 0 ≤ P := by
    have := Real.rpow_pos_of_pos h2π (-σ₁)
    have := Real.rpow_pos_of_pos h2π (-σ₂)
    rw [hP]
    positivity
  refine ⟨P * (2 ^ (M + 2) * (2 * G)) * max A 0, fun s hs1 hs2 => ?_⟩
  have hre : 0 < s.re := h1.trans_le hs1
  set t : ℝ := |s.im| with ht
  have ht0 : 0 ≤ t := abs_nonneg _
  have hden : (0 : ℝ) < 1 + s.im ^ 2 := by positivity
  -- the three factors
  have e1 : ‖(2 * π : ℂ) ^ (-s)‖ ≤ P := by
    have h : (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
    rw [h, norm_ofReal_cpow h2π, Complex.neg_re]
    exact rpow_neg_le_add h2π hs1 hs2
  have e2 : ‖Complex.Gamma s‖ * (1 + t) ^ (M + 2) ≤ 2 ^ (M + 2) * (2 * G) := by
    have ha := norm_Gamma_le hre
    have hb := norm_Gamma_mul_abs_im_pow_le (M + 2) hre
    have hGa : Real.Gamma s.re ≤ G := hG _ hs1 (by
      have : (0 : ℝ) ≤ ((M + 2 : ℕ) : ℝ) := by positivity
      linarith)
    have hGb : Real.Gamma (s.re + (M + 2 : ℕ)) ≤ G := hG _ (by
      have : (0 : ℝ) ≤ ((M + 2 : ℕ) : ℝ) := by positivity
      linarith) (by linarith)
    calc ‖Complex.Gamma s‖ * (1 + t) ^ (M + 2)
        ≤ ‖Complex.Gamma s‖ * (2 ^ (M + 2) * (1 + t ^ (M + 2))) :=
          mul_le_mul_of_nonneg_left (one_add_pow_le _ ht0) (norm_nonneg _)
      _ = 2 ^ (M + 2) * (‖Complex.Gamma s‖ + ‖Complex.Gamma s‖ * t ^ (M + 2)) := by ring
      _ ≤ 2 ^ (M + 2) * (G + G) := by
          refine mul_le_mul_of_nonneg_left (add_le_add (ha.trans hGa) (hb.trans hGb)) (by positivity)
      _ = _ := by ring
  have e3 : ‖F s‖ ≤ max A 0 * (1 + t) ^ M :=
    (hF s hs1 hs2).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have e4 : 1 + s.im ^ 2 ≤ (1 + t) ^ 2 := by
    have : s.im ^ 2 = t ^ 2 := by rw [ht, sq_abs]
    nlinarith
  rw [norm_mul, norm_mul, le_div_iff₀ hden]
  have hGam0 : 0 ≤ ‖Complex.Gamma s‖ := norm_nonneg _
  have hmax0 : 0 ≤ max A 0 := le_max_right _ _
  calc ‖(2 * π : ℂ) ^ (-s)‖ * ‖Complex.Gamma s‖ * ‖F s‖ * (1 + s.im ^ 2)
      ≤ P * ‖Complex.Gamma s‖ * (max A 0 * (1 + t) ^ M) * (1 + t) ^ 2 := by
        gcongr
    _ = P * (‖Complex.Gamma s‖ * (1 + t) ^ (M + 2)) * max A 0 := by ring
    _ ≤ P * (2 ^ (M + 2) * (2 * G)) * max A 0 := by
        gcongr

section

variable {a : ℕ → ℂ} {c : ℝ}

/-- **Theta relation.** For an L-function with entire completed function
`Λ = Γ_ℂ · F`, functional equation `Λ(s) = w N^{1−s} Λ(2 − s)` and polynomial
growth of `F` on the strip `2 − σ ≤ Re s ≤ σ`. -/
theorem thetaSeries_inversion_of_growth (ha0 : a 0 = 0) (hc : 0 < c)
    (hsum : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ c) {N : ℝ} (hN : 0 < N) {w : ℂ}
    {F Λ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ) {σ : ℝ} (hσ : c < σ) (hσ1 : 1 ≤ σ) (hσ2 : σ < 2)
    (hrel : ∀ s : ℂ, 0 < s.re → Λ s = Complex.Gammaℂ s * F s)
    (hF : ∀ s : ℂ, c < s.re → F s = LSeries a s)
    (hFE : ∀ s : ℂ, Λ s = w * (N : ℂ) ^ (1 - s) * Λ (2 - s)) {A : ℝ} {M : ℕ}
    (hgrow : ∀ s : ℂ, 2 - σ ≤ s.re → s.re ≤ σ → ‖F s‖ ≤ A * (1 + |s.im|) ^ M)
    {y : ℝ} (hy : 0 < y) :
    thetaSeries a y = w * (N : ℂ)⁻¹ * ((y : ℂ) ^ 2)⁻¹ * thetaSeries a (1 / (N * y)) := by
  have hσ0 : 0 < 2 - σ := by linarith
  have hΦeq : ∀ s : ℂ, 0 < s.re →
      Λ s / 2 = (2 * π : ℂ) ^ (-s) * Complex.Gamma s * F s := by
    intro s hs
    rw [hrel s hs, Complex.Gammaℂ_def]
    ring
  obtain ⟨C, hC⟩ := norm_two_pi_cpow_mul_Gamma_mul_le hσ0 hgrow
  refine thetaSeries_inversion (Φ := fun s => Λ s / 2) ha0 hc hsum hN (hΛ.div_const 2) hσ hσ1
    (fun s hs => ?_) (fun s => ?_) (C := C) (fun s h1 h2 => ?_) hy
  · show Λ s / 2 = _
    rw [hΦeq s (hc.trans hs), hF s hs, mellin_thetaSeries ha0 hc hsum hs.le]
  · show Λ s / 2 = w * (N : ℂ) ^ (1 - s) * (Λ (2 - s) / 2)
    rw [hFE s]
    ring
  · show ‖Λ s / 2‖ ≤ _
    rw [hΦeq s (hσ0.trans_le h1)]
    exact hC s h1 h2

end

end CMPoints
