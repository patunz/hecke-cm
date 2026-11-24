import HeckeCM.ThetaSeries

/-!
# From the functional equation to the theta relation

Mathlib only. This is Hecke's argument, read from the L-function to the theta
series.

* `integral_vertical_line_eq`: for an entire `g` with `‖g(s)‖ ≤ C / (1 + (Im s)²)`
  on a vertical strip, the integrals of `g` along the two edges coincide
  (Cauchy on rectangles);
* `thetaSeries_eq_mellinInv`: `θ(y)` is the inverse Mellin transform of its
  Mellin transform along a line where the latter decays;
* `thetaSeries_inversion`: if `Φ` is entire, agrees with the Mellin transform of
  `θ` to the right of `c`, satisfies `Φ(s) = w · N^{1−s} · Φ(2 − s)` and decays
  like `C / (1 + (Im s)²)` on the strip `2 − σ ≤ Re s ≤ σ`, then

  `θ(y) = w · N⁻¹ · y⁻² · θ(1 / (N y))`  for every `y > 0`.
-/

set_option autoImplicit false

noncomputable section

open Real Complex MeasureTheory Set Filter Asymptotics
open scoped Topology

namespace CMPoints

/-! ## Shifting a vertical line of integration -/

/-- Integrability along a vertical line, from the decay. -/
lemma integrable_vertical_line {g : ℂ → ℂ} (hg : Continuous g) {C σ : ℝ}
    (hb : ∀ t : ℝ, ‖g (σ + t * I)‖ ≤ C / (1 + t ^ 2)) :
    Integrable fun t : ℝ => g (σ + t * I) := by
  have hcont : Continuous fun t : ℝ => g ((σ : ℂ) + t * I) := hg.comp (by fun_prop)
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul C) hcont.aestronglyMeasurable
    (ae_of_all _ fun t => ?_)
  simpa [div_eq_mul_inv] using hb t

/-- **Shift of the line of integration.** For an entire `g` with
`‖g(s)‖ ≤ C / (1 + (Im s)²)` on `σ₁ ≤ Re s ≤ σ₂`, the integrals along the two
vertical edges coincide. -/
theorem integral_vertical_line_eq {g : ℂ → ℂ} (hg : Differentiable ℂ g) {σ₁ σ₂ C : ℝ}
    (h12 : σ₁ ≤ σ₂)
    (hb : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖g s‖ ≤ C / (1 + s.im ^ 2)) :
    ∫ t : ℝ, g (σ₁ + t * I) = ∫ t : ℝ, g (σ₂ + t * I) := by
  have hline : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ σ₂ → Integrable fun t : ℝ => g (σ + t * I) := by
    intro σ h1 h2
    refine integrable_vertical_line hg.continuous (C := C) fun t => ?_
    have := hb (σ + t * I) (by simpa using h1) (by simpa using h2)
    simpa using this
  -- Cauchy on the rectangle `[σ₁, σ₂] × [−T, T]`
  have hrect : ∀ T : ℝ,
      (∫ x : ℝ in σ₁..σ₂, g (x + ((-T : ℝ) : ℂ) * I)) - (∫ x : ℝ in σ₁..σ₂, g (x + (T : ℂ) * I)) +
        I • (∫ y : ℝ in (-T)..T, g (σ₂ + y * I)) - I • ∫ y : ℝ in (-T)..T, g (σ₁ + y * I) = 0 :=
    fun T => Complex.integral_boundary_rect_eq_zero_of_differentiableOn g (⟨σ₁, -T⟩ : ℂ) ⟨σ₂, T⟩
      hg.differentiableOn
  -- the horizontal sides tend to `0`
  have hhor : ∀ u : ℝ → ℝ, (∀ T, u T ^ 2 = T ^ 2) →
      Tendsto (fun T : ℝ => ∫ x : ℝ in σ₁..σ₂, g (x + ((u T : ℝ) : ℂ) * I)) atTop (𝓝 0) := by
    intro u hu
    have hbound : ∀ T : ℝ, ‖∫ x : ℝ in σ₁..σ₂, g (x + ((u T : ℝ) : ℂ) * I)‖ ≤
        C / (1 + T ^ 2) * |σ₂ - σ₁| := by
      intro T
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
      rw [Set.uIoc_of_le h12] at hx
      have := hb (x + ((u T : ℝ) : ℂ) * I) (by simpa using hx.1.le) (by simpa using hx.2)
      simpa [hu T] using this
    have hto : Tendsto (fun T : ℝ => C / (1 + T ^ 2) * |σ₂ - σ₁|) atTop (𝓝 0) := by
      have h1 : Tendsto (fun T : ℝ => 1 + T ^ 2) atTop atTop :=
        tendsto_atTop_add_const_left atTop 1 (tendsto_pow_atTop two_ne_zero)
      have h2 : Tendsto (fun T : ℝ => C / (1 + T ^ 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop h1
      simpa using h2.mul_const |σ₂ - σ₁|
    exact squeeze_zero_norm hbound hto
  have hbot := hhor (fun T => -T) (fun T => by ring)
  have htop := hhor (fun T => T) (fun T => rfl)
  -- the vertical sides tend to the integrals over the lines
  have hver : ∀ σ : ℝ, σ₁ ≤ σ → σ ≤ σ₂ →
      Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T, g (σ + y * I)) atTop
        (𝓝 (∫ y : ℝ, g (σ + y * I))) :=
    fun σ h1 h2 => intervalIntegral_tendsto_integral (hline σ h1 h2) tendsto_neg_atTop_atBot
      tendsto_id
  have hlim := ((hbot.sub htop).add ((hver σ₂ h12 le_rfl).const_smul I)).sub
    ((hver σ₁ le_rfl h12).const_smul I)
  have hzero : (fun T : ℝ => (∫ x : ℝ in σ₁..σ₂, g (x + ((-T : ℝ) : ℂ) * I)) -
      (∫ x : ℝ in σ₁..σ₂, g (x + (T : ℂ) * I)) +
        I • (∫ y : ℝ in (-T)..T, g (σ₂ + y * I)) - I • ∫ y : ℝ in (-T)..T, g (σ₁ + y * I)) =
      fun _ => 0 := funext hrect
  rw [hzero] at hlim
  have h0 := tendsto_nhds_unique hlim tendsto_const_nhds
  simp only [smul_eq_mul] at h0
  have h1 : I * ((∫ t : ℝ, g (σ₂ + t * I)) - ∫ t : ℝ, g (σ₁ + t * I)) = 0 := by
    linear_combination h0
  rcases mul_eq_zero.1 h1 with h | h
  · exact absurd h Complex.I_ne_zero
  · exact (sub_eq_zero.1 h).symm

/-! ## Powers of positive reals -/

lemma ofReal_cpow_eq_exp {x : ℝ} (hx : 0 < x) (z : ℂ) :
    (x : ℂ) ^ z = Complex.exp ((Real.log x : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hx.ne'), Complex.ofReal_log hx.le]

lemma norm_ofReal_cpow {x : ℝ} (hx : 0 < x) (z : ℂ) : ‖(x : ℂ) ^ z‖ = x ^ z.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hx z

/-- `x^{−t} ≤ x^{−σ₁} + x^{−σ₂}` for `σ₁ ≤ t ≤ σ₂`, `x > 0`. -/
lemma rpow_neg_le_add {x : ℝ} (hx : 0 < x) {σ₁ σ₂ t : ℝ} (h1 : σ₁ ≤ t) (h2 : t ≤ σ₂) :
    x ^ (-t) ≤ x ^ (-σ₁) + x ^ (-σ₂) := by
  have p1 : 0 < x ^ (-σ₁) := Real.rpow_pos_of_pos hx _
  have p2 : 0 < x ^ (-σ₂) := Real.rpow_pos_of_pos hx _
  rcases le_total 1 x with hx1 | hx1
  · have : x ^ (-t) ≤ x ^ (-σ₁) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    linarith
  · have : x ^ (-t) ≤ x ^ (-σ₂) := Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith)
    linarith

/-! ## The theta relation -/

section

variable {a : ℕ → ℂ} {c : ℝ}

/-- `θ(y)` as an inverse Mellin transform along `Re s = σ`. -/
theorem thetaSeries_eq_mellinInv (ha0 : a 0 = 0) (hc : 0 < c)
    (hsum : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ c) {Φ : ℂ → ℂ} (hΦc : Continuous Φ)
    {σ : ℝ} (hσ : c < σ) (hΦ : ∀ s : ℂ, c < s.re → Φ s = mellin (thetaSeries a) s) {C : ℝ}
    (hdec : ∀ t : ℝ, ‖Φ (σ + t * I)‖ ≤ C / (1 + t ^ 2)) {y : ℝ} (hy : 0 < y) :
    thetaSeries a y =
      (1 / (2 * π) : ℝ) • ∫ t : ℝ, (y : ℂ) ^ (-((σ : ℂ) + t * I)) • Φ (σ + t * I) := by
  have hre : ∀ t : ℝ, c < ((σ : ℂ) + t * I).re := fun t => by simpa using hσ
  have hfun : (fun t : ℝ => mellin (thetaSeries a) (σ + t * I)) = fun t : ℝ => Φ (σ + t * I) :=
    funext fun t => (hΦ _ (hre t)).symm
  have hVI : VerticalIntegrable (mellin (thetaSeries a)) σ := by
    unfold VerticalIntegrable
    rw [hfun]
    exact integrable_vertical_line hΦc hdec
  have hconv : MellinConvergent (thetaSeries a) σ :=
    mellinConvergent_thetaSeries ha0 hc hsum (by simpa using hσ)
  have hcont : ContinuousAt (thetaSeries a) y :=
    (continuousOn_thetaSeries ha0 hc hsum).continuousAt (Ioi_mem_nhds hy)
  have key := mellinInv_mellin_eq σ (thetaSeries a) hy hconv hVI hcont
  rw [← key, mellinInv]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  show (y : ℂ) ^ (-((σ : ℂ) + t * I)) • mellin (thetaSeries a) (σ + t * I) = _
  rw [← hΦ _ (hre t)]

/-- **Theta relation from the functional equation.** -/
theorem thetaSeries_inversion (ha0 : a 0 = 0) (hc : 0 < c)
    (hsum : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ c) {N : ℝ} (hN : 0 < N) {w : ℂ}
    {Φ : ℂ → ℂ} (hΦd : Differentiable ℂ Φ) {σ : ℝ} (hσ : c < σ) (hσ1 : 1 ≤ σ)
    (hΦ : ∀ s : ℂ, c < s.re → Φ s = mellin (thetaSeries a) s)
    (hFE : ∀ s : ℂ, Φ s = w * (N : ℂ) ^ (1 - s) * Φ (2 - s)) {C : ℝ}
    (hdec : ∀ s : ℂ, 2 - σ ≤ s.re → s.re ≤ σ → ‖Φ s‖ ≤ C / (1 + s.im ^ 2))
    {y : ℝ} (hy : 0 < y) :
    thetaSeries a y = w * (N : ℂ)⁻¹ * ((y : ℂ) ^ 2)⁻¹ * thetaSeries a (1 / (N * y)) := by
  have h12 : 2 - σ ≤ σ := by linarith
  have hC : 0 ≤ C := by
    have h := hdec (σ : ℂ) (by simpa using h12) (by simp)
    have h' : (0 : ℝ) ≤ C / (1 + ((σ : ℂ)).im ^ 2) := (norm_nonneg _).trans h
    simpa using h'
  have hdecσ : ∀ t : ℝ, ‖Φ (σ + t * I)‖ ≤ C / (1 + t ^ 2) := by
    intro t
    have := hdec (σ + t * I) (by simpa using h12) (by simp)
    simpa using this
  have hy' : 0 < 1 / (N * y) := by positivity
  -- both sides as integrals along `Re s = σ`
  have e1 := thetaSeries_eq_mellinInv ha0 hc hsum hΦd.continuous hσ hΦ hdecσ hy
  have e2 := thetaSeries_eq_mellinInv ha0 hc hsum hΦd.continuous hσ hΦ hdecσ hy'
  -- shift the first one to `Re s = 2 − σ`
  set g : ℂ → ℂ := fun s => (y : ℂ) ^ (-s) * Φ s with hg
  have hgd : Differentiable ℂ g :=
    (differentiable_neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.2 hy.ne'))).mul hΦd
  set D : ℝ := (y ^ (-(2 - σ)) + y ^ (-σ)) * C with hD
  have hgb : ∀ s : ℂ, 2 - σ ≤ s.re → s.re ≤ σ → ‖g s‖ ≤ D / (1 + s.im ^ 2) := by
    intro s h1 h2
    have hpos : (0 : ℝ) < 1 + s.im ^ 2 := by positivity
    rw [hg, norm_mul, norm_ofReal_cpow hy, Complex.neg_re, hD, mul_div_assoc]
    exact mul_le_mul (rpow_neg_le_add hy h1 h2) (hdec s h1 h2) (norm_nonneg _) (by positivity)
  have hshift := integral_vertical_line_eq hgd h12 hgb
  -- the integrand on the left edge, through the functional equation
  have hleft : ∀ t : ℝ, g (((2 - σ : ℝ) : ℂ) + t * I) =
      w * (N : ℂ)⁻¹ * ((y : ℂ) ^ 2)⁻¹ *
        (((1 / (N * y) : ℝ) : ℂ) ^ (-((σ : ℂ) + ((-t : ℝ) : ℂ) * I)) *
          Φ ((σ : ℂ) + ((-t : ℝ) : ℂ) * I)) := by
    intro t
    have hs2 : (2 : ℂ) - (((2 - σ : ℝ) : ℂ) + t * I) = (σ : ℂ) + ((-t : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [hg]
    show (y : ℂ) ^ (-(((2 - σ : ℝ) : ℂ) + t * I)) * Φ (((2 - σ : ℝ) : ℂ) + t * I) = _
    rw [hFE (((2 - σ : ℝ) : ℂ) + t * I), hs2]
    have hpow : (y : ℂ) ^ (-(((2 - σ : ℝ) : ℂ) + t * I)) *
        (N : ℂ) ^ (1 - (((2 - σ : ℝ) : ℂ) + t * I)) =
        (N : ℂ)⁻¹ * ((y : ℂ) ^ 2)⁻¹ *
          ((1 / (N * y) : ℝ) : ℂ) ^ (-((σ : ℂ) + ((-t : ℝ) : ℂ) * I)) := by
      have hNinv : (N : ℂ)⁻¹ = Complex.exp (-(Real.log N : ℂ)) := by
        rw [Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hN]
      have hyinv : ((y : ℂ) ^ 2)⁻¹ = Complex.exp (-(2 * (Real.log y : ℂ))) := by
        rw [Complex.exp_neg, two_mul, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hy, sq]
      have hlog : Real.log (1 / (N * y)) = -(Real.log N + Real.log y) := by
        rw [one_div, Real.log_inv, Real.log_mul hN.ne' hy.ne']
      rw [ofReal_cpow_eq_exp hy, ofReal_cpow_eq_exp hN, ofReal_cpow_eq_exp hy', hNinv, hyinv,
        hlog, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc (y : ℂ) ^ (-(((2 - σ : ℝ) : ℂ) + t * I)) *
          (w * (N : ℂ) ^ (1 - (((2 - σ : ℝ) : ℂ) + t * I)) * Φ ((σ : ℂ) + ((-t : ℝ) : ℂ) * I))
        = w * ((y : ℂ) ^ (-(((2 - σ : ℝ) : ℂ) + t * I)) *
            (N : ℂ) ^ (1 - (((2 - σ : ℝ) : ℂ) + t * I))) *
              Φ ((σ : ℂ) + ((-t : ℝ) : ℂ) * I) := by ring
      _ = _ := by
          rw [hpow]
          ring
  -- assemble
  have hI1 : ∫ t : ℝ, (y : ℂ) ^ (-((σ : ℂ) + t * I)) • Φ (σ + t * I) =
      ∫ t : ℝ, g (((2 - σ : ℝ) : ℂ) + t * I) := by
    rw [hshift]
    rfl
  have hI2 : ∫ t : ℝ, g (((2 - σ : ℝ) : ℂ) + t * I) =
      w * (N : ℂ)⁻¹ * ((y : ℂ) ^ 2)⁻¹ *
        ∫ t : ℝ, ((1 / (N * y) : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) • Φ (σ + t * I) := by
    rw [← integral_const_mul]
    have hneg := integral_neg_eq_self (fun t : ℝ => w * (N : ℂ)⁻¹ * ((y : ℂ) ^ 2)⁻¹ *
      (((1 / (N * y) : ℝ) : ℂ) ^ (-((σ : ℂ) + t * I)) • Φ (σ + t * I))) volume
    rw [← hneg]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    show g (((2 - σ : ℝ) : ℂ) + t * I) = _
    rw [hleft t]
    simp only [smul_eq_mul]
  rw [e1, hI1, hI2, e2]
  simp only [Complex.real_smul]
  ring

end

end CMPoints
