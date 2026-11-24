import HeckeCM.ThetaInversion

/-!
# The derivative at the centre, from the theta relation

Mathlib only. Let `θ(y) = ∑ a n e^{−2π n y}` satisfy
`θ(y) = −N⁻¹ y⁻² θ(1 / (N y))` (sign `−1`), let `A > 0` with `N A² = 1`, and let
`Λ` be entire with `Λ(s) = 2 · ∫₀^∞ θ(y) y^{s−1} dy` for `Re s > c`. Then

`Λ(1) = 0`  and  `Λ'(1) = 4 · ∫_A^∞ log(t / A) θ(t) dt`.

* `mellin_of_inversion`: the substitution `t ↦ 1 / (N t)` in a Mellin transform,
  through Mathlib's identities (no integral is computed by hand);
* `exists_norm_thetaSeries_le_of_inversion`: the relation makes `θ` bounded
  near `0`;
* `hasDerivAt_mellin_thetaSeries`: so its Mellin transform is holomorphic on
  `Re s > 0`, with derivative the Mellin transform of `log · θ`;
* `hasDerivAt_of_thetaSeries_inversion`: the statement above.
-/

set_option autoImplicit false

noncomputable section

open Real Complex MeasureTheory Set Filter Asymptotics
open scoped Topology

namespace CMPoints

/-- **Mellin transform and the substitution `t ↦ 1 / (N t)`.** -/
theorem mellin_of_inversion {f f' : ℝ → ℂ} {N : ℝ} (hN : 0 < N) {ε : ℂ}
    (h : ∀ t : ℝ, 0 < t → f t = ε * (N : ℂ)⁻¹ * ((t : ℂ) ^ 2)⁻¹ * f' (1 / (N * t))) (s : ℂ) :
    mellin f s = ε * (N : ℂ) ^ (1 - s) * mellin f' (2 - s) := by
  have hN0 : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hN.ne'
  have h1 : mellin f s =
      mellin (fun t : ℝ => (ε * (N : ℂ)⁻¹) • ((t : ℂ) ^ (-2 : ℂ) • f' (N * t)⁻¹)) s := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    have e2 : (t : ℂ) ^ (-2 : ℂ) = ((t : ℂ) ^ 2)⁻¹ := by
      rw [Complex.cpow_neg]
      congr 1
      exact_mod_cast Complex.cpow_natCast (t : ℂ) 2
    show (t : ℂ) ^ (s - 1) • f t =
      (t : ℂ) ^ (s - 1) • ((ε * (N : ℂ)⁻¹) • ((t : ℂ) ^ (-2 : ℂ) • f' (N * t)⁻¹))
    rw [h t ht0, e2, one_div]
    simp only [smul_eq_mul]
    ring
  have a1 := mellin_const_smul (fun t : ℝ => (t : ℂ) ^ (-2 : ℂ) • f' (N * t)⁻¹) s (ε * (N : ℂ)⁻¹)
  have a2 := mellin_cpow_smul (fun t : ℝ => f' (N * t)⁻¹) s (-2)
  have a3 := mellin_comp_mul_left (fun t : ℝ => f' t⁻¹) (s + -2) hN
  have a4 := mellin_comp_inv f' (s + -2)
  have e3 : -(s + -2) = 2 - s := by ring
  have e4 : (N : ℂ) ^ (1 - s) = (N : ℂ)⁻¹ * (N : ℂ) ^ (2 - s) := by
    rw [show (1 : ℂ) - s = (2 - s) - 1 by ring, Complex.cpow_sub _ _ hN0, Complex.cpow_one,
      div_eq_inv_mul]
  calc mellin f s
      = (ε * (N : ℂ)⁻¹) • mellin (fun t : ℝ => (t : ℂ) ^ (-2 : ℂ) • f' (N * t)⁻¹) s :=
        h1.trans a1
    _ = (ε * (N : ℂ)⁻¹) • mellin (fun t : ℝ => f' (N * t)⁻¹) (s + -2) := by
        rw [show mellin (fun t : ℝ => (t : ℂ) ^ (-2 : ℂ) • f' (N * t)⁻¹) s = _ from a2]
    _ = (ε * (N : ℂ)⁻¹) • ((N : ℂ) ^ (-(s + -2)) • mellin (fun t : ℝ => f' t⁻¹) (s + -2)) := by
        rw [show mellin (fun t : ℝ => f' (N * t)⁻¹) (s + -2) = _ from a3]
    _ = (ε * (N : ℂ)⁻¹) • ((N : ℂ) ^ (-(s + -2)) • mellin f' (-(s + -2))) := by rw [a4]
    _ = ε * (N : ℂ) ^ (1 - s) * mellin f' (2 - s) := by
        simp only [smul_eq_mul]
        rw [e3, e4]
        ring

section

variable {a : ℕ → ℂ} {c : ℝ}

/-- The theta relation makes `θ` bounded near `0`. -/
theorem exists_norm_thetaSeries_le_of_inversion (ha0 : a 0 = 0) (hc : 0 < c)
    (hsum : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ c) {N : ℝ} (hN : 0 < N) {ε : ℂ}
    (hθ : ∀ y : ℝ, 0 < y → thetaSeries a y =
      ε * (N : ℂ)⁻¹ * ((y : ℂ) ^ 2)⁻¹ * thetaSeries a (1 / (N * y))) :
    ∃ B : ℝ, ∀ y : ℝ, 0 < y → y < 1 / N → ‖thetaSeries a y‖ ≤ B := by
  refine ⟨‖ε‖ * (thetaConst a c * π ^ (-c)) * (2 * N), fun y hy hyN => ?_⟩
  have hNy : 0 < N * y := mul_pos hN hy
  have hu1 : 1 ≤ 1 / (N * y) := by
    rw [le_div_iff₀ hNy, one_mul]
    have := (lt_div_iff₀ hN).1 hyN
    linarith
  set u : ℝ := 1 / (N * y) with hu
  have hu0 : 0 < u := by positivity
  have hθu := norm_thetaSeries_le_exp ha0 hc hsum hu1
  have hK0 : 0 ≤ thetaConst a c * π ^ (-c) :=
    mul_nonneg (thetaConst_nonneg a c) (Real.rpow_pos_of_pos Real.pi_pos _).le
  -- `u² e^{−π u} ≤ 2`
  have hexp : u ^ 2 * Real.exp (-π * u) ≤ 2 := by
    have h1 := Real.quadratic_le_exp_of_nonneg hu0.le
    have h2 : Real.exp u ≤ Real.exp (π * u) := Real.exp_le_exp.2 (by
      nlinarith [Real.pi_gt_three])
    have h3 : u ^ 2 ≤ 2 * Real.exp (π * u) := by nlinarith
    have h4 : Real.exp (-π * u) * Real.exp (π * u) = 1 := by
      rw [← Real.exp_add]
      simp
    have h5 : 0 < Real.exp (-π * u) := Real.exp_pos _
    calc u ^ 2 * Real.exp (-π * u) ≤ 2 * Real.exp (π * u) * Real.exp (-π * u) :=
          mul_le_mul_of_nonneg_right h3 h5.le
      _ = 2 := by linear_combination 2 * h4
  have hy2 : (y ^ 2)⁻¹ = N ^ 2 * u ^ 2 := by
    rw [hu]
    field_simp
  rw [hθ y hy, norm_mul, norm_mul, norm_mul, norm_inv, norm_inv, norm_pow, Complex.norm_real,
    Complex.norm_real, Real.norm_of_nonneg hN.le, Real.norm_of_nonneg hy.le, hy2]
  calc ‖ε‖ * N⁻¹ * (N ^ 2 * u ^ 2) * ‖thetaSeries a u‖
      ≤ ‖ε‖ * N⁻¹ * (N ^ 2 * u ^ 2) * (thetaConst a c * π ^ (-c) * Real.exp (-π * u)) :=
        mul_le_mul_of_nonneg_left hθu (by positivity)
    _ = ‖ε‖ * (thetaConst a c * π ^ (-c)) * (N * (u ^ 2 * Real.exp (-π * u))) := by
        field_simp
    _ ≤ ‖ε‖ * (thetaConst a c * π ^ (-c)) * (N * 2) := by
        gcongr
    _ = _ := by ring

/-- With the theta relation, the Mellin transform of `θ` converges and is
holomorphic on `Re s > 0`; its derivative is the Mellin transform of `log · θ`. -/
theorem hasDerivAt_mellin_thetaSeries (ha0 : a 0 = 0) (hc : 0 < c)
    (hsum : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ c) {N : ℝ} (hN : 0 < N) {ε : ℂ}
    (hθ : ∀ y : ℝ, 0 < y → thetaSeries a y =
      ε * (N : ℂ)⁻¹ * ((y : ℂ) ^ 2)⁻¹ * thetaSeries a (1 / (N * y))) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (thetaSeries a) s ∧
      MellinConvergent (fun t => Real.log t • thetaSeries a t) s ∧
      HasDerivAt (mellin (thetaSeries a)) (mellin (fun t => Real.log t • thetaSeries a t) s) s := by
  obtain ⟨B, hB⟩ := exists_norm_thetaSeries_le_of_inversion ha0 hc hsum hN hθ
  have hfc : LocallyIntegrableOn (thetaSeries a) (Ioi 0) :=
    (continuousOn_thetaSeries ha0 hc hsum).locallyIntegrableOn measurableSet_Ioi
  have htop : thetaSeries a =O[atTop] fun t : ℝ => t ^ (-(s.re + 1)) := by
    have h1 : thetaSeries a =O[atTop] fun t : ℝ => Real.exp (-π * t) := by
      refine IsBigO.of_bound (thetaConst a c * π ^ (-c)) ?_
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact norm_thetaSeries_le_exp ha0 hc hsum hy
    exact h1.trans (isLittleO_exp_neg_mul_rpow_atTop Real.pi_pos _).isBigO
  have hbot : thetaSeries a =O[𝓝[>] 0] fun t : ℝ => t ^ (-(0 : ℝ)) := by
    refine IsBigO.of_bound B ?_
    have hmem : Ioo (0 : ℝ) (1 / N) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by positivity)
    filter_upwards [hmem] with y hy
    simpa using hB y hy.1 hy.2
  refine ⟨mellinConvergent_of_isBigO_rpow hfc htop (by linarith) hbot hs, ?_⟩
  exact mellin_hasDerivAt_of_isBigO_rpow hfc htop (by linarith) hbot hs

/-- **The derivative at the centre.** -/
theorem hasDerivAt_of_thetaSeries_inversion (ha0 : a 0 = 0) (hc : 0 < c)
    (hsum : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ c) {N A : ℝ} (hN : 0 < N) (hA : 0 < A)
    (hNA : N * A ^ 2 = 1)
    (hθ : ∀ y : ℝ, 0 < y → thetaSeries a y =
      (-1 : ℂ) * (N : ℂ)⁻¹ * ((y : ℂ) ^ 2)⁻¹ * thetaSeries a (1 / (N * y)))
    {Λ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ)
    (hΛθ : ∀ s : ℂ, c < s.re → Λ s = 2 * mellin (thetaSeries a) s) :
    Λ 1 = 0 ∧
      HasDerivAt Λ (4 * ∫ t in Ioi A, (Real.log (t / A) : ℂ) * thetaSeries a t) 1 := by
  set θ := thetaSeries a with hθdef
  set U : Set ℂ := {s : ℂ | 0 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have h1U : (1 : ℂ) ∈ U := by simp [hU]
  have hmd := fun (s : ℂ) (hs : s ∈ U) =>
    hasDerivAt_mellin_thetaSeries ha0 hc hsum hN hθ (s := s) hs
  -- `Λ = 2 · mellin θ` on `Re s > 0`
  have hEq : EqOn Λ (fun s => 2 * mellin θ s) U := by
    have hΛa : AnalyticOnNhd ℂ Λ U := hΛ.differentiableOn.analyticOnNhd hUo
    have hMa : AnalyticOnNhd ℂ (fun s => 2 * mellin θ s) U :=
      DifferentiableOn.analyticOnNhd (fun s hs =>
        ((hmd s hs).2.2.differentiableAt.const_mul 2).differentiableWithinAt) hUo
    have hz0 : (((c + 1 : ℝ) : ℂ)) ∈ U := by
      simp only [hU, mem_setOf_eq, Complex.ofReal_re]
      linarith
    have hopen : IsOpen {s : ℂ | c < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : Λ =ᶠ[𝓝 ((c + 1 : ℝ) : ℂ)] fun s => 2 * mellin θ s :=
      Filter.eventually_of_mem (hopen.mem_nhds (by simp)) fun s hs => hΛθ s hs
    exact hΛa.eqOn_of_preconnected_of_eventuallyEq hMa (convex_halfSpace_re_gt 0).isPreconnected
      hz0 hev
  -- `mellin θ 1 = 0`
  have hM0 : mellin θ 1 = 0 := by
    have h := mellin_of_inversion hN hθ 1
    rw [sub_self, Complex.cpow_zero, show (2 : ℂ) - 1 = 1 by norm_num] at h
    linear_combination h / 2
  have hΛ1 : Λ 1 = 0 := by
    rw [hEq h1U]
    show 2 * mellin θ 1 = 0
    rw [hM0, mul_zero]
  refine ⟨hΛ1, ?_⟩
  have hder : HasDerivAt Λ (2 * mellin (fun t => Real.log t • θ t) 1) 1 :=
    ((hmd 1 h1U).2.2.const_mul 2).congr_of_eventuallyEq
      (Filter.eventually_of_mem (hUo.mem_nhds h1U) fun s hs => hEq hs)
  -- the integrand `k(t) = log(t / A) θ(t)`
  set k : ℝ → ℂ := fun t => (Real.log (t / A) : ℂ) * θ t with hk
  have hconvθ : MellinConvergent θ 1 := (hmd 1 h1U).1
  have hconvlog : MellinConvergent (fun t => Real.log t • θ t) 1 := (hmd 1 h1U).2.1
  have hsub := hasMellin_sub hconvlog (hconvθ.const_smul (Real.log A : ℂ))
  have hkfun : ∀ t ∈ Ioi (0 : ℝ),
      (t : ℂ) ^ ((1 : ℂ) - 1) • k t =
        (t : ℂ) ^ ((1 : ℂ) - 1) • (Real.log t • θ t - (Real.log A : ℂ) • θ t) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    simp only [hk, smul_eq_mul, Complex.real_smul]
    rw [Real.log_div ht0.ne' hA.ne']
    push_cast
    ring
  have hck : MellinConvergent k 1 :=
    (integrableOn_congr_fun hkfun measurableSet_Ioi).2 hsub.1
  have hmk : mellin k 1 = mellin (fun t => Real.log t • θ t) 1 := by
    have e : mellin k 1 = mellin (fun t => Real.log t • θ t - (Real.log A : ℂ) • θ t) 1 :=
      setIntegral_congr_fun measurableSet_Ioi hkfun
    rw [e, hsub.2, mellin_const_smul, hM0, smul_zero, sub_zero]
  -- symmetry of `k`
  have hA' : 1 / (N * A) = A := by
    have hNA0 : N * A ≠ 0 := (mul_pos hN hA).ne'
    rw [div_eq_iff hNA0]
    linear_combination -hNA
  have hksym : ∀ t : ℝ, 0 < t → k t = (1 : ℂ) * (N : ℂ)⁻¹ * ((t : ℂ) ^ 2)⁻¹ * k (1 / (N * t)) := by
    intro t ht
    have hNt : 0 < N * t := mul_pos hN ht
    have hquot : 1 / (N * t) / A = A / t := by
      have : A = 1 / (N * A) := hA'.symm
      field_simp
      nlinarith [hNA]
    have hlog : Real.log (1 / (N * t) / A) = -Real.log (t / A) := by
      rw [hquot, Real.log_div hA.ne' ht.ne', Real.log_div ht.ne' hA.ne']
      ring
    simp only [hk]
    rw [hlog, hθ t ht]
    push_cast
    ring
  -- the two halves
  set kp : ℝ → ℂ := (Ioi A).indicator k with hkp
  set km : ℝ → ℂ := (Iio A).indicator k with hkm
  have hkA : k A = 0 := by
    simp [hk, div_self hA.ne']
  have hsplit : k = fun t => kp t + km t := by
    funext t
    rcases lt_trichotomy t A with h | h | h
    · simp [hkp, hkm, h, not_lt.2 h.le]
    · subst h
      simp [hkp, hkm, hkA]
    · simp [hkp, hkm, h, not_lt.2 h.le]
  have hkmsym : ∀ t : ℝ, 0 < t →
      km t = (1 : ℂ) * (N : ℂ)⁻¹ * ((t : ℂ) ^ 2)⁻¹ * kp (1 / (N * t)) := by
    intro t ht
    have hNt : 0 < N * t := mul_pos hN ht
    have hNA' : 0 < N * A := mul_pos hN hA
    by_cases h : t < A
    · have h' : A < 1 / (N * t) := by
        rw [← hA']
        exact one_div_lt_one_div_of_lt hNt (by nlinarith)
      rw [hkm, hkp, indicator_of_mem (show t ∈ Iio A from h),
        indicator_of_mem (show 1 / (N * t) ∈ Ioi A from h')]
      exact hksym t ht
    · have h' : ¬ A < 1 / (N * t) := by
        rw [not_lt, ← hA']
        exact one_div_le_one_div_of_le hNA' (by nlinarith [not_lt.1 h])
      rw [hkm, hkp, indicator_of_notMem (show t ∉ Iio A from h),
        indicator_of_notMem (show 1 / (N * t) ∉ Ioi A from h'), mul_zero]
  have hmkm : mellin km 1 = mellin kp 1 := by
    have h := mellin_of_inversion hN hkmsym 1
    rw [sub_self, Complex.cpow_zero, show (2 : ℂ) - 1 = 1 by norm_num] at h
    rw [h]
    ring
  have hind : ∀ S : Set ℝ, MeasurableSet S → MellinConvergent (S.indicator k) 1 := by
    intro S hS
    have e : (fun t : ℝ => (t : ℂ) ^ ((1 : ℂ) - 1) • S.indicator k t) =
        S.indicator (fun t : ℝ => (t : ℂ) ^ ((1 : ℂ) - 1) • k t) := by
      funext t
      by_cases h : t ∈ S <;> simp [h]
    unfold MellinConvergent
    rw [e]
    exact IntegrableOn.indicator hck hS
  have hadd := hasMellin_add (hind (Ioi A) measurableSet_Ioi) (hind (Iio A) measurableSet_Iio)
  have hmk2 : mellin k 1 = mellin kp 1 + mellin km 1 := by
    rw [hsplit]
    exact hadd.2
  have hmkp : mellin kp 1 = ∫ t in Ioi A, k t := by
    have e : mellin kp 1 = ∫ t in Ioi (0 : ℝ), (Ioi A).indicator k t := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      simp [hkp]
    rw [e, setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_right.2 hA.le]
  have hfinal : mellin (fun t => Real.log t • θ t) 1 = 2 * ∫ t in Ioi A, k t := by
    rw [← hmk, hmk2, hmkm, hmkp]
    ring
  rw [hfinal] at hder
  convert hder using 1
  ring

end

end CMPoints
