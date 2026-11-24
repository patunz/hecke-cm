import Mathlib

/-!
# Bounds for `∫_A^∞ log(t / A) e^{−p t} dt`

Mathlib only. For `A > 0` and `p > 0` put `J = ∫_A^∞ log(t / A) e^{−p t} dt`
(it is `E₁(p A) / p`, but the exponential integral is not needed). Then

* `integrableOn_log_mul_exp`: the integrand is integrable on `(A, ∞)`;
* `integral_log_mul_exp_le`: `J ≤ e^{−p A} / (A p²)`, from `log x ≤ x − 1`;
* `le_integral_log_mul_exp`: `J ≥ log 2 · (e^{−2 p A} + e^{−4 p A}) / p`, from
  `log(t / A) ≥ log 2` on `t > 2A` and `≥ 2 log 2` on `t > 4A`.
-/

set_option autoImplicit false

noncomputable section

open Real MeasureTheory Set Filter
open scoped Topology

namespace CMPoints

variable {A p : ℝ}

/-- `∫_A^∞ (t − A) e^{−p t} dt = e^{−p A} / p²`, by the fundamental theorem of calculus. -/
theorem integral_sub_mul_exp (hp : 0 < p) (A : ℝ) :
    IntegrableOn (fun t : ℝ => (t - A) * Real.exp (-p * t)) (Ioi A) ∧
      ∫ t in Ioi A, (t - A) * Real.exp (-p * t) = Real.exp (-p * A) / p ^ 2 := by
  set G : ℝ → ℝ := fun t => -(Real.exp (-p * t) * ((t - A) / p + 1 / p ^ 2)) with hG
  have hderiv : ∀ x ∈ Ici A, HasDerivAt G ((x - A) * Real.exp (-p * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (-p * t)) (Real.exp (-p * x) * -p) x := by
      have h0 : HasDerivAt (fun t : ℝ => -p * t) (-p) x := by
        simpa using (hasDerivAt_id x).const_mul (-p)
      exact h0.exp
    have h2 : HasDerivAt (fun t : ℝ => (t - A) / p + 1 / p ^ 2) (1 / p) x := by
      have h0 : HasDerivAt (fun t : ℝ => t - A) 1 x := (hasDerivAt_id x).sub_const A
      simpa using (h0.div_const p).add_const (1 / p ^ 2)
    have h3 := (h1.mul h2).neg
    have e : (x - A) * Real.exp (-p * x) =
        -(Real.exp (-p * x) * -p * ((x - A) / p + 1 / p ^ 2) + Real.exp (-p * x) * (1 / p)) := by
      field_simp
      ring
    rw [e]
    exact h3
  have hpos : ∀ x ∈ Ioi A, 0 ≤ (x - A) * Real.exp (-p * x) := fun x hx =>
    mul_nonneg (sub_nonneg.2 (le_of_lt hx)) (Real.exp_pos _).le
  have htend : Tendsto G atTop (𝓝 0) := by
    have t1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 p hp
    have t0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 p hp
    have hcomb := (t1.const_mul (-(1 / p))).add (t0.const_mul (A / p - 1 / p ^ 2))
    simp only [mul_zero, add_zero] at hcomb
    refine hcomb.congr fun t => ?_
    simp only [hG, Real.rpow_one, Real.rpow_zero]
    ring
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hderiv hpos htend, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos htend]
  simp only [hG, sub_self, zero_div, zero_add]
  field_simp
  ring

/-- For `t > A > 0`: `0 ≤ log(t / A) ≤ (t − A) / A`. -/
lemma log_div_bounds (hA : 0 < A) {t : ℝ} (ht : A < t) :
    0 ≤ Real.log (t / A) ∧ Real.log (t / A) ≤ (t - A) / A := by
  have h1 : 1 ≤ t / A := by
    rw [le_div_iff₀ hA]
    linarith
  refine ⟨Real.log_nonneg h1, ?_⟩
  have := Real.log_le_sub_one_of_pos (lt_of_lt_of_le one_pos h1)
  have e : t / A - 1 = (t - A) / A := by
    field_simp
  linarith

/-- The integrand `log(t / A) e^{−p t}` is integrable on `(A, ∞)`. -/
theorem integrableOn_log_mul_exp (hA : 0 < A) (hp : 0 < p) :
    IntegrableOn (fun t : ℝ => Real.log (t / A) * Real.exp (-p * t)) (Ioi A) := by
  have hdom : IntegrableOn (fun t : ℝ => A⁻¹ * ((t - A) * Real.exp (-p * t))) (Ioi A) :=
    (integral_sub_mul_exp hp A).1.const_mul _
  have hmeas : Measurable fun t : ℝ => Real.log (t / A) * Real.exp (-p * t) :=
    (Real.measurable_log.comp (measurable_id.div_const A)).mul
      (Real.measurable_exp.comp (measurable_id.const_mul (-p)))
  refine Integrable.mono' hdom hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht => ?_)
  obtain ⟨h0, h1⟩ := log_div_bounds hA (show A < t from ht)
  rw [Real.norm_of_nonneg (mul_nonneg h0 (Real.exp_pos _).le)]
  calc Real.log (t / A) * Real.exp (-p * t) ≤ (t - A) / A * Real.exp (-p * t) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = A⁻¹ * ((t - A) * Real.exp (-p * t)) := by
        field_simp

/-- `∫_A^∞ log(t / A) e^{−p t} dt ≤ e^{−p A} / (A p²)`. -/
theorem integral_log_mul_exp_le (hA : 0 < A) (hp : 0 < p) :
    ∫ t in Ioi A, Real.log (t / A) * Real.exp (-p * t) ≤ Real.exp (-p * A) / (A * p ^ 2) := by
  obtain ⟨hint, hval⟩ := integral_sub_mul_exp hp A
  have hdom : IntegrableOn (fun t : ℝ => A⁻¹ * ((t - A) * Real.exp (-p * t))) (Ioi A) :=
    hint.const_mul _
  calc ∫ t in Ioi A, Real.log (t / A) * Real.exp (-p * t)
      ≤ ∫ t in Ioi A, A⁻¹ * ((t - A) * Real.exp (-p * t)) := by
        refine setIntegral_mono_on (integrableOn_log_mul_exp hA hp) hdom measurableSet_Ioi
          fun t ht => ?_
        obtain ⟨-, h1⟩ := log_div_bounds hA (show A < t from ht)
        calc Real.log (t / A) * Real.exp (-p * t) ≤ (t - A) / A * Real.exp (-p * t) :=
              mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
          _ = A⁻¹ * ((t - A) * Real.exp (-p * t)) := by
              field_simp
    _ = Real.exp (-p * A) / (A * p ^ 2) := by
        rw [integral_const_mul, hval]
        field_simp

/-- `∫_c^∞ e^{−p t} dt = e^{−p c} / p`. -/
lemma integral_exp_neg_mul (hp : 0 < p) (c : ℝ) :
    ∫ t in Ioi c, Real.exp (-p * t) = Real.exp (-p * c) / p := by
  rw [integral_exp_mul_Ioi (neg_lt_zero.2 hp) c]
  field_simp

/-- `∫_A^∞ log(t / A) e^{−p t} dt ≥ log 2 · (e^{−2 p A} + e^{−4 p A}) / p`. -/
theorem le_integral_log_mul_exp (hA : 0 < A) (hp : 0 < p) :
    Real.log 2 * (Real.exp (-p * (2 * A)) + Real.exp (-p * (4 * A))) / p ≤
      ∫ t in Ioi A, Real.log (t / A) * Real.exp (-p * t) := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hexpint : ∀ c : ℝ, IntegrableOn (fun t : ℝ => Real.exp (-p * t)) (Ioi c) := fun c =>
    integrableOn_exp_mul_Ioi (neg_lt_zero.2 hp) c
  set h : ℝ → ℝ := fun t => Real.log 2 * Real.exp (-p * t) with hh
  have hhint : ∀ c : ℝ, IntegrableOn h (Ioi c) := fun c => (hexpint c).const_mul _
  set low : ℝ → ℝ := fun t => (Ioi (2 * A)).indicator h t + (Ioi (4 * A)).indicator h t with hlow
  have hlowint : IntegrableOn low (Ioi A) :=
    ((hhint A).indicator measurableSet_Ioi).add ((hhint A).indicator measurableSet_Ioi)
  have hle : ∫ t in Ioi A, low t ≤ ∫ t in Ioi A, Real.log (t / A) * Real.exp (-p * t) := by
    refine setIntegral_mono_on hlowint (integrableOn_log_mul_exp hA hp) measurableSet_Ioi
      fun t ht => ?_
    have htA : A < t := ht
    have he : 0 < Real.exp (-p * t) := Real.exp_pos _
    have hlogt0 : 0 ≤ Real.log (t / A) := (log_div_bounds hA htA).1
    by_cases h4 : 4 * A < t
    · have h2 : 2 * A < t := by linarith
      have hl : 2 * Real.log 2 ≤ Real.log (t / A) := by
        have e4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
          norm_num
        rw [← e4]
        refine Real.log_le_log (by norm_num) ?_
        rw [le_div_iff₀ hA]
        linarith
      simp only [hlow, hh, indicator_of_mem (show t ∈ Ioi (2 * A) from h2),
        indicator_of_mem (show t ∈ Ioi (4 * A) from h4)]
      nlinarith
    · by_cases h2 : 2 * A < t
      · have hl : Real.log 2 ≤ Real.log (t / A) := by
          refine Real.log_le_log (by norm_num) ?_
          rw [le_div_iff₀ hA]
          linarith
        simp only [hlow, hh, indicator_of_mem (show t ∈ Ioi (2 * A) from h2),
          indicator_of_notMem (show t ∉ Ioi (4 * A) from h4), add_zero]
        nlinarith
      · simp only [hlow, hh, indicator_of_notMem (show t ∉ Ioi (2 * A) from h2),
          indicator_of_notMem (show t ∉ Ioi (4 * A) from h4), add_zero]
        positivity
  have hval : ∫ t in Ioi A, low t =
      Real.log 2 * (Real.exp (-p * (2 * A)) + Real.exp (-p * (4 * A))) / p := by
    have e2 : Ioi A ∩ Ioi (2 * A) = Ioi (2 * A) := by
      rw [Ioi_inter_Ioi, sup_eq_right.2 (by linarith)]
    have e4 : Ioi A ∩ Ioi (4 * A) = Ioi (4 * A) := by
      rw [Ioi_inter_Ioi, sup_eq_right.2 (by linarith)]
    rw [integral_add ((hhint A).indicator measurableSet_Ioi)
      ((hhint A).indicator measurableSet_Ioi), setIntegral_indicator measurableSet_Ioi,
      setIntegral_indicator measurableSet_Ioi, e2, e4]
    simp only [hh, integral_const_mul, integral_exp_neg_mul hp]
    ring
  rw [← hval]
  exact hle

end CMPoints
