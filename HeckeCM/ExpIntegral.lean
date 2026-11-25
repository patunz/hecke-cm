import HeckeCM.ThetaNumerics

/-!
# The exponential integral, with explicit bounds

Mathlib only. `expInt z = ∫_z^∞ e^{−t} / t dt` (the function `E₁`).

* `logExpIntegral_eq`: `∫_A^∞ log(t / A) e^{−p t} dt = expInt (p A) / p`
  (integration by parts);
* `expInt_eq_add`: `expInt a = ∫_a^b e^{−t} / t dt + expInt b`;
* `expTaylor_sub_exp_sign`: the Taylor polynomials of `e^{−t}` alternate around
  it for `t ≥ 0`;
* `integral_exp_div_le`, `le_integral_exp_div`: hence
  `∫_a^b e^{−t} / t dt` lies between `log(b / a) + Sₙ(b) − Sₙ(a)` for `n` odd
  and for `n` even, `Sₙ(t) = ∑_{k=1}^n (−t)^k / (k · k!)`;
* `expInt_le_upper`, `lower_le_expInt`: for `z > 0`,
  `e^{−z} (z² + 8z + 11) / (z³ + 9z² + 18z + 6) ≤ expInt z ≤
  e^{−z} (z² + 5z + 2) / (z³ + 6z² + 6z)`
  (two convergents of the continued fraction of `e^z E₁(z)`), each proved by
  comparing derivatives.
-/

set_option autoImplicit false

noncomputable section

open Real MeasureTheory Set Filter
open scoped Topology Nat

namespace CMPoints

/-- `expInt z = ∫_z^∞ e^{−t} / t dt`. -/
def expInt (z : ℝ) : ℝ := ∫ t in Ioi z, Real.exp (-t) / t

lemma integrableOn_exp_div {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Ioi z) := by
  have hmeas : Measurable fun t : ℝ => Real.exp (-t) / t :=
    (Real.measurable_exp.comp measurable_neg).div measurable_id
  refine Integrable.mono' ((integrableOn_exp_neg_Ioi z).const_mul z⁻¹)
    hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht => ?_)
  have ht0 : 0 < t := hz.trans ht
  rw [Real.norm_of_nonneg (div_nonneg (Real.exp_pos _).le ht0.le), inv_mul_eq_div]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le hz (le_of_lt ht)

lemma expInt_nonneg {z : ℝ} (hz : 0 < z) : 0 ≤ expInt z :=
  setIntegral_nonneg measurableSet_Ioi fun t ht =>
    div_nonneg (Real.exp_pos _).le (hz.trans ht).le

lemma expInt_le {z : ℝ} (hz : 0 < z) : expInt z ≤ Real.exp (-z) / z := by
  have h := setIntegral_mono_on (integrableOn_exp_div hz)
    ((integrableOn_exp_neg_Ioi z).const_mul z⁻¹) measurableSet_Ioi (fun t ht => by
      have ht0 : 0 < t := hz.trans ht
      rw [inv_mul_eq_div]
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le hz (le_of_lt ht))
  rw [integral_const_mul, integral_exp_neg_Ioi, inv_mul_eq_div] at h
  exact h

/-- `expInt a = ∫_a^b e^{−t} / t dt + expInt b` for `0 < a ≤ b`. -/
theorem expInt_eq_add {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    expInt a = (∫ t in a..b, Real.exp (-t) / t) + expInt b := by
  have hb : 0 < b := ha.trans_le hab
  rw [intervalIntegral.integral_of_le hab, expInt, expInt,
    ← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      ((integrableOn_exp_div ha).mono_set Ioc_subset_Ioi_self) (integrableOn_exp_div hb),
    Ioc_union_Ioi_eq_Ioi hab]

lemma hasDerivAt_exp_neg (t : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-t)) t :=
  ((hasDerivAt_neg t).exp).congr_deriv (mul_neg_one _)

/-! ## Integration by parts -/

/-- `∫_A^∞ log(t / A) e^{−p t} dt = expInt (p A) / p`. -/
theorem logExpIntegral_eq {A p : ℝ} (hA : 0 < A) (hp : 0 < p) :
    logExpIntegral A p = expInt (p * A) / p := by
  set u : ℝ → ℝ := fun t => Real.log (t / A) with hu
  set u' : ℝ → ℝ := fun t => 1 / t with hu'
  set v : ℝ → ℝ := fun t => -(Real.exp (-p * t)) / p with hv
  set v' : ℝ → ℝ := fun t => Real.exp (-p * t) with hv'
  have hud : ∀ t ∈ Ioi A, HasDerivAt u (u' t) t := by
    intro t ht
    have ht0 : 0 < t := hA.trans ht
    have h1 : HasDerivAt (fun s : ℝ => s / A) (1 / A) t := (hasDerivAt_id t).div_const A
    have h2 := (Real.hasDerivAt_log (div_pos ht0 hA).ne').comp t h1
    refine h2.congr_deriv ?_
    show (t / A)⁻¹ * (1 / A) = 1 / t
    field_simp
  have hvd : ∀ t ∈ Ioi A, HasDerivAt v (v' t) t := by
    intro t _
    have h0 : HasDerivAt (fun s : ℝ => -p * s) (-p) t :=
      ((hasDerivAt_id t).const_mul (-p)).congr_deriv (mul_one _)
    have h1 := (h0.exp.neg).div_const p
    refine h1.congr_deriv ?_
    show -(Real.exp (-p * t) * -p) / p = Real.exp (-p * t)
    field_simp
  have huv' : IntegrableOn (u * v') (Ioi A) := integrableOn_log_mul_exp hA hp
  have hu'v : IntegrableOn (u' * v) (Ioi A) := by
    have hmeas : Measurable (u' * v) :=
      (measurable_const.div measurable_id).mul
        ((Real.measurable_exp.comp (measurable_id.const_mul (-p))).neg.div_const p)
    refine Integrable.mono' ((integrableOn_exp_mul_Ioi (neg_lt_zero.2 hp) A).const_mul
      (A⁻¹ * p⁻¹)) hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht => ?_)
    have ht0 : 0 < t := hA.trans ht
    have hval : (u' * v) t = -(Real.exp (-p * t) / (t * p)) := by
      show 1 / t * (-(Real.exp (-p * t)) / p) = -(Real.exp (-p * t) / (t * p))
      field_simp
    rw [hval, norm_neg, Real.norm_of_nonneg (div_nonneg (Real.exp_pos _).le (by positivity))]
    have : Real.exp (-p * t) / (t * p) ≤ Real.exp (-p * t) / (A * p) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity)
        (mul_le_mul_of_nonneg_right (le_of_lt ht) hp.le)
    refine this.trans_eq ?_
    field_simp
  have hzero : Tendsto (u * v) (𝓝[>] A) (𝓝 0) := by
    have hcu : ContinuousAt u A :=
      (continuousAt_id.div_const A).log (by simp [hA.ne'])
    have hcv : ContinuousAt v A := by
      show ContinuousAt (fun t : ℝ => -(Real.exp (-p * t)) / p) A
      fun_prop
    have ht : Tendsto (u * v) (𝓝[>] A) (𝓝 ((u * v) A)) :=
      (hcu.mul hcv).tendsto.mono_left nhdsWithin_le_nhds
    have h0 : (u * v) A = 0 := by
      show Real.log (A / A) * (-(Real.exp (-p * A)) / p) = 0
      rw [div_self hA.ne', Real.log_one, zero_mul]
    rwa [h0] at ht
  have hinf : Tendsto (u * v) atTop (𝓝 0) := by
    have hto : Tendsto (fun t : ℝ => (A * p)⁻¹ * (t ^ (1 : ℝ) * Real.exp (-p * t))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 p hp).const_mul (A * p)⁻¹
    refine squeeze_zero_norm' ?_ hto
    filter_upwards [eventually_gt_atTop A] with t ht
    have ht0 : 0 < t := hA.trans ht
    obtain ⟨hl0, hl1⟩ := log_div_bounds hA ht
    have hval : (u * v) t = -(Real.log (t / A) * Real.exp (-p * t) / p) := by
      show Real.log (t / A) * (-(Real.exp (-p * t)) / p) = _
      ring
    rw [hval, norm_neg, Real.norm_of_nonneg (by positivity), Real.rpow_one]
    have h1 : Real.log (t / A) ≤ t / A := hl1.trans (by
      rw [div_le_div_iff_of_pos_right hA]
      linarith)
    calc Real.log (t / A) * Real.exp (-p * t) / p ≤ t / A * Real.exp (-p * t) / p := by
          gcongr
      _ = (A * p)⁻¹ * (t * Real.exp (-p * t)) := by
          field_simp
  have key := integral_Ioi_mul_deriv_eq_deriv_mul hud hvd huv' hu'v hzero hinf
  have hsub := integral_comp_mul_left_Ioi (fun s : ℝ => Real.exp (-s) / s) A hp
  have hint : ∫ t in Ioi A, u' t * v t = -(p⁻¹ * expInt (p * A)) := by
    have e : ∫ t in Ioi A, u' t * v t = ∫ t in Ioi A, -(Real.exp (-(p * t)) / (p * t)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht0 : t ≠ 0 := (hA.trans ht).ne'
      show 1 / t * (-(Real.exp (-p * t)) / p) = -(Real.exp (-(p * t)) / (p * t))
      rw [neg_mul]
      field_simp
    rw [e, integral_neg, hsub, smul_eq_mul, expInt]
  rw [hint] at key
  have hL : logExpIntegral A p = ∫ t in Ioi A, u t * v' t := rfl
  rw [hL, key]
  field_simp
  ring

/-! ## The Taylor polynomials of `e^{−t}` -/

/-- `∑_{k ≤ n} (−t)^k / k!`. -/
def expTaylor (n : ℕ) (t : ℝ) : ℝ := ∑ k ∈ Finset.range (n + 1), (-t) ^ k / (k ! : ℝ)

lemma expTaylor_succ_eq (n : ℕ) (t : ℝ) :
    expTaylor (n + 1) t = (∑ k ∈ Finset.range (n + 1), (-t) ^ (k + 1) / ((k + 1)! : ℝ)) + 1 := by
  rw [expTaylor, Finset.sum_range_succ']
  simp

lemma expTaylor_apply_zero (n : ℕ) : expTaylor n 0 = 1 := by
  induction n with
  | zero => simp [expTaylor]
  | succ n _ =>
    rw [expTaylor_succ_eq]
    simp

lemma hasDerivAt_pow_div_factorial (k : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (-s) ^ (k + 1) / ((k + 1)! : ℝ)) (-((-t) ^ k / (k ! : ℝ))) t := by
  have h1 := ((hasDerivAt_id t).neg.pow (k + 1)).div_const ((k + 1)! : ℝ)
  have hf : ((k + 1)! : ℝ) = ((k : ℝ) + 1) * (k ! : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hk0 : (k ! : ℝ) ≠ 0 := by positivity
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  refine h1.congr_deriv ?_
  show ((k + 1 : ℕ) : ℝ) * (-t) ^ (k + 1 - 1) * (-1) / ((k + 1)! : ℝ) = -((-t) ^ k / (k ! : ℝ))
  rw [Nat.add_sub_cancel, hf]
  push_cast
  field_simp

lemma hasDerivAt_expTaylor_succ (n : ℕ) (t : ℝ) :
    HasDerivAt (expTaylor (n + 1)) (-(expTaylor n t)) t := by
  have hfun : expTaylor (n + 1) =
      fun s => (∑ k ∈ Finset.range (n + 1), (-s) ^ (k + 1) / ((k + 1)! : ℝ)) + 1 :=
    funext fun s => expTaylor_succ_eq n s
  rw [hfun]
  have h := (HasDerivAt.fun_sum (u := Finset.range (n + 1))
    fun k _ => hasDerivAt_pow_div_factorial k t).add_const 1
  refine h.congr_deriv ?_
  rw [Finset.sum_neg_distrib]
  rfl

/-- **The Taylor polynomials of `e^{−t}` alternate around it**, for `t ≥ 0`. -/
theorem expTaylor_sub_exp_sign (n : ℕ) :
    ∀ t : ℝ, 0 ≤ t → 0 ≤ (-1 : ℝ) ^ n * (expTaylor n t - Real.exp (-t)) := by
  induction n with
  | zero =>
    intro t ht
    have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    simp only [expTaylor, zero_add, Finset.sum_range_one, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, one_mul]
    linarith
  | succ n ih =>
    intro t ht
    set g : ℝ → ℝ := fun s => (-1 : ℝ) ^ (n + 1) * (expTaylor (n + 1) s - Real.exp (-s)) with hg
    have hgd : ∀ s : ℝ, HasDerivAt g ((-1 : ℝ) ^ n * (expTaylor n s - Real.exp (-s))) s := by
      intro s
      have h := ((hasDerivAt_expTaylor_succ n s).sub (hasDerivAt_exp_neg s)).const_mul
        ((-1 : ℝ) ^ (n + 1))
      refine h.congr_deriv ?_
      rw [pow_succ]
      ring
    have hmono : MonotoneOn g (Ici 0) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
        (fun s _ => (hgd s).continuousAt.continuousWithinAt)
        (fun s _ => (hgd s).differentiableAt.differentiableWithinAt) fun s hs => ?_
      rw [interior_Ici] at hs
      rw [(hgd s).deriv]
      exact ih s (le_of_lt hs)
    have h0 : g 0 = 0 := by
      show (-1 : ℝ) ^ (n + 1) * (expTaylor (n + 1) 0 - Real.exp (-0)) = 0
      rw [expTaylor_apply_zero, neg_zero, Real.exp_zero, sub_self, mul_zero]
    have := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 ht) ht
    rw [h0] at this
    exact this

lemma exp_neg_le_expTaylor {n : ℕ} (hn : Even n) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) ≤ expTaylor n t := by
  have := expTaylor_sub_exp_sign n t ht
  rw [hn.neg_one_pow, one_mul] at this
  linarith

lemma expTaylor_le_exp_neg {n : ℕ} (hn : Odd n) {t : ℝ} (ht : 0 ≤ t) :
    expTaylor n t ≤ Real.exp (-t) := by
  have := expTaylor_sub_exp_sign n t ht
  rw [hn.neg_one_pow] at this
  linarith

/-! ## The integral of `e^{−t} / t` over a bounded interval -/

/-- `Sₙ(t) = ∑_{k=1}^n (−t)^k / (k · k!)`. -/
def expTaylorInt (n : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (-t) ^ (k + 1) / (((k : ℝ) + 1) * ((k + 1)! : ℝ))

lemma hasDerivAt_expTaylorInt (n : ℕ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (expTaylorInt n) ((expTaylor n t - 1) / t) t := by
  have hterm : ∀ k ∈ Finset.range n,
      HasDerivAt (fun s : ℝ => (-s) ^ (k + 1) / (((k : ℝ) + 1) * ((k + 1)! : ℝ)))
        ((-t) ^ (k + 1) / ((k + 1)! : ℝ) / t) t := by
    intro k _
    have h1 := ((hasDerivAt_id t).neg.pow (k + 1)).div_const (((k : ℝ) + 1) * ((k + 1)! : ℝ))
    have hk0 : ((k + 1)! : ℝ) ≠ 0 := by positivity
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    refine h1.congr_deriv ?_
    show ((k + 1 : ℕ) : ℝ) * (-t) ^ (k + 1 - 1) * (-1) / (((k : ℝ) + 1) * ((k + 1)! : ℝ)) =
      (-t) ^ (k + 1) / ((k + 1)! : ℝ) / t
    rw [Nat.add_sub_cancel, pow_succ]
    push_cast
    field_simp
  have h := HasDerivAt.fun_sum hterm
  have hval : (expTaylor n t - 1) / t =
      ∑ k ∈ Finset.range n, (-t) ^ (k + 1) / ((k + 1)! : ℝ) / t := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [expTaylor]
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
      rw [expTaylor_succ_eq, add_sub_cancel_right, Finset.sum_div]
  rw [hval]
  exact h

lemma continuous_expTaylor (n : ℕ) : Continuous (expTaylor n) := by
  unfold expTaylor
  fun_prop

/-- For `0 < a ≤ b`, `∫_a^b Tₙ(t) / t dt = log b − log a + Sₙ(b) − Sₙ(a)`. -/
lemma integral_expTaylor_div (n : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => expTaylor n t / t) volume a b ∧
      ∫ t in a..b, expTaylor n t / t =
        Real.log b - Real.log a + (expTaylorInt n b - expTaylorInt n a) := by
  have hpos : ∀ t ∈ uIcc a b, 0 < t := fun t ht => by
    rw [uIcc_of_le hab] at ht
    exact ha.trans_le ht.1
  have hcont : ContinuousOn (fun t : ℝ => expTaylor n t / t) (uIcc a b) :=
    (continuous_expTaylor n).continuousOn.div continuousOn_id fun t ht => (hpos t ht).ne'
  have hint : IntervalIntegrable (fun t : ℝ => expTaylor n t / t) volume a b :=
    hcont.intervalIntegrable
  refine ⟨hint, ?_⟩
  have hderiv : ∀ t ∈ uIcc a b,
      HasDerivAt (fun s => Real.log s + expTaylorInt n s) (expTaylor n t / t) t := by
    intro t ht
    have h := (Real.hasDerivAt_log (hpos t ht).ne').add (hasDerivAt_expTaylorInt n (hpos t ht).ne')
    refine h.congr_deriv ?_
    rw [inv_eq_one_div, ← add_div]
    congr 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

lemma intervalIntegrable_exp_div {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => Real.exp (-t) / t) volume a b := by
  have hpos : ∀ t ∈ uIcc a b, t ≠ 0 := fun t ht => by
    rw [uIcc_of_le hab] at ht
    exact (ha.trans_le ht.1).ne'
  have hcont : ContinuousOn (fun t : ℝ => Real.exp (-t) / t) (uIcc a b) :=
    (Real.continuous_exp.comp continuous_neg).continuousOn.div continuousOn_id hpos
  exact hcont.intervalIntegrable

/-- Upper bound, `n` even. -/
theorem integral_exp_div_le {n : ℕ} (hn : Even n) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, Real.exp (-t) / t ≤
      Real.log b - Real.log a + (expTaylorInt n b - expTaylorInt n a) := by
  obtain ⟨hint, hval⟩ := integral_expTaylor_div n ha hab
  rw [← hval]
  refine intervalIntegral.integral_mono_on hab (intervalIntegrable_exp_div ha hab) hint
    fun t ht => ?_
  have ht0 : 0 < t := ha.trans_le ht.1
  exact div_le_div_of_nonneg_right (exp_neg_le_expTaylor hn ht0.le) ht0.le

/-- Lower bound, `n` odd. -/
theorem le_integral_exp_div {n : ℕ} (hn : Odd n) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log b - Real.log a + (expTaylorInt n b - expTaylorInt n a) ≤
      ∫ t in a..b, Real.exp (-t) / t := by
  obtain ⟨hint, hval⟩ := integral_expTaylor_div n ha hab
  rw [← hval]
  refine intervalIntegral.integral_mono_on hab hint (intervalIntegrable_exp_div ha hab)
    fun t ht => ?_
  have ht0 : 0 < t := ha.trans_le ht.1
  exact div_le_div_of_nonneg_right (expTaylor_le_exp_neg hn ht0.le) ht0.le

/-! ## Two rational comparison functions -/

/-- `expInt z ≤ e^{−z} (z² + 5z + 2) / (z³ + 6z² + 6z)`. -/
theorem expInt_le_upper {z : ℝ} (hz : 0 < z) :
    expInt z ≤ Real.exp (-z) * ((z ^ 2 + 5 * z + 2) / (z ^ 3 + 6 * z ^ 2 + 6 * z)) := by
  set g : ℝ → ℝ := fun t =>
    -(Real.exp (-t) * ((t ^ 2 + 5 * t + 2) / (t ^ 3 + 6 * t ^ 2 + 6 * t))) with hg
  set g' : ℝ → ℝ := fun t =>
    Real.exp (-t) * (1 / t + 12 / (t ^ 3 + 6 * t ^ 2 + 6 * t) ^ 2) with hg'
  have hderiv : ∀ t ∈ Ici z, HasDerivAt g (g' t) t := by
    intro t ht
    have ht0 : 0 < t := hz.trans_le ht
    have hD : t ^ 3 + 6 * t ^ 2 + 6 * t ≠ 0 := by positivity
    have he := hasDerivAt_exp_neg t
    have hN : HasDerivAt (fun x : ℝ => x ^ 2 + 5 * x + 2) (2 * t + 5) t := by
      have h := ((hasDerivAt_pow 2 t).add ((hasDerivAt_id t).const_mul 5)).add_const 2
      exact h.congr_deriv (by norm_num)
    have hDd : HasDerivAt (fun x : ℝ => x ^ 3 + 6 * x ^ 2 + 6 * x) (3 * t ^ 2 + 12 * t + 6) t := by
      have h := ((hasDerivAt_pow 3 t).add ((hasDerivAt_pow 2 t).const_mul 6)).add
        ((hasDerivAt_id t).const_mul 6)
      exact h.congr_deriv (by norm_num <;> ring)
    have h := (he.mul (hN.div hDd hD)).neg
    refine h.congr_deriv ?_
    show _ = Real.exp (-t) * (1 / t + 12 / (t ^ 3 + 6 * t ^ 2 + 6 * t) ^ 2)
    simp only [Pi.div_apply]
    field_simp
    ring
  have hpos : ∀ t ∈ Ioi z, 0 ≤ g' t := by
    intro t ht
    have ht0 : 0 < t := hz.trans ht
    show 0 ≤ Real.exp (-t) * (1 / t + 12 / (t ^ 3 + 6 * t ^ 2 + 6 * t) ^ 2)
    positivity
  have htend : Tendsto g atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ Real.tendsto_exp_neg_atTop_nhds_zero
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    have hDp : 0 < t ^ 3 + 6 * t ^ 2 + 6 * t := by positivity
    have hR : (t ^ 2 + 5 * t + 2) / (t ^ 3 + 6 * t ^ 2 + 6 * t) ≤ 1 := by
      rw [div_le_one hDp]
      nlinarith [mul_pos ht0 ht0]
    show ‖-(Real.exp (-t) * ((t ^ 2 + 5 * t + 2) / (t ^ 3 + 6 * t ^ 2 + 6 * t)))‖ ≤ Real.exp (-t)
    rw [norm_neg, Real.norm_of_nonneg (by positivity)]
    calc Real.exp (-t) * ((t ^ 2 + 5 * t + 2) / (t ^ 3 + 6 * t ^ 2 + 6 * t))
        ≤ Real.exp (-t) * 1 := mul_le_mul_of_nonneg_left hR (Real.exp_pos _).le
      _ = Real.exp (-t) := mul_one _
  have hint := integrableOn_Ioi_deriv_of_nonneg' hderiv hpos htend
  have hval := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos htend
  have hle : expInt z ≤ ∫ t in Ioi z, g' t := by
    refine setIntegral_mono_on (integrableOn_exp_div hz) hint measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := hz.trans ht
    show Real.exp (-t) / t ≤ Real.exp (-t) * (1 / t + 12 / (t ^ 3 + 6 * t ^ 2 + 6 * t) ^ 2)
    have h12 : 0 ≤ 12 / (t ^ 3 + 6 * t ^ 2 + 6 * t) ^ 2 := by positivity
    have he := (Real.exp_pos (-t)).le
    calc Real.exp (-t) / t = Real.exp (-t) * (1 / t) := by ring
      _ ≤ Real.exp (-t) * (1 / t + 12 / (t ^ 3 + 6 * t ^ 2 + 6 * t) ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) he
  rw [hval] at hle
  have hg0 : (0 : ℝ) - g z =
      Real.exp (-z) * ((z ^ 2 + 5 * z + 2) / (z ^ 3 + 6 * z ^ 2 + 6 * z)) := by
    show (0 : ℝ) - -(Real.exp (-z) * ((z ^ 2 + 5 * z + 2) / (z ^ 3 + 6 * z ^ 2 + 6 * z))) = _
    ring
  rw [hg0] at hle
  exact hle

/-- `e^{−z} (z² + 8z + 11) / (z³ + 9z² + 18z + 6) ≤ expInt z`. -/
theorem lower_le_expInt {z : ℝ} (hz : 0 < z) :
    Real.exp (-z) * ((z ^ 2 + 8 * z + 11) / (z ^ 3 + 9 * z ^ 2 + 18 * z + 6)) ≤ expInt z := by
  set g : ℝ → ℝ := fun t =>
    -(Real.exp (-t) * ((t ^ 2 + 8 * t + 11) / (t ^ 3 + 9 * t ^ 2 + 18 * t + 6))) with hg
  set g' : ℝ → ℝ := fun t =>
    Real.exp (-t) * (1 / t - 36 / (t * (t ^ 3 + 9 * t ^ 2 + 18 * t + 6) ^ 2)) with hg'
  have hsmall : ∀ t : ℝ, 0 < t →
      36 / (t * (t ^ 3 + 9 * t ^ 2 + 18 * t + 6) ^ 2) ≤ 1 / t ∧
        0 ≤ 36 / (t * (t ^ 3 + 9 * t ^ 2 + 18 * t + 6) ^ 2) := by
    intro t ht0
    have hD6 : 6 ≤ t ^ 3 + 9 * t ^ 2 + 18 * t + 6 := by
      have : 0 ≤ t ^ 3 + 9 * t ^ 2 + 18 * t := by positivity
      linarith
    have hD2 : 36 ≤ (t ^ 3 + 9 * t ^ 2 + 18 * t + 6) ^ 2 := by nlinarith
    refine ⟨?_, by positivity⟩
    rw [div_le_div_iff₀ (by positivity) ht0]
    nlinarith
  have hderiv : ∀ t ∈ Ici z, HasDerivAt g (g' t) t := by
    intro t ht
    have ht0 : 0 < t := hz.trans_le ht
    have hD : t ^ 3 + 9 * t ^ 2 + 18 * t + 6 ≠ 0 := by positivity
    have he := hasDerivAt_exp_neg t
    have hN : HasDerivAt (fun x : ℝ => x ^ 2 + 8 * x + 11) (2 * t + 8) t := by
      have h := ((hasDerivAt_pow 2 t).add ((hasDerivAt_id t).const_mul 8)).add_const 11
      exact h.congr_deriv (by norm_num)
    have hDd : HasDerivAt (fun x : ℝ => x ^ 3 + 9 * x ^ 2 + 18 * x + 6)
        (3 * t ^ 2 + 18 * t + 18) t := by
      have h := (((hasDerivAt_pow 3 t).add ((hasDerivAt_pow 2 t).const_mul 9)).add
        ((hasDerivAt_id t).const_mul 18)).add_const 6
      exact h.congr_deriv (by norm_num <;> ring)
    have h := (he.mul (hN.div hDd hD)).neg
    refine h.congr_deriv ?_
    show _ = Real.exp (-t) * (1 / t - 36 / (t * (t ^ 3 + 9 * t ^ 2 + 18 * t + 6) ^ 2))
    simp only [Pi.div_apply]
    field_simp
    ring
  have hpos : ∀ t ∈ Ioi z, 0 ≤ g' t := by
    intro t ht
    have ht0 : 0 < t := hz.trans ht
    show 0 ≤ Real.exp (-t) * (1 / t - 36 / (t * (t ^ 3 + 9 * t ^ 2 + 18 * t + 6) ^ 2))
    exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.2 (hsmall t ht0).1)
  have htend : Tendsto g atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ Real.tendsto_exp_neg_atTop_nhds_zero
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    have hDp : 0 < t ^ 3 + 9 * t ^ 2 + 18 * t + 6 := by positivity
    have hR : (t ^ 2 + 8 * t + 11) / (t ^ 3 + 9 * t ^ 2 + 18 * t + 6) ≤ 1 := by
      rw [div_le_one hDp]
      nlinarith [mul_pos ht0 ht0, mul_pos (mul_pos ht0 ht0) ht0]
    show ‖-(Real.exp (-t) * ((t ^ 2 + 8 * t + 11) / (t ^ 3 + 9 * t ^ 2 + 18 * t + 6)))‖ ≤
      Real.exp (-t)
    rw [norm_neg, Real.norm_of_nonneg (by positivity)]
    calc Real.exp (-t) * ((t ^ 2 + 8 * t + 11) / (t ^ 3 + 9 * t ^ 2 + 18 * t + 6))
        ≤ Real.exp (-t) * 1 := mul_le_mul_of_nonneg_left hR (Real.exp_pos _).le
      _ = Real.exp (-t) := mul_one _
  have hint := integrableOn_Ioi_deriv_of_nonneg' hderiv hpos htend
  have hval := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos htend
  have hle : ∫ t in Ioi z, g' t ≤ expInt z := by
    refine setIntegral_mono_on hint (integrableOn_exp_div hz) measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := hz.trans ht
    show Real.exp (-t) * (1 / t - 36 / (t * (t ^ 3 + 9 * t ^ 2 + 18 * t + 6) ^ 2)) ≤
      Real.exp (-t) / t
    have he := (Real.exp_pos (-t)).le
    calc Real.exp (-t) * (1 / t - 36 / (t * (t ^ 3 + 9 * t ^ 2 + 18 * t + 6) ^ 2))
        ≤ Real.exp (-t) * (1 / t) :=
          mul_le_mul_of_nonneg_left (by linarith [(hsmall t ht0).2]) he
      _ = Real.exp (-t) / t := by ring
  rw [hval] at hle
  have hg0 : (0 : ℝ) - g z =
      Real.exp (-z) * ((z ^ 2 + 8 * z + 11) / (z ^ 3 + 9 * z ^ 2 + 18 * z + 6)) := by
    show (0 : ℝ) - -(Real.exp (-z) * ((z ^ 2 + 8 * z + 11) / (z ^ 3 + 9 * z ^ 2 + 18 * z + 6))) = _
    ring
  rw [hg0] at hle
  exact hle

end CMPoints
