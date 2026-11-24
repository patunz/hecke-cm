import HeckeCM.ThetaSeries
import HeckeCM.ExpLogIntegral

/-!
# Non-vanishing of `∫_A^∞ log(t / A) θ(t) dt`

Mathlib only. For `θ(t) = ∑ a n e^{−2π n t}`:

* `hasSum_integral_log_mul_thetaSeries`: the integral is the sum of the
  integrals of the terms, `∑ a n · J(2π n)` with
  `J(p) = ∫_A^∞ log(t / A) e^{−p t} dt`;
* `norm_integral_log_mul_thetaSeries_sub_le`: if `a 1 = 1`, `a n = 0` for
  `2 ≤ n ≤ 8` and `‖a n‖ ≤ (7/6) n`, the integral differs from its first term
  `J(2π)` by at most `(7/54) / (A (2π)²) · r⁹ / (1 − r)`, `r = e^{−2π A}`;
* `integral_log_mul_thetaSeries_ne_zero`: hence it does not vanish as soon as
  `(7/54) e^{−9x} < x · log 2 · (e^{−2x} + e^{−4x}) (1 − e^{−x})`, `x = 2π A`;
* `numeric_ineq`: that inequality holds for `0.2221 ≤ x ≤ 0.2222`.
-/

set_option autoImplicit false

noncomputable section

open Real Complex MeasureTheory Set Filter
open scoped Topology

namespace CMPoints

/-- `J(A, p) = ∫_A^∞ log(t / A) e^{−p t} dt`. -/
def logExpIntegral (A p : ℝ) : ℝ := ∫ t in Ioi A, Real.log (t / A) * Real.exp (-p * t)

lemma exp_neg_lt_one {y : ℝ} (hy : 0 < y) : Real.exp (-y) < 1 := by
  have := Real.exp_lt_exp.2 (neg_lt_zero.2 hy)
  rwa [Real.exp_zero] at this

lemma logExpIntegral_nonneg {A : ℝ} (hA : 0 < A) (p : ℝ) : 0 ≤ logExpIntegral A p :=
  setIntegral_nonneg measurableSet_Ioi fun t ht =>
    mul_nonneg (log_div_bounds hA (show A < t from ht)).1 (Real.exp_pos _).le

section

variable {a : ℕ → ℂ} {c A K : ℝ}

/-- `‖a n‖ · J(2π n) ≤ K / (A (2π)²) · rⁿ`, `r = e^{−2π A}`, if `‖a n‖ ≤ K n`. -/
lemma norm_mul_logExpIntegral_le (hA : 0 < A) (hK : 0 ≤ K) (hbound : ∀ n : ℕ, ‖a n‖ ≤ K * n)
    {n : ℕ} (hn : 0 < n) :
    ‖a n‖ * logExpIntegral A (2 * π * n) ≤
      K / (A * (2 * π) ^ 2) / n * Real.exp (-(2 * π * A)) ^ n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : (0 : ℝ) < 2 * π * n := by positivity
  have hJ := integral_log_mul_exp_le hA hp
  have hexp : Real.exp (-(2 * π * n) * A) = Real.exp (-(2 * π * A)) ^ n := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hJ' : logExpIntegral A (2 * π * n) ≤
      Real.exp (-(2 * π * A)) ^ n / (A * (2 * π * n) ^ 2) := by
    rw [← hexp]
    exact hJ
  have hr0 : 0 ≤ Real.exp (-(2 * π * A)) ^ n := by positivity
  calc ‖a n‖ * logExpIntegral A (2 * π * n)
      ≤ K * n * (Real.exp (-(2 * π * A)) ^ n / (A * (2 * π * n) ^ 2)) :=
        mul_le_mul (hbound n) hJ' (logExpIntegral_nonneg hA _) (by positivity)
    _ = K / (A * (2 * π) ^ 2) / n * Real.exp (-(2 * π * A)) ^ n := by
        field_simp

/-- **Term-by-term integration.** -/
theorem hasSum_integral_log_mul_thetaSeries (ha0 : a 0 = 0) (hA : 0 < A) (hK : 0 ≤ K)
    (hbound : ∀ n : ℕ, ‖a n‖ ≤ K * n) :
    HasSum (fun n : ℕ => a n * (logExpIntegral A (2 * π * n) : ℂ))
      (∫ t in Ioi A, (Real.log (t / A) : ℂ) * thetaSeries a t) := by
  set F : ℕ → ℝ → ℂ := fun n t =>
    a n * ((Real.log (t / A) * Real.exp (-(2 * π * n) * t) : ℝ) : ℂ) with hF
  have hr1 : Real.exp (-(2 * π * A)) < 1 := exp_neg_lt_one (by positivity)
  have hr0 : 0 ≤ Real.exp (-(2 * π * A)) := (Real.exp_pos _).le
  have hint : ∀ n : ℕ, Integrable (F n) (volume.restrict (Ioi A)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF, ha0]
    · have hp : (0 : ℝ) < 2 * π * n := by
        have : (0 : ℝ) < n := by exact_mod_cast hn
        positivity
      exact (Integrable.ofReal (integrableOn_log_mul_exp hA hp)).const_mul (a n)
  have hnorm : ∀ n : ℕ, ∫ t in Ioi A, ‖F n t‖ = ‖a n‖ * logExpIntegral A (2 * π * n) := by
    intro n
    rw [logExpIntegral, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have h0 : 0 ≤ Real.log (t / A) * Real.exp (-(2 * π * n) * t) :=
      mul_nonneg (log_div_bounds hA (show A < t from ht)).1 (Real.exp_pos _).le
    simp only [hF, norm_mul, Complex.norm_real, Real.norm_of_nonneg h0]
  have hsumm : Summable fun n : ℕ => ∫ t in Ioi A, ‖F n t‖ := by
    simp only [hnorm]
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (norm_nonneg _) (logExpIntegral_nonneg hA _)) (fun n => ?_)
      ((summable_geometric_of_lt_one hr0 hr1).mul_left (K / (A * (2 * π) ^ 2)))
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [ha0, norm_zero, zero_mul, pow_zero, mul_one]
      positivity
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hC : 0 ≤ K / (A * (2 * π) ^ 2) := by positivity
      refine (norm_mul_logExpIntegral_le hA hK hbound hn).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact div_le_self hC hn1
  have key := hasSum_integral_of_summable_integral_norm hint hsumm
  have e1 : (fun n : ℕ => ∫ t in Ioi A, F n t) =
      fun n : ℕ => a n * (logExpIntegral A (2 * π * n) : ℂ) := by
    funext n
    simp only [hF]
    rw [integral_const_mul, logExpIntegral]
    congr 1
    exact integral_ofReal
  have e2 : ∫ t in Ioi A, ∑' n : ℕ, F n t =
      ∫ t in Ioi A, (Real.log (t / A) : ℂ) * thetaSeries a t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    show ∑' n : ℕ, F n t = (Real.log (t / A) : ℂ) * thetaSeries a t
    rw [thetaSeries, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [hF]
    push_cast
    ring
  rw [e1, e2] at key
  exact key

/-- **The integral is close to its first term.** -/
theorem norm_integral_log_mul_thetaSeries_sub_le (ha0 : a 0 = 0) (ha1 : a 1 = 1)
    (hzero : ∀ n : ℕ, 2 ≤ n → n ≤ 8 → a n = 0) (hbound : ∀ n : ℕ, ‖a n‖ ≤ 7 / 6 * n)
    (hA : 0 < A) :
    ‖(∫ t in Ioi A, (Real.log (t / A) : ℂ) * thetaSeries a t) - (logExpIntegral A (2 * π) : ℂ)‖ ≤
      7 / 54 / (A * (2 * π) ^ 2) *
        (Real.exp (-(2 * π * A)) ^ 9 / (1 - Real.exp (-(2 * π * A)))) := by
  set r : ℝ := Real.exp (-(2 * π * A)) with hr
  have hr1 : r < 1 := exp_neg_lt_one (by positivity)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  set C9 : ℝ := 7 / 54 / (A * (2 * π) ^ 2) with hC9
  have hC90 : 0 ≤ C9 := by positivity
  set f : ℕ → ℂ := fun n => a n * (logExpIntegral A (2 * π * n) : ℂ) with hf
  have hs := hasSum_integral_log_mul_thetaSeries (K := 7 / 6) ha0 hA (by norm_num) hbound
  have hf1 : f 1 = (logExpIntegral A (2 * π) : ℂ) := by
    simp [hf, ha1]
  have hsplit : ∑' n : ℕ, f n = f 1 + ∑' n : ℕ, (if n = 1 then (0 : ℂ) else f n) :=
    hs.summable.tsum_eq_add_tsum_ite 1
  have hI : ∑' n : ℕ, f n = ∫ t in Ioi A, (Real.log (t / A) : ℂ) * thetaSeries a t := hs.tsum_eq
  rw [hI, hf1] at hsplit
  set g : ℕ → ℝ := fun n => if n < 9 then 0 else C9 * r ^ n with hg
  have hgle : ∀ n : ℕ, ‖(if n = 1 then (0 : ℂ) else f n)‖ ≤ g n := by
    intro n
    by_cases h9 : n < 9
    · have : (if n = 1 then (0 : ℂ) else f n) = 0 := by
        by_cases h1 : n = 1
        · simp [h1]
        · rw [if_neg h1]
          rcases Nat.eq_zero_or_pos n with rfl | hn
          · simp [hf, ha0]
          · simp [hf, hzero n (by omega) (by omega)]
      rw [this, norm_zero]
      simp [hg, h9]
    · have hn9 : 9 ≤ n := not_lt.1 h9
      have hn : 0 < n := by omega
      have hn9' : (9 : ℝ) ≤ n := by exact_mod_cast hn9
      rw [if_neg (by omega : n ≠ 1)]
      simp only [hg, if_neg h9, hf, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (logExpIntegral_nonneg hA _)]
      refine (norm_mul_logExpIntegral_le hA (by norm_num) hbound hn).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hpos : 0 < A * (2 * π) ^ 2 := by positivity
      have e : 7 / 6 / (A * (2 * π) ^ 2) / (n : ℝ) = 7 / 6 / (n : ℝ) / (A * (2 * π) ^ 2) := by
        ring
      rw [hC9, e]
      refine div_le_div_of_nonneg_right ?_ hpos.le
      rw [div_le_iff₀ hn0]
      linarith
  have hgsum : Summable g := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      ((summable_geometric_of_lt_one hr0 hr1).mul_left C9)
    · simp only [hg]
      split_ifs
      · exact le_rfl
      · positivity
    · simp only [hg]
      split_ifs
      · positivity
      · exact le_rfl
  have hnormsum : Summable fun n : ℕ => ‖(if n = 1 then (0 : ℂ) else f n)‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hgle hgsum
  have hgval : ∑' n : ℕ, g n = C9 * (r ^ 9 / (1 - r)) := by
    rw [← hgsum.sum_add_tsum_nat_add 9]
    have h0 : ∑ i ∈ Finset.range 9, g i = 0 :=
      Finset.sum_eq_zero fun i hi => by
        simp [hg, Finset.mem_range.1 hi]
    have h1 : ∀ i : ℕ, g (i + 9) = C9 * r ^ 9 * r ^ i := by
      intro i
      simp only [hg, if_neg (by omega : ¬ i + 9 < 9)]
      rw [pow_add]
      ring
    rw [h0, zero_add]
    simp only [h1]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
    field_simp
  calc ‖(∫ t in Ioi A, (Real.log (t / A) : ℂ) * thetaSeries a t) - (logExpIntegral A (2 * π) : ℂ)‖
      = ‖∑' n : ℕ, (if n = 1 then (0 : ℂ) else f n)‖ := by
        rw [hsplit]
        ring_nf
    _ ≤ ∑' n : ℕ, ‖(if n = 1 then (0 : ℂ) else f n)‖ := norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' n : ℕ, g n := hnormsum.tsum_le_tsum hgle hgsum
    _ = _ := hgval

/-- **Non-vanishing.** -/
theorem integral_log_mul_thetaSeries_ne_zero (ha0 : a 0 = 0) (ha1 : a 1 = 1)
    (hzero : ∀ n : ℕ, 2 ≤ n → n ≤ 8 → a n = 0) (hbound : ∀ n : ℕ, ‖a n‖ ≤ 7 / 6 * n)
    (hA : 0 < A)
    (hx : 7 / 54 * Real.exp (-(9 * (2 * π * A))) <
      2 * π * A * Real.log 2 *
        (Real.exp (-(2 * (2 * π * A))) + Real.exp (-(4 * (2 * π * A)))) *
          (1 - Real.exp (-(2 * π * A)))) :
    ∫ t in Ioi A, (Real.log (t / A) : ℂ) * thetaSeries a t ≠ 0 := by
  intro h0
  have hle := norm_integral_log_mul_thetaSeries_sub_le ha0 ha1 hzero hbound hA
  rw [h0, zero_sub, norm_neg, Complex.norm_real,
    Real.norm_of_nonneg (logExpIntegral_nonneg hA _)] at hle
  have hlow := le_integral_log_mul_exp hA (p := 2 * π) (by positivity)
  have hr1 : Real.exp (-(2 * π * A)) < 1 := exp_neg_lt_one (by positivity)
  have h1r : 0 < 1 - Real.exp (-(2 * π * A)) := by linarith
  have hden : 0 < A * (2 * π) ^ 2 * (1 - Real.exp (-(2 * π * A))) := by positivity
  have e9 : Real.exp (-(2 * π * A)) ^ 9 = Real.exp (-(9 * (2 * π * A))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have e2 : Real.exp (-(2 * π) * (2 * A)) = Real.exp (-(2 * (2 * π * A))) := by
    congr 1
    ring
  have e4 : Real.exp (-(2 * π) * (4 * A)) = Real.exp (-(4 * (2 * π * A))) := by
    congr 1
    ring
  rw [e2, e4] at hlow
  have hchain := hlow.trans (show logExpIntegral A (2 * π) ≤ _ from hle)
  rw [e9] at hchain
  have hR : 7 / 54 / (A * (2 * π) ^ 2) *
      (Real.exp (-(9 * (2 * π * A))) / (1 - Real.exp (-(2 * π * A)))) =
      7 / 54 * Real.exp (-(9 * (2 * π * A))) /
        (A * (2 * π) ^ 2 * (1 - Real.exp (-(2 * π * A)))) := by
    field_simp
  have hL : Real.log 2 *
      (Real.exp (-(2 * (2 * π * A))) + Real.exp (-(4 * (2 * π * A)))) / (2 * π) =
      2 * π * A * Real.log 2 *
        (Real.exp (-(2 * (2 * π * A))) + Real.exp (-(4 * (2 * π * A)))) *
          (1 - Real.exp (-(2 * π * A))) /
        (A * (2 * π) ^ 2 * (1 - Real.exp (-(2 * π * A)))) := by
    field_simp
  rw [hR, hL, div_le_div_iff_of_pos_right hden] at hchain
  linarith

end

/-- The numerical inequality, for `0.2221 ≤ x ≤ 0.2222`. -/
theorem numeric_ineq {x : ℝ} (h1 : 0.2221 ≤ x) (h2 : x ≤ 0.2222) :
    7 / 54 * Real.exp (-(9 * x)) <
      x * Real.log 2 * (Real.exp (-(2 * x)) + Real.exp (-(4 * x))) * (1 - Real.exp (-x)) := by
  have hlog : (0.6931 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  -- `e^{−9x} ≤ (1 + u + u²/2)^{−4}`, `u = 9x/4`
  have hu : (0 : ℝ) ≤ 9 * x / 4 := by linarith
  have hq := Real.quadratic_le_exp_of_nonneg hu
  have hE9 : Real.exp (-(9 * x)) ≤ (1 / (1 + 9 * x / 4 + (9 * x / 4) ^ 2 / 2)) ^ 4 := by
    have hpos : 0 < 1 + 9 * x / 4 + (9 * x / 4) ^ 2 / 2 := by positivity
    have h : Real.exp (-(9 * x / 4)) ≤ 1 / (1 + 9 * x / 4 + (9 * x / 4) ^ 2 / 2) := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le hpos hq
    have e : Real.exp (-(9 * x)) = Real.exp (-(9 * x / 4)) ^ 4 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [e]
    exact pow_le_pow_left₀ (Real.exp_pos _).le h 4
  have hE9' : Real.exp (-(9 * x)) ≤ 0.1437 := by
    refine hE9.trans ?_
    have hb : 1 / (1 + 9 * x / 4 + (9 * x / 4) ^ 2 / 2) ≤ 1 / 1.6245 := by
      refine one_div_le_one_div_of_le (by norm_num) ?_
      nlinarith
    refine (pow_le_pow_left₀ (by positivity) hb 4).trans ?_
    norm_num
  -- `e^{−t} ≥ (1 − t/4)⁴`
  have hlow : ∀ t : ℝ, 0 ≤ t → t ≤ 4 → (1 - t / 4) ^ 4 ≤ Real.exp (-t) := by
    intro t ht0 ht4
    have h := Real.add_one_le_exp (-(t / 4))
    have h' : 1 - t / 4 ≤ Real.exp (-(t / 4)) := by linarith
    have e : Real.exp (-t) = Real.exp (-(t / 4)) ^ 4 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [e]
    exact pow_le_pow_left₀ (by linarith) h' 4
  have hE2 : (0.6243 : ℝ) ≤ Real.exp (-(2 * x)) := by
    refine le_trans ?_ (hlow (2 * x) (by linarith) (by linarith))
    have : (0.8889 : ℝ) ≤ 1 - 2 * x / 4 := by linarith
    refine le_trans ?_ (pow_le_pow_left₀ (by norm_num) this 4)
    norm_num
  have hE4 : (0.3659 : ℝ) ≤ Real.exp (-(4 * x)) := by
    refine le_trans ?_ (hlow (4 * x) (by linarith) (by linarith))
    have : (0.7778 : ℝ) ≤ 1 - 4 * x / 4 := by linarith
    refine le_trans ?_ (pow_le_pow_left₀ (by norm_num) this 4)
    norm_num
  -- `1 − e^{−x} ≥ x / (1 + x)`
  have hE1 : (0.1817 : ℝ) ≤ 1 - Real.exp (-x) := by
    have h := Real.add_one_le_exp x
    have hpos : (0 : ℝ) < x + 1 := by linarith
    have h' : Real.exp (-x) ≤ 1 / (x + 1) := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le hpos h
    have h'' : 1 / (x + 1) ≤ 1 / 1.2221 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    have : (1 : ℝ) / 1.2221 ≤ 0.8183 := by norm_num
    linarith
  have hL : 7 / 54 * Real.exp (-(9 * x)) ≤ 0.01863 := by
    have : 7 / 54 * Real.exp (-(9 * x)) ≤ 7 / 54 * 0.1437 :=
      mul_le_mul_of_nonneg_left hE9' (by norm_num)
    refine this.trans ?_
    norm_num
  have hR : (0.0276 : ℝ) ≤
      x * Real.log 2 * (Real.exp (-(2 * x)) + Real.exp (-(4 * x))) * (1 - Real.exp (-x)) := by
    have hsum : (0.9902 : ℝ) ≤ Real.exp (-(2 * x)) + Real.exp (-(4 * x)) := by linarith
    have hxl : (0.2221 * 0.6931 : ℝ) ≤ x * Real.log 2 :=
      mul_le_mul h1 hlog.le (by norm_num) (by linarith)
    have h3 : (0.2221 * 0.6931 * 0.9902 : ℝ) ≤
        x * Real.log 2 * (Real.exp (-(2 * x)) + Real.exp (-(4 * x))) :=
      mul_le_mul hxl hsum (by norm_num) (by positivity)
    have h4 : (0.2221 * 0.6931 * 0.9902 * 0.1817 : ℝ) ≤
        x * Real.log 2 * (Real.exp (-(2 * x)) + Real.exp (-(4 * x))) * (1 - Real.exp (-x)) :=
      mul_le_mul h3 hE1 (by norm_num) (by positivity)
    refine le_trans ?_ h4
    norm_num
  linarith

end CMPoints
