import HeckeCM.ExpIntegral

/-!
# Numerical bounds for the exponential integral

Mathlib only. For `0.22214 ≤ x ≤ 0.22215` (the interval containing
`2π / √800`):

* `expInt_bounds_one`: `1.137466 ≤ expInt x ≤ 1.137934`;
* `expInt_bounds_nine`, `_thirteen`, `_seventeen`: two-sided bounds for
  `expInt (9x)`, `expInt (13x)`, `expInt (17x)`;
* `expInt_le_twentyNine`, `_thirtySeven`, `_fortyOne`: upper bounds further out;
* `tail_bound`: `(7/3) / (49x) · e^{−49x} / (1 − e^{−x}) ≤ 0.0000536`.

Method: `expInt` is decreasing; at `z ≈ 2, 2.9, 3.8` it is squeezed between
`e^{−z}` times two rational functions, with `e^{−z}` between two Taylor
polynomials; `expInt x = ∫_x^{9x} e^{−t}/t dt + expInt (9x)` and the integral
is `log 9` plus a polynomial expression. All numerical steps are rational
arithmetic, done by `norm_num`.
-/

set_option autoImplicit false

noncomputable section

open Real MeasureTheory Set
open scoped Nat

namespace CMPoints

/-! ## Generic steps -/

/-- `expInt` is decreasing on the positive reals. -/
lemma expInt_anti {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : expInt b ≤ expInt a := by
  rw [expInt_eq_add ha hab]
  have : 0 ≤ ∫ t in a..b, Real.exp (-t) / t :=
    intervalIntegral.integral_nonneg hab fun t ht =>
      div_nonneg (Real.exp_pos _).le (ha.trans_le ht.1).le
  linarith

lemma expInt_le_taylor {n : ℕ} (hn : Even n) {z : ℝ} (hz : 0 < z) :
    expInt z ≤ expTaylor n z * ((z ^ 2 + 5 * z + 2) / (z ^ 3 + 6 * z ^ 2 + 6 * z)) :=
  (expInt_le_upper hz).trans
    (mul_le_mul_of_nonneg_right (exp_neg_le_expTaylor hn hz.le) (by positivity))

lemma taylor_le_expInt {n : ℕ} (hn : Odd n) {z : ℝ} (hz : 0 < z) :
    expTaylor n z * ((z ^ 2 + 8 * z + 11) / (z ^ 3 + 9 * z ^ 2 + 18 * z + 6)) ≤ expInt z :=
  (mul_le_mul_of_nonneg_right (expTaylor_le_exp_neg hn hz.le) (by positivity)).trans
    (lower_le_expInt hz)

/-! ## `log 3` -/

/-- `1.0986122 < log 3 < 1.0986124`. -/
lemma log_three_bounds : (1.0986122 : ℝ) < Real.log 3 ∧ Real.log 3 < 1.0986124 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (1 / 3 : ℝ)) (by norm_num) 16
  have hlog : Real.log (1 - 1 / 3) = Real.log 2 - Real.log 3 := by
    rw [show (1 - 1 / 3 : ℝ) = 2 / 3 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [hlog] at h
  have he : |(1 / 3 : ℝ)| ^ (16 + 1) / (1 - |(1 / 3 : ℝ)|) ≤ 0.00000002 := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 3)]
    norm_num
  have hs1 : (0.40546510 : ℝ) ≤ ∑ i ∈ Finset.range 16, (1 / 3 : ℝ) ^ (i + 1) / ((i : ℝ) + 1) := by
    norm_num [Finset.sum_range_succ]
  have hs2 : ∑ i ∈ Finset.range 16, (1 / 3 : ℝ) ^ (i + 1) / ((i : ℝ) + 1) ≤ (0.40546511 : ℝ) := by
    norm_num [Finset.sum_range_succ]
  have h2a := Real.log_two_gt_d9
  have h2b := Real.log_two_lt_d9
  obtain ⟨h1, h2⟩ := abs_le.1 (h.trans he)
  constructor <;> linarith

/-! ## Numerical evaluations (rational arithmetic) -/

lemma num_nine_upper :
    expTaylor 16 1.99926 * ((1.99926 ^ 2 + 5 * 1.99926 + 2) /
      (1.99926 ^ 3 + 6 * 1.99926 ^ 2 + 6 * 1.99926)) ≤ (0.04926356 : ℝ) := by
  norm_num [expTaylor, Finset.sum_range_succ, Nat.factorial]

lemma num_nine_lower :
    (0.04882743 : ℝ) ≤ expTaylor 17 1.99935 * ((1.99935 ^ 2 + 8 * 1.99935 + 11) /
      (1.99935 ^ 3 + 9 * 1.99935 ^ 2 + 18 * 1.99935 + 6)) := by
  norm_num [expTaylor, Finset.sum_range_succ, Nat.factorial]

lemma num_int_upper :
    expTaylorInt 14 1.99926 - expTaylorInt 14 0.22214 ≤ (-1.10855543 : ℝ) := by
  norm_num [expTaylorInt, Finset.sum_range_succ, Nat.factorial]

lemma num_int_lower :
    (-1.10858541 : ℝ) ≤ expTaylorInt 13 1.99935 - expTaylorInt 13 0.22215 := by
  norm_num [expTaylorInt, Finset.sum_range_succ, Nat.factorial]

lemma num_thirteen_upper :
    expTaylor 22 2.88782 * ((2.88782 ^ 2 + 5 * 2.88782 + 2) /
      (2.88782 ^ 3 + 6 * 2.88782 ^ 2 + 6 * 2.88782)) ≤ (0.015092 : ℝ) := by
  norm_num [expTaylor, Finset.sum_range_succ, Nat.factorial]

lemma num_thirteen_lower :
    (0.015042 : ℝ) ≤ expTaylor 23 2.88795 * ((2.88795 ^ 2 + 8 * 2.88795 + 11) /
      (2.88795 ^ 3 + 9 * 2.88795 ^ 2 + 18 * 2.88795 + 6)) := by
  norm_num [expTaylor, Finset.sum_range_succ, Nat.factorial]

lemma num_seventeen_upper :
    expTaylor 26 3.77638 * ((3.77638 ^ 2 + 5 * 3.77638 + 2) /
      (3.77638 ^ 3 + 6 * 3.77638 ^ 2 + 6 * 3.77638)) ≤ (0.0049665 : ℝ) := by
  norm_num [expTaylor, Finset.sum_range_succ, Nat.factorial]

lemma num_seventeen_lower :
    (0.0049588 : ℝ) ≤ expTaylor 27 3.77655 * ((3.77655 ^ 2 + 8 * 3.77655 + 11) /
      (3.77655 ^ 3 + 9 * 3.77655 ^ 2 + 18 * 3.77655 + 6)) := by
  norm_num [expTaylor, Finset.sum_range_succ, Nat.factorial]

/-- `e^{−k} < 1 / c` as soon as `c < 2.7182818283^k`. -/
lemma exp_neg_nat_lt {k : ℕ} {c : ℝ} (hc0 : 0 < c) (hc : c < (2.7182818283 : ℝ) ^ k) :
    Real.exp (-(k : ℝ)) < 1 / c := by
  have h1 : (2.7182818283 : ℝ) ^ k ≤ Real.exp 1 ^ k :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le k
  have h2 : Real.exp (k : ℝ) = Real.exp 1 ^ k := by
    rw [← Real.exp_nat_mul, mul_one]
  have h3 : c < Real.exp (k : ℝ) := by
    rw [h2]
    exact hc.trans_le h1
  rw [Real.exp_neg, ← one_div]
  exact one_div_lt_one_div_of_lt hc0 h3

/-! ## The bounds -/

section

variable {x : ℝ}

/-- `0.04882743 ≤ expInt (9x) ≤ 0.04926356`. -/
theorem expInt_bounds_nine (h1 : 0.22214 ≤ x) (h2 : x ≤ 0.22215) :
    (0.04882743 : ℝ) ≤ expInt (9 * x) ∧ expInt (9 * x) ≤ 0.04926356 := by
  constructor
  · have hle : 9 * x ≤ (1.99935 : ℝ) := by linarith
    exact num_nine_lower.trans ((taylor_le_expInt (by decide) (by norm_num)).trans
      (expInt_anti (by linarith) hle))
  · have hle : (1.99926 : ℝ) ≤ 9 * x := by linarith
    exact (expInt_anti (by norm_num) hle).trans
      ((expInt_le_taylor (by decide) (by norm_num)).trans num_nine_upper)

/-- `1.137466 ≤ expInt x ≤ 1.137934`. -/
theorem expInt_bounds_one (h1 : 0.22214 ≤ x) (h2 : x ≤ 0.22215) :
    (1.137466 : ℝ) ≤ expInt x ∧ expInt x ≤ 1.137934 := by
  obtain ⟨hl3, hu3⟩ := log_three_bounds
  have hlog9 : ∀ a b : ℝ, 0 < a → b = 9 * a → Real.log b - Real.log a = 2 * Real.log 3 := by
    intro a b ha hb
    rw [hb, Real.log_mul (by norm_num) ha.ne', show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  constructor
  · -- lower bound, at `0.22215`
    have hx : (0 : ℝ) < x := by linarith
    have hstep := expInt_anti hx h2
    have hsplit := expInt_eq_add (a := 0.22215) (b := 1.99935) (by norm_num) (by norm_num)
    have hint := le_integral_exp_div (n := 13) (by decide) (a := 0.22215) (b := 1.99935)
      (by norm_num) (by norm_num)
    have hl := hlog9 0.22215 1.99935 (by norm_num) (by norm_num)
    have h9 := num_nine_lower.trans (taylor_le_expInt (n := 17) (by decide)
      (z := 1.99935) (by norm_num))
    have hnum := num_int_lower
    linarith
  · -- upper bound, at `0.22214`
    have hstep := expInt_anti (a := 0.22214) (by norm_num) h1
    have hsplit := expInt_eq_add (a := 0.22214) (b := 1.99926) (by norm_num) (by norm_num)
    have hint := integral_exp_div_le (n := 14) (by decide) (a := 0.22214) (b := 1.99926)
      (by norm_num) (by norm_num)
    have hl := hlog9 0.22214 1.99926 (by norm_num) (by norm_num)
    have h9 := (expInt_le_taylor (n := 16) (by decide) (z := 1.99926) (by norm_num)).trans
      num_nine_upper
    have hnum := num_int_upper
    linarith

/-- `0.015042 ≤ expInt (13x) ≤ 0.015092`. -/
theorem expInt_bounds_thirteen (h1 : 0.22214 ≤ x) (h2 : x ≤ 0.22215) :
    (0.015042 : ℝ) ≤ expInt (13 * x) ∧ expInt (13 * x) ≤ 0.015092 := by
  constructor
  · have hle : 13 * x ≤ (2.88795 : ℝ) := by linarith
    exact num_thirteen_lower.trans ((taylor_le_expInt (by decide) (by norm_num)).trans
      (expInt_anti (by linarith) hle))
  · have hle : (2.88782 : ℝ) ≤ 13 * x := by linarith
    exact (expInt_anti (by norm_num) hle).trans
      ((expInt_le_taylor (by decide) (by norm_num)).trans num_thirteen_upper)

/-- `0.0049588 ≤ expInt (17x) ≤ 0.0049665`. -/
theorem expInt_bounds_seventeen (h1 : 0.22214 ≤ x) (h2 : x ≤ 0.22215) :
    (0.0049588 : ℝ) ≤ expInt (17 * x) ∧ expInt (17 * x) ≤ 0.0049665 := by
  constructor
  · have hle : 17 * x ≤ (3.77655 : ℝ) := by linarith
    exact num_seventeen_lower.trans ((taylor_le_expInt (by decide) (by norm_num)).trans
      (expInt_anti (by linarith) hle))
  · have hle : (3.77638 : ℝ) ≤ 17 * x := by linarith
    exact (expInt_anti (by norm_num) hle).trans
      ((expInt_le_taylor (by decide) (by norm_num)).trans num_seventeen_upper)

/-- A crude bound: `expInt z ≤ (1/c) / m` if `m ≤ z`, `k ≤ z` and `c < 2.7182818283^k`. -/
lemma expInt_le_crude {z m c : ℝ} {k : ℕ} (hm : 0 < m) (hmz : m ≤ z) (hkz : (k : ℝ) ≤ z)
    (hc0 : 0 < c) (hc : c < (2.7182818283 : ℝ) ^ k) : expInt z ≤ 1 / c / m := by
  have hz : 0 < z := hm.trans_le hmz
  have h1 : Real.exp (-z) ≤ Real.exp (-(k : ℝ)) := Real.exp_le_exp.2 (by linarith)
  have h2 := (exp_neg_nat_lt hc0 hc).le
  calc expInt z ≤ Real.exp (-z) / z := expInt_le hz
    _ ≤ (1 / c) / z := div_le_div_of_nonneg_right (h1.trans h2) hz.le
    _ ≤ 1 / c / m := div_le_div_of_nonneg_left (by positivity) hm hmz

theorem expInt_le_twentyNine (h1 : 0.22214 ≤ x) : expInt (29 * x) ≤ 0.000386 := by
  have h := expInt_le_crude (z := 29 * x) (m := 6.44) (c := 403) (k := 6) (by norm_num)
    (by linarith) (by push_cast; linarith) (by norm_num) (by norm_num)
  refine h.trans ?_
  norm_num

theorem expInt_le_thirtySeven (h1 : 0.22214 ≤ x) : expInt (37 * x) ≤ 0.0000409 := by
  have h := expInt_le_crude (z := 37 * x) (m := 8.219) (c := 2980) (k := 8) (by norm_num)
    (by linarith) (by push_cast; linarith) (by norm_num) (by norm_num)
  refine h.trans ?_
  norm_num

theorem expInt_le_fortyOne (h1 : 0.22214 ≤ x) : expInt (41 * x) ≤ 0.0000136 := by
  have h := expInt_le_crude (z := 41 * x) (m := 9.107) (c := 8103) (k := 9) (by norm_num)
    (by linarith) (by push_cast; linarith) (by norm_num) (by norm_num)
  refine h.trans ?_
  norm_num

/-- The tail constant. -/
theorem tail_bound (h1 : 0.22214 ≤ x) (h2 : x ≤ 0.22215) :
    7 / 3 / (49 * x) * (Real.exp (-x) ^ 49 / (1 - Real.exp (-x))) ≤ 0.0000536 := by
  have hx : 0 < x := by linarith
  -- `e^{−49x} ≤ e^{−10} < 1/22026`
  have hpow : Real.exp (-x) ^ 49 = Real.exp (-(49 * x)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h10 : Real.exp (-(49 * x)) ≤ 1 / 22026 := by
    have ha : Real.exp (-(49 * x)) ≤ Real.exp (-((10 : ℕ) : ℝ)) :=
      Real.exp_le_exp.2 (by push_cast; linarith)
    exact ha.trans (exp_neg_nat_lt (k := 10) (c := 22026) (by norm_num) (by norm_num)).le
  -- `1 − e^{−x} ≥ x / (1 + x)`
  have hden : x / (1 + x) ≤ 1 - Real.exp (-x) := by
    have h := Real.add_one_le_exp x
    have hpos : (0 : ℝ) < x + 1 := by linarith
    have h' : Real.exp (-x) ≤ 1 / (x + 1) := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le hpos h
    have e : 1 - 1 / (x + 1) = x / (1 + x) := by
      field_simp
      ring
    linarith
  have hdpos : 0 < x / (1 + x) := by positivity
  have hfrac : Real.exp (-x) ^ 49 / (1 - Real.exp (-x)) ≤ (1 / 22026) / (x / (1 + x)) := by
    rw [hpow]
    exact (div_le_div_of_nonneg_right h10 (hdpos.le.trans hden)).trans
      (div_le_div_of_nonneg_left (by norm_num) hdpos hden)
  have hpre : 0 ≤ 7 / 3 / (49 * x) := by positivity
  calc 7 / 3 / (49 * x) * (Real.exp (-x) ^ 49 / (1 - Real.exp (-x)))
      ≤ 7 / 3 / (49 * x) * ((1 / 22026) / (x / (1 + x))) :=
        mul_le_mul_of_nonneg_left hfrac hpre
    _ = 7 / 3 / 49 / 22026 * ((1 + x) / x ^ 2) := by
        field_simp
    _ ≤ 7 / 3 / 49 / 22026 * (1.22215 / 0.22214 ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact (div_le_div_of_nonneg_right (by linarith : 1 + x ≤ 1.22215) (by positivity)).trans
          (div_le_div_of_nonneg_left (by norm_num) (by norm_num)
            (pow_le_pow_left₀ (by norm_num) h1 2))
    _ ≤ 0.0000536 := by norm_num

end

end CMPoints
