import HeckeCM.ExpIntegralNumerics

/-!
# An interval for `4π · ∫_A^∞ log(t / A) θ(t) dt`

Mathlib only. Let `θ(t) = ∑ a n e^{−2π n t}` with real coefficients such that

* `a n` is given by `fiveTable` for `n < 49` (the only nonzero values are at
  `n = 1, 9, 13, 17, 29, 37, 41`),
* `‖a n‖ ≤ (7/6) n` for every `n`,

and let `A > 0` with `0.22214 ≤ 2π A ≤ 0.22215`. Then
`π · 4 · ∫_A^∞ log(t / A) θ(t) dt` is a real number in `(2.22, 2.23)`
(`integral_value_bounds`).
-/

set_option autoImplicit false

noncomputable section

open Real Complex MeasureTheory Set
open scoped Topology

namespace CMPoints

/-- The coefficients `a n` of `y² = x³ − 25x` for `n < 49`. -/
def fiveTable (n : ℕ) : ℝ :=
  if n = 1 then 1 else if n = 9 then -3 else if n = 13 then -6 else if n = 17 then -2
  else if n = 29 then -10 else if n = 37 then 2 else if n = 41 then 10 else 0

theorem integral_value_bounds {a : ℕ → ℂ} {α : ℕ → ℝ} (hα : ∀ n, a n = (α n : ℂ))
    (ha0 : a 0 = 0) (htab : ∀ n, n < 49 → α n = fiveTable n)
    (hbound : ∀ n : ℕ, ‖a n‖ ≤ 7 / 6 * n) {A : ℝ} (hA : 0 < A)
    (h1 : 0.22214 ≤ 2 * π * A) (h2 : 2 * π * A ≤ 0.22215) :
    ∃ r : ℝ, 2.22 < r ∧ r < 2.23 ∧
      (π : ℂ) * (4 * ∫ t in Ioi A, (Real.log (t / A) : ℂ) * thetaSeries a t) = (r : ℂ) := by
  set I : ℂ := ∫ t in Ioi A, (Real.log (t / A) : ℂ) * thetaSeries a t with hI
  set x : ℝ := 2 * π * A with hx
  have hx0 : 0 < x := by positivity
  set J : ℕ → ℝ := fun n => logExpIntegral A (2 * π * n) with hJ
  have hJ0 : ∀ n, 0 ≤ J n := fun n => logExpIntegral_nonneg hA _
  -- the sum is real
  have hs := hasSum_integral_log_mul_thetaSeries (K := 7 / 6) ha0 hA (by norm_num) hbound
  have hfun : (fun n : ℕ => a n * (logExpIntegral A (2 * π * n) : ℂ)) =
      fun n : ℕ => ((α n * J n : ℝ) : ℂ) := by
    funext n
    rw [hα n]
    push_cast
    rfl
  rw [hfun] at hs
  obtain ⟨hre, him⟩ := (Complex.hasSum_iff _ _).1 hs
  simp only [Complex.ofReal_re, Complex.ofReal_im] at hre him
  have him0 : I.im = 0 := him.unique hasSum_zero
  have hIre : I = ((I.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him0])
  set S : ℝ := I.re with hS
  -- finite part and tail
  have hsplit := hre.summable.sum_add_tsum_nat_add 49
  rw [hre.tsum_eq] at hsplit
  set T : ℝ := ∑' i : ℕ, α (i + 49) * J (i + 49) with hT
  have hfin : ∑ n ∈ Finset.range 49, α n * J n =
      J 1 + -3 * J 9 + -6 * J 13 + -2 * J 17 + -10 * J 29 + 2 * J 37 + 10 * J 41 := by
    rw [Finset.sum_congr rfl fun n hn => by rw [htab n (Finset.mem_range.1 hn)]]
    norm_num [Finset.sum_range_succ, fiveTable] <;> ring
  rw [hfin] at hsplit
  -- the tail
  set r : ℝ := Real.exp (-x) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := exp_neg_lt_one hx0
  set C49 : ℝ := 7 / 6 / (A * (2 * π) ^ 2) / 49 with hC49
  have hC0 : 0 ≤ C49 := by positivity
  have hterm : ∀ i : ℕ, |α (i + 49) * J (i + 49)| ≤ C49 * r ^ 49 * r ^ i := by
    intro i
    have hn : 0 < i + 49 := by omega
    have hb := norm_mul_logExpIntegral_le hA (K := 7 / 6) (by norm_num) hbound hn
    have hnorm : ‖a (i + 49)‖ = |α (i + 49)| := by
      rw [hα, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_mul, abs_of_nonneg (hJ0 _), ← hnorm]
    refine hb.trans ?_
    have hpos : (0 : ℝ) < A * (2 * π) ^ 2 := by positivity
    have hcast : (49 : ℝ) ≤ ((i + 49 : ℕ) : ℝ) := by
      push_cast
      linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    have hC : 7 / 6 / (A * (2 * π) ^ 2) / ((i + 49 : ℕ) : ℝ) ≤ C49 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hcast
    have hrp : 0 ≤ Real.exp (-(2 * π * A)) ^ (i + 49) := by positivity
    calc 7 / 6 / (A * (2 * π) ^ 2) / ((i + 49 : ℕ) : ℝ) * Real.exp (-(2 * π * A)) ^ (i + 49)
        ≤ C49 * Real.exp (-(2 * π * A)) ^ (i + 49) := mul_le_mul_of_nonneg_right hC hrp
      _ = C49 * r ^ 49 * r ^ i := by
          rw [pow_add]
          ring
  have hg : Summable fun i : ℕ => C49 * r ^ 49 * r ^ i :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hsn : Summable fun i : ℕ => |α (i + 49) * J (i + 49)| :=
    Summable.of_nonneg_of_le (fun i => abs_nonneg _) hterm hg
  have hTabs : |T| ≤ C49 * r ^ 49 * (1 - r)⁻¹ := by
    have h := norm_tsum_le_tsum_norm (f := fun i : ℕ => α (i + 49) * J (i + 49)) hsn
    have h' : |T| ≤ ∑' i : ℕ, |α (i + 49) * J (i + 49)| := h
    refine h'.trans ((hsn.tsum_le_tsum hterm hg).trans_eq ?_)
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  -- `4π · (tail bound) ≤ 0.0000536`
  have htail := tail_bound h1 h2
  have hpi : 0 < π := Real.pi_pos
  have h1r : 0 < 1 - r := by linarith
  have h4T : |4 * π * T| ≤ 0.0000536 := by
    have h1r' : 1 - r ≠ 0 := h1r.ne'
    have e : 4 * π * (C49 * r ^ 49 * (1 - r)⁻¹) =
        7 / 3 / (49 * x) * (Real.exp (-x) ^ 49 / (1 - Real.exp (-x))) := by
      show 4 * π * (7 / 6 / (A * (2 * π) ^ 2) / 49 * r ^ 49 * (1 - r)⁻¹) =
        7 / 3 / (49 * (2 * π * A)) * (r ^ 49 / (1 - r))
      field_simp
      ring
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * π)]
    calc 4 * π * |T| ≤ 4 * π * (C49 * r ^ 49 * (1 - r)⁻¹) :=
          mul_le_mul_of_nonneg_left hTabs (by positivity)
      _ = _ := e
      _ ≤ 0.0000536 := htail
  -- the terms through `expInt`
  have hJe : ∀ k : ℕ, 0 < k → J k = expInt (k * x) / (2 * π * k) := by
    intro k hk
    have hk' : (0 : ℝ) < k := by exact_mod_cast hk
    show logExpIntegral A (2 * π * k) = _
    rw [logExpIntegral_eq hA (by positivity)]
    congr 2
    rw [hx]
    ring
  have e1 : J 1 = expInt x / (2 * π) := by
    have := hJe 1 one_pos
    simpa using this
  have e9 : J 9 = expInt (9 * x) / (2 * π * 9) := by
    have := hJe 9 (by norm_num)
    push_cast at this
    exact this
  have e13 : J 13 = expInt (13 * x) / (2 * π * 13) := by
    have := hJe 13 (by norm_num)
    push_cast at this
    exact this
  have e17 : J 17 = expInt (17 * x) / (2 * π * 17) := by
    have := hJe 17 (by norm_num)
    push_cast at this
    exact this
  have e29 : J 29 = expInt (29 * x) / (2 * π * 29) := by
    have := hJe 29 (by norm_num)
    push_cast at this
    exact this
  have e37 : J 37 = expInt (37 * x) / (2 * π * 37) := by
    have := hJe 37 (by norm_num)
    push_cast at this
    exact this
  have e41 : J 41 = expInt (41 * x) / (2 * π * 41) := by
    have := hJe 41 (by norm_num)
    push_cast at this
    exact this
  have hV : π * (4 * S) = 2 * expInt x - 2 / 3 * expInt (9 * x) - 12 / 13 * expInt (13 * x) -
      4 / 17 * expInt (17 * x) - 20 / 29 * expInt (29 * x) + 4 / 37 * expInt (37 * x) +
      20 / 41 * expInt (41 * x) + 4 * π * T := by
    rw [← hsplit, e1, e9, e13, e17, e29, e37, e41]
    field_simp
    ring
  obtain ⟨b1l, b1u⟩ := expInt_bounds_one h1 h2
  obtain ⟨b9l, b9u⟩ := expInt_bounds_nine h1 h2
  obtain ⟨b13l, b13u⟩ := expInt_bounds_thirteen h1 h2
  obtain ⟨b17l, b17u⟩ := expInt_bounds_seventeen h1 h2
  have b29 := expInt_le_twentyNine h1
  have b37 := expInt_le_thirtySeven h1
  have b41 := expInt_le_fortyOne h1
  have p29 : 0 ≤ expInt (29 * x) := expInt_nonneg (by positivity)
  have p37 : 0 ≤ expInt (37 * x) := expInt_nonneg (by positivity)
  have p41 : 0 ≤ expInt (41 * x) := expInt_nonneg (by positivity)
  obtain ⟨t1, t2⟩ := abs_le.1 h4T
  refine ⟨π * (4 * S), by rw [hV]; linarith, by rw [hV]; linarith, ?_⟩
  rw [hIre]
  push_cast
  ring

end CMPoints
