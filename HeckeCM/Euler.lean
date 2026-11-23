import Mathlib
import HeckeCM.Dirichlet

/-!
# The local series of `cmPow`

* `hasSum_cmPow`: `∑ₖ cmPow p a k · xᵏ = (1 - a x + p x²)⁻¹` for `‖x‖ √p < 1`.
-/

open LSeriesConv

namespace CMPoints

/-- `∑ₖ cmPow p a k · xᵏ = (1 - a x + p x²)⁻¹`, for `a² ≤ 4p` and `‖x‖ √p < 1`. -/
theorem hasSum_cmPow {p : ℕ} {a : ℤ} (h : a ^ 2 ≤ 4 * p) {x : ℂ} (hx : ‖x‖ * √(p : ℝ) < 1) :
    HasSum (fun k => ((cmPow p a k : ℤ) : ℂ) * x ^ k) (1 - a * x + p * x ^ 2)⁻¹ := by
  set u : ℕ → ℂ := fun k => ((cmPow p a k : ℤ) : ℂ) * x ^ k with hu
  set r : ℝ := ‖x‖ * √(p : ℝ) with hr
  have hr0 : 0 ≤ r := by positivity
  have hsum : Summable u := by
    refine Summable.of_norm_bounded (g := fun k : ℕ => ((k : ℝ) + 1) * r ^ k) ?_ fun k => ?_
    · have h1 : Summable fun k : ℕ => ((k : ℝ) ^ 1) * r ^ k :=
        summable_pow_mul_geometric_of_norm_lt_one 1 (by rwa [Real.norm_of_nonneg hr0])
      have h2 : Summable fun k : ℕ => r ^ k := summable_geometric_of_lt_one hr0 hx
      refine (h1.add h2).congr fun k => ?_
      ring
    · rw [hu, norm_mul, norm_pow, hr, mul_pow, mul_comm (‖x‖ ^ k), ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (norm_cmPow_le h k) (by positivity)
  have hs1 : Summable fun k => u (k + 1) := (summable_nat_add_iff 1).2 hsum
  have hs2 : Summable fun k => u (k + 2) := (summable_nat_add_iff 2).2 hsum
  have e1 : ∑' k, u k = u 0 + ∑' k, u (k + 1) := hsum.tsum_eq_zero_add
  have e2 : ∑' k, u (k + 1) = u 1 + ∑' k, u (k + 2) := hs1.tsum_eq_zero_add
  have hrec : ∀ k, u (k + 2) - a * x * u (k + 1) + p * x ^ 2 * u k = 0 := by
    intro k
    simp only [hu, cmPow]
    push_cast
    ring
  have e3 : ∑' k, u (k + 2) - a * x * ∑' k, u (k + 1) + p * x ^ 2 * ∑' k, u k = 0 := by
    have H := ((hs2.hasSum.sub (hs1.hasSum.mul_left ((a : ℂ) * x))).add
      (hsum.hasSum.mul_left ((p : ℂ) * x ^ 2)))
    have hz : (fun k => u (k + 2) - (a : ℂ) * x * u (k + 1) + (p : ℂ) * x ^ 2 * u k) =
        fun _ => 0 := funext hrec
    rw [hz] at H
    exact H.unique hasSum_zero
  have hu0 : u 0 = 1 := by simp [hu, cmPow]
  have hu1 : u 1 = a * x := by simp [hu, cmPow]
  have hmul : (∑' k, u k) * (1 - a * x + p * x ^ 2) = 1 := by
    linear_combination (1 - a * x) * e1 + e2 + e3 + (1 - a * x) * hu0 + hu1
  have hne : (1 - a * x + p * x ^ 2 : ℂ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmul
    exact zero_ne_one hmul
  have : ∑' k, u k = (1 - a * x + p * x ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hmul
  rw [← this]
  exact hsum.hasSum

end CMPoints
