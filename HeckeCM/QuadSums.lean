import Mathlib

/-!
# Two sums of the quadratic character

For `p` an odd prime and `χ` the quadratic character of `ZMod p`:

* `sum_quadraticChar_sq_add`: `Σ_y χ(y² + c) = −1` for `c ≠ 0`;
* `sum_quadraticChar_sq`: `Σ_y χ(y²) = p − 1`.
-/

set_option autoImplicit false

namespace CMPoints

variable {p : ℕ} [Fact p.Prime]

lemma sum_comp_sq_zmod (hp2 : ringChar (ZMod p) ≠ 2) (f : ZMod p → ℤ) :
    ∑ y : ZMod p, f (y ^ 2) = ∑ t : ZMod p, (quadraticChar (ZMod p) t + 1) * f t := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun y : ZMod p => y ^ 2) (fun y => f (y ^ 2))]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h1 : ∀ y ∈ Finset.univ.filter (fun y : ZMod p => y ^ 2 = t), f (y ^ 2) = f t :=
    fun y hy => by rw [(Finset.mem_filter.1 hy).2]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, ← quadraticChar_card_sqrts hp2 t]
  congr 2
  simp [Set.toFinset_setOf]

theorem sum_quadraticChar_mul_add (hp2 : ringChar (ZMod p) ≠ 2) {c : ZMod p} (hc : c ≠ 0) :
    ∑ t : ZMod p, quadraticChar (ZMod p) t * quadraticChar (ZMod p) (t + c) = -1 := by
  have hne : quadraticChar (ZMod p) ≠ 1 := quadraticChar_ne_one hp2
  have hJ := jacobiSum_nontrivial_inv hne
  rw [(quadraticChar_isQuadratic (ZMod p)).inv] at hJ
  have hm1 : quadraticChar (ZMod p) (-1) ^ 2 = 1 :=
    quadraticChar_sq_one (neg_ne_zero.2 one_ne_zero)
  have hcc : quadraticChar (ZMod p) c ^ 2 = 1 := quadraticChar_sq_one hc
  rw [← Fintype.sum_equiv (Equiv.mulLeft₀ (-c) (neg_ne_zero.2 hc))
    (fun u => quadraticChar (ZMod p) (-c * u) * quadraticChar (ZMod p) (-c * u + c))
    (fun t => quadraticChar (ZMod p) t * quadraticChar (ZMod p) (t + c)) (fun u => rfl)]
  have hterm : ∀ u : ZMod p, quadraticChar (ZMod p) (-c * u) *
      quadraticChar (ZMod p) (-c * u + c) =
      quadraticChar (ZMod p) (-1) * (quadraticChar (ZMod p) u * quadraticChar (ZMod p) (1 - u)) := by
    intro u
    rw [show -c * u + c = c * (1 - u) by ring, show -c * u = -1 * c * u by ring, map_mul, map_mul,
      map_mul]
    linear_combination (quadraticChar (ZMod p) (-1) * quadraticChar (ZMod p) u *
      quadraticChar (ZMod p) (1 - u)) * hcc
  rw [Finset.sum_congr rfl fun u _ => hterm u, ← Finset.mul_sum]
  unfold jacobiSum at hJ
  rw [hJ]
  linear_combination -hm1

/-- **`Σ_y χ(y² + c) = −1` for `c ≠ 0`.** -/
theorem sum_quadraticChar_sq_add (hp2 : ringChar (ZMod p) ≠ 2) {c : ZMod p} (hc : c ≠ 0) :
    ∑ y : ZMod p, quadraticChar (ZMod p) (y ^ 2 + c) = -1 := by
  rw [sum_comp_sq_zmod hp2 (fun t => quadraticChar (ZMod p) (t + c))]
  have h0 : ∑ t : ZMod p, quadraticChar (ZMod p) (t + c) = 0 := by
    rw [Fintype.sum_equiv (Equiv.addRight c) (fun t => quadraticChar (ZMod p) (t + c))
      (fun t => quadraticChar (ZMod p) t) (fun t => rfl)]
    exact quadraticChar_sum_zero hp2
  simp only [add_mul, one_mul, Finset.sum_add_distrib]
  rw [h0, add_zero, sum_quadraticChar_mul_add hp2 hc]

/-- **`Σ_y χ(y²) = p − 1`.** -/
theorem sum_quadraticChar_sq (hp2 : ringChar (ZMod p) ≠ 2) :
    ∑ y : ZMod p, quadraticChar (ZMod p) (y ^ 2) = (p : ℤ) - 1 := by
  classical
  have h : ∀ y : ZMod p, quadraticChar (ZMod p) (y ^ 2) = 1 - (if y = 0 then 1 else 0) := by
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · rw [if_neg hy, sub_zero, quadraticChar_sq_one' hy]
  rw [Finset.sum_congr rfl fun y _ => h y, Finset.sum_sub_distrib, Finset.sum_ite_eq' ]
  simp [ZMod.card]

end CMPoints
