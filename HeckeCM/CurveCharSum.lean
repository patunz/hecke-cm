import Mathlib

/-!
# The sum of the quadratic character over `x³ - x`

Over a finite field `F` of characteristic different from 2, with `η` the quadratic
character:

* `sum_quadraticChar_cubic_eq_zero`: if `-1` is not a square,
  `∑ x, η (x ^ 3 - x) = 0`;
* `sum_quadraticChar_cubic_eq_jacobiSum`: if `χ` is a character of order 4,
  `∑ x, η (x ^ 3 - x) = χ (-1) * (J(χ, χ) + J(χ⁻¹, χ⁻¹))`.

It depends only on Mathlib.
-/

open Finset

namespace CMPoints

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The number of square roots of `t` is `η t + 1`. -/
lemma card_filter_sq (hF : ringChar F ≠ 2) (t : F) :
    ((univ.filter fun x : F => x ^ 2 = t).card : ℤ) = quadraticChar F t + 1 := by
  rw [← quadraticChar_card_sqrts hF t]
  congr 2
  ext x
  simp

/-- Summing `g (x ^ 2)` over `x` is summing `(1 + η t) * g t` over `t`. -/
lemma sum_comp_sq {R : Type*} [CommRing R] (hF : ringChar F ≠ 2) (g : F → R) :
    ∑ x : F, g (x ^ 2) = ∑ t : F, (1 + ((quadraticChar F t : ℤ) : R)) * g t := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := univ) (g := fun x : F => x ^ 2)
    (fun _ _ => mem_univ _)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_congr rfl (fun x hx => by rw [(mem_filter.1 hx).2] : ∀ x ∈ univ.filter
    (fun x : F => x ^ 2 = t), g (x ^ 2) = g t), Finset.sum_const, nsmul_eq_mul]
  congr 1
  have := congrArg (Int.cast : ℤ → R) (card_filter_sq hF t)
  push_cast at this
  rw [this]
  ring

/-- If `-1` is not a square, the sum vanishes. -/
theorem sum_quadraticChar_cubic_eq_zero
    (h : quadraticChar F (-1) = -1) : ∑ x : F, quadraticChar F (x ^ 3 - x) = 0 := by
  have hneg : ∑ x : F, quadraticChar F (x ^ 3 - x) = ∑ x : F, quadraticChar F ((-x) ^ 3 - -x) :=
    (Equiv.sum_comp (Equiv.neg F) fun x => quadraticChar F (x ^ 3 - x)).symm
  have hterm : ∀ x : F, quadraticChar F ((-x) ^ 3 - -x) = -quadraticChar F (x ^ 3 - x) := by
    intro x
    have : (-x) ^ 3 - -x = -1 * (x ^ 3 - x) := by ring
    rw [this, map_mul, h]
    ring
  rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_neg_distrib] at hneg
  omega

section Quartico

variable {R : Type*} [CommRing R] [IsDomain R] {χ : MulChar F R}

/-- For a character of order 4, `χ²` is the quadratic character. -/
lemma sq_eq_quadraticChar (hχ : orderOf χ = 4) (a : F) :
    χ a ^ 2 = ((quadraticChar F a : ℤ) : R) := by
  have h4 : χ ^ 4 = 1 := hχ ▸ pow_orderOf_eq_one χ
  have hpow : ∀ b : F, b ≠ 0 → χ b ^ 4 = 1 := by
    intro b hb
    have := congrArg (fun ψ : MulChar F R => ψ b) h4
    simpa [MulChar.pow_apply' _ (by norm_num : (4 : ℕ) ≠ 0), MulChar.one_apply (isUnit_iff_ne_zero.2 hb)]
      using this
  have hsq : χ ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hχ] at this
    omega
  obtain ⟨c, hc⟩ : ∃ c : Fˣ, (χ ^ 2) c ≠ 1 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hsq (MulChar.ext fun u => by rw [hall u, MulChar.one_apply_coe])
  rw [MulChar.pow_apply' _ (by norm_num : (2 : ℕ) ≠ 0)] at hc
  have hc0 : (c : F) ≠ 0 := c.ne_zero
  have hcns : ¬ IsSquare (c : F) := by
    rintro ⟨b, hb⟩
    have hb0 : b ≠ 0 := fun h0 => hc0 (by rw [hb, h0, mul_zero])
    apply hc
    rw [hb, map_mul, mul_pow, ← pow_add]
    exact hpow b hb0
  have hcm1 : χ c ^ 2 = -1 := by
    have h1 : (χ c ^ 2 - 1) * (χ c ^ 2 + 1) = 0 := by
      have := hpow c hc0
      linear_combination this
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h) hc
    · exact eq_neg_of_add_eq_zero_left h
  by_cases ha : a = 0
  · subst ha
    rw [quadraticChar_zero, MulChar.map_zero]
    simp
  by_cases hsqa : IsSquare a
  · obtain ⟨b, hb⟩ := hsqa
    have hb0 : b ≠ 0 := fun h0 => ha (by rw [hb, h0, mul_zero])
    rw [(quadraticChar_one_iff_isSquare ha).2 ⟨b, hb⟩, hb, map_mul, mul_pow, ← pow_add]
    simpa using hpow b hb0
  · have hηa : quadraticChar F a = -1 := (quadraticChar_neg_one_iff_not_isSquare).2 hsqa
    have hηc : quadraticChar F (c : F) = -1 := (quadraticChar_neg_one_iff_not_isSquare).2 hcns
    have hac : IsSquare (a * c) := by
      rw [← quadraticChar_one_iff_isSquare (mul_ne_zero ha hc0), map_mul, hηa, hηc]
      norm_num
    obtain ⟨b, hb⟩ := hac
    have hb0 : b ≠ 0 := fun h0 => (mul_ne_zero ha hc0) (by rw [hb, h0, mul_zero])
    have h1 : χ a ^ 2 * χ c ^ 2 = 1 := by
      rw [← mul_pow, ← map_mul, hb, map_mul, mul_pow, ← pow_add]
      exact hpow b hb0
    rw [hηa]
    push_cast
    rw [hcm1] at h1
    linear_combination -h1

omit [Fintype F] [DecidableEq F] [IsDomain R] in
/-- For a character of order 4 over a field in which `-1` is a square,
`χ 4 = χ (-1)`: indeed `-4 = (1 + j) ^ 4` with `j ^ 2 = -1`. -/
lemma apply_four_eq_apply_neg_one (hF : ringChar F ≠ 2) (hχ : orderOf χ = 4)
    (hm1 : IsSquare (-1 : F)) : χ 4 = χ (-1) := by
  have h4 : χ ^ 4 = 1 := hχ ▸ pow_orderOf_eq_one χ
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  obtain ⟨j, hj⟩ := hm1
  have hj4 : (1 + j) ^ 4 = -4 := by
    have hj2 : j ^ 2 = -1 := by rw [sq, ← hj]
    linear_combination (j ^ 2 + 4 * j + 5) * hj2
  have hne : (1 + j) ≠ 0 := by
    intro h0
    rw [h0] at hj4
    have : (4 : F) = 0 := by linear_combination hj4
    exact h2 (by
      have h22 : (2 : F) * 2 = 0 := by linear_combination this
      exact (mul_self_eq_zero.1 h22))
  have h1 : χ (-4) = 1 := by
    rw [← hj4, map_pow]
    have := congrArg (fun ψ : MulChar F R => ψ (1 + j)) h4
    simpa [MulChar.pow_apply' _ (by norm_num : (4 : ℕ) ≠ 0),
      MulChar.one_apply (isUnit_iff_ne_zero.2 hne)] using this
  have hm : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul]
    simp
  have : χ (-4) = χ (-1) * χ 4 := by
    rw [← map_mul]
    congr 1
    ring
  rw [this] at h1
  calc χ 4 = (χ (-1) * χ (-1)) * χ 4 := by rw [hm, one_mul]
    _ = χ (-1) * (χ (-1) * χ 4) := by ring
    _ = χ (-1) := by rw [h1, mul_one]

/-- `J(χ, χ) * χ 4 = ∑ v, χ v * χ (1 - v) ^ 2` for a character of order 4. -/
lemma jacobiSum_mul_apply_four (hF : ringChar F ≠ 2) (hχ : orderOf χ = 4) :
    jacobiSum χ χ * χ 4 = ∑ v : F, χ v * χ (1 - v) ^ 2 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have hχ1 : χ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hχ
    omega
  -- `J(χ, χ) = ∑ t, χ (t * (1 - t))`, and `4 * t * (1 - t) = 1 - (2 * t - 1) ^ 2`
  have hJ : jacobiSum χ χ * χ 4 = ∑ x : F, χ (1 - x ^ 2) := by
    rw [jacobiSum, Finset.sum_mul]
    rw [← Equiv.sum_comp ((Equiv.mulLeft₀ (2 : F) h2).trans (Equiv.subRight (1 : F)))
      fun x : F => χ (1 - x ^ 2)]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← map_mul, ← map_mul]
    congr 1
    simp only [Equiv.trans_apply, Equiv.mulLeft₀_apply, Equiv.subRight_apply]
    ring
  rw [hJ, sum_comp_sq hF fun t => χ (1 - t)]
  have hsum0 : ∑ t : F, χ (1 - t) = 0 := by
    rw [← Equiv.sum_comp (Equiv.subLeft (1 : F)) fun t => χ (1 - t)]
    simp only [Equiv.subLeft_apply, sub_sub_cancel]
    exact MulChar.sum_eq_zero_of_ne_one hχ1
  simp only [add_mul, one_mul, Finset.sum_add_distrib, hsum0, zero_add]
  rw [← Equiv.sum_comp (Equiv.subLeft (1 : F)) fun v => χ v * χ (1 - v) ^ 2]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [Equiv.subLeft_apply, sub_sub_cancel]
  rw [← sq_eq_quadraticChar hχ t]
  ring

/-- **The sum of the quadratic character over `x³ - x`**, for a character `χ` of
order 4 over a field in which `-1` is a square. -/
theorem sum_quadraticChar_cubic_eq_jacobiSum (hF : ringChar F ≠ 2) (hχ : orderOf χ = 4)
    (hm1 : IsSquare (-1 : F)) :
    ((∑ x : F, quadraticChar F (x ^ 3 - x) : ℤ) : R) =
      χ (-1) * (jacobiSum χ χ + jacobiSum χ⁻¹ χ⁻¹) := by
  have h4 : χ ^ 4 = 1 := hχ ▸ pow_orderOf_eq_one χ
  have hχinv : orderOf χ⁻¹ = 4 := by rw [orderOf_inv, hχ]
  have hm : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul]
    simp
  -- `η (x ^ 3 - x) = χ (x ^ 2) * χ (x ^ 2 - 1) ^ 2`
  have hterm : ∀ x : F, ((quadraticChar F (x ^ 3 - x) : ℤ) : R) = χ (x ^ 2) * χ (1 - x ^ 2) ^ 2 := by
    intro x
    have hx : x ^ 3 - x = x * (-1 * (1 - x ^ 2)) := by ring
    rw [hx, map_mul, Int.cast_mul, ← sq_eq_quadraticChar hχ, ← sq_eq_quadraticChar hχ, map_pow,
      map_mul, mul_pow, sq (χ (-1)), hm, one_mul]
  rw [Int.cast_sum, Finset.sum_congr rfl fun x _ => hterm x,
    sum_comp_sq hF fun t => χ t * χ (1 - t) ^ 2]
  simp only [add_mul, one_mul, Finset.sum_add_distrib]
  have e1 : ∑ t : F, χ t * χ (1 - t) ^ 2 = jacobiSum χ χ * χ 4 := (jacobiSum_mul_apply_four hF hχ).symm
  have hinv : ∀ a : F, χ⁻¹ a = χ a ^ 3 := by
    intro a
    have : χ⁻¹ = χ ^ 3 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ', h4])
    rw [this, MulChar.pow_apply' _ (by norm_num : (3 : ℕ) ≠ 0)]
  have e2 : ∑ t : F, ((quadraticChar F t : ℤ) : R) * (χ t * χ (1 - t) ^ 2) =
      jacobiSum χ⁻¹ χ⁻¹ * χ⁻¹ 4 := by
    rw [jacobiSum_mul_apply_four hF hχinv]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← sq_eq_quadraticChar hχ, hinv, hinv]
    by_cases ht : 1 - t = 0
    · rw [ht, MulChar.map_zero]
      ring
    · have h1t : χ (1 - t) ^ 4 = 1 := by
        have := congrArg (fun ψ : MulChar F R => ψ (1 - t)) h4
        simpa [MulChar.pow_apply' _ (by norm_num : (4 : ℕ) ≠ 0),
          MulChar.one_apply (isUnit_iff_ne_zero.2 ht)] using this
      linear_combination (-(χ t ^ 3 * χ (1 - t) ^ 2)) * h1t
  have h4a := apply_four_eq_apply_neg_one hF hχ hm1
  have h4b : χ⁻¹ 4 = χ (-1) := by
    have := apply_four_eq_apply_neg_one hF hχinv hm1
    rw [this, hinv]
    linear_combination (χ (-1)) * hm
  rw [e1, e2, h4a, h4b]
  ring

end Quartico

end CMPoints
