import HeckeCM.Descent.SquareClass
import HeckeCM.Descent.RankAux

/-!
# Local analysis on `y² = (x + 5) x (x − 5)`

Mathlib only. For a rational point `(x, y)` with `y ≠ 0` put `a = x + 5`,
`b = x`, `c = x − 5`. Then

* `pos_and_sign`: `a > 0`, and `b`, `c` have the same sign;
* `even_padicValRat_a`, `even_padicValRat_b`: the valuations of `a` are even
  outside `{2, 5}`, those of `b` outside `{5}`;
* `parity_relation`: `v₂(a)` is even if and only if `v₅(b)` is even.

The last statement is the one that brings the image of the 2-descent map down
to 8 classes. It is proved by writing `a = 2^i 5^j s²`, `b = ± 5^k t²` and
using that `2s² ∓ t²` has even 5-adic valuation (`even_padicValRat_two_sq_sub`).
-/

set_option autoImplicit false

namespace BSD

/-! ## Valuations of the constants -/

lemma padicValRat_prime_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ≠ q) :
    padicValRat p (q : ℚ) = 0 := by
  haveI := Fact.mk hp
  haveI := Fact.mk hq
  rw [padicValRat.of_nat, padicValNat_primes h]
  rfl

lemma padicValRat_prime_self {p : ℕ} (hp : p.Prime) : padicValRat p (p : ℚ) = 1 := by
  haveI := Fact.mk hp
  exact padicValRat.self hp.one_lt

/-- A positive rational with even valuations outside `{2, 5}` is `2^i 5^j s²`
with `i, j ∈ {0, 1}` the parities of its valuations at `2` and `5`. -/
lemma exists_sq_of_even_outside {q : ℚ} (hq : 0 < q)
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 5 → Even (padicValRat p q)) :
    ∃ (i j : ℕ) (s : ℚ), s ≠ 0 ∧ q = 2 ^ i * 5 ^ j * s ^ 2 ∧
      (i = 0 ∨ i = 1) ∧ (j = 0 ∨ j = 1) ∧
      (Even (padicValRat 2 q) ↔ i = 0) ∧ (Even (padicValRat 5 q) ↔ j = 0) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set i : ℕ := if Even (padicValRat 2 q) then 0 else 1 with hi
  set j : ℕ := if Even (padicValRat 5 q) then 0 else 1 with hj
  have hi01 : i = 0 ∨ i = 1 := by
    rw [hi]
    split_ifs <;> simp
  have hj01 : j = 0 ∨ j = 1 := by
    rw [hj]
    split_ifs <;> simp
  have hc0 : (2 : ℚ) ^ i * 5 ^ j ≠ 0 := by positivity
  have hcpos : (0 : ℚ) < 2 ^ i * 5 ^ j := by positivity
  set q' : ℚ := q / (2 ^ i * 5 ^ j) with hq'
  have hq'pos : 0 < q' := div_pos hq hcpos
  have hval : ∀ p : ℕ, p.Prime → padicValRat p q' =
      padicValRat p q - (i * padicValRat p (2 : ℚ) + j * padicValRat p (5 : ℚ)) := by
    intro p hp
    haveI := Fact.mk hp
    rw [hq', padicValRat.div hq.ne' hc0,
      padicValRat.mul (pow_ne_zero i (by norm_num)) (pow_ne_zero j (by norm_num)),
      padicValRat.pow, padicValRat.pow]
  have h22 : padicValRat 2 (2 : ℚ) = 1 := by exact_mod_cast padicValRat_prime_self Nat.prime_two
  have h25 : padicValRat 2 (5 : ℚ) = 0 := by
    exact_mod_cast padicValRat_prime_ne Nat.prime_two Nat.prime_five (by norm_num)
  have h52 : padicValRat 5 (2 : ℚ) = 0 := by
    exact_mod_cast padicValRat_prime_ne Nat.prime_five Nat.prime_two (by norm_num)
  have h55 : padicValRat 5 (5 : ℚ) = 1 := by exact_mod_cast padicValRat_prime_self Nat.prime_five
  have heven : ∀ p : ℕ, p.Prime → Even (padicValRat p q') := by
    intro p hp
    rw [hval p hp]
    by_cases hp2 : p = 2
    · subst hp2
      rw [h22, h25, hi]
      split_ifs with he
      · simpa using he
      · have ho : Odd (padicValRat 2 q) := Int.not_even_iff_odd.1 he
        obtain ⟨k, hk⟩ := ho
        refine ⟨k, ?_⟩
        simp only [Nat.cast_one, one_mul, mul_zero, add_zero, zero_add]
        omega
    · by_cases hp5 : p = 5
      · subst hp5
        rw [h52, h55, hj]
        split_ifs with he
        · simpa using he
        · have ho : Odd (padicValRat 5 q) := Int.not_even_iff_odd.1 he
          obtain ⟨k, hk⟩ := ho
          refine ⟨k, ?_⟩
          simp only [Nat.cast_one, one_mul, mul_zero, add_zero, zero_add]
          omega
      · have e2 : padicValRat p (2 : ℚ) = 0 := by
          exact_mod_cast padicValRat_prime_ne hp Nat.prime_two hp2
        have e5 : padicValRat p (5 : ℚ) = 0 := by
          exact_mod_cast padicValRat_prime_ne hp Nat.prime_five hp5
        rw [e2, e5]
        simpa using h p hp hp2 hp5
  obtain ⟨s, hs⟩ := isSquare_rat_of_even hq'pos heven
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    exact hq'pos.ne' hs
  refine ⟨i, j, s, hs0, ?_, hi01, hj01, ?_, ?_⟩
  · have : q = 2 ^ i * 5 ^ j * q' := by
      rw [hq']
      field_simp
    rw [this, hs]
    ring
  · rw [hi]
    split_ifs with he
    · simp [he]
    · simp [he]
  · rw [hj]
    split_ifs with he
    · simp [he]
    · simp [he]

/-- If `U² = 5 X` with `U ≠ 0`, the 5-adic valuation of `X` is odd. -/
lemma not_even_of_sq_eq_five_mul {U X : ℚ} (hU : U ≠ 0) (h : U ^ 2 = 5 * X) :
    ¬ Even (padicValRat 5 X) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hX : X ≠ 0 := by
    rintro rfl
    rw [mul_zero] at h
    exact hU (pow_eq_zero_iff (two_ne_zero) |>.1 h)
  have h55 : padicValRat 5 (5 : ℚ) = 1 := by exact_mod_cast padicValRat_prime_self Nat.prime_five
  have hv := congrArg (padicValRat 5) h
  rw [padicValRat.pow, padicValRat.mul (by norm_num) hX, h55] at hv
  rintro ⟨k, hk⟩
  push_cast at hv
  omega

section Point

variable {x y : ℚ}

/-- `a > 0`, and `b`, `c` have the same sign. -/
lemma pos_and_sign (hE : y ^ 2 = (x - (-5)) * (x - 0) * (x - 5)) (hy : y ≠ 0) :
    0 < x - (-5) ∧ (0 < x - 0 ↔ 0 < x - 5) := by
  have hpos : 0 < (x - (-5)) * (x - 0) * (x - 5) := by
    rw [← hE]
    positivity
  have ha : 0 < x - (-5) := by
    by_contra h
    have h1 : x - (-5) ≤ 0 := not_lt.1 h
    have h2 : x - 0 ≤ 0 := by linarith
    have h3 : x - 5 ≤ 0 := by linarith
    have h4 : 0 ≤ (x - (-5)) * (x - 0) := mul_nonneg_of_nonpos_of_nonpos h1 h2
    have h5 := mul_nonpos_of_nonneg_of_nonpos h4 h3
    linarith
  refine ⟨ha, ⟨fun hb => ?_, fun hc => by linarith⟩⟩
  by_contra h
  have h3 : x - 5 ≤ 0 := not_lt.1 h
  have h4 : 0 ≤ (x - (-5)) * (x - 0) := mul_nonneg ha.le hb.le
  have h5 := mul_nonpos_of_nonneg_of_nonpos h4 h3
  linarith

lemma ne_zero_of_point (hE : y ^ 2 = (x - (-5)) * (x - 0) * (x - 5)) (hy : y ≠ 0) :
    x - (-5) ≠ 0 ∧ x - 0 ≠ 0 ∧ x - 5 ≠ 0 := by
  have hp : (x - (-5)) * (x - 0) * (x - 5) ≠ 0 := by
    rw [← hE]
    exact pow_ne_zero 2 hy
  exact ⟨left_ne_zero_of_mul (left_ne_zero_of_mul hp), right_ne_zero_of_mul (left_ne_zero_of_mul hp),
    right_ne_zero_of_mul hp⟩

/-- The valuations of `a = x + 5` are even outside `{2, 5}`. -/
lemma even_padicValRat_a (hE : y ^ 2 = (x - (-5)) * (x - 0) * (x - 5)) (hy : y ≠ 0) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : p ≠ 5) : Even (padicValRat p (x - (-5))) := by
  haveI := Fact.mk hp
  have e5 : padicValRat p (5 : ℚ) = 0 := by
    exact_mod_cast padicValRat_prime_ne hp Nat.prime_five hp5
  have e2 : padicValRat p (2 : ℚ) = 0 := by
    exact_mod_cast padicValRat_prime_ne hp Nat.prime_two hp2
  refine even_padicValRat_sub_root hE hy hp (by norm_num) (by norm_num) ?_ ?_
  · rw [show (-5 : ℚ) - 0 = -5 by norm_num, padicValRat.neg, e5]
  · rw [show (-5 : ℚ) - 5 = -(2 * 5) by norm_num, padicValRat.neg,
      padicValRat.mul (by norm_num) (by norm_num), e2, e5, add_zero]

/-- The valuations of `b = x` are even outside `{5}`. -/
lemma even_padicValRat_b (hE : y ^ 2 = (x - (-5)) * (x - 0) * (x - 5)) (hy : y ≠ 0) {p : ℕ}
    (hp : p.Prime) (hp5 : p ≠ 5) : Even (padicValRat p (x - 0)) := by
  haveI := Fact.mk hp
  have e5 : padicValRat p (5 : ℚ) = 0 := by
    exact_mod_cast padicValRat_prime_ne hp Nat.prime_five hp5
  have hE' : y ^ 2 = (x - 0) * (x - (-5)) * (x - 5) := by
    rw [hE]
    ring
  refine even_padicValRat_sub_root hE' hy hp (by norm_num) (by norm_num) ?_ ?_
  · rw [show (0 : ℚ) - (-5) = 5 by norm_num, e5]
  · rw [show (0 : ℚ) - 5 = -5 by norm_num, padicValRat.neg, e5]

/-- **`v₂(x + 5)` is even if and only if `v₅(x)` is even.** -/
theorem parity_relation (hE : y ^ 2 = (x - (-5)) * (x - 0) * (x - 5)) (hy : y ≠ 0) :
    Even (padicValRat 2 (x - (-5))) ↔ Even (padicValRat 5 (x - 0)) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨ha, hsign⟩ := pos_and_sign hE hy
  obtain ⟨ha0, hb0, hc0⟩ := ne_zero_of_point hE hy
  -- `a = 2^i 5^j s²`
  obtain ⟨i, j, s, hs0, haeq, hi01, hj01, hi, -⟩ :=
    exists_sq_of_even_outside ha fun p hp h2 h5 => even_padicValRat_a hE hy hp h2 h5
  -- `b = σ 5^k t²`
  obtain ⟨σ, hσ, hσb⟩ : ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ 0 < (σ : ℚ) * (x - 0) := by
    rcases lt_or_gt_of_ne hb0 with h | h
    · exact ⟨-1, Or.inr rfl, by push_cast; linarith⟩
    · exact ⟨1, Or.inl rfl, by push_cast; linarith⟩
  have hσsq : (σ : ℚ) * σ = 1 := by
    rcases hσ with rfl | rfl <;> norm_num
  have hσ0 : (σ : ℚ) ≠ 0 := by
    rcases hσ with rfl | rfl <;> norm_num
  have hvalσ : ∀ p : ℕ, p.Prime → padicValRat p ((σ : ℚ) * (x - 0)) = padicValRat p (x - 0) := by
    intro p hp
    haveI := Fact.mk hp
    rcases hσ with rfl | rfl
    · norm_num
    · push_cast
      rw [neg_one_mul, padicValRat.neg]
  obtain ⟨i', k, t, ht0, hbeq, -, hk01, hi', hk⟩ :=
    exists_sq_of_even_outside hσb fun p hp _ h5 => by
      rw [hvalσ p hp]
      exact even_padicValRat_b hE hy hp h5
  have hi'0 : i' = 0 := hi'.1 (by
    rw [hvalσ 2 Nat.prime_two]
    exact even_padicValRat_b hE hy Nat.prime_two (by norm_num))
  subst hi'0
  have hb : x - 0 = (σ : ℚ) * (5 ^ k * t ^ 2) := by
    have : x - 0 = (σ : ℚ) * ((σ : ℚ) * (x - 0)) := by
      rw [← mul_assoc, hσsq, one_mul]
    rw [this, hbeq]
    ring
  rw [hvalσ 5 Nat.prime_five] at hk
  rw [hi, hk]
  -- it remains to show `i = 0 ↔ k = 0`
  have hdiff : x - (-5) - (x - 0) = 5 := by ring
  have hE1 := even_padicValRat_two_sq_sub (Or.inl rfl : (1 : ℤ) = 1 ∨ (1 : ℤ) = -1)
  have h55 : padicValRat 5 (5 : ℚ) = 1 := by exact_mod_cast padicValRat_prime_self Nat.prime_five
  rcases hi01 with rfl | rfl <;> rcases hk01 with rfl | rfl
  · simp
  · -- `i = 0`, `k = 1`: `a = 5^j s²`, `b = 5 σ t²`
    exfalso
    have ha' : x - (-5) = 5 ^ j * s ^ 2 := by
      rw [haeq]
      ring
    have hb' : x - 0 = 5 * ((σ : ℚ) * t ^ 2) := by
      rw [hb]
      ring
    have hc' : x - 5 = 5 * ((σ : ℚ) * t ^ 2 - 1) := by
      have : x - 5 = x - 0 - 5 := by ring
      rw [this, hb']
      ring
    have ha'' : x - (-5) = 5 * ((σ : ℚ) * t ^ 2 + 1) := by
      have : x - (-5) = x - 0 + 5 := by ring
      rw [this, hb']
      ring
    rcases hj01 with rfl | rfl
    · -- `s² = 5 (σ t² + 1)`
      have h1 : s ^ 2 = 5 * ((σ : ℚ) * t ^ 2 + 1) := by
        rw [← ha'', ha']
        ring
      have hodd := not_even_of_sq_eq_five_mul hs0 h1
      have h5st : 5 * s * t ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hs0) ht0
      set r : ℚ := y / (5 * s * t) with hr
      have hr2 : r ^ 2 = t ^ 2 - σ := by
        have hy2 : y ^ 2 = (5 * s * t) ^ 2 * (t ^ 2 - σ) := by
          rw [hE, ha', hb', hc']
          have : (σ : ℚ) * ((σ : ℚ) * t ^ 2 - 1) = t ^ 2 - σ := by
            linear_combination t ^ 2 * hσsq
          linear_combination (25 * s ^ 2 * t ^ 2) * this
        rw [hr, div_pow, hy2, mul_div_cancel_left₀ _ (pow_ne_zero 2 h5st)]
      have hform : 2 * (1 : ℚ) ^ 2 - ((-σ : ℤ) : ℚ) * r ^ 2 = (σ : ℚ) * t ^ 2 + 1 := by
        rw [hr2]
        push_cast
        linear_combination -hσsq
      have hEv := even_padicValRat_two_sq_sub
        (by rcases hσ with rfl | rfl <;> simp : (-σ = 1 ∨ -σ = -1)) 1 r
      rw [hform] at hEv
      exact hodd hEv
    · -- `s² = σ t² + 1`, and `r² = 5 (t² − σ)`
      have h1 : s ^ 2 = (σ : ℚ) * t ^ 2 + 1 := by
        have : (5 : ℚ) * s ^ 2 = 5 * ((σ : ℚ) * t ^ 2 + 1) := by
          rw [← ha'', ha']
          ring
        linarith
      have h5st : 5 * s * t ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hs0) ht0
      set r : ℚ := y / (5 * s * t) with hr
      have hr0 : r ≠ 0 := div_ne_zero hy h5st
      have hr2 : r ^ 2 = 5 * (t ^ 2 - σ) := by
        have hy2 : y ^ 2 = (5 * s * t) ^ 2 * (5 * (t ^ 2 - σ)) := by
          rw [hE, ha', hb', hc']
          have : (σ : ℚ) * ((σ : ℚ) * t ^ 2 - 1) = t ^ 2 - σ := by
            linear_combination t ^ 2 * hσsq
          linear_combination (125 * s ^ 2 * t ^ 2) * this
        rw [hr, div_pow, hy2, mul_div_cancel_left₀ _ (pow_ne_zero 2 h5st)]
      have hodd := not_even_of_sq_eq_five_mul hr0 hr2
      have hform : 2 * (1 : ℚ) ^ 2 - ((1 : ℤ) : ℚ) * s ^ 2 = -((σ : ℚ) * (t ^ 2 - σ)) := by
        rw [h1]
        push_cast
        linear_combination -hσsq
      have hEv := hE1 1 s
      rw [hform, padicValRat.neg] at hEv
      have hX0 : t ^ 2 - (σ : ℚ) ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hr2
        exact hr0 (pow_eq_zero_iff two_ne_zero |>.1 hr2)
      rw [padicValRat.mul hσ0 hX0] at hEv
      have hσv : padicValRat 5 (σ : ℚ) = 0 := by
        rcases hσ with rfl | rfl <;> simp
      rw [hσv, zero_add] at hEv
      exact hodd hEv
  · -- `i = 1`, `k = 0`: `a = 2 · 5^j s²`, `b = σ t²`
    exfalso
    have hb' : x - 0 = (σ : ℚ) * t ^ 2 := by
      rw [hb]
      ring
    rcases hj01 with rfl | rfl
    · -- `2 s² − σ t² = 5`
      have h1 : 2 * s ^ 2 - (σ : ℚ) * t ^ 2 = 5 := by
        rw [← hdiff, haeq, hb']
        ring
      have hEv := even_padicValRat_two_sq_sub hσ s t
      rw [h1, h55] at hEv
      exact Int.not_even_one hEv
    · -- `10 s² − σ t² = 5`, so `t² = 5 σ (2 s² − 1)`
      have h1 : t ^ 2 = 5 * ((σ : ℚ) * (2 * s ^ 2 - 1)) := by
        have h2 : 10 * s ^ 2 - (σ : ℚ) * t ^ 2 = 5 := by
          rw [← hdiff, haeq, hb']
          ring
        linear_combination (-(σ : ℚ)) * h2 - t ^ 2 * hσsq
      have hodd := not_even_of_sq_eq_five_mul ht0 h1
      have hEv := hE1 s 1
      have hform : 2 * s ^ 2 - ((1 : ℤ) : ℚ) * (1 : ℚ) ^ 2 = 2 * s ^ 2 - 1 := by
        push_cast
        ring
      rw [hform] at hEv
      have hX0 : 2 * s ^ 2 - 1 ≠ (0 : ℚ) := by
        intro h0
        rw [h0, mul_zero, mul_zero] at h1
        exact ht0 (pow_eq_zero_iff two_ne_zero |>.1 h1)
      have hσv : padicValRat 5 (σ : ℚ) = 0 := by
        rcases hσ with rfl | rfl <;> simp
      apply hodd
      rw [padicValRat.mul hσ0 hX0, hσv, zero_add]
      exact hEv
  · simp

end Point

end BSD
