import HeckeCM.GenEuler

/-!
# Values and a bound for a sequence of CM type

Mathlib only.

* `gCoeff_eq_zero_of_bad`, `gCoeff_prime`: values at multiples of a bad prime
  and at good primes;
* `norm_gCoeff_le`: `‖aₙ‖ ≤ (7/6) n` when `2` is bad (Hasse on prime powers and
  multiplicativity; the factor `7/6` is only needed at `n = 3`).
-/

set_option autoImplicit false

noncomputable section

open Real

namespace CMPoints

section

variable {B : ℕ → Prop} [DecidablePred B] {a : ℕ → ℤ}

/-- A sequence of CM type vanishes at the multiples of a bad prime. -/
lemma gCoeff_eq_zero_of_bad {p n : ℕ} (hp : p.Prime) (hB : B p) (hpn : p ∣ n) :
    gCoeff B a n = 0 := by
  by_cases hn : n = 0
  · rw [hn, gCoeff_zero]
  rw [gCoeff, if_neg hn, Finsupp.prod]
  refine Finset.prod_eq_zero (i := p) ?_ (if_pos hB)
  rw [Nat.support_factorization, Nat.mem_primeFactors]
  exact ⟨hp, hpn, hn⟩

/-- At a good prime the value is `a p`. -/
lemma gCoeff_prime {p : ℕ} (hp : p.Prime) (hB : ¬ B p) : gCoeff B a p = a p := by
  have h := gCoeff_prime_pow (B := B) (a := a) hp (k := 1) one_ne_zero
  rw [pow_one, if_neg hB] at h
  rw [h]
  rfl

/-- `k + 1 ≤ q^k` for `q ≥ 2`. -/
lemma succ_le_pow_of_two_le {q : ℝ} (hq : 2 ≤ q) (k : ℕ) : (k : ℝ) + 1 ≤ q ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [pow_succ]
    push_cast
    nlinarith

/-- `k + 1 ≤ (7/6) q^k` for `q ≥ 12/7` and `k ≥ 1`. -/
lemma succ_le_mul_pow {q : ℝ} (hq : 12 / 7 ≤ q) : ∀ k : ℕ, 1 ≤ k → (k : ℝ) + 1 ≤ 7 / 6 * q ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    simp
    linarith
  | succ k hk ih =>
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [pow_succ]
    push_cast
    nlinarith

/-- **`‖aₙ‖ ≤ (7/6) n`** for a sequence of CM type in which `2` is bad. -/
theorem norm_gCoeff_le (hB2 : B 2) (ha : ∀ p : ℕ, p.Prime → a p ^ 2 ≤ 4 * p) (n : ℕ) :
    ‖((gCoeff B a n : ℤ) : ℂ)‖ ≤ 7 / 6 * n := by
  have key : ∀ n : ℕ, ‖((gCoeff B a n : ℤ) : ℂ)‖ ≤ (n : ℝ) * (if 3 ∣ n then 7 / 6 else 1) := by
    intro n
    induction n using Nat.recOnPosPrimePosCoprime with
    | zero => simp [gCoeff_zero]
    | one => simp [gCoeff_one]
    | prime_pow p k hp hk =>
      have hp' : Nat.Prime p := hp
      by_cases h2 : p = 2
      · subst h2
        rw [gCoeff_bad_pow hp' hB2, if_neg hk.ne']
        simp only [Int.cast_zero, norm_zero]
        split_ifs <;> positivity
      have h := norm_gCoeff_prime_pow_le (B := B) ha hp' k
      set q : ℝ := √(p : ℝ) with hq
      have hq0 : 0 ≤ q := Real.sqrt_nonneg _
      have hqq : q * q = p := Real.mul_self_sqrt (Nat.cast_nonneg p)
      have hpk : ((p ^ k : ℕ) : ℝ) = q ^ k * q ^ k := by
        rw [Nat.cast_pow, ← hqq, mul_pow]
      have hqk : 0 ≤ q ^ k := pow_nonneg hq0 k
      refine h.trans ?_
      rw [hpk]
      by_cases h3 : p = 3
      · subst h3
        have hq3 : 12 / 7 ≤ q := by
          rw [hq]
          refine Real.le_sqrt_of_sq_le ?_
          norm_num
        have hdvd : 3 ∣ 3 ^ k := dvd_pow_self 3 hk.ne'
        rw [if_pos hdvd]
        have := succ_le_mul_pow hq3 k hk
        nlinarith
      · have hp5 : 5 ≤ p := by
          have h2' := hp'.two_le
          rcases Nat.lt_or_ge p 5 with hlt | hge
          · interval_cases p
            · exact absurd rfl h2
            · exact absurd rfl h3
            · exact absurd hp' (by decide)
          · exact hge
        have hq2 : 2 ≤ q := by
          rw [hq]
          refine Real.le_sqrt_of_sq_le ?_
          have : (5 : ℝ) ≤ p := by exact_mod_cast hp5
          linarith
        have h1 := succ_le_pow_of_two_le hq2 k
        have hm : (1 : ℝ) ≤ (if 3 ∣ p ^ k then (7 / 6 : ℝ) else 1) := by
          split_ifs <;> norm_num
        nlinarith [mul_nonneg hqk hqk]
    | coprime m n hm hn hmn ihm ihn =>
      rw [gCoeff_mul_of_coprime hmn, Int.cast_mul, norm_mul]
      have h3 : ¬ (3 ∣ m ∧ 3 ∣ n) := by
        rintro ⟨h1, h2⟩
        have := Nat.dvd_gcd h1 h2
        rw [Nat.Coprime.gcd_eq_one hmn] at this
        omega
      have hmul : (3 ∣ m * n) ↔ (3 ∣ m ∨ 3 ∣ n) := Nat.prime_three.dvd_mul
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hprod := mul_le_mul ihm ihn (norm_nonneg _) (by split_ifs <;> positivity)
      refine hprod.trans_eq ?_
      push_cast
      by_cases h1 : 3 ∣ m
      · have h2 : ¬ 3 ∣ n := fun h => h3 ⟨h1, h⟩
        rw [if_pos h1, if_neg h2, if_pos (hmul.2 (Or.inl h1))]
        ring
      · by_cases h2 : 3 ∣ n
        · rw [if_neg h1, if_pos h2, if_pos (hmul.2 (Or.inr h2))]
          ring
        · rw [if_neg h1, if_neg h2, if_neg (fun h => (hmul.1 h).elim h1 h2)]
          ring
  refine (key n).trans ?_
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  split_ifs
  · linarith
  · linarith

end

end CMPoints
