import HeckeCM.Euler

/-!
# Convergence and Euler product for a CM-type sequence

Given a set of "bad" primes `B` and values `a p` with `a p ^ 2 ≤ 4 p`, the
sequence `gCoeff B a` has local factor `1` at the bad primes and
`(1 - a_p T + p T²)⁻¹` at the others. `cmCoeff` is the case `B = (· = 2)`,
`a = cmPrime` (`cmCoeff_eq_gCoeff`).

* `lseriesSummable_gCoeff`: absolute convergence for `Re s > 3/2`;
* `hasProd_gFactor`: Euler product.
-/

open LSeriesConv

namespace CMPoints

/-- The sequence with local factors `(1 - a_p T + p T²)⁻¹` outside `B`. -/
def gCoeff (B : ℕ → Prop) [DecidablePred B] (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 0 else n.factorization.prod fun p k => if B p then 0 else cmPow p (a p) k

variable {B : ℕ → Prop} [DecidablePred B] {a : ℕ → ℤ}

/-- `cmCoeff` is the case `B = (· = 2)`, `a = cmPrime`. -/
lemma cmCoeff_eq_gCoeff : cmCoeff = gCoeff (· = 2) cmPrime := rfl

lemma gCoeff_zero : gCoeff B a 0 = 0 := by simp [gCoeff]

lemma gCoeff_one : gCoeff B a 1 = 1 := by simp [gCoeff]

lemma gCoeff_mul_of_coprime {m n : ℕ} (h : m.Coprime n) :
    gCoeff B a (m * n) = gCoeff B a m * gCoeff B a n := by
  by_cases hm : m = 0
  · subst hm
    simp [gCoeff]
  by_cases hn : n = 0
  · subst hn
    simp [gCoeff]
  rw [gCoeff, gCoeff, gCoeff, if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn,
    Nat.factorization_mul_of_coprime h]
  refine Finsupp.prod_add_index_of_disjoint ?_ _
  rw [Nat.support_factorization, Nat.support_factorization]
  exact h.disjoint_primeFactors

lemma gCoeff_prime_pow {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k ≠ 0) :
    gCoeff B a (p ^ k) = if B p then 0 else cmPow p (a p) k := by
  rw [gCoeff, if_neg (pow_ne_zero _ hp.ne_zero), hp.factorization_pow, Finsupp.prod,
    Finsupp.support_single_ne_zero _ hk, Finset.prod_singleton, Finsupp.single_eq_same]

/-- On the powers of an odd prime, also for `k = 0`. -/
lemma gCoeff_prime_pow_of_not_bad {p : ℕ} (hp : p.Prime) (h2 : ¬ B p) (k : ℕ) :
    gCoeff B a (p ^ k) = cmPow p (a p) k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero, gCoeff_one]
    rfl
  · rw [gCoeff_prime_pow hp hk.ne', if_neg h2]

lemma gCoeff_bad_pow {p : ℕ} (hp : p.Prime) (hb : B p) (k : ℕ) :
    gCoeff B a (p ^ k) = if k = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero, gCoeff_one, if_pos rfl]
  · rw [gCoeff_prime_pow hp hk.ne', if_pos hb, if_neg hk.ne']

/-- **Hasse estimate on the prime powers.** -/
theorem norm_gCoeff_prime_pow_le (ha : ∀ p : ℕ, p.Prime → a p ^ 2 ≤ 4 * p) {p : ℕ}
    (hp : p.Prime) (k : ℕ) :
    ‖((gCoeff B a (p ^ k) : ℤ) : ℂ)‖ ≤ (k + 1) * √(p : ℝ) ^ k := by
  by_cases h2 : B p
  · rw [gCoeff_bad_pow hp h2]
    split_ifs with hk
    · subst hk
      simp
    · simp only [Int.cast_zero, norm_zero]
      positivity
  · rw [gCoeff_prime_pow_of_not_bad hp h2]
    exact norm_cmPow_le (ha p hp) k

/-- **The Dirichlet series of `gCoeff B a` converges absolutely for `Re s > 3/2`.** -/
theorem lseriesSummable_gCoeff (ha : ∀ p : ℕ, p.Prime → a p ^ 2 ≤ 4 * p) {s : ℂ}
    (hs : 3 / 2 < s.re) :
    LSeriesSummable (fun n => ((gCoeff B a n : ℤ) : ℂ)) s := by
  set σ := s.re with hσ
  set F : ℕ → ℝ := fun n => ‖((gCoeff B a n : ℤ) : ℂ)‖ * (n : ℝ) ^ (-σ) with hF
  have hterm : ∀ n, ‖LSeries.term (fun n => ((gCoeff B a n : ℤ) : ℂ)) s n‖ = F n := by
    intro n
    rw [LSeries.norm_term_eq]
    split_ifs with h0
    · simp [hF, h0, gCoeff_zero]
    · change _ / (n : ℝ) ^ s.re = _ * (n : ℝ) ^ (-s.re)
      rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  refine Summable.of_norm ((summable_congr hterm).2 ?_)
  have he : 1 / 2 - σ < -1 := by linarith
  refine summable_of_multiplicative (G := fun n => tailConst * (n : ℝ) ^ (1 / 2 - σ))
    (fun n => by positivity) ?_ ?_ ?_ ?_ ?_ ?_
  · simp [hF, gCoeff_one]
  · intro m n hmn
    simp only [hF]
    rw [gCoeff_mul_of_coprime hmn, Int.cast_mul, norm_mul, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring
  all_goals
    have hbound : ∀ {p : ℕ}, p.Prime →
        (0 ≤ (p : ℝ) ^ (1 / 2 - σ) ∧ (p : ℝ) ^ (1 / 2 - σ) ≤ 1 / 2) ∧
        ∀ k : ℕ, F (p ^ k) ≤ ((k : ℝ) + 1) * ((p : ℝ) ^ (1 / 2 - σ)) ^ k := by
      intro p hpp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
      refine ⟨⟨by positivity, ?_⟩, fun k => ?_⟩
      · calc (p : ℝ) ^ (1 / 2 - σ) ≤ (p : ℝ) ^ (-1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) he.le
          _ = (p : ℝ)⁻¹ := Real.rpow_neg_one _
          _ ≤ 1 / 2 := by
              rw [one_div]
              exact inv_anti₀ (by norm_num) hp2
      · have h1 := norm_gCoeff_prime_pow_le (B := B) ha hpp k
        have h2 : ((p ^ k : ℕ) : ℝ) ^ (-σ) = ((p : ℝ) ^ (-σ)) ^ k := by
          rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le,
            ← Real.rpow_mul hp0.le, mul_comm]
        have h3 : (p : ℝ) ^ (1 / 2 - σ) = √(p : ℝ) * (p : ℝ) ^ (-σ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add hp0]
          congr 1
        simp only [hF]
        rw [h2, h3, mul_pow, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
  · intro p hpp
    obtain ⟨⟨hy0, hy⟩, hb⟩ := hbound hpp
    exact (summable_and_tail_le hy0 hy (fun k => by positivity) hb).1
  · intro n
    exact mul_nonneg (tsum_nonneg fun k => by positivity) (by positivity)
  · exact (Real.summable_nat_rpow.2 he).mul_left _
  · intro p hpp
    obtain ⟨⟨hy0, hy⟩, hb⟩ := hbound hpp
    exact (summable_and_tail_le hy0 hy (fun k => by positivity) hb).2

/-- The Euler factor of the sequence at the prime `p`. -/
noncomputable def gFactor (B : ℕ → Prop) [DecidablePred B] (a : ℕ → ℤ) (p : ℕ) (s : ℂ) : ℂ :=
  if B p then 1 else
    (1 - (a p : ℂ) * (p : ℂ) ^ (-s) + (p : ℂ) * ((p : ℂ) ^ (-s)) ^ 2)⁻¹

/-- The term of the Dirichlet series at `p ^ k`. -/
lemma term_prime_pow_gen {p : ℕ} (hp : p.Prime) (s : ℂ) (k : ℕ) :
    LSeries.term (fun n => ((gCoeff B a n : ℤ) : ℂ)) s (p ^ k) =
      ((gCoeff B a (p ^ k) : ℤ) : ℂ) * ((p : ℂ) ^ (-s)) ^ k := by
  rw [LSeries.term_of_ne_zero (pow_ne_zero k hp.ne_zero), div_eq_mul_inv]
  congr 1
  rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul, Complex.cpow_neg,
    inv_pow]

/-- The local sum of the Dirichlet series is the factor `gFactor`. -/
theorem tsum_term_prime_pow_gen (ha : ∀ p : ℕ, p.Prime → a p ^ 2 ≤ 4 * p) {p : ℕ}
    (hp : p.Prime) {s : ℂ} (hs : 3 / 2 < s.re) :
    ∑' k, LSeries.term (fun n => ((gCoeff B a n : ℤ) : ℂ)) s (p ^ k) = gFactor B a p s := by
  simp only [term_prime_pow_gen hp]
  by_cases h2 : B p
  · rw [gFactor, if_pos h2, tsum_eq_single 0]
    · simp [gCoeff_one]
    · intro k hk
      rw [gCoeff_bad_pow hp h2, if_neg hk]
      simp
  · rw [gFactor, if_neg h2]
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hx : ‖(p : ℂ) ^ (-s)‖ * √(p : ℝ) < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hp.pos, Real.sqrt_eq_rpow, ← Real.rpow_add (by linarith)]
      exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by
        simp only [Complex.neg_re]
        linarith)
    have := (hasSum_cmPow (ha p hp) hx).tsum_eq
    simp only [gCoeff_prime_pow_of_not_bad hp h2]
    rw [this]

/-- **Euler product.** For `Re s > 3/2` the Dirichlet series of `gCoeff B a`
is the product over the primes of the factors `gFactor B a p s`. -/
theorem hasProd_gFactor (ha : ∀ p : ℕ, p.Prime → a p ^ 2 ≤ 4 * p) {s : ℂ}
    (hs : 3 / 2 < s.re) :
    HasProd (fun p : Nat.Primes => gFactor B a p s) (LSeries (fun n => ((gCoeff B a n : ℤ) : ℂ)) s) := by
  set f : ℕ → ℂ := LSeries.term (fun n => ((gCoeff B a n : ℤ) : ℂ)) s with hf
  have h0 : f 0 = 0 := LSeries.term_zero _ _
  have h1 : f 1 = 1 := by
    rw [hf, LSeries.term_of_ne_zero one_ne_zero]
    simp [gCoeff_one]
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n := by
    intro m n hmn
    by_cases hm : m = 0
    · subst hm
      simp [h0]
    by_cases hn : n = 0
    · subst hn
      simp [h0]
    rw [hf, LSeries.term_of_ne_zero (mul_ne_zero hm hn), LSeries.term_of_ne_zero hm,
      LSeries.term_of_ne_zero hn, gCoeff_mul_of_coprime hmn, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow]
    push_cast
    field_simp
  have hsum : Summable fun n => ‖f n‖ := (lseriesSummable_gCoeff (B := B) ha hs).norm
  have := EulerProduct.eulerProduct_hasProd h1 hmul hsum h0
  have e : (fun p : Nat.Primes => ∑' k, f (p ^ k)) = fun p : Nat.Primes => gFactor B a p s :=
    funext fun p => tsum_term_prime_pow_gen (B := B) ha p.prop hs
  rw [← e]
  exact this

end CMPoints
