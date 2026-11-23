import Mathlib

/-!
# The sequence in closed form

The sequence `cmCoeff : ℕ → ℤ` is defined using only integer arithmetic:

* a pair `(a, b)` is *primary* if `a ≡ 1`, `b ≡ 0` or `a ≡ 3`, `b ≡ 2`
  modulo 4 (that is, `a + bi ≡ 1` modulo `(1 + i)³` in `ℤ[i]`);
* `cmA p` is the unique `a` such that `p = a² + b²` with `(a, b)` primary
  (a finite, computable search over naturals);
* `cmPrime p` is `2 * cmA p` if `p ≡ 1 (mod 4)` and `0` otherwise;
* `cmPow p a k` is the recurrence `c₀ = 1`, `c₁ = a`, `c_{k+2} = a c_{k+1} - p c_k`;
* `cmCoeff n` is the product, over the primes `p` of `n`, of `cmPow p (cmPrime p) k`
  for `p` odd and of `0` for `p = 2`.

This file depends only on Mathlib and uses nothing specific to a version: it is
meant to be copied verbatim elsewhere. It also contains the uniqueness that
makes `cmA` well defined (`cmA_eq`).
-/

namespace CMPoints

/-- The pair `(a, b)` is primary: `a + bi ≡ 1` modulo `(1 + i)³`. -/
def IsPrimaryPair (a b : ℤ) : Prop :=
  a % 4 = 1 ∧ b % 4 = 0 ∨ a % 4 = 3 ∧ b % 4 = 2

instance (a b : ℤ) : Decidable (IsPrimaryPair a b) := by
  unfold IsPrimaryPair
  infer_instance

/-- The unique `a` with `p = a² + b²` and `(a, b)` primary. The search is over
`0 ≤ x, y ≤ p`, with the sign of `a` chosen by the primarity condition: thus
the definition uses only intervals of naturals. -/
def cmA (p : ℕ) : ℤ :=
  ∑ x ∈ Finset.range (p + 1), ∑ y ∈ Finset.range (p + 1),
    if (x : ℤ) ^ 2 + (y : ℤ) ^ 2 = p then
      (if IsPrimaryPair x y then (x : ℤ) else if IsPrimaryPair (-(x : ℤ)) y then -(x : ℤ) else 0)
    else 0

/-- The coefficient at a prime. -/
def cmPrime (p : ℕ) : ℤ := if p % 4 = 1 then 2 * cmA p else 0

/-- The coefficients at the powers of an odd prime. -/
def cmPow (p : ℕ) (a : ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => a
  | (k + 2) => a * cmPow p a (k + 1) - p * cmPow p a k

/-- **The sequence in closed form.** -/
def cmCoeff (n : ℕ) : ℤ :=
  if n = 0 then 0 else
    n.factorization.prod fun p k => if p = 2 then 0 else cmPow p (cmPrime p) k

/-- Two representations of a prime as a sum of two squares, with the first summand
odd and the second even, have the same first summand up to sign. -/
lemma sq_eq_sq_of_two_squares {p : ℕ} (hp : p.Prime) {a b c d : ℤ} (h1 : a ^ 2 + b ^ 2 = p)
    (h2 : c ^ 2 + d ^ 2 = p) (ha : a % 2 = 1) (hc : c % 2 = 1) (hb : b % 2 = 0)
    (hd : d % 2 = 0) : a ^ 2 = c ^ 2 := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hprod : (a * d - b * c) * (a * d + b * c) = p * (a ^ 2 - c ^ 2) := by
    linear_combination (a ^ 2) * h2 - (c ^ 2) * h1
  have hL1 : (a * d - b * c) ^ 2 + (a * c + b * d) ^ 2 = (p : ℤ) ^ 2 := by
    have : (a * d - b * c) ^ 2 + (a * c + b * d) ^ 2 = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by ring
    rw [this, h1, h2]
    ring
  have hL2 : (a * d + b * c) ^ 2 + (a * c - b * d) ^ 2 = (p : ℤ) ^ 2 := by
    have : (a * d + b * c) ^ 2 + (a * c - b * d) ^ 2 = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by ring
    rw [this, h1, h2]
    ring
  have hodd1 : (a * c + b * d) % 2 = 1 := by
    simp [Int.add_emod, Int.mul_emod, ha, hc, hb, hd]
  have hodd2 : (a * c - b * d) % 2 = 1 := by
    simp [Int.sub_emod, Int.mul_emod, ha, hc, hb, hd]
  -- if `p ∣ x` and `x² + y² = p²` with `y` odd, then `x = 0`
  have key : ∀ x y : ℤ, (p : ℤ) ∣ x → x ^ 2 + y ^ 2 = (p : ℤ) ^ 2 → y % 2 = 1 → x = 0 := by
    rintro x y ⟨t, rfl⟩ hxy hy
    have ht : t ^ 2 ≤ 1 := by
      by_contra hlt
      push Not at hlt
      have h4 : (2 : ℤ) ≤ t ^ 2 := hlt
      nlinarith [sq_nonneg y, mul_pos hp0 hp0]
    have ht' : t = 0 ∨ t ^ 2 = 1 := by
      have h0 : 0 ≤ t ^ 2 := sq_nonneg t
      rcases (by omega : t ^ 2 = 0 ∨ t ^ 2 = 1) with h | h
      · exact Or.inl (pow_eq_zero_iff (by norm_num) |>.1 h)
      · exact Or.inr h
    rcases ht' with rfl | ht1
    · simp
    · exfalso
      have hy0 : y ^ 2 = 0 := by nlinarith
      have : y = 0 := pow_eq_zero_iff (by norm_num) |>.1 hy0
      rw [this] at hy
      norm_num at hy
  have hzero : a * d - b * c = 0 ∨ a * d + b * c = 0 := by
    rcases hpp.dvd_or_dvd (Dvd.intro _ hprod.symm) with h | h
    · exact Or.inl (key _ _ h hL1 hodd1)
    · exact Or.inr (key _ _ h hL2 hodd2)
  have hfin : (p : ℤ) * (a ^ 2 - c ^ 2) = 0 := by
    rw [← hprod]
    rcases hzero with h | h <;> rw [h] <;> ring
  have := (mul_eq_zero.1 hfin).resolve_left hp0.ne'
  linarith

/-- **Uniqueness**: the first summand of a primary representation is determined. -/
theorem eq_of_isPrimaryPair {p : ℕ} (hp : p.Prime) {a b c d : ℤ} (h1 : a ^ 2 + b ^ 2 = p)
    (h2 : c ^ 2 + d ^ 2 = p) (hab : IsPrimaryPair a b) (hcd : IsPrimaryPair c d) : a = c := by
  have ha : a % 2 = 1 := by rcases hab with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have hc : c % 2 = 1 := by rcases hcd with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have hb : b % 2 = 0 := by rcases hab with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have hd : d % 2 = 0 := by rcases hcd with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have hsq := sq_eq_sq_of_two_squares hp h1 h2 ha hc hb hd
  have hbd : b ^ 2 = d ^ 2 := by linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · exact h
  · exfalso
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hbd with h' | h'
    · rcases hab with ⟨x, y⟩ | ⟨x, y⟩ <;> rcases hcd with ⟨z, w⟩ | ⟨z, w⟩ <;> omega
    · rcases hab with ⟨x, y⟩ | ⟨x, y⟩ <;> rcases hcd with ⟨z, w⟩ | ⟨z, w⟩ <;> omega

/-- `cmA p` is the first summand of any primary representation of `p`. -/
theorem cmA_eq {p : ℕ} (hp : p.Prime) {a b : ℤ} (h : a ^ 2 + b ^ 2 = p)
    (hab : IsPrimaryPair a b) : cmA p = a := by
  have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hX : (a.natAbs : ℤ) = a ∨ (a.natAbs : ℤ) = -a := by omega
  have hY : (b.natAbs : ℤ) = b ∨ (b.natAbs : ℤ) = -b := by omega
  have hXsq : (a.natAbs : ℤ) ^ 2 = a ^ 2 := by rcases hX with h' | h' <;> rw [h'] <;> ring
  have hYsq : (b.natAbs : ℤ) ^ 2 = b ^ 2 := by rcases hY with h' | h' <;> rw [h'] <;> ring
  have hbound : ∀ x y : ℤ, 0 ≤ x → x ^ 2 + y ^ 2 = p → x ≤ p := by
    intro x y hx0 hxy
    nlinarith [sq_nonneg y, sq_nonneg (x - 1)]
  -- the parity does not change with the sign of the second summand
  have habs : IsPrimaryPair a (b.natAbs : ℤ) := by
    unfold IsPrimaryPair at hab ⊢
    omega
  -- a nonzero term comes from a primary representation, hence from `(|a|, |b|)`
  have hterm : ∀ x y : ℕ, (x : ℤ) ^ 2 + (y : ℤ) ^ 2 = p →
      (if IsPrimaryPair x y then (x : ℤ) else if IsPrimaryPair (-(x : ℤ)) y then -(x : ℤ) else 0)
        ≠ 0 → x = a.natAbs ∧ y = b.natAbs := by
    intro x y hxy hne
    have hxa : (x : ℤ) = a ∨ -(x : ℤ) = a := by
      by_cases h1 : IsPrimaryPair x y
      · exact Or.inl (eq_of_isPrimaryPair hp hxy h h1 hab)
      · by_cases h2 : IsPrimaryPair (-(x : ℤ)) y
        · exact Or.inr (eq_of_isPrimaryPair hp (by rw [neg_sq]; exact hxy) h h2 hab)
        · rw [if_neg h1, if_neg h2] at hne
          exact absurd rfl hne
    have hx : x = a.natAbs := by omega
    refine ⟨hx, ?_⟩
    have hy2 : (y : ℤ) ^ 2 = (b.natAbs : ℤ) ^ 2 := by
      rw [hYsq]
      have : (x : ℤ) ^ 2 = a ^ 2 := by rcases hxa with h' | h' <;> rw [← h'] <;> ring
      linarith
    have := abs_eq_abs.2 (sq_eq_sq_iff_eq_or_eq_neg.1 hy2)
    simp only [Nat.abs_cast] at this
    exact_mod_cast this
  have hval : (if IsPrimaryPair (a.natAbs : ℤ) (b.natAbs : ℤ) then (a.natAbs : ℤ)
      else if IsPrimaryPair (-(a.natAbs : ℤ)) (b.natAbs : ℤ) then -(a.natAbs : ℤ) else 0) = a := by
    rcases hX with h' | h'
    · rw [h', if_pos habs]
    · have hneg : -(a.natAbs : ℤ) = a := by omega
      have hnot : ¬ IsPrimaryPair (a.natAbs : ℤ) (b.natAbs : ℤ) := by
        unfold IsPrimaryPair at habs ⊢
        omega
      rw [if_neg hnot, hneg, if_pos habs]
  rw [cmA, Finset.sum_eq_single a.natAbs, Finset.sum_eq_single b.natAbs]
  · rw [if_pos (by rw [hXsq, hYsq]; exact h), hval]
  · intro y _ hy
    by_cases hc : (a.natAbs : ℤ) ^ 2 + (y : ℤ) ^ 2 = p
    · rw [if_pos hc]
      by_contra hne
      exact hy (hterm _ _ hc hne).2
    · rw [if_neg hc]
  · intro hmem
    exfalso
    apply hmem
    rw [Finset.mem_range]
    have := hbound (b.natAbs : ℤ) (a.natAbs : ℤ) (by positivity) (by rw [hXsq, hYsq]; linarith)
    omega
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    by_cases hc : (x : ℤ) ^ 2 + (y : ℤ) ^ 2 = p
    · rw [if_pos hc]
      by_contra hne
      exact hx (hterm _ _ hc hne).1
    · rw [if_neg hc]
  · intro hmem
    exfalso
    apply hmem
    rw [Finset.mem_range]
    have := hbound (a.natAbs : ℤ) (b.natAbs : ℤ) (by positivity) (by rw [hXsq, hYsq]; exact h)
    omega

end CMPoints
