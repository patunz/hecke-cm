import Mathlib

/-!
# Square classes of rationals

The arithmetic ingredients of 2-descent over `ℚ`:

* a positive rational with all `p`-adic valuations even is a square;
* if `y² = (x - e₁)(x - e₂)(x - e₃)` with `eᵢ` rational and `y ≠ 0`, then the
  `p`-adic valuation of `x - e₁` is even for every prime `p` at which
  the differences `e₁ - eⱼ` have zero valuation.
-/

namespace BSD

/-- A nonzero natural number with all valuations even is a square. -/
lemma isSquare_nat_of_even {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → Even (padicValNat p n)) : IsSquare n := by
  set f : ℕ →₀ ℕ := n.factorization.mapRange (· / 2) (by simp) with hf
  have hfp : ∀ p ∈ f.support, p.Prime := by
    intro p hp
    have hp' : p ∈ n.factorization.support := Finsupp.support_mapRange hp
    rw [Nat.support_factorization] at hp'
    exact Nat.prime_of_mem_primeFactors hp'
  set m := f.prod (· ^ ·) with hm
  have hmf : m.factorization = f := Nat.prod_pow_factorization_eq_self hfp
  have hm0 : m ≠ 0 := by
    rw [hm, Finsupp.prod_ne_zero_iff]
    intro p hp
    exact pow_ne_zero _ (hfp p hp).ne_zero
  refine ⟨m, ?_⟩
  apply Nat.eq_of_factorization_eq hn (mul_ne_zero hm0 hm0)
  intro p
  rw [Nat.factorization_mul hm0 hm0, hmf, Finsupp.add_apply, hf, Finsupp.mapRange_apply]
  by_cases hp : p.Prime
  · have := h p hp
    rw [← Nat.factorization_def n hp] at this
    obtain ⟨k, hk⟩ := this
    rw [hk]
    omega
  · rw [Nat.factorization_eq_zero_of_not_prime n hp]

/-- A positive rational with all `p`-adic valuations even is a square. -/
lemma isSquare_rat_of_even {q : ℚ} (hq : 0 < q)
    (h : ∀ p : ℕ, p.Prime → Even (padicValRat p q)) : IsSquare q := by
  rw [Rat.isSquare_iff]
  have hnum : 0 < q.num := Rat.num_pos.2 hq
  have hcop : Nat.Coprime q.num.natAbs q.den := q.reduced
  have key : ∀ p : ℕ, p.Prime →
      Even (padicValNat p q.num.natAbs) ∧ Even (padicValNat p q.den) := by
    intro p hp
    have hv := h p hp
    rw [padicValRat_def] at hv
    have hint : padicValInt p q.num = padicValNat p q.num.natAbs := rfl
    rw [hint] at hv
    by_cases hd : p ∣ q.den
    · have hn : ¬ p ∣ q.num.natAbs := by
        intro hn
        have := Nat.dvd_gcd hn hd
        rw [hcop.gcd_eq_one] at this
        exact hp.one_lt.ne' (Nat.dvd_one.1 this)
      have h0 : padicValNat p q.num.natAbs = 0 := padicValNat.eq_zero_of_not_dvd hn
      rw [h0] at hv
      refine ⟨by rw [h0]; exact ⟨0, rfl⟩, ?_⟩
      have : Even ((padicValNat p q.den : ℤ)) := by
        have := hv.neg
        simpa using this
      exact (Int.even_coe_nat _).1 this
    · have h0 : padicValNat p q.den = 0 := padicValNat.eq_zero_of_not_dvd hd
      rw [h0] at hv
      refine ⟨?_, by rw [h0]; exact ⟨0, rfl⟩⟩
      have : Even ((padicValNat p q.num.natAbs : ℤ)) := by simpa using hv
      exact (Int.even_coe_nat _).1 this
  constructor
  · have : q.num = (q.num.natAbs : ℤ) := (Int.natAbs_of_nonneg hnum.le).symm
    rw [this, Int.isSquare_natCast_iff]
    exact isSquare_nat_of_even (Int.natAbs_ne_zero.2 hnum.ne') fun p hp => (key p hp).1
  · exact isSquare_nat_of_even q.den_nz fun p hp => (key p hp).2

/-- Two nonzero rationals with the same sign and valuations congruent modulo 2
have a square product. -/
lemma isSquare_mul_of_same_class {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hsign : 0 < a ↔ 0 < b)
    (h : ∀ p : ℕ, p.Prime → Even (padicValRat p a + padicValRat p b)) : IsSquare (a * b) := by
  have hpos : 0 < a * b := by
    rcases lt_or_gt_of_ne ha with h1 | h1
    · have hb' : b < 0 := lt_of_le_of_ne (not_lt.1 fun hb' => absurd (hsign.2 hb') (not_lt.2 h1.le)) hb
      exact mul_pos_of_neg_of_neg h1 hb'
    · exact mul_pos h1 (hsign.1 h1)
  refine isSquare_rat_of_even hpos fun p hp => ?_
  have := Fact.mk hp
  rw [padicValRat.mul ha hb]
  exact h p hp

/-- If `a ≠ 0` and both `a` and `a·b` are squares, so is `b`. -/
lemma isSquare_of_mul_left {K : Type*} [Field K] {a b : K} (ha : a ≠ 0) (h1 : IsSquare a)
    (h2 : IsSquare (a * b)) : IsSquare b := by
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  have hs0 : s ≠ 0 := by rintro rfl; exact ha (by rw [hs, mul_zero])
  refine ⟨t / s, ?_⟩
  rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hs0 hs0), ← hs, mul_comm]
  exact ht

/-- If the differences `e₁ - e₂` and `e₁ - e₃` have zero `p`-adic valuation, the
valuation of `x - e₁` is even. -/
lemma even_padicValRat_sub_root {x y e₁ e₂ e₃ : ℚ}
    (hE : y ^ 2 = (x - e₁) * (x - e₂) * (x - e₃)) (hy : y ≠ 0) {p : ℕ} (hp : p.Prime)
    (n12 : e₁ ≠ e₂) (n13 : e₁ ≠ e₃) (h12 : padicValRat p (e₁ - e₂) = 0)
    (h13 : padicValRat p (e₁ - e₃) = 0) :
    Even (padicValRat p (x - e₁)) := by
  have := Fact.mk hp
  have hprod : (x - e₁) * (x - e₂) * (x - e₃) ≠ 0 := by rw [← hE]; exact pow_ne_zero 2 hy
  have a1 : x - e₁ ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hprod)
  have a2 : x - e₂ ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hprod)
  have a3 : x - e₃ ≠ 0 := right_ne_zero_of_mul hprod
  have hsum : padicValRat p (x - e₁) + padicValRat p (x - e₂) + padicValRat p (x - e₃) =
      2 * padicValRat p y := by
    rw [← padicValRat.mul a1 a2, ← padicValRat.mul (mul_ne_zero a1 a2) a3, ← hE, padicValRat.pow]
    norm_num
  -- negative valuation: all equal
  have shift : ∀ a d : ℚ, a ≠ 0 → a + d ≠ 0 → d ≠ 0 → padicValRat p d = 0 →
      padicValRat p a < 0 → padicValRat p (a + d) = padicValRat p a := fun a d ha had hd hd0 hlt =>
    padicValRat.add_eq_of_lt had ha hd (by rw [hd0]; exact hlt)
  -- two valuations cannot both be positive
  have excl : ∀ a b d : ℚ, a - b = d → d ≠ 0 → padicValRat p d = 0 →
      ¬ (0 < padicValRat p a ∧ 0 < padicValRat p b) := by
    rintro a b d hab hd hd0 ⟨h1, h2⟩
    have := padicValRat.min_le_padicValRat_add (p := p) (q := a) (r := -b)
      (by rw [← sub_eq_add_neg, hab]; exact hd)
    rw [← sub_eq_add_neg, hab, hd0, padicValRat.neg] at this
    exact absurd this (not_le.2 (lt_min h1 h2))
  have d12 : e₁ - e₂ ≠ 0 := sub_ne_zero.2 n12
  have d13 : e₁ - e₃ ≠ 0 := sub_ne_zero.2 n13
  have d21 : e₂ - e₁ ≠ 0 := sub_ne_zero.2 n12.symm
  have d31 : e₃ - e₁ ≠ 0 := sub_ne_zero.2 n13.symm
  have h21 : padicValRat p (e₂ - e₁) = 0 := by rw [← neg_sub, padicValRat.neg]; exact h12
  have h31 : padicValRat p (e₃ - e₁) = 0 := by rw [← neg_sub, padicValRat.neg]; exact h13
  have e12 : x - e₂ = (x - e₁) + (e₁ - e₂) := by ring
  have e13 : x - e₃ = (x - e₁) + (e₁ - e₃) := by ring
  have e21 : x - e₁ = (x - e₂) + (e₂ - e₁) := by ring
  have e31 : x - e₁ = (x - e₃) + (e₃ - e₁) := by ring
  have F1a : padicValRat p (x - e₁) < 0 → padicValRat p (x - e₂) = padicValRat p (x - e₁) :=
    fun hlt => by rw [e12]; exact shift _ _ a1 (by rw [← e12]; exact a2) d12 h12 hlt
  have F1b : padicValRat p (x - e₁) < 0 → padicValRat p (x - e₃) = padicValRat p (x - e₁) :=
    fun hlt => by rw [e13]; exact shift _ _ a1 (by rw [← e13]; exact a3) d13 h13 hlt
  have F2 : padicValRat p (x - e₂) < 0 → padicValRat p (x - e₁) = padicValRat p (x - e₂) :=
    fun hlt => by rw [e21]; exact shift _ _ a2 (by rw [← e21]; exact a1) d21 h21 hlt
  have F3 : padicValRat p (x - e₃) < 0 → padicValRat p (x - e₁) = padicValRat p (x - e₃) :=
    fun hlt => by rw [e31]; exact shift _ _ a3 (by rw [← e31]; exact a1) d31 h31 hlt
  have G2 := excl (x - e₁) (x - e₂) (e₂ - e₁) (by ring) d21 h21
  have G3 := excl (x - e₁) (x - e₃) (e₃ - e₁) (by ring) d31 h31
  rw [Int.even_iff]
  rcases lt_trichotomy (padicValRat p (x - e₁)) 0 with hlt | heq | hgt
  · have := F1a hlt
    have := F1b hlt
    omega
  · omega
  · have h2 : padicValRat p (x - e₂) = 0 := by
      rcases lt_trichotomy (padicValRat p (x - e₂)) 0 with h | h | h
      · have := F2 h; omega
      · exact h
      · exact absurd ⟨hgt, h⟩ G2
    have h3 : padicValRat p (x - e₃) = 0 := by
      rcases lt_trichotomy (padicValRat p (x - e₃)) 0 with h | h | h
      · have := F3 h; omega
      · exact h
      · exact absurd ⟨hgt, h⟩ G3
    omega

end BSD
