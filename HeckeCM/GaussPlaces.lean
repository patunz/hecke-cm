import Mathlib

/-!
# The places of `ℚ(i)` above an odd prime

Let `K` be a number field with `IsCyclotomicExtension {4} ℚ K`, i.e. `ℚ(i)`.

* `exists_unique_place_of_mod_four_eq_three`: if `p ≡ 3 (mod 4)` there is a single
  place above `p`, of norm `p²`;
* `exists_two_places_of_mod_four_eq_one`: if `p ≡ 1 (mod 4)` there are
  exactly two distinct places above `p`, each of norm `p`.

Everything follows from Mathlib's results on cyclotomic fields: for `p ∤ 4` the
inertia degree is the order of `p` modulo 4 and there is no ramification.
-/

open IsDedekindDomain NumberField Ideal IsCyclotomicExtension.Rat

namespace CMPoints

variable (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

lemma not_dvd_four {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : ¬ p ∣ 4 := by
  intro h
  have h' : p ∣ 2 ^ 2 := by simpa using h
  exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h'))

lemma orderOf_natCast_zmod_four_of_one {p : ℕ} (h : p % 4 = 1) :
    orderOf ((p : ℕ) : ZMod 4) = 1 := by
  have : ((p : ℕ) : ZMod 4) = 1 := by
    rw [← ZMod.natCast_mod p 4, h]
    rfl
  rw [this, orderOf_one]

lemma orderOf_natCast_zmod_four_of_three {p : ℕ} (h : p % 4 = 3) :
    orderOf ((p : ℕ) : ZMod 4) = 2 := by
  have : ((p : ℕ) : ZMod 4) = 3 := by
    rw [← ZMod.natCast_mod p 4, h]
    rfl
  rw [this]
  exact orderOf_eq_prime (by decide) (by decide)

/-- The number of primes above `p` times the order of `p` modulo 4 equals 2. -/
theorem ncard_primesOver_mul_orderOf (p : ℕ) [hp : Fact p.Prime] (h2 : p ≠ 2) :
    ((span {(p : ℤ)}).primesOver (𝓞 K)).ncard * orderOf ((p : ℕ) : ZMod 4) = 2 := by
  have hndvd := not_dvd_four hp.out h2
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {4} ℚ K
  have h_main := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (span {(p : ℤ)}) (𝓞 K) Gal(K/ℚ)
  rw [ramificationIdxIn_eq_of_not_dvd p K hndvd, inertiaDegIn_eq_of_not_dvd p K hndvd, one_mul,
    IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K,
    IsCyclotomicExtension.finrank (n := 4) K (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
    at h_main
  have h4 : Nat.totient 4 = 2 := by decide
  rw [h4] at h_main
  exact h_main

variable {K}

/-- A place contains `p` if and only if its ideal lies above `(p)`. -/
lemma natCast_mem_iff_mem_primesOver (u : HeightOneSpectrum (𝓞 K)) (p : ℕ) (hp : p.Prime) :
    ((p : ℕ) : 𝓞 K) ∈ u.asIdeal ↔ u.asIdeal ∈ (span {(p : ℤ)}).primesOver (𝓞 K) := by
  constructor
  · intro hv
    haveI := u.isMaximal
    haveI := u.isPrime
    have hmax : (span {(p : ℤ)}).IsMaximal :=
      Ideal.IsPrime.isMaximal (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero) |>.2
        (Nat.prime_iff_prime_int.1 hp)) (by simpa using hp.ne_zero)
    haveI : (u.asIdeal.under ℤ).IsPrime := Ideal.IsPrime.under ℤ u.asIdeal
    refine ⟨u.isPrime, ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩⟩
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change algebraMap ℤ (𝓞 K) (p : ℤ) ∈ u.asIdeal
    rwa [map_natCast]
  · rintro ⟨-, hover⟩
    have hmem : (p : ℤ) ∈ u.asIdeal.under ℤ := by
      rw [← hover.over]
      exact Ideal.mem_span_singleton_self _
    have := Ideal.mem_comap.1 hmem
    rwa [map_natCast] at this

/-- A prime above `(p)` is a place. -/
noncomputable def placeOfPrimesOver {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)}
    (hP : P ∈ (span {(p : ℤ)}).primesOver (𝓞 K)) : HeightOneSpectrum (𝓞 K) :=
  ⟨P, hP.1, by
    rintro rfl
    have hover := hP.2
    have hmem : (p : ℤ) ∈ (⊥ : Ideal (𝓞 K)).under ℤ := by
      rw [← hover.over]
      exact Ideal.mem_span_singleton_self _
    have h0 := Ideal.mem_comap.1 hmem
    rw [Ideal.mem_bot, map_natCast] at h0
    exact hp.ne_zero (by exact_mod_cast h0)⟩

/-- The norm of a place above an odd prime `p` is `p` raised to the order of
`p` modulo 4. -/
theorem absNorm_eq_pow_orderOf (u : HeightOneSpectrum (𝓞 K)) (p : ℕ) [hp : Fact p.Prime]
    (h2 : p ≠ 2) (hu : ((p : ℕ) : 𝓞 K) ∈ u.asIdeal) :
    absNorm u.asIdeal = p ^ orderOf ((p : ℕ) : ZMod 4) := by
  obtain ⟨hprime, hover⟩ := (natCast_mem_iff_mem_primesOver u p hp.out).1 hu
  haveI := hprime
  haveI := hover
  rw [absNorm_eq_pow_inertiaDeg' u.asIdeal hp.out, Ideal.inertiaDeg'_eq_inertiaDeg,
    inertiaDeg_eq_of_not_dvd p K u.asIdeal (not_dvd_four hp.out h2)]

/-- **`p ≡ 3 (mod 4)`**: a single place above `p`, of norm `p²`. -/
theorem exists_unique_place_of_mod_four_eq_three (p : ℕ) [hp : Fact p.Prime] (h : p % 4 = 3) :
    ∃ v : HeightOneSpectrum (𝓞 K), (∀ u : HeightOneSpectrum (𝓞 K),
      ((p : ℕ) : 𝓞 K) ∈ u.asIdeal ↔ u = v) ∧ absNorm v.asIdeal = p ^ 2 := by
  have h2 : p ≠ 2 := by rintro rfl; omega
  have hcount := ncard_primesOver_mul_orderOf K p h2
  rw [orderOf_natCast_zmod_four_of_three h] at hcount
  have h1 : ((span {(p : ℤ)}).primesOver (𝓞 K)).ncard = 1 := by omega
  obtain ⟨P, hP⟩ := Set.ncard_eq_one.1 h1
  have hPmem : P ∈ (span {(p : ℤ)}).primesOver (𝓞 K) := by rw [hP]; exact Set.mem_singleton _
  refine ⟨placeOfPrimesOver hp.out hPmem, fun u => ?_, ?_⟩
  · rw [natCast_mem_iff_mem_primesOver u p hp.out, hP, Set.mem_singleton_iff]
    constructor
    · intro hu
      exact HeightOneSpectrum.ext hu
    · rintro rfl
      rfl
  · have hmem : ((p : ℕ) : 𝓞 K) ∈ (placeOfPrimesOver hp.out hPmem).asIdeal :=
      (natCast_mem_iff_mem_primesOver _ p hp.out).2 hPmem
    rw [absNorm_eq_pow_orderOf _ p h2 hmem, orderOf_natCast_zmod_four_of_three h]

/-- **`p ≡ 1 (mod 4)`**: exactly two places above `p`, each of norm `p`. -/
theorem exists_two_places_of_mod_four_eq_one (p : ℕ) [hp : Fact p.Prime] (h : p % 4 = 1) :
    ∃ v w : HeightOneSpectrum (𝓞 K), v ≠ w ∧
      (∀ u : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ u.asIdeal ↔ u = v ∨ u = w) ∧
      absNorm v.asIdeal = p ∧ absNorm w.asIdeal = p := by
  have h2 : p ≠ 2 := by rintro rfl; omega
  have hcount := ncard_primesOver_mul_orderOf K p h2
  rw [orderOf_natCast_zmod_four_of_one h, mul_one] at hcount
  obtain ⟨P, Q, hPQ, hset⟩ := Set.ncard_eq_two.1 hcount
  have hPmem : P ∈ (span {(p : ℤ)}).primesOver (𝓞 K) := by rw [hset]; exact Set.mem_insert _ _
  have hQmem : Q ∈ (span {(p : ℤ)}).primesOver (𝓞 K) := by
    rw [hset]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  refine ⟨placeOfPrimesOver hp.out hPmem, placeOfPrimesOver hp.out hQmem, ?_, fun u => ?_, ?_, ?_⟩
  · intro heq
    exact hPQ (congrArg HeightOneSpectrum.asIdeal heq)
  · rw [natCast_mem_iff_mem_primesOver u p hp.out, hset, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (hu | hu)
      · exact Or.inl (HeightOneSpectrum.ext hu)
      · exact Or.inr (HeightOneSpectrum.ext hu)
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
  · have hmem : ((p : ℕ) : 𝓞 K) ∈ (placeOfPrimesOver hp.out hPmem).asIdeal :=
      (natCast_mem_iff_mem_primesOver _ p hp.out).2 hPmem
    rw [absNorm_eq_pow_orderOf _ p h2 hmem, orderOf_natCast_zmod_four_of_one h, pow_one]
  · have hmem : ((p : ℕ) : 𝓞 K) ∈ (placeOfPrimesOver hp.out hQmem).asIdeal :=
      (natCast_mem_iff_mem_primesOver _ p hp.out).2 hQmem
    rw [absNorm_eq_pow_orderOf _ p h2 hmem, orderOf_natCast_zmod_four_of_one h, pow_one]

end CMPoints
