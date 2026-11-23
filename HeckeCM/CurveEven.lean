import HeckeCM.CurveSquare

/-!
# `y² = x³ − d²x` with `d` even: the prime 2

For `d = 2e` with `e` odd the discriminant `64 d⁶` has valuation 12 at 2, and
the criterion `ϖ¹² ∤ Δ` does not apply. Here:

* `isMinimal_curveD_two`: over a discrete valuation ring with
  uniformizer 2, the equation `y² = x³ − (2e)²x` with `e` invertible is
  minimal. If a change of variables gave a better integral model, its
  `c₄` would be `4 ·` a unit; but `c₄ = (a₁² + 4a₂)² − 24(2a₄ + a₁a₃)` is
  either a unit or divisible by 16;
* `localPolynomial_smul_eq_one_of_isMinimal`: hence the local polynomial is `1`;
* `LFunction_curveD_two_mul_eq_cmCoeffTw`: for `e` odd and squarefree, the
  L-series of `y² = x³ − (2e)²x` is `cmCoeffTw (2e)`;
* `LFunction_curveD_two_mul_sq`: and it does not change on multiplying by a square.
-/

open WeierstrassCurve IsLocalRing IsDedekindDomain NumberField Rat.HeightOneSpectrum
  Polynomial LSeriesConv

namespace CMPoints

section Locale

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*}
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Minimality at 2.** -/
theorem isMinimal_curveD_two (h2 : Irreducible (2 : R)) {e : R} (he : IsUnit e) :
    IsMinimal R (curveD K (algebraMap R K (2 * e))) := by
  have hint : IsIntegral R (curveD K (algebraMap R K (2 * e))) :=
    ⟨⟨curveD R (2 * e), (map_curveD _ _).symm⟩⟩
  have h2p : Prime (2 : R) := h2.prime
  have h20 : (2 : R) ≠ 0 := h2.ne_zero
  have hmax : ∀ r : R, ¬ IsUnit r → (2 : R) ∣ r := by
    intro r hr
    have : r ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal r).2 hr
    rw [h2.maximalIdeal_eq, Ideal.mem_span_singleton] at this
    exact this
  have h3 : IsUnit (3 : R) := by
    by_contra h
    obtain ⟨k, hk⟩ := hmax 3 h
    exact h2.not_isUnit (IsUnit.of_mul_eq_one (k - 1) (by linear_combination -hk))
  refine ⟨⟨by simpa using hint, ?_⟩⟩
  intro C hC _
  haveI := hC
  simp only [one_smul, ← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral R (C • _),
    valuation_Δ_aux_eq_of_isIntegral R (curveD K (algebraMap R K (2 * e)))]
  rw [variableChange_Δ, map_mul, map_pow]
  refine mul_le_of_le_one_left' (pow_le_one' (not_lt.1 fun hu => ?_) 12)
  -- `u` lies in `R` and is not a unit
  have hu0 : ((C.u : Kˣ) : K) ≠ 0 := C.u.ne_zero
  have htinv : ((C.u⁻¹ : Kˣ) : K) = ((C.u : Kˣ) : K)⁻¹ := Units.val_inv_eq_inv_val _
  obtain ⟨r, hr⟩ : ∃ r : R, algebraMap R K r = ((C.u : Kˣ) : K) := by
    rcases ValuationRing.isInteger_or_isInteger R ((C.u : Kˣ) : K) with h | h
    · exact h
    · exfalso
      obtain ⟨s, hs⟩ := h
      rw [htinv, ← hs] at hu
      exact absurd (HeightOneSpectrum.valuation_le_one (IsDiscreteValuationRing.maximalIdeal R) s)
        (not_le.2 hu)
  have hrnu : ¬ IsUnit r := by
    intro hunit
    have h1 := (valuation_algebraMap_eq_one_iff (K := K) R r).2 hunit
    rw [htinv, map_inv₀, ← hr, h1, inv_one] at hu
    exact lt_irrefl _ hu
  obtain ⟨r', rfl⟩ := hmax r hrnu
  -- the transformed integral model
  set W' := integralModel R (C • curveD K (algebraMap R K (2 * e))) with hW'
  have hinj := IsFractionRing.injective R K
  have hΔ : (2 * r') ^ 12 * W'.Δ = 64 * (2 * e) ^ 6 := by
    apply hinj
    have e1 : algebraMap R K W'.Δ =
        ((C.u⁻¹ : Kˣ) : K) ^ 12 * (64 * (algebraMap R K (2 * e)) ^ 6) := by
      rw [integralModel_Δ_eq, variableChange_Δ, Δ_curveD]
    have e2 : algebraMap R K ((2 * r') ^ 12) = ((C.u : Kˣ) : K) ^ 12 := by rw [map_pow, hr]
    rw [map_mul, e1, e2, htinv, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hu0, one_pow, one_mul]
    simp only [map_mul, map_pow, map_ofNat]
  have hc₄ : (2 * r') ^ 4 * W'.c₄ = 48 * (2 * e) ^ 2 := by
    apply hinj
    have e1 : algebraMap R K W'.c₄ =
        ((C.u⁻¹ : Kˣ) : K) ^ 4 * (48 * (algebraMap R K (2 * e)) ^ 2) := by
      rw [integralModel_c₄_eq, variableChange_c₄, c₄_curveD]
    have e2 : algebraMap R K ((2 * r') ^ 4) = ((C.u : Kˣ) : K) ^ 4 := by rw [map_pow, hr]
    rw [map_mul, e1, e2, htinv, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hu0, one_pow, one_mul]
    simp only [map_mul, map_pow, map_ofNat]
  -- `r'` is a unit
  have hr'u : IsUnit r' := by
    have h1 : r' ^ 12 * W'.Δ = e ^ 6 := by
      have h212 : (2 : R) ^ 12 ≠ 0 := pow_ne_zero _ h20
      apply mul_left_cancel₀ h212
      linear_combination hΔ
    have : IsUnit (r' ^ 12) := isUnit_of_mul_isUnit_left (h1 ▸ he.pow 6)
    exact (isUnit_pow_iff (by norm_num)).1 this
  have hc₄' : r' ^ 4 * W'.c₄ = 12 * e ^ 2 := by
    have h24 : (2 : R) ^ 4 ≠ 0 := pow_ne_zero _ h20
    apply mul_left_cancel₀ h24
    linear_combination hc₄
  have hexp : W'.c₄ = (W'.a₁ ^ 2 + 4 * W'.a₂) ^ 2 - 24 * (2 * W'.a₄ + W'.a₁ * W'.a₃) := by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  by_cases ha : (2 : R) ∣ W'.a₁
  · obtain ⟨f, hf⟩ := ha
    -- `c₄` is divisible by 16, hence `2 ∣ 3 e²`
    have h16 : W'.c₄ = 16 * ((f ^ 2 + W'.a₂) ^ 2 - 3 * (W'.a₄ + f * W'.a₃)) := by
      rw [hexp, hf]
      ring
    have h4 : (4 : R) ≠ 0 := by
      have : (4 : R) = 2 ^ 2 := by norm_num
      rw [this]
      exact pow_ne_zero _ h20
    have hdiv : (2 : R) ∣ 3 * e ^ 2 := by
      refine ⟨2 * r' ^ 4 * ((f ^ 2 + W'.a₂) ^ 2 - 3 * (W'.a₄ + f * W'.a₃)), ?_⟩
      apply mul_left_cancel₀ h4
      rw [h16] at hc₄'
      linear_combination -hc₄'
    rcases h2p.dvd_or_dvd hdiv with h | h
    · exact h2.not_isUnit (isUnit_of_dvd_unit h h3)
    · exact h2.not_isUnit (isUnit_of_dvd_unit h (he.pow 2))
  · -- `c₄` is even, hence `a₁` is even
    have hdiv : (2 : R) ∣ r' ^ 4 * W'.c₄ := ⟨6 * e ^ 2, by rw [hc₄']; ring⟩
    have hc : (2 : R) ∣ W'.c₄ := by
      rcases h2p.dvd_or_dvd hdiv with h | h
      · exact absurd (isUnit_of_dvd_unit h (hr'u.pow 4)) h2.not_isUnit
      · exact h
    have ha4 : (2 : R) ∣ W'.a₁ ^ 4 := by
      obtain ⟨q, hq⟩ := hc
      exact ⟨q - 4 * W'.a₁ ^ 2 * W'.a₂ - 8 * W'.a₂ ^ 2 + 12 * (2 * W'.a₄ + W'.a₁ * W'.a₃), by
        rw [hexp] at hq
        linear_combination hq⟩
    exact ha (h2p.dvd_of_dvd_pow ha4)

variable (d : R) [hmin : IsMinimal R (curveD K (algebraMap R K d))]
  (h0 : (64 * d ^ 6 : R) ≠ 0) (h2d : ¬ IsUnit (2 * d)) (D : VariableChange K)
include h0 h2d

/-- **Additive reduction**, from minimality alone: the local polynomial
of a transform of `y² = x³ − d²x` is `1` if `2d` is not invertible. -/
theorem localPolynomial_smul_eq_one_of_isMinimal :
    (D • curveD K (algebraMap R K d)).localPolynomial R = 1 := by
  haveI : (curveD K (algebraMap R K d)).IsElliptic := by
    rw [isElliptic_iff, Δ_curveD, isUnit_iff_ne_zero]
    have : (64 * (algebraMap R K d) ^ 6 : K) = algebraMap R K (64 * d ^ 6) := by
      rw [map_mul, map_pow, map_ofNat]
    rw [this]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 h0
  have eΔ : algebraMap R K (64 * d ^ 6) = 64 * (algebraMap R K d) ^ 6 := by
    rw [map_mul, map_pow, map_ofNat]
  have ec : algebraMap R K (48 * d ^ 2) = 48 * (algebraMap R K d) ^ 2 := by
    rw [map_mul, map_pow, map_ofNat]
  obtain ⟨C, hC⟩ := (D • curveD K (algebraMap R K d)).exists_smul_eq_minimal R
  have hCD : (C * D) • curveD K (algebraMap R K d) =
      (D • curveD K (algebraMap R K d)).minimal R := by
    rw [mul_smul, hC]
  have hΔ := valuation_Δ_eq_of_isMinimal_smul R (C * D) hCD
  have hc₄ := valuation_c₄_eq_of_isMinimal_smul R (C * D) hCD
  rw [Δ_curveD, ← eΔ] at hΔ
  rw [c₄_curveD, ← ec] at hc₄
  have hadd : ((D • curveD K (algebraMap R K d)).minimal R).HasAdditiveReduction R := by
    rw [hasAdditiveReduction_iff]
    refine ⟨inferInstance, ?_, ?_⟩
    · rw [hΔ, valuation_algebraMap_lt_one_iff,
        show (64 * d ^ 6 : R) = (2 * d) ^ 6 by ring]
      exact fun h => h2d ((isUnit_pow_iff (by norm_num)).1 h)
    · rw [hc₄, valuation_algebraMap_lt_one_iff]
      exact fun h => h2d (isUnit_of_dvd_unit ⟨24 * d, by ring⟩ h)
  have hbad : ¬ ((D • curveD K (algebraMap R K d)).minimal R).HasGoodReduction R := by
    intro hg
    have h1 := hg.goodReduction
    have h3 := hadd.badReduction
    rw [h1] at h3
    exact lt_irrefl _ h3
  have hmult :
      ¬ ((D • curveD K (algebraMap R K d)).minimal R).HasMultiplicativeReduction R :=
    hadd.not_hasMultiplicativeReduction R
  rw [localPolynomial, if_neg hbad, if_neg fun hs => hmult hs.toHasMultiplicativeReduction,
    if_neg hmult]

end Locale

/-! ## The place 2 of `ℚ` -/

section Posto

variable (v : HeightOneSpectrum (𝓞 ℚ)) (hv : (primesEquiv v : ℕ) = 2) {e : ℤ} (he : Odd e)
include hv he

/-- At the place 2 the local polynomial of a transform of `y² = x³ − (2e)²x` is `1`. -/
theorem localPolynomial_smul_curveD_two_mul (D : VariableChange (v.adicCompletion ℚ)) :
    (D • curveD (v.adicCompletion ℚ) (algebraMap (v.adicCompletionIntegers ℚ)
      (v.adicCompletion ℚ) (((2 * e : ℤ)) : v.adicCompletionIntegers ℚ))).localPolynomial
        (v.adicCompletionIntegers ℚ) = 1 := by
  have h2irr : Irreducible (2 : v.adicCompletionIntegers ℚ) := by
    have := irreducible_natCast_primesEquiv v
    rwa [hv, Nat.cast_ofNat] at this
  have heu : IsUnit ((e : ℤ) : v.adicCompletionIntegers ℚ) := by
    rw [isUnit_intCast_iff, hv]
    intro h
    exact (Int.not_even_iff_odd.2 he) (even_iff_two_dvd.2 (by exact_mod_cast h))
  have hcast : (((2 * e : ℤ)) : v.adicCompletionIntegers ℚ) =
      2 * ((e : ℤ) : v.adicCompletionIntegers ℚ) := by push_cast; ring
  rw [hcast]
  haveI := isMinimal_curveD_two (K := v.adicCompletion ℚ) h2irr heu
  have h20 : (2 : v.adicCompletionIntegers ℚ) ≠ 0 := h2irr.ne_zero
  refine localPolynomial_smul_eq_one_of_isMinimal _ ?_ ?_ D
  · have : (64 * (2 * ((e : ℤ) : v.adicCompletionIntegers ℚ)) ^ 6 : v.adicCompletionIntegers ℚ) =
        2 ^ 12 * ((e : ℤ) : v.adicCompletionIntegers ℚ) ^ 6 := by ring
    rw [this]
    exact mul_ne_zero (pow_ne_zero _ h20) (pow_ne_zero _ heu.ne_zero)
  · intro h
    exact h2irr.not_isUnit (isUnit_of_dvd_unit ⟨2 * ((e : ℤ) : v.adicCompletionIntegers ℚ), by ring⟩ h)

end Posto

/-! ## Global -/

/-- For `e` odd and squarefree and `p` odd, `p¹² ∤ 64 (2e)⁶`. -/
lemma not_pow_twelve_dvd_two_mul {e : ℤ} (hodd : Odd e) (hsq : Squarefree e) (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) : ¬ (p : ℤ) ^ 12 ∣ 64 * (2 * e) ^ 6 := by
  intro h
  have hcop : IsCoprime ((p : ℤ) ^ 12) 64 := by
    have h2' : IsCoprime (p : ℤ) 2 := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      have : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
      simpa [Int.gcd] using this
    have : (64 : ℤ) = 2 ^ 6 := by norm_num
    rw [this]
    exact IsCoprime.pow h2'
  have e1 : (64 : ℤ) * (2 * e) ^ 6 = 64 * (64 * e ^ 6) := by ring
  rw [e1] at h
  exact not_pow_twelve_dvd_of_odd_squarefree hodd hsq p hp (hcop.dvd_of_dvd_mul_left h)

/-- **The L-series of `y² = x³ − (2e)²x` is the twisted sequence**, for `e`
odd and squarefree. -/
theorem LFunction_curveD_two_mul_eq_cmCoeffTw {e : ℤ} (hodd : Odd e) (hsq : Squarefree e)
    (n : ℕ) : (curveD ℚ ((2 * e : ℤ) : ℚ)).LFunction n = cmCoeffTw (2 * e) n := by
  by_cases hn : n = 0
  · subst hn
    simp [cmCoeffTw]
  rw [cmCoeffTw, if_neg hn,
    (curveD ℚ ((2 * e : ℤ) : ℚ)).isMultiplicative_LFunction.multiplicative_factorization _ hn]
  refine Finsupp.prod_congr fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)
  have hk : n.factorization p ≠ 0 := Finsupp.mem_support_iff.1 hp
  haveI : Fact p.Prime := ⟨hpp⟩
  by_cases h : (p : ℤ) ∣ 2 * (2 * e)
  · rw [if_pos h]
    by_cases hp2 : p = 2
    · subst hp2
      have hv := primesEquiv_placeOfPrime Nat.prime_two
      rw [LFunction_apply_prime_pow_eq_coeff (curveD ℚ ((2 * e : ℤ) : ℚ)) Nat.prime_two _,
        localSeries_curveD]
      have := localPolynomial_smul_curveD_two_mul (placeOfPrime Nat.prime_two) hv hodd 1
      rw [one_smul] at this
      rw [this]
      have h0 := coeff_invOfUnit_eq_cmPow 0 0 (n.factorization 2)
      rw [cmPow_zero_zero, if_neg hk] at h0
      simpa using h0
    · exact LFunction_curveD_prime_pow_of_dvd (2 * e) h
        (not_pow_twelve_dvd_two_mul hodd hsq p hpp hp2) hk
  · rw [if_neg h, LFunction_curveD_prime_pow_of_not_dvd (2 * e) h,
      frobeniusTrace_curveD_zmod (2 * e) h]

/-- **`y² = x³ − (2e m²)²x` and `y² = x³ − (2e)²x` have the same L-series.** -/
theorem LFunction_curveD_two_mul_sq {e : ℤ} (hodd : Odd e) (hsq : Squarefree e) {m : ℤ}
    (hm : m ≠ 0) :
    (curveD ℚ ((2 * e * m ^ 2 : ℤ) : ℚ)).LFunction = (curveD ℚ ((2 * e : ℤ) : ℚ)).LFunction := by
  refine LFunction_congr fun v => ?_
  have hmv : algebraMap ℚ (v.adicCompletion ℚ) (m : ℚ) ≠ 0 :=
    (_root_.map_ne_zero _).2 (Int.cast_ne_zero.2 hm)
  have e2 : (curveD ℚ ((2 * e : ℤ) : ℚ)).baseChange (v.adicCompletion ℚ) =
      curveD (v.adicCompletion ℚ) (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)
        (((2 * e : ℤ)) : v.adicCompletionIntegers ℚ)) := by
    rw [WeierstrassCurve.baseChange, map_curveD, map_intCast, map_intCast]
  have e1 : (curveD ℚ ((2 * e * m ^ 2 : ℤ) : ℚ)).baseChange (v.adicCompletion ℚ) =
      (⟨(Units.mk0 _ hmv)⁻¹, 0, 0, 0⟩ : VariableChange (v.adicCompletion ℚ)) •
        curveD (v.adicCompletion ℚ) (algebraMap (v.adicCompletionIntegers ℚ)
          (v.adicCompletion ℚ) (((2 * e : ℤ)) : v.adicCompletionIntegers ℚ)) := by
    rw [← curveD_mul_sq, WeierstrassCurve.baseChange, map_curveD]
    congr 1
    rw [map_intCast (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) (2 * e),
      map_intCast (algebraMap ℚ (v.adicCompletion ℚ)) m, map_intCast]
    push_cast
    rfl
  rw [e1, e2]
  by_cases hv : (primesEquiv v : ℕ) = 2
  · have h1 := localPolynomial_smul_curveD_two_mul v hv hodd 1
    rw [one_smul] at h1
    rw [localPolynomial_smul_curveD_two_mul v hv hodd, h1]
  · have h64 : ¬ (((primesEquiv v : ℕ) : ℕ) : v.adicCompletionIntegers ℚ) ^ 12 ∣
        (64 * (((2 * e : ℤ)) : v.adicCompletionIntegers ℚ) ^ 6) := by
      have := not_pow_dvd_intCast v
        (not_pow_twelve_dvd_two_mul hodd hsq _ (primesEquiv v).2 hv)
      rwa [Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at this
    exact localPolynomial_smul_curveD (irreducible_natCast_primesEquiv v) _ h64 _

end CMPoints
