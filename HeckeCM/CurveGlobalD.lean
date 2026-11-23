import HeckeCM.CurveLSeries
import HeckeCM.CurveLocalD

/-!
# The L-series of `y² = x³ − d²x` is the twisted sequence

For `d` an integer with `p¹² ∤ 64 d⁶` at every prime `p` (for example `d` odd and
squarefree), `LFunction_curveD_eq_cmCoeffTw`: the `n`-th coefficient
of the Mathlib L-series of `y² = x³ − d²x` over `ℚ` is `cmCoeffTw d n`, that is

* at primes `p ∣ 2d` the local factor is `1`;
* at primes `p ∤ 2d` we have `a_p = (d/p) · cmPrime p`, with the same recurrence
  on powers.

For `d = 1` this is `cmCoeff`.
-/

open WeierstrassCurve IsLocalRing IsDedekindDomain NumberField Rat.HeightOneSpectrum
  Polynomial LSeriesConv

namespace CMPoints

/-- The sequence of coefficients of the L-series of `y² = x³ − d²x`. -/
def cmCoeffTw (d : ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 0 else n.factorization.prod fun p k =>
    if (p : ℤ) ∣ 2 * d then 0 else cmPow p (jacobiSym d p * cmPrime p) k

/-- The Frobenius trace of `y² = x³ − d²x` is invariant under field isomorphism. -/
lemma frobeniusTrace_curveD_congr {F F' : Type*} [Field F] [Field F'] [Finite F] [Finite F']
    (e : F ≃+* F') (d : F) :
    (curveD F d).frobeniusTrace = (curveD F' (e d)).frobeniusTrace := by
  rw [frobeniusTrace_def, frobeniusTrace_def, pointCount_def, pointCount_def,
    Nat.card_congr e.toEquiv]
  congr 3
  refine Nat.card_congr (Equiv.subtypeEquiv (e.toEquiv.prodCongr e.toEquiv) fun p => ?_)
  rw [show curveD F' (e d) = (curveD F d).map e.toRingHom from (map_curveD e.toRingHom d).symm]
  exact (Affine.map_equation _ e.injective p.1 p.2).symm

section Posto

variable (v : HeightOneSpectrum (𝓞 ℚ)) (d : ℤ)

/-- The local factor of `y² = x³ − d²x`, written with the equation over the completion. -/
lemma localSeries_curveD :
    localSeries (curveD ℚ (d : ℚ)) v =
      PowerSeries.invOfUnit (((curveD (v.adicCompletion ℚ)
        (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)
          ((d : ℤ) : v.adicCompletionIntegers ℚ))).localPolynomial
        (v.adicCompletionIntegers ℚ) : ℤ[X]) : PowerSeries ℤ) 1 := by
  rw [localSeries, WeierstrassCurve.localPowerSeries, WeierstrassCurve.baseChange, map_curveD,
    map_intCast, map_intCast]

lemma residueEquiv_intCast (m : ℤ) :
    residueEquiv v (IsLocalRing.residue _ ((m : ℤ) : v.adicCompletionIntegers ℚ)) =
      ((m : ℤ) : ZMod (primesEquiv v : ℕ)) := by
  rw [map_intCast, map_intCast]

lemma isUnit_intCast_iff (m : ℤ) :
    IsUnit ((m : ℤ) : v.adicCompletionIntegers ℚ) ↔ ¬ ((primesEquiv v : ℕ) : ℤ) ∣ m := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, Ne, ← (residueEquiv v).map_eq_zero_iff,
    residueEquiv_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma irreducible_natCast_primesEquiv :
    Irreducible (((primesEquiv v : ℕ) : ℕ) : v.adicCompletionIntegers ℚ) := by
  let e : v.adicCompletionIntegers ℚ ≃+* ℤ_[primesEquiv v] :=
    (adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv
  rw [← MulEquiv.irreducible_iff e.toMulEquiv]
  change Irreducible (e _)
  rw [map_natCast]
  exact PadicInt.irreducible_p

lemma not_pow_dvd_intCast {m : ℤ} {n : ℕ} (h : ¬ ((primesEquiv v : ℕ) : ℤ) ^ n ∣ m) :
    ¬ (((primesEquiv v : ℕ) : ℕ) : v.adicCompletionIntegers ℚ) ^ n ∣
      ((m : ℤ) : v.adicCompletionIntegers ℚ) := by
  let e : v.adicCompletionIntegers ℚ ≃+* ℤ_[primesEquiv v] :=
    (adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv
  intro hdvd
  have := map_dvd e hdvd
  rw [map_pow, map_natCast, map_intCast, PadicInt.pow_p_dvd_int_iff] at this
  exact h (by exact_mod_cast this)

/-- At primes not dividing `2d` the coefficients of the local factor follow
the recurrence, starting from the Frobenius trace over `ZMod p`. -/
lemma coeff_localSeries_curveD_of_not_dvd (h : ¬ ((primesEquiv v : ℕ) : ℤ) ∣ 2 * d) (k : ℕ) :
    PowerSeries.coeff k (localSeries (curveD ℚ (d : ℚ)) v) =
      cmPow (primesEquiv v : ℕ)
        (curveD (ZMod (primesEquiv v : ℕ)) ((d : ℤ) : ZMod (primesEquiv v : ℕ))).frobeniusTrace
        k := by
  have hu : IsUnit (2 * ((d : ℤ) : v.adicCompletionIntegers ℚ)) := by
    have := (isUnit_intCast_iff v (2 * d)).2 h
    rwa [Int.cast_mul, Int.cast_ofNat] at this
  rw [localSeries_curveD, localPolynomial_curveD_of_isUnit _ hu, card_residueField,
    coeff_invOfUnit_eq_cmPow, frobeniusTrace_curveD_congr (residueEquiv v), residueEquiv_intCast]

/-- At primes dividing `2d` the local factor is `1`. -/
lemma coeff_localSeries_curveD_of_dvd (h : ((primesEquiv v : ℕ) : ℤ) ∣ 2 * d)
    (hmin : ¬ ((primesEquiv v : ℕ) : ℤ) ^ 12 ∣ 64 * d ^ 6) (k : ℕ) :
    PowerSeries.coeff k (localSeries (curveD ℚ (d : ℚ)) v) = if k = 0 then 1 else 0 := by
  have hnu : ¬ IsUnit (2 * ((d : ℤ) : v.adicCompletionIntegers ℚ)) := by
    have := (isUnit_intCast_iff v (2 * d)).not.2 (not_not.2 h)
    rwa [Int.cast_mul, Int.cast_ofNat] at this
  have h64 : ¬ (((primesEquiv v : ℕ) : ℕ) : v.adicCompletionIntegers ℚ) ^ 12 ∣
      (64 * ((d : ℤ) : v.adicCompletionIntegers ℚ) ^ 6) := by
    have := not_pow_dvd_intCast v hmin
    rwa [Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at this
  rw [localSeries_curveD,
    localPolynomial_curveD_of_not_isUnit _ (irreducible_natCast_primesEquiv v) h64 hnu,
    ← cmPow_zero_zero]
  have := coeff_invOfUnit_eq_cmPow 0 0 k
  simpa using this

end Posto

variable (d : ℤ)

theorem LFunction_curveD_prime_pow_of_not_dvd {p : ℕ} [hp : Fact p.Prime]
    (h : ¬ (p : ℤ) ∣ 2 * d) (k : ℕ) :
    (curveD ℚ (d : ℚ)).LFunction (p ^ k) =
      cmPow p (curveD (ZMod p) ((d : ℤ) : ZMod p)).frobeniusTrace k := by
  have hv := primesEquiv_placeOfPrime hp.out
  rw [LFunction_apply_prime_pow_eq_coeff (curveD ℚ (d : ℚ)) hp.out k,
    coeff_localSeries_curveD_of_not_dvd _ d (by rw [hv]; exact h),
    frobeniusTrace_curveD_congr (ZMod.ringEquivCongr hv), map_intCast, hv]

theorem LFunction_curveD_prime_pow_of_dvd {p : ℕ} [hp : Fact p.Prime] (h : (p : ℤ) ∣ 2 * d)
    (hmin : ¬ (p : ℤ) ^ 12 ∣ 64 * d ^ 6) {k : ℕ} (hk : k ≠ 0) :
    (curveD ℚ (d : ℚ)).LFunction (p ^ k) = 0 := by
  have hv := primesEquiv_placeOfPrime hp.out
  rw [LFunction_apply_prime_pow_eq_coeff (curveD ℚ (d : ℚ)) hp.out k,
    coeff_localSeries_curveD_of_dvd _ d (by rw [hv]; exact h) (by rw [hv]; exact hmin),
    if_neg hk]

/-- **The twist**: for `p ∤ 2d` the trace of `y² = x³ − d²x` over `ZMod p` is
`(d/p) · cmPrime p`. -/
theorem frobeniusTrace_curveD_zmod {p : ℕ} [hp : Fact p.Prime] (h : ¬ (p : ℤ) ∣ 2 * d) :
    (curveD (ZMod p) ((d : ℤ) : ZMod p)).frobeniusTrace = jacobiSym d p * cmPrime p := by
  classical
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact h (Dvd.intro d rfl)
  have hd : ((d : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun hd => h (Dvd.dvd.mul_left hd 2)
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  rw [frobeniusTrace_curveD hF hd, ← LFunction_curve_prime hp2,
    LFunction_curve_prime_eq_cmPrime hp2, ← jacobiSym.legendreSym.to_jacobiSym]
  rfl

/-- **The L-series of `y² = x³ − d²x` is the twisted sequence.** -/
theorem LFunction_curveD_eq_cmCoeffTw
    (hmin : ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ^ 12 ∣ 64 * d ^ 6) (n : ℕ) :
    (curveD ℚ (d : ℚ)).LFunction n = cmCoeffTw d n := by
  by_cases hn : n = 0
  · subst hn
    simp [cmCoeffTw]
  rw [cmCoeffTw, if_neg hn,
    (curveD ℚ (d : ℚ)).isMultiplicative_LFunction.multiplicative_factorization _ hn]
  refine Finsupp.prod_congr fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)
  have hk : n.factorization p ≠ 0 := Finsupp.mem_support_iff.1 hp
  haveI : Fact p.Prime := ⟨hpp⟩
  by_cases h : (p : ℤ) ∣ 2 * d
  · rw [if_pos h, LFunction_curveD_prime_pow_of_dvd d h (hmin p hpp) hk]
  · rw [if_neg h, LFunction_curveD_prime_pow_of_not_dvd d h, frobeniusTrace_curveD_zmod d h]

/-- For `d` odd and squarefree the equation is minimal at every prime. -/
lemma not_pow_twelve_dvd_of_odd_squarefree {d : ℤ} (hodd : Odd d) (hsq : Squarefree d) (p : ℕ)
    (hp : p.Prime) : ¬ (p : ℤ) ^ 12 ∣ 64 * d ^ 6 := by
  intro h
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  by_cases h2 : p = 2
  · subst h2
    have h' : (2 : ℤ) ^ 6 * 2 ^ 6 ∣ 2 ^ 6 * d ^ 6 := by
      have e1 : ((2 : ℕ) : ℤ) ^ 12 = 2 ^ 6 * 2 ^ 6 := by norm_num
      have e2 : (64 : ℤ) * d ^ 6 = 2 ^ 6 * d ^ 6 := by norm_num
      rwa [e1, e2] at h
    have h'' : (2 : ℤ) ^ 6 ∣ d ^ 6 := (mul_dvd_mul_iff_left (by norm_num)).1 h'
    have h2d : (2 : ℤ) ∣ d :=
      Int.prime_two.dvd_of_dvd_pow (dvd_trans (dvd_pow_self 2 (by norm_num)) h'')
    exact (Int.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2d)
  · have hcop : IsCoprime ((p : ℤ) ^ 12) 64 := by
      have h2' : IsCoprime (p : ℤ) 2 := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        have : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 h2
        simpa [Int.gcd] using this
      have : (64 : ℤ) = 2 ^ 6 := by norm_num
      rw [this]
      exact IsCoprime.pow h2'
    have h' : (p : ℤ) ^ 12 ∣ d ^ 6 := hcop.dvd_of_dvd_mul_left h
    have e : (p : ℤ) ^ 12 = ((p : ℤ) ^ 2) ^ 6 := by ring
    rw [e] at h'
    have hpd : (p : ℤ) ^ 2 ∣ d := (Int.pow_dvd_pow_iff (by norm_num)).1 h'
    rw [sq] at hpd
    exact hpZ.not_unit (hsq _ hpd)

/-- **For `d` odd and squarefree**, the L-series of `y² = x³ − d²x` is the
twisted sequence. -/
theorem LFunction_curveD_eq_cmCoeffTw_of_odd_squarefree {d : ℤ} (hodd : Odd d)
    (hsq : Squarefree d) (n : ℕ) : (curveD ℚ (d : ℚ)).LFunction n = cmCoeffTw d n :=
  LFunction_curveD_eq_cmCoeffTw d (not_pow_twelve_dvd_of_odd_squarefree hodd hsq) n

end CMPoints
