import HeckeCM.CurveLocal
import HeckeCM.CurvePointCount
import HeckeCM.CurvePlace

/-!
# The coefficients of the L-series of `y² = x³ - x` at primes

For the curve `E : y² = x³ - x` over `ℚ` and the Mathlib L-series
(`WeierstrassCurve.LFunction`):

* `LFunction_curve_prime`: for `p` an odd prime, `a_p` is the Frobenius trace
  of `y² = x³ - x` over `ZMod p`, that is `p + 1 - #E(𝔽_p)`;
* `LFunction_curve_two`: `a_2 = 0`;
* `LFunction_curve_prime_of_mod_four_eq_three`: if `p ≡ 3 (mod 4)`, `a_p = 0`.
-/

open WeierstrassCurve IsLocalRing IsDedekindDomain NumberField Rat.HeightOneSpectrum CMPoints
  Polynomial LSeriesConv

namespace CMPoints

/-- The coefficient of `T` in the inverse of `1 - a T + q T²` is `a`. -/
lemma coeff_one_invOfUnit (a q : ℤ) :
    PowerSeries.coeff 1
      (PowerSeries.invOfUnit ((1 - C a * X + C q * X ^ 2 : ℤ[X]) : PowerSeries ℤ) 1) = a := by
  have hanti : Finset.HasAntidiagonal.antidiagonal (1 : ℕ) = {(0, 1), (1, 0)} := by decide
  have h1 : PowerSeries.coeff 1 ((1 - C a * X + C q * X ^ 2 : ℤ[X]) : PowerSeries ℤ) = -a := by
    rw [Polynomial.coeff_coe]
    simp [Polynomial.coeff_one, Polynomial.coeff_X_pow]
  set P : PowerSeries ℤ := ((1 - C a * X + C q * X ^ 2 : ℤ[X]) : PowerSeries ℤ) with hP
  rw [PowerSeries.coeff_invOfUnit, if_neg one_ne_zero, hanti, Finset.sum_pair (by decide)]
  simp [h1, PowerSeries.constantCoeff_invOfUnit]

/-- The local factor of `y² = x³ - x`, written with the equation over the completion. -/
lemma localSeries_curve {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    localSeries (CurveX3SubX.curve K) v =
      PowerSeries.invOfUnit (((CurveX3SubX.curve (v.adicCompletion K)).localPolynomial
        (v.adicCompletionIntegers K) : ℤ[X]) : PowerSeries ℤ) 1 := by
  rw [localSeries, WeierstrassCurve.localPowerSeries,
    show (CurveX3SubX.curve K).baseChange (v.adicCompletion K) = CurveX3SubX.curve _ from
      CurveX3SubX.map_curve _]

/-- The Frobenius trace of `y² = x³ - x` is invariant under field isomorphism. -/
lemma frobeniusTrace_curve_congr {F F' : Type*} [Field F] [Field F'] [Finite F] [Finite F']
    (e : F ≃+* F') :
    (CurveX3SubX.curve F).frobeniusTrace = (CurveX3SubX.curve F').frobeniusTrace := by
  rw [frobeniusTrace_def, frobeniusTrace_def, pointCount_def, pointCount_def,
    Nat.card_congr e.toEquiv]
  congr 3
  refine Nat.card_congr (Equiv.subtypeEquiv (e.toEquiv.prodCongr e.toEquiv) fun p => ?_)
  rw [← CurveX3SubX.map_curve e.toRingHom]
  exact (Affine.map_equation _ e.injective p.1 p.2).symm

section Posto

variable (v : HeightOneSpectrum (𝓞 ℚ))

/-- At odd primes the coefficient of `T` of the local factor is the Frobenius
trace over `ZMod p`. -/
lemma coeff_one_localSeries_of_ne_two (h : (primesEquiv v : ℕ) ≠ 2) :
    PowerSeries.coeff 1 (localSeries (CurveX3SubX.curve ℚ) v) =
      (CurveX3SubX.curve (ZMod (primesEquiv v : ℕ))).frobeniusTrace := by
  have h2 : IsUnit (2 : v.adicCompletionIntegers ℚ) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    intro h0
    have := congrArg (residueEquiv v) h0
    simp only [map_ofNat, map_zero] at this
    have hdvd : (primesEquiv v : ℕ) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 _).1 (by exact_mod_cast this)
    exact h ((Nat.prime_dvd_prime_iff_eq (primesEquiv v).2 Nat.prime_two).1 hdvd)
  rw [localSeries_curve, localPolynomial_curve_of_isUnit_two _ h2, coeff_one_invOfUnit]
  exact frobeniusTrace_curve_congr (residueEquiv v)

/-- At the prime 2 the local factor is `1`. -/
lemma coeff_one_localSeries_of_eq_two (h : (primesEquiv v : ℕ) = 2) :
    PowerSeries.coeff 1 (localSeries (CurveX3SubX.curve ℚ) v) = 0 := by
  have h2 : Irreducible (2 : v.adicCompletionIntegers ℚ) := by
    let e : v.adicCompletionIntegers ℚ ≃+* ℤ_[primesEquiv v] :=
      (adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv
    rw [← MulEquiv.irreducible_iff e.toMulEquiv]
    have h2' : e.toMulEquiv (2 : v.adicCompletionIntegers ℚ) =
        ((primesEquiv v : ℕ) : ℤ_[primesEquiv v]) := by
      have : ((2 : ℕ) : ℤ_[primesEquiv v]) = ((primesEquiv v : ℕ) : ℤ_[primesEquiv v]) :=
        congrArg (Nat.cast : ℕ → ℤ_[primesEquiv v]) h.symm
      rw [← this]
      change e 2 = _
      rw [map_ofNat]
      norm_num
    rw [h2']
    exact PadicInt.irreducible_p
  rw [localSeries_curve, localPolynomial_curve_of_irreducible_two _ h2]
  simpa using coeff_one_invOfUnit 0 0

end Posto

/-- **The coefficient `a_p` of `y² = x³ - x` at an odd prime** is the Frobenius
trace over `ZMod p`, that is `p + 1 - #E(𝔽_p)`. -/
theorem LFunction_curve_prime {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    (CurveX3SubX.curve ℚ).LFunction p = (CurveX3SubX.curve (ZMod p)).frobeniusTrace := by
  have hv := primesEquiv_placeOfPrime hp.out
  have h := LFunction_apply_prime_pow_eq_coeff (CurveX3SubX.curve ℚ) hp.out 1
  rw [pow_one] at h
  rw [h, coeff_one_localSeries_of_ne_two _ (by rw [hv]; exact hp2)]
  exact frobeniusTrace_curve_congr (ZMod.ringEquivCongr hv)

/-- **The coefficient `a_2` of `y² = x³ - x` is `0`** (additive reduction). -/
theorem LFunction_curve_two : (CurveX3SubX.curve ℚ).LFunction 2 = 0 := by
  have hv := primesEquiv_placeOfPrime Nat.prime_two
  have h := LFunction_apply_prime_pow_eq_coeff (CurveX3SubX.curve ℚ) Nat.prime_two 1
  rw [pow_one] at h
  rw [h, coeff_one_localSeries_of_eq_two _ hv]

/-- **Se `p ≡ 3 (mod 4)`, `a_p = 0`.** -/
theorem LFunction_curve_prime_of_mod_four_eq_three {p : ℕ} [hp : Fact p.Prime] (h : p % 4 = 3) :
    (CurveX3SubX.curve ℚ).LFunction p = 0 := by
  rw [LFunction_curve_prime (by rintro rfl; omega)]
  classical
  exact frobeniusTrace_curve_eq_zero (by rw [ZMod.card]; exact h)

end CMPoints
