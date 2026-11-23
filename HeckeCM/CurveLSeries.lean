/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/- The notice above is reproduced from the original file and covers the two theorems
`isMultiplicative_localEulerFactor` and `isMultiplicative_LFunction` below, copied with
modifications; the rest of this file is not from that source. See `THIRD_PARTY.md`; the license
text is in `LICENSE-APACHE-2.0`. -/
import HeckeCM.CurveGlobal
import HeckeCM.CurveGauss

/-!
# The L-series of `y² = x³ - x` is the sequence in closed form

`LFunction_curve_eq_cmCoeff`: for every `n`, the `n`-th coefficient of the
Mathlib L-series of the curve `y² = x³ - x` over `ℚ` is `cmCoeff n`.

Lean 4.33.1 version of `cm-pointcount/CMPoints/LSeries.lean`. The two lemmas
on the multiplicativity of the L-series are copied from Tau Ceti
(`TauCeti/AlgebraicGeometry/EllipticCurve/LFunction/Basic.lean`, commit
`b608709b`, Apache 2.0).
-/

namespace WeierstrassCurve

open ArithmeticFunction IsDedekindDomain NumberField

/-- **The local Euler factor of a Weierstrass curve is multiplicative.** (Tau Ceti) -/
theorem isMultiplicative_localEulerFactor (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve K) : (W.localEulerFactor R).IsMultiplicative := by
  have hc : (W.localPowerSeries R).constantCoeff = 1 := by
    simp [localPowerSeries, PowerSeries.constantCoeff_invOfUnit]
  by_cases hq : IsPrimePow (Nat.card (IsLocalRing.ResidueField R))
  · exact isMultiplicative_ofPowerSeries_of_isPrimePow _ hq _ hc
  · have : Nat.card (IsLocalRing.ResidueField R) = 0 := by
      by_contra h
      have := Nat.finite_of_card_ne_zero h
      let := Fintype.ofFinite (IsLocalRing.ResidueField R)
      exact hq (Nat.card_eq_fintype_card (α := IsLocalRing.ResidueField R) ▸
        FiniteField.isPrimePow_card _)
    rw [localEulerFactor, this]
    simp [ofPowerSeries, hc]

/-- **The `L`-function of a Weierstrass curve is multiplicative.** (Tau Ceti) -/
theorem isMultiplicative_LFunction {K : Type*} [Field K] [NumberField K] (W : WeierstrassCurve K) :
    W.LFunction.IsMultiplicative :=
  isMultiplicative_eulerProduct _ fun _ ↦ isMultiplicative_localEulerFactor _ _

end WeierstrassCurve


open WeierstrassCurve IsLocalRing IsDedekindDomain NumberField Rat.HeightOneSpectrum
  Polynomial LSeriesConv

namespace CMPoints

/-- The coefficients of the inverse of `1 - a T + q T²` satisfy the two-step recurrence. -/
lemma coeff_invOfUnit_add_two (a q : ℤ) (k : ℕ) :
    PowerSeries.coeff (k + 2) (PowerSeries.invOfUnit
        ((1 - C a * X + C q * X ^ 2 : ℤ[X]) : PowerSeries ℤ) 1) =
      a * PowerSeries.coeff (k + 1) (PowerSeries.invOfUnit
        ((1 - C a * X + C q * X ^ 2 : ℤ[X]) : PowerSeries ℤ) 1) -
      q * PowerSeries.coeff k (PowerSeries.invOfUnit
        ((1 - C a * X + C q * X ^ 2 : ℤ[X]) : PowerSeries ℤ) 1) := by
  have hP : ((1 - C a * X + C q * X ^ 2 : ℤ[X]) : PowerSeries ℤ) =
      1 - PowerSeries.C a * PowerSeries.X + PowerSeries.C q * PowerSeries.X ^ 2 := by
    simp only [Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_pow,
      Polynomial.coe_one, Polynomial.coe_C, Polynomial.coe_X]
  rw [hP]
  set P : PowerSeries ℤ := 1 - PowerSeries.C a * PowerSeries.X + PowerSeries.C q * PowerSeries.X ^ 2
    with hPdef
  set g := PowerSeries.invOfUnit P 1 with hg
  have hmul : P * g = 1 := PowerSeries.mul_invOfUnit P 1 (by simp [hPdef])
  have e : P * g = g - PowerSeries.C a * (PowerSeries.X * g) +
      PowerSeries.C q * (PowerSeries.X ^ 2 * g) := by
    rw [hPdef]; ring
  have h2 := congrArg (PowerSeries.coeff (k + 2)) hmul
  rw [e] at h2
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_X_pow_mul, PowerSeries.coeff_one] at h2
  have h0 : ¬ (k + 2 = 0) := by omega
  rw [if_neg h0] at h2
  linarith

/-- The coefficients of the inverse of `1 - a T + p T²` are `cmPow p a`. -/
lemma coeff_invOfUnit_eq_cmPow (a : ℤ) (p k : ℕ) :
    PowerSeries.coeff k (PowerSeries.invOfUnit
      ((1 - C a * X + C (p : ℤ) * X ^ 2 : ℤ[X]) : PowerSeries ℤ) 1) = cmPow p a k := by
  induction k using Nat.twoStepInduction with
  | zero =>
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_invOfUnit]
    simp [cmPow]
  | one => rw [coeff_one_invOfUnit]; rfl
  | more k ih1 ih2 => rw [coeff_invOfUnit_add_two, ih2, ih1]; rfl

lemma cmPow_zero_zero (k : ℕ) : cmPow 0 0 k = if k = 0 then 1 else 0 := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more k _ _ => simp [cmPow]

section Posto

variable (v : HeightOneSpectrum (𝓞 ℚ))

/-- At odd primes the coefficients of the local factor follow the recurrence. -/
lemma coeff_localSeries_of_ne_two (h : (primesEquiv v : ℕ) ≠ 2) (k : ℕ) :
    PowerSeries.coeff k (localSeries (CurveX3SubX.curve ℚ) v) =
      cmPow (primesEquiv v : ℕ)
        (PowerSeries.coeff 1 (localSeries (CurveX3SubX.curve ℚ) v)) k := by
  have h2 : IsUnit (2 : v.adicCompletionIntegers ℚ) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    intro h0
    have := congrArg (residueEquiv v) h0
    simp only [map_ofNat, map_zero] at this
    have hdvd : (primesEquiv v : ℕ) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 _).1 (by exact_mod_cast this)
    exact h ((Nat.prime_dvd_prime_iff_eq (primesEquiv v).2 Nat.prime_two).1 hdvd)
  rw [localSeries_curve, localPolynomial_curve_of_isUnit_two _ h2, card_residueField,
    coeff_invOfUnit_eq_cmPow, coeff_one_invOfUnit]

/-- At the prime 2 the coefficients of the local factor are `1, 0, 0, …`. -/
lemma coeff_localSeries_of_eq_two (h : (primesEquiv v : ℕ) = 2) (k : ℕ) :
    PowerSeries.coeff k (localSeries (CurveX3SubX.curve ℚ) v) = if k = 0 then 1 else 0 := by
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
  rw [localSeries_curve, localPolynomial_curve_of_irreducible_two _ h2, ← cmPow_zero_zero]
  have := coeff_invOfUnit_eq_cmPow 0 0 k
  simpa using this

end Posto

/-- The powers of an odd prime follow the recurrence. -/
theorem LFunction_curve_prime_pow {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (k : ℕ) :
    (CurveX3SubX.curve ℚ).LFunction (p ^ k) = cmPow p ((CurveX3SubX.curve ℚ).LFunction p) k := by
  have hv := primesEquiv_placeOfPrime hp.out
  have h1 := LFunction_apply_prime_pow_eq_coeff (CurveX3SubX.curve ℚ) hp.out 1
  rw [pow_one] at h1
  rw [LFunction_apply_prime_pow_eq_coeff (CurveX3SubX.curve ℚ) hp.out k,
    coeff_localSeries_of_ne_two _ (by rw [hv]; exact hp2), hv, h1]

/-- The positive powers of 2 have zero coefficient. -/
theorem LFunction_curve_two_pow {k : ℕ} (hk : k ≠ 0) :
    (CurveX3SubX.curve ℚ).LFunction (2 ^ k) = 0 := by
  have hv := primesEquiv_placeOfPrime Nat.prime_two
  rw [LFunction_apply_prime_pow_eq_coeff (CurveX3SubX.curve ℚ) Nat.prime_two k,
    coeff_localSeries_of_eq_two _ hv, if_neg hk]

/-- The coefficient at an odd prime is `cmPrime p`. -/
theorem LFunction_curve_prime_eq_cmPrime {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    (CurveX3SubX.curve ℚ).LFunction p = cmPrime p := by
  have hodd : p % 2 = 1 := (hp.out.eq_two_or_odd).resolve_left hp2
  rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h | h
  · have inst : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
      CyclotomicField.isCyclotomicExtension 4 ℚ
    obtain ⟨a, b, hab, hpair, htr⟩ :=
      exists_primary_frobeniusTrace_zmod (CyclotomicField 4 ℚ) (p := p) h
    rw [LFunction_curve_prime hp2, htr, cmPrime, if_pos h, cmA_eq hp.out hab hpair]
  · rw [LFunction_curve_prime_of_mod_four_eq_three h, cmPrime, if_neg (by omega)]

/-- **The L-series of `y² = x³ - x` is the sequence in closed form.** -/
theorem LFunction_curve_eq_cmCoeff (n : ℕ) :
    (CurveX3SubX.curve ℚ).LFunction n = cmCoeff n := by
  by_cases hn : n = 0
  · subst hn
    simp [cmCoeff]
  rw [cmCoeff, if_neg hn,
    (CurveX3SubX.curve ℚ).isMultiplicative_LFunction.multiplicative_factorization _ hn]
  refine Finsupp.prod_congr fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)
  have hk : n.factorization p ≠ 0 := Finsupp.mem_support_iff.1 hp
  by_cases h2 : p = 2
  · subst h2
    rw [if_pos rfl, LFunction_curve_two_pow hk]
  · haveI : Fact p.Prime := ⟨hpp⟩
    rw [if_neg h2, LFunction_curve_prime_pow h2, LFunction_curve_prime_eq_cmPrime h2]

end CMPoints
