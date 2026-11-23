import HeckeCM.CurveGlobalD

/-!
# `y² = x³ − d²x` when `d` has square factors

If `d = d' m²`, the curve `y² = x³ − d²x` is obtained from `y² = x³ − d'²x` by the
change of variables `(x, y) ↦ (m² x, m³ y)`, and the two have the same
local polynomial at every place where the equation with `d'` is minimal
(`localPolynomial_smul_curveD`). Hence they have the same L-series
(`LFunction_curveD_mul_sq`, for `d'` odd and squarefree).

This is not the general theorem on the invariance of the L-series under a change
of variables: we use that for these curves the reduction is good or additive,
never multiplicative.
-/

open WeierstrassCurve IsLocalRing IsDedekindDomain NumberField Rat.HeightOneSpectrum
  Polynomial LSeriesConv

namespace CMPoints

/-- `y² = x³ − (δ μ²)² x` is `y² = x³ − δ² x` after the change of variables with
factor `u = μ⁻¹`. -/
lemma curveD_mul_sq {F : Type*} [Field F] (δ μ : F) (hμ : μ ≠ 0) :
    curveD F (δ * μ ^ 2) =
      (⟨(Units.mk0 μ hμ)⁻¹, 0, 0, 0⟩ : VariableChange F) • curveD F δ := by
  ext
  · simp [curveD, variableChange_a₁]
  · simp [curveD, variableChange_a₂]
  · simp [curveD, variableChange_a₃]
  · simp [curveD, variableChange_a₄]
    ring
  · simp [curveD, variableChange_a₆]

section Locale

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*}
  [Field K] [Algebra R K] [IsFractionRing R K]

variable {ϖ : R} (hϖ : Irreducible ϖ) (d : R) (h64 : ¬ ϖ ^ 12 ∣ (64 * d ^ 6 : R))
  (D : VariableChange K)
include hϖ h64

/-- The minimal model chosen by Mathlib for a transform of
`y² = x³ − d²x` has the same local invariants as the starting equation. -/
lemma minimal_smul_curveD_facts [Finite (ResidueField R)] :
    haveI := isMinimal_curveD (K := K) hϖ d h64
    HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R)
        ((D • curveD K (algebraMap R K d)).minimal R).Δ =
      HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R)
        (algebraMap R K (64 * d ^ 6)) ∧
    HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R)
        ((D • curveD K (algebraMap R K d)).minimal R).c₄ =
      HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R)
        (algebraMap R K (48 * d ^ 2)) ∧
    (((D • curveD K (algebraMap R K d)).minimal R).reduction R).frobeniusTrace =
      (curveD (ResidueField R) (residue R d)).frobeniusTrace := by
  have := isMinimal_curveD (K := K) hϖ d h64
  have := isElliptic_curveD (K := K) hϖ d h64
  have eΔ : algebraMap R K (64 * d ^ 6) = 64 * (algebraMap R K d) ^ 6 := by
    rw [map_mul, map_pow, map_ofNat]
  have ec : algebraMap R K (48 * d ^ 2) = 48 * (algebraMap R K d) ^ 2 := by
    rw [map_mul, map_pow, map_ofNat]
  obtain ⟨C, hC⟩ := (D • curveD K (algebraMap R K d)).exists_smul_eq_minimal R
  have hCD : (C * D) • curveD K (algebraMap R K d) =
      (D • curveD K (algebraMap R K d)).minimal R := by
    rw [mul_smul, hC]
  refine ⟨?_, ?_, ?_⟩
  · rw [valuation_Δ_eq_of_isMinimal_smul R (C * D) hCD, Δ_curveD, eΔ]
  · rw [valuation_c₄_eq_of_isMinimal_smul R (C * D) hCD, c₄_curveD, ec]
  · obtain ⟨E, hE⟩ := exists_smul_reduction_eq_of_isMinimal_smul R (C * D) hCD
    rw [← hE, variableChange_frobeniusTrace]
    congr 1
    rw [reduction, integralModel_eq_of_baseChange_eq
      (show (curveD R d).baseChange K = _ from map_curveD _ d), map_curveD]

/-- **The local polynomial does not change under a change of variables**, for the
curves `y² = x³ − d²x` with minimal equation. -/
theorem localPolynomial_smul_curveD [Finite (ResidueField R)] :
    (D • curveD K (algebraMap R K d)).localPolynomial R =
      (curveD K (algebraMap R K d)).localPolynomial R := by
  by_cases h2d : IsUnit (2 * d)
  · rw [localPolynomial_curveD_of_isUnit R h2d]
    have hu64 : IsUnit (64 * d ^ 6 : R) := by
      have : (64 * d ^ 6 : R) = (2 * d) ^ 6 := by ring
      rw [this]
      exact h2d.pow 6
    obtain ⟨hΔ, -, htr⟩ := minimal_smul_curveD_facts (K := K) hϖ d h64 D
    have hgood : ((D • curveD K (algebraMap R K d)).minimal R).HasGoodReduction R := by
      rw [hasGoodReduction_iff]
      exact ⟨inferInstance, by rw [hΔ, valuation_algebraMap_eq_one_iff]; exact hu64⟩
    haveI : (((D • curveD K (algebraMap R K d)).minimal R).reduction R).IsElliptic :=
      (hasGoodReduction_iff_isElliptic_reduction R).1 hgood
    rw [← htr, frobeniusTrace_eq_card_point, localPolynomial, if_pos hgood]
  · rw [localPolynomial_curveD_of_not_isUnit R hϖ h64 h2d]
    obtain ⟨hΔ, hc₄, -⟩ := minimal_smul_curveD_facts (K := K) hϖ d h64 D
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

/-- Two curves with the same local polynomials have the same L-series. -/
theorem LFunction_congr {K : Type*} [Field K] [NumberField K] {W₁ W₂ : WeierstrassCurve K}
    (h : ∀ v : HeightOneSpectrum (𝓞 K),
      (W₁.baseChange (v.adicCompletion K)).localPolynomial (v.adicCompletionIntegers K) =
        (W₂.baseChange (v.adicCompletion K)).localPolynomial (v.adicCompletionIntegers K)) :
    W₁.LFunction = W₂.LFunction := by
  unfold WeierstrassCurve.LFunction
  congr 1
  funext v
  unfold WeierstrassCurve.localEulerFactor WeierstrassCurve.localPowerSeries
  rw [h v]

/-- **`y² = x³ − (d' m²)² x` and `y² = x³ − d'² x` have the same L-series**, for
`d'` odd and squarefree and `m ≠ 0`. -/
theorem LFunction_curveD_mul_sq {d' : ℤ} (hodd : Odd d') (hsq : Squarefree d') {m : ℤ}
    (hm : m ≠ 0) :
    (curveD ℚ ((d' * m ^ 2 : ℤ) : ℚ)).LFunction = (curveD ℚ (d' : ℚ)).LFunction := by
  refine LFunction_congr fun v => ?_
  have hmv : algebraMap ℚ (v.adicCompletion ℚ) (m : ℚ) ≠ 0 :=
    (_root_.map_ne_zero _).2 (Int.cast_ne_zero.2 hm)
  have e2 : (curveD ℚ (d' : ℚ)).baseChange (v.adicCompletion ℚ) =
      curveD (v.adicCompletion ℚ) (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)
        ((d' : ℤ) : v.adicCompletionIntegers ℚ)) := by
    rw [WeierstrassCurve.baseChange, map_curveD, map_intCast, map_intCast]
  have e1 : (curveD ℚ ((d' * m ^ 2 : ℤ) : ℚ)).baseChange (v.adicCompletion ℚ) =
      (⟨(Units.mk0 _ hmv)⁻¹, 0, 0, 0⟩ : VariableChange (v.adicCompletion ℚ)) •
        curveD (v.adicCompletion ℚ) (algebraMap (v.adicCompletionIntegers ℚ)
          (v.adicCompletion ℚ) ((d' : ℤ) : v.adicCompletionIntegers ℚ)) := by
    rw [← curveD_mul_sq, WeierstrassCurve.baseChange, map_curveD]
    congr 1
    rw [map_intCast (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) d',
      map_intCast (algebraMap ℚ (v.adicCompletion ℚ)) m, map_intCast]
    push_cast
    rfl
  have h64 : ¬ (((primesEquiv v : ℕ) : ℕ) : v.adicCompletionIntegers ℚ) ^ 12 ∣
      (64 * ((d' : ℤ) : v.adicCompletionIntegers ℚ) ^ 6) := by
    have := not_pow_dvd_intCast v
      (not_pow_twelve_dvd_of_odd_squarefree hodd hsq _ (primesEquiv v).2)
    rwa [Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at this
  rw [e1, e2]
  exact localPolynomial_smul_curveD (irreducible_natCast_primesEquiv v) _ h64 _

end CMPoints
