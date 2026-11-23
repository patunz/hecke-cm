import HeckeCM.CurveModel

/-!
# The local polynomial of `y² = x³ - x`

Over a discrete valuation ring `R` with fraction field `K` and finite residue
field:

* `localPolynomial_curve_of_isUnit_two`: if `2` is invertible in `R`, the
  local polynomial of `y² = x³ - x` is `1 - a T + q T²`, with `a` the Frobenius
  trace of the same equation over the residue field;
* `localPolynomial_curve_of_irreducible_two`: if `2` is a uniformizer, the
  local polynomial is `1` (additive reduction).

The point is that the equation `y² = x³ - x`, of discriminant `64`, is already
minimal in both cases, and that two minimal models have reductions with the
same number of points.

Lean 4.33.1 version of `cm-pointcount/CMPoints/Local.lean`: the Tau Ceti lemmas
used are in `CurveModel.lean`; the two lemmas on the local polynomial are
replaced by a direct unfolding of the Mathlib definition.
-/

open WeierstrassCurve IsLocalRing IsDedekindDomain CMPoints Polynomial

namespace CMPoints

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*}
  [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
lemma baseChange_curve : (CurveX3SubX.curve R).baseChange K = CurveX3SubX.curve K :=
  CurveX3SubX.map_curve _

lemma c₄_curve (S : Type*) [CommRing S] : (CurveX3SubX.curve S).c₄ = 48 := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, CurveX3SubX.curve]
  ring

/-- The valuation of an element of `R` is `1` if and only if it is invertible. -/
lemma valuation_algebraMap_eq_one_iff (r : R) :
    HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) (algebraMap R K r) = 1 ↔
      IsUnit r := by
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
  exact IsLocalRing.notMem_maximalIdeal

lemma valuation_algebraMap_lt_one_iff (r : R) :
    HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) (algebraMap R K r) < 1 ↔
      ¬ IsUnit r := by
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_lt_one_iff_mem]
  exact IsLocalRing.mem_maximalIdeal r

section Minimale

variable {R} {ϖ : R} (hϖ : Irreducible ϖ) (h64 : ¬ ϖ ^ 12 ∣ (64 : R))
include hϖ h64

lemma isMinimal_curve : IsMinimal R (CurveX3SubX.curve K) := by
  have := isMinimal_baseChange_of_not_pow_twelve_dvd_Δ R (K := K) (CurveX3SubX.curve R) hϖ
    (by rwa [CurveX3SubX.Δ_curve])
  rwa [baseChange_curve] at this

omit [IsDomain R] [IsDiscreteValuationRing R] hϖ in
lemma isElliptic_curve : (CurveX3SubX.curve K).IsElliptic := by
  rw [isElliptic_iff, CurveX3SubX.Δ_curve, isUnit_iff_ne_zero]
  have h0 : (64 : R) ≠ 0 := fun h => h64 (h ▸ dvd_zero _)
  have : (64 : K) = algebraMap R K 64 := (map_ofNat _ 64).symm
  rw [this]
  exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 h0

/-- The minimal model chosen by Mathlib and the equation `y² = x³ - x` have the
same valuation of the discriminant and of `c₄`, and reductions with the same
Frobenius trace. -/
lemma minimal_curve_facts [Finite (ResidueField R)] :
    haveI := isMinimal_curve (K := K) hϖ h64
    HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R)
        ((CurveX3SubX.curve K).minimal R).Δ =
      HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) (algebraMap R K 64) ∧
    HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R)
        ((CurveX3SubX.curve K).minimal R).c₄ =
      HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R) (algebraMap R K 48) ∧
    (((CurveX3SubX.curve K).minimal R).reduction R).frobeniusTrace =
      (CurveX3SubX.curve (ResidueField R)).frobeniusTrace := by
  have := isMinimal_curve (K := K) hϖ h64
  have := isElliptic_curve (K := K) h64
  obtain ⟨D, hD⟩ := (CurveX3SubX.curve K).exists_smul_eq_minimal R
  refine ⟨?_, ?_, ?_⟩
  · rw [valuation_Δ_eq_of_isMinimal_smul R D hD, CurveX3SubX.Δ_curve,
      ← map_ofNat (algebraMap R K) 64]
  · rw [valuation_c₄_eq_of_isMinimal_smul R D hD, c₄_curve, ← map_ofNat (algebraMap R K) 48]
  · obtain ⟨C, hC⟩ := exists_smul_reduction_eq_of_isMinimal_smul R D hD
    rw [← hC, variableChange_frobeniusTrace]
    congr 1
    rw [reduction, integralModel_eq_of_baseChange_eq (baseChange_curve R), CurveX3SubX.map_curve]

end Minimale

variable [Finite (ResidueField R)]

/-- **Good reduction**: if `2` is invertible in `R`, the local polynomial of
`y² = x³ - x` is `1 - a T + q T²`. -/
theorem localPolynomial_curve_of_isUnit_two (h2 : IsUnit (2 : R)) :
    (CurveX3SubX.curve K).localPolynomial R =
      1 - C (CurveX3SubX.curve (ResidueField R)).frobeniusTrace * X +
        C (Nat.card (ResidueField R) : ℤ) * X ^ 2 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hu64 : IsUnit (64 : R) := by
    have : (64 : R) = 2 ^ 6 := by norm_num
    rw [this]
    exact h2.pow 6
  have h64 : ¬ ϖ ^ 12 ∣ (64 : R) := fun h =>
    hϖ.not_isUnit (isUnit_of_dvd_unit (dvd_trans (dvd_pow_self ϖ (by norm_num)) h) hu64)
  have := isMinimal_curve (K := K) hϖ h64
  obtain ⟨hΔ, -, htr⟩ := minimal_curve_facts (K := K) hϖ h64
  have hgood : ((CurveX3SubX.curve K).minimal R).HasGoodReduction R := by
    rw [hasGoodReduction_iff]
    exact ⟨inferInstance, by rw [hΔ, valuation_algebraMap_eq_one_iff]; exact hu64⟩
  haveI : (((CurveX3SubX.curve K).minimal R).reduction R).IsElliptic :=
    (hasGoodReduction_iff_isElliptic_reduction R).1 hgood
  rw [← htr, frobeniusTrace_eq_card_point, localPolynomial, if_pos hgood]

/-- **Additive reduction**: if `2` is a uniformizer of `R`, the local polynomial
of `y² = x³ - x` is `1`. -/
theorem localPolynomial_curve_of_irreducible_two (h2 : Irreducible (2 : R)) :
    (CurveX3SubX.curve K).localPolynomial R = 1 := by
  have h20 : (2 : R) ≠ 0 := h2.ne_zero
  have e64 : (64 : R) = 2 ^ 6 := by norm_num
  have h64 : ¬ (2 : R) ^ 12 ∣ (64 : R) := by
    rw [e64, pow_dvd_pow_iff h20 h2.not_isUnit]
    norm_num
  have := isMinimal_curve (K := K) h2 h64
  obtain ⟨hΔ, hc₄, -⟩ := minimal_curve_facts (K := K) h2 h64
  have hadd : ((CurveX3SubX.curve K).minimal R).HasAdditiveReduction R := by
    rw [hasAdditiveReduction_iff]
    refine ⟨inferInstance, ?_, ?_⟩
    · rw [hΔ, valuation_algebraMap_lt_one_iff, e64]
      exact fun h => h2.not_isUnit ((isUnit_pow_iff (by norm_num)).1 h)
    · rw [hc₄, valuation_algebraMap_lt_one_iff]
      exact fun h => h2.not_isUnit (isUnit_of_dvd_unit ⟨24, by norm_num⟩ h)
  have hbad : ¬ ((CurveX3SubX.curve K).minimal R).HasGoodReduction R := by
    intro hg
    have h1 := hg.goodReduction
    have h3 := hadd.badReduction
    rw [h1] at h3
    exact lt_irrefl _ h3
  have hmult : ¬ ((CurveX3SubX.curve K).minimal R).HasMultiplicativeReduction R :=
    hadd.not_hasMultiplicativeReduction R
  rw [localPolynomial, if_neg hbad, if_neg fun hs => hmult hs.toHasMultiplicativeReduction,
    if_neg hmult]

end CMPoints
