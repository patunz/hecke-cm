import HeckeCM.CurveLocal
import HeckeCM.CurveTwist

/-!
# The local polynomial of `y² = x³ − d²x`

Over a discrete valuation ring `R` with fraction field `K` and finite residue
field, for `d ∈ R` with `ϖ¹² ∤ 64 d⁶`:

* `localPolynomial_curveD_of_isUnit`: if `2d` is invertible, the local
  polynomial is `1 − a T + q T²`, with `a` the Frobenius trace of
  `y² = x³ − d̄²x` over the residue field;
* `localPolynomial_curveD_of_not_isUnit`: if `2d` is not invertible, the
  local polynomial is `1` (additive reduction).

The hypothesis `ϖ¹² ∤ 64 d⁶` guarantees that the equation is minimal. It does not
cover the case `v(2) = v(d) = 1`, in which the discriminant has valuation 12.
-/

open WeierstrassCurve IsLocalRing IsDedekindDomain CMPoints Polynomial

namespace CMPoints

lemma map_curveD {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (d : A) :
    (curveD A d).map f = curveD B (f d) := by
  ext <;> simp [curveD]

lemma Δ_curveD (S : Type*) [CommRing S] (d : S) : (curveD S d).Δ = 64 * d ^ 6 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, curveD]
  ring

lemma c₄_curveD (S : Type*) [CommRing S] (d : S) : (curveD S d).c₄ = 48 * d ^ 2 := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, curveD]
  ring

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*}
  [Field K] [Algebra R K] [IsFractionRing R K]

section Minimale

variable {R} {ϖ : R} (hϖ : Irreducible ϖ) (d : R) (h64 : ¬ ϖ ^ 12 ∣ (64 * d ^ 6 : R))
include hϖ h64

lemma isMinimal_curveD : IsMinimal R (curveD K (algebraMap R K d)) := by
  have := isMinimal_baseChange_of_not_pow_twelve_dvd_Δ R (K := K) (curveD R d) hϖ
    (by rwa [Δ_curveD])
  rwa [WeierstrassCurve.baseChange, map_curveD] at this

lemma isElliptic_curveD : (curveD K (algebraMap R K d)).IsElliptic := by
  rw [isElliptic_iff, Δ_curveD, isUnit_iff_ne_zero]
  have h0 : (64 * d ^ 6 : R) ≠ 0 := fun h => h64 (h ▸ dvd_zero _)
  have : (64 * (algebraMap R K d) ^ 6 : K) = algebraMap R K (64 * d ^ 6) := by
    rw [map_mul, map_pow, map_ofNat]
  rw [this]
  exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 h0

lemma minimal_curveD_facts [Finite (ResidueField R)] :
    haveI := isMinimal_curveD (K := K) hϖ d h64
    HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R)
        ((curveD K (algebraMap R K d)).minimal R).Δ =
      HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R)
        (algebraMap R K (64 * d ^ 6)) ∧
    HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R)
        ((curveD K (algebraMap R K d)).minimal R).c₄ =
      HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R)
        (algebraMap R K (48 * d ^ 2)) ∧
    (((curveD K (algebraMap R K d)).minimal R).reduction R).frobeniusTrace =
      (curveD (ResidueField R) (residue R d)).frobeniusTrace := by
  have := isMinimal_curveD (K := K) hϖ d h64
  have := isElliptic_curveD (K := K) hϖ d h64
  have eΔ : algebraMap R K (64 * d ^ 6) = 64 * (algebraMap R K d) ^ 6 := by
    rw [map_mul, map_pow, map_ofNat]
  have ec : algebraMap R K (48 * d ^ 2) = 48 * (algebraMap R K d) ^ 2 := by
    rw [map_mul, map_pow, map_ofNat]
  obtain ⟨D, hD⟩ := (curveD K (algebraMap R K d)).exists_smul_eq_minimal R
  refine ⟨?_, ?_, ?_⟩
  · rw [valuation_Δ_eq_of_isMinimal_smul R D hD, Δ_curveD, eΔ]
  · rw [valuation_c₄_eq_of_isMinimal_smul R D hD, c₄_curveD, ec]
  · obtain ⟨C, hC⟩ := exists_smul_reduction_eq_of_isMinimal_smul R D hD
    rw [← hC, variableChange_frobeniusTrace]
    congr 1
    rw [reduction, integralModel_eq_of_baseChange_eq
      (show (curveD R d).baseChange K = _ from map_curveD _ d), map_curveD]

end Minimale

variable [Finite (ResidueField R)]

/-- **Good reduction**: if `2d` is invertible in `R`, the local polynomial of
`y² = x³ − d²x` is `1 − a T + q T²`. -/
theorem localPolynomial_curveD_of_isUnit {d : R} (h2d : IsUnit (2 * d)) :
    (curveD K (algebraMap R K d)).localPolynomial R =
      1 - C (curveD (ResidueField R) (residue R d)).frobeniusTrace * X +
        C (Nat.card (ResidueField R) : ℤ) * X ^ 2 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hu64 : IsUnit (64 * d ^ 6 : R) := by
    have : (64 * d ^ 6 : R) = (2 * d) ^ 6 := by ring
    rw [this]
    exact h2d.pow 6
  have h64 : ¬ ϖ ^ 12 ∣ (64 * d ^ 6 : R) := fun h =>
    hϖ.not_isUnit (isUnit_of_dvd_unit (dvd_trans (dvd_pow_self ϖ (by norm_num)) h) hu64)
  have := isMinimal_curveD (K := K) hϖ d h64
  obtain ⟨hΔ, -, htr⟩ := minimal_curveD_facts (K := K) hϖ d h64
  have hgood : ((curveD K (algebraMap R K d)).minimal R).HasGoodReduction R := by
    rw [hasGoodReduction_iff]
    exact ⟨inferInstance, by rw [hΔ, valuation_algebraMap_eq_one_iff]; exact hu64⟩
  haveI : (((curveD K (algebraMap R K d)).minimal R).reduction R).IsElliptic :=
    (hasGoodReduction_iff_isElliptic_reduction R).1 hgood
  rw [← htr, frobeniusTrace_eq_card_point, localPolynomial, if_pos hgood]

/-- **Additive reduction**: if `2d` is not invertible and `ϖ¹² ∤ 64 d⁶`, the
local polynomial of `y² = x³ − d²x` is `1`. -/
theorem localPolynomial_curveD_of_not_isUnit {ϖ : R} (hϖ : Irreducible ϖ) {d : R}
    (h64 : ¬ ϖ ^ 12 ∣ (64 * d ^ 6 : R)) (h2d : ¬ IsUnit (2 * d)) :
    (curveD K (algebraMap R K d)).localPolynomial R = 1 := by
  have := isMinimal_curveD (K := K) hϖ d h64
  obtain ⟨hΔ, hc₄, -⟩ := minimal_curveD_facts (K := K) hϖ d h64
  have hadd : ((curveD K (algebraMap R K d)).minimal R).HasAdditiveReduction R := by
    rw [hasAdditiveReduction_iff]
    refine ⟨inferInstance, ?_, ?_⟩
    · rw [hΔ, valuation_algebraMap_lt_one_iff,
        show (64 * d ^ 6 : R) = (2 * d) ^ 6 by ring]
      exact fun h => h2d ((isUnit_pow_iff (by norm_num)).1 h)
    · rw [hc₄, valuation_algebraMap_lt_one_iff]
      exact fun h => h2d (isUnit_of_dvd_unit ⟨24 * d, by ring⟩ h)
  have hbad : ¬ ((curveD K (algebraMap R K d)).minimal R).HasGoodReduction R := by
    intro hg
    have h1 := hg.goodReduction
    have h3 := hadd.badReduction
    rw [h1] at h3
    exact lt_irrefl _ h3
  have hmult : ¬ ((curveD K (algebraMap R K d)).minimal R).HasMultiplicativeReduction R :=
    hadd.not_hasMultiplicativeReduction R
  rw [localPolynomial, if_neg hbad, if_neg fun hs => hmult hs.toHasMultiplicativeReduction,
    if_neg hmult]

end CMPoints
