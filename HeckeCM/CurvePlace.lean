import HeckeCM.EulerAtPrime

/-!
# The `p^k`-th coefficient of the L-series of a curve over `ℚ`

`LFunction_apply_prime_pow_eq_coeff`: it is the coefficient of `T^k` in the local
factor at `p`. Lean 4.33.1 version of the part of
`lseries-convergence/LSeriesConv/Main.lean` that does not use Hasse's bound.
-/

open IsDedekindDomain IsLocalRing NumberField Rat.HeightOneSpectrum PowerSeries

namespace LSeriesConv

/-- The local factor of the L-series at a finite place, as a power series.
Defined over a generic number field so that the algebra structure on the
completion is the one used by Mathlib in the definition of the L-series. -/
noncomputable abbrev localSeries {K : Type*} [Field K] [NumberField K] (W : WeierstrassCurve K)
    (v : HeightOneSpectrum (𝓞 K)) : PowerSeries ℤ :=
  (W.baseChange (v.adicCompletion K)).localPowerSeries (v.adicCompletionIntegers K)

lemma LFunction_eq_eulerProduct {K : Type*} [Field K] [NumberField K] (W : WeierstrassCurve K) :
    W.LFunction = ArithmeticFunction.eulerProduct fun v : HeightOneSpectrum (𝓞 K) =>
      ArithmeticFunction.ofPowerSeries (Nat.card (ResidueField (v.adicCompletionIntegers K)))
        (localSeries W v) := rfl

lemma constantCoeff_localSeries {K : Type*} [Field K] [NumberField K] (W : WeierstrassCurve K)
    (v : HeightOneSpectrum (𝓞 K)) : constantCoeff (localSeries W v) = 1 :=
  by simp [WeierstrassCurve.localPowerSeries, PowerSeries.constantCoeff_invOfUnit]

section Posto

variable (v : HeightOneSpectrum (𝓞 ℚ))

instance : Fact (Nat.Prime (primesEquiv v : ℕ)) := ⟨(primesEquiv v).2⟩

/-- The residue field of the completion of `ℚ` at the place `v` is `ℤ/p`. -/
noncomputable def residueEquiv :
    ResidueField (v.adicCompletionIntegers ℚ) ≃+* ZMod (primesEquiv v : ℕ) :=
  (ResidueField.mapEquiv
    (adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv).trans PadicInt.residueField

lemma card_residueField :
    Nat.card (ResidueField (v.adicCompletionIntegers ℚ)) = (primesEquiv v : ℕ) := by
  rw [Nat.card_congr (residueEquiv v).toEquiv, Nat.card_zmod]

lemma one_lt_card_residueField :
    1 < Nat.card (ResidueField (v.adicCompletionIntegers ℚ)) := by
  rw [card_residueField]
  exact (primesEquiv v).2.one_lt

instance : Finite (ResidueField (v.adicCompletionIntegers ℚ)) :=
  Nat.finite_of_card_ne_zero (by have := one_lt_card_residueField v; omega)

end Posto

/-- The place of `ℚ` associated to the prime `p`. -/
noncomputable def placeOfPrime {p : ℕ} (hp : p.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  primesEquiv.symm ⟨p, hp⟩

lemma primesEquiv_placeOfPrime {p : ℕ} (hp : p.Prime) :
    (primesEquiv (placeOfPrime hp) : ℕ) = p :=
  congrArg Subtype.val (primesEquiv.apply_symm_apply ⟨p, hp⟩)

variable (W : WeierstrassCurve ℚ)

/-- The `p^k`-th coefficient of the L-series is the coefficient of `T^k` in the
local factor at `p`. -/
theorem LFunction_apply_prime_pow_eq_coeff {p : ℕ} (hp : p.Prime) (k : ℕ) :
    W.LFunction (p ^ k) = coeff k (localSeries W (placeOfPrime hp)) := by
  let q : HeightOneSpectrum (𝓞 ℚ) → ℕ := fun v =>
    Nat.card (ResidueField (v.adicCompletionIntegers ℚ))
  let f : HeightOneSpectrum (𝓞 ℚ) → PowerSeries ℤ := fun v => localSeries W v
  have hq : ∀ v, q v = (primesEquiv v : ℕ) := card_residueField
  have hqinj : Function.Injective q := by
    intro v w hvw
    rw [hq, hq] at hvw
    exact primesEquiv.injective (Subtype.ext hvw)
  have hf : ∀ v, constantCoeff (f v) = 1 := fun v => constantCoeff_localSeries W v
  set v₀ : HeightOneSpectrum (𝓞 ℚ) := placeOfPrime hp with hv₀def
  have hv₀ : (primesEquiv v₀ : ℕ) = p := primesEquiv_placeOfPrime hp
  have hne : ∀ v, v ≠ v₀ → ∀ m j, j ≠ 0 → q v ^ m ≠ p ^ j := by
    intro v hv m j hj hk
    apply hv
    have hqv : (q v).Prime := by rw [hq]; exact (primesEquiv v).2
    have hdvd : q v ∣ p := by
      rcases m with _ | m
      · rw [pow_zero] at hk
        exact absurd hk (Nat.one_lt_pow hj hp.one_lt).ne
      · have : q v ∣ p ^ j := by
          rw [← hk]
          exact dvd_pow_self _ (Nat.succ_ne_zero m)
        exact hqv.dvd_of_dvd_pow this
    have heq : (primesEquiv v : ℕ) = p := by
      rw [← hq]
      exact (Nat.prime_dvd_prime_iff_eq hqv hp).1 hdvd
    apply primesEquiv.injective
    apply Subtype.ext
    rw [heq, hv₀]
  have key := eulerProduct_apply_prime_pow q hqinj (fun v => one_lt_card_residueField v) f hf hp
    v₀ (by rw [hq, hv₀]) hne k
  rw [LFunction_eq_eulerProduct]
  exact key

end LSeriesConv
