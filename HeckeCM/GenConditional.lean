import Mathlib
import HeckeCM.GenPlaces
import Theorems.Thm_NumberField_TateGlobal_exists_entire_zetaIntegral_eq_mul_prod_Gamma_mul_eulerProduct_and_one_sub_eq_root_mul_cpow_of_archLocalChar_eq
import Theorems.Thm_NumberField_TateGlobal_exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar

/-!
# The entire continuation, given the product over the places

`exists_entire_lseries_of_hasProd_places`: let `K` be a number field and `χ` a
continuous unitary character of the idèle class group of `K`, unramified
outside a finite set, which is not an imaginary power of the norm. If for
`Re s > 1` the Euler product of `χ` over the places is the Dirichlet series
of `f` at `s + 1/2`, then this series has an entire continuation. Here `f` is
an arbitrary sequence.
-/

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal
open scoped Classical

namespace CMPoints

/-- **Entire continuation of a Dirichlet series that is the Euler product
of a Hecke character.** -/
theorem exists_entire_lseries_of_hasProd_places (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ))
    (hχu : IsUnitaryChar (𝓞 K) K χ) (hχF : IsIdeleClassChar (𝓞 K) K χ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hunr : ∀ v, v ∉ S → IsUnramifiedCharAt χ v)
    (hnot : ∀ τ₀ : ℝ, χ ≠ normPowChar K τ₀)
    (f : ℕ → ℂ)
    (hP : ∀ s : ℂ, 1 < s.re → HasProd (fun v : HeightOneSpectrum (𝓞 K) =>
        (1 - (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) (LSeries f (s + 1 / 2))) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ s : ℂ, 3 / 2 < s.re → F s = LSeries f s := by
  obtain ⟨Nf, -, hT⟩ :=
    NumberField.TateGlobal.exists_entire_zetaIntegral_eq_mul_prod_Gamma_mul_eulerProduct_and_one_sub_eq_root_mul_cpow_of_archLocalChar_eq
      K S (fun v => localChar χ v)
  obtain ⟨τ, m, hτ, hm, -⟩ :=
    NumberField.TateGlobal.exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar K χ hχu hχc
  obtain ⟨Z, A, ε, hZ, hA, -, hZeq, -⟩ :=
    (hT χ hχc hχu hχF hunr (fun v _ u _ _ => rfl) τ m hτ hm).1 hnot
  -- the inverse of the gamma factor is entire
  set Ginv : ℂ → ℂ := fun s => ∏ v : InfinitePlace K,
    (if v.IsReal then (Complex.Gammaℝ (s + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ)))⁻¹
      else (Complex.Gammaℂ (s + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2))⁻¹)
    with hGinv
  have hGdiff : Differentiable ℂ Ginv := by
    have hfac : ∀ v : InfinitePlace K, Differentiable ℂ fun s : ℂ =>
        (if v.IsReal then
          (Complex.Gammaℝ (s + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ)))⁻¹
        else (Complex.Gammaℂ (s + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2))⁻¹) := by
      intro v
      by_cases hv : v.IsReal
      · simp only [hv, if_true]
        exact Complex.differentiable_Gammaℝ_inv.comp
          ((differentiable_id.add_const _).add_const _)
      · simp only [hv, if_false]
        exact Complex.differentiable_Gammaℂ_inv.comp
          ((differentiable_id.add_const _).add_const _)
    have hall : ∀ t : Finset (InfinitePlace K), Differentiable ℂ fun s : ℂ => ∏ v ∈ t,
        (if v.IsReal then
          (Complex.Gammaℝ (s + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ)))⁻¹
        else (Complex.Gammaℂ (s + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2))⁻¹) := by
      intro t
      induction t using Finset.induction_on with
      | empty => simpa using (differentiable_const (1 : ℂ))
      | insert a t ha ih =>
        simp only [Finset.prod_insert ha]
        exact (hfac a).mul ih
    exact hall Finset.univ
  refine ⟨fun s => A⁻¹ * Z (s - 1 / 2) * Ginv (s - 1 / 2),
    ((hZ.comp (differentiable_id.sub_const _)).const_mul _).mul
      (hGdiff.comp (differentiable_id.sub_const _)), fun s hs => ?_⟩
  have hs' : 1 < (s - 1 / 2).re := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    linarith
  have hP := (hP (s - 1 / 2) hs').tprod_eq
  have hsub : s - 1 / 2 + 1 / 2 = s := by ring
  rw [hsub] at hP
  have hZs := hZeq (s - 1 / 2) hs'
  simp only at hZs
  rw [hP] at hZs
  -- the gamma factor does not vanish for `Re s > 1`
  have hγ : (∏ v : InfinitePlace K,
      (if v.IsReal then Complex.Gammaℝ (s - 1 / 2 + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
        else Complex.Gammaℂ (s - 1 / 2 + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2))) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun v _ => ?_
    by_cases hv : v.IsReal
    · simp only [hv, if_true]
      refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.natCast_re]
      have : (0 : ℝ) ≤ (((m v).natAbs % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    · simp only [hv, if_false]
      rw [Complex.Gammaℂ_def]
      refine mul_ne_zero (mul_ne_zero two_ne_zero (by simp [Real.pi_ne_zero]))
        (Complex.Gamma_ne_zero_of_re_pos ?_)
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.div_ofNat_re,
        Complex.natCast_re]
      have : (0 : ℝ) ≤ (((m v).natAbs : ℕ) : ℝ) / 2 := by positivity
      linarith
  have hGeq : Ginv (s - 1 / 2) = (∏ v : InfinitePlace K,
      (if v.IsReal then Complex.Gammaℝ (s - 1 / 2 + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
        else Complex.Gammaℂ (s - 1 / 2 + ((τ v : ℝ) : ℂ) * Complex.I + (((m v).natAbs : ℕ) : ℂ) / 2)))⁻¹ := by
    rw [hGinv, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    split_ifs <;> rfl
  change A⁻¹ * Z (s - 1 / 2) * Ginv (s - 1 / 2) = _
  rw [hZs, hGeq]
  have key : ∀ G L : ℂ, G ≠ 0 → A⁻¹ * (A * (G * L)) * G⁻¹ = L := by
    intro G L hG
    field_simp
  exact key _ _ hγ

end CMPoints
