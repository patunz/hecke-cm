import HeckeCM.RootUnits
import Definitions.Def_NumberField_IntegralAdelicTrace
import Theorems.Thm_LanglandsTunnell_TateLocal_setIntegral_psiLocal_mul_charExt_inv_mul_cpow_eq_charExt_mul_stdRootNumberAt
import Theorems.Thm_LanglandsTunnell_TateLocal_selfDualHaarAt_real_image_higherUnitsAt

/-!
# The local root number of `cmChar` at the place above 2

`stdRootNumberAt_cmChar_two`: `ε_{v₂}(cmChar) = −i`.

The units of the completion at 2 are the disjoint union of the four classes
`cls k = i^k · U³`. On each of them the integrand of the local Gauss sum is
constant, and each class has measure `1/16`. The sum of the four terms is
`−2i(1 + J)`, with `J = σ(i)`; the character at `z₂ = (1+i)/8` equals
`(1 + J)/√2`.
-/

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero MeasureTheory
open NumberField.AdelicLevel AutomorphicForm NumberField.TateGlobal
open NumberField.StandardAddChar LanglandsTunnell.TateLocal
open scoped Classical

namespace CMPoints

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

local notation "𝔸" => AdeleRing (𝓞 K) K
local notation "K₂" => HeightOneSpectrum.adicCompletion K (placeTwo K)

attribute [local instance] localBorel borelSpace_localBorel

/-! ## The four classes -/

variable (K) in
/-- The class of `i^k` modulo `(1 + i)^3`. -/
def cls (k : Fin 4) : Set K₂ :=
  {u | Valued.v (u - toCompl K (placeTwo K) (unitPow K k)) ≤ exp (-3 : ℤ)}

lemma iUnion_cls : (⋃ k, cls K k) = {u : K₂ | Valued.v u = 1} := by
  ext u
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, cls]
  constructor
  · rintro ⟨k, hk⟩
    exact valued_eq_one_of_sub_le hk
  · intro hu
    obtain ⟨w, hw⟩ := exists_unit_valued_sub_le u hu
    obtain ⟨k, rfl⟩ := exists_unitPow w
    exact ⟨k, hw⟩

lemma disjoint_cls : Pairwise (Function.onFun Disjoint (cls K)) := by
  intro k l hkl
  refine Set.disjoint_left.2 fun u hk hl => hkl ?_
  exact unitPow_injective (unit_eq_of_valued_sub_le hk hl)

lemma measurableSet_cls (k : Fin 4) : MeasurableSet (cls K k) := by
  have hc : IsClosed (cls K k) :=
    (NumberField.AdelicTrace.isClosed_setOf_valued_le (F := K) (placeTwo K) (exp (-3 : ℤ))).preimage
      (continuous_id.sub continuous_const)
  exact hc.measurableSet

instance : (selfDualHaarAt K (placeTwo K)).IsAddLeftInvariant := by
  unfold selfDualHaarAt
  infer_instance

lemma cls_eq_image :
    {u : K₂ | Valued.v (u - 1) ≤ exp (-3 : ℤ)} =
      ((↑) : (K₂)ˣ → K₂) '' higherUnitsAt K (placeTwo K) 3 := by
  ext u
  constructor
  · intro hu
    have hu' : Valued.v (u - toCompl K (placeTwo K) ((1 : (𝓞 K)ˣ) : 𝓞 K)) ≤ exp (-3 : ℤ) := by
      rwa [Units.val_one, map_one]
    have h1 := valued_eq_one_of_sub_le hu'
    have hne : u ≠ 0 := fun h => by
      rw [h, map_zero] at h1
      exact zero_ne_one h1
    exact ⟨Units.mk0 u hne, ⟨h1, Or.inr (by exact_mod_cast hu)⟩, rfl⟩
  · rintro ⟨t, ⟨-, h3⟩, rfl⟩
    rcases h3 with h | h
    · exact absurd h (by norm_num)
    · exact_mod_cast h

lemma absNorm_placeTwo : Ideal.absNorm (placeTwo K).asIdeal = 2 := by
  rw [placeTwo_asIdeal]
  exact absNorm_span_one_add_gaussI

lemma real_cls (k : Fin 4) : (selfDualHaarAt K (placeTwo K)).real (cls K k) = 1 / 16 := by
  have hpre : (fun h : K₂ => (toCompl K (placeTwo K) (unitPow K k) - 1) + h) ⁻¹' cls K k =
      {u : K₂ | Valued.v (u - 1) ≤ exp (-3 : ℤ)} := by
    ext u
    simp only [Set.mem_preimage, cls, Set.mem_setOf_eq]
    rw [show toCompl K (placeTwo K) (unitPow K k) - 1 + u - toCompl K (placeTwo K) (unitPow K k) =
      u - 1 by ring]
  have hm : (selfDualHaarAt K (placeTwo K)) (cls K k) =
      (selfDualHaarAt K (placeTwo K)) {u : K₂ | Valued.v (u - 1) ≤ exp (-3 : ℤ)} := by
    rw [← hpre, measure_preimage_add]
  have h := selfDualHaarAt_real_image_higherUnitsAt K (placeTwo K) 3 (by norm_num)
  rw [← cls_eq_image, absNorm_placeTwo, addCharLevel_psiLocal_placeTwo] at h
  unfold Measure.real
  rw [hm]
  unfold Measure.real at h
  rw [h, show (-((2 : ℤ) : ℝ) / 2) = -1 by norm_num, Real.rpow_neg_one]
  norm_num

/-! ## The integrand is constant on the classes -/

lemma integrand_cls (k : Fin 4) {u : K₂} (hu : u ∈ cls K k) :
    psiLocal K (placeTwo K) (z₂ K * u) * charExt (localChar (cmChar K) (placeTwo K))⁻¹ u =
      psiLocal K (placeTwo K) (z₂ K * toCompl K (placeTwo K) (unitPow K k)) *
        ((((sigmaU K (unitPow K k))⁻¹ : ℂˣ)) : ℂ) := by
  have hu1 : Valued.v u = 1 := valued_eq_one_of_sub_le hu
  have hne : u ≠ 0 := fun h => by
    rw [h, map_zero] at hu1
    exact zero_ne_one hu1
  have hψ : psiLocal K (placeTwo K) (z₂ K * u) =
      psiLocal K (placeTwo K) (z₂ K * toCompl K (placeTwo K) (unitPow K k)) := by
    have h1 : psiLocal K (placeTwo K) (z₂ K * (u - toCompl K (placeTwo K) (unitPow K k))) = 1 := by
      refine psiLocal_two_eq_one_of_valued_le ?_
      rw [map_mul, valued_z₂]
      calc exp (5 : ℤ) * Valued.v (u - toCompl K (placeTwo K) (unitPow K k))
          ≤ exp (5 : ℤ) * exp (-3 : ℤ) := mul_le_mul' le_rfl hu
        _ = exp (2 : ℤ) := by rw [← exp_add]; norm_num
    rw [show z₂ K * u = z₂ K * toCompl K (placeTwo K) (unitPow K k) +
      z₂ K * (u - toCompl K (placeTwo K) (unitPow K k)) by ring, AddChar.map_add_eq_mul,
      h1, mul_one]
  have hχ : localChar (cmChar K) (placeTwo K) (Units.mk0 u hne) = sigmaU K (unitPow K k) := by
    show cmChar K (locIdele K (placeTwo K) (Units.mk0 u hne)) = _
    rw [cmChar_locIdele_two_unit (Units.mk0 u hne) hu1, Units.val_mk0, root2_eq hu]
  rw [hψ, charExt_of_ne_zero _ hne, MonoidHom.inv_apply, hχ]

/-! ## The values -/

lemma exp_quarter :
    Complex.exp (-(2 * Real.pi * Complex.I) * ((1 : ℂ) / 4)) = -Complex.I := by
  have : -(2 * (Real.pi : ℂ) * Complex.I) * ((1 : ℂ) / 4) =
      ((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
    Real.sin_neg, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

lemma exp_neg_quarter :
    Complex.exp (-(2 * Real.pi * Complex.I) * ((-1 : ℂ) / 4)) = Complex.I := by
  have : -(2 * (Real.pi : ℂ) * Complex.I) * ((-1 : ℂ) / 4) =
      (((Real.pi / 2) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

lemma sigmaU_unitPow_inv (k : Fin 4) :
    ((((sigmaU K (unitPow K k))⁻¹ : ℂˣ)) : ℂ) = ((uA k : ℂ) + (uB k : ℂ) * sigJ K)⁻¹ := by
  rw [Units.val_inv_eq_inv_val, sigmaU_val, unitPow_val, sigma_gaussOf]

/-- The sum of the four terms. -/
lemma gauss_sum_two :
    ∑ k : Fin 4, psiLocal K (placeTwo K) (z₂ K * toCompl K (placeTwo K) (unitPow K k)) *
        ((((sigmaU K (unitPow K k))⁻¹ : ℂˣ)) : ℂ) =
      -(2 * Complex.I * (1 + sigJ K)) := by
  have hJ := sigJ_sq (K := K)
  have i1 : (sigJ K)⁻¹ = -sigJ K := inv_eq_of_mul_eq_one_right (by linear_combination (-1) * hJ)
  have i3 : (-sigJ K)⁻¹ = sigJ K := inv_eq_of_mul_eq_one_right (by linear_combination (-1) * hJ)
  have a0 : uA 0 - uB 0 = 1 := by decide
  have a1 : uA 1 - uB 1 = -1 := by decide
  have a2 : uA 2 - uB 2 = -1 := by decide
  have a3 : uA 3 - uB 3 = 1 := by decide
  have h0 := psi_z₂_mul_unit (K := K) 0
  have h1 := psi_z₂_mul_unit (K := K) 1
  have h2 := psi_z₂_mul_unit (K := K) 2
  have h3 := psi_z₂_mul_unit (K := K) 3
  rw [a0, Int.cast_one, exp_quarter] at h0
  rw [a1, Int.cast_neg, Int.cast_one, exp_neg_quarter] at h1
  rw [a2, Int.cast_neg, Int.cast_one, exp_neg_quarter] at h2
  rw [a3, Int.cast_one, exp_quarter] at h3
  have s0 : ((((sigmaU K (unitPow K 0))⁻¹ : ℂˣ)) : ℂ) = 1 := by
    rw [sigmaU_unitPow_inv, show uA 0 = 1 from rfl, show uB 0 = 0 from rfl]
    simp
  have s1 : ((((sigmaU K (unitPow K 1))⁻¹ : ℂˣ)) : ℂ) = -sigJ K := by
    rw [sigmaU_unitPow_inv, show uA 1 = 0 from rfl, show uB 1 = 1 from rfl, Int.cast_zero,
      Int.cast_one, zero_add, one_mul, i1]
  have s2 : ((((sigmaU K (unitPow K 2))⁻¹ : ℂˣ)) : ℂ) = -1 := by
    rw [sigmaU_unitPow_inv, show uA 2 = -1 from rfl, show uB 2 = 0 from rfl]
    simp
  have s3 : ((((sigmaU K (unitPow K 3))⁻¹ : ℂˣ)) : ℂ) = sigJ K := by
    rw [sigmaU_unitPow_inv, show uA 3 = 0 from rfl, show uB 3 = -1 from rfl, Int.cast_zero,
      Int.cast_neg, Int.cast_one, zero_add, neg_one_mul, i3]
  rw [Fin.sum_univ_four, h0, h1, h2, h3, s0, s1, s2, s3]
  ring

/-- The local Gauss integral over the units. -/
lemma gauss_integral_two :
    ∫ u in {u : K₂ | Valued.v u = 1},
        psiLocal K (placeTwo K) (z₂ K * u) * charExt (localChar (cmChar K) (placeTwo K))⁻¹ u
        ∂(selfDualHaarAt K (placeTwo K)) =
      (1 / 16 : ℂ) * -(2 * Complex.I * (1 + sigJ K)) := by
  have hfin : ∀ k : Fin 4, (selfDualHaarAt K (placeTwo K)) (cls K k) ≠ ⊤ := fun k h => by
    have := real_cls (K := K) k
    unfold Measure.real at this
    rw [h, ENNReal.toReal_top] at this
    norm_num at this
  have hconst : ∀ k : Fin 4, Set.EqOn
      (fun _ : K₂ => psiLocal K (placeTwo K) (z₂ K * toCompl K (placeTwo K) (unitPow K k)) *
        ((((sigmaU K (unitPow K k))⁻¹ : ℂˣ)) : ℂ))
      (fun u : K₂ => psiLocal K (placeTwo K) (z₂ K * u) *
        charExt (localChar (cmChar K) (placeTwo K))⁻¹ u) (cls K k) :=
    fun k u hu => (integrand_cls k hu).symm
  rw [← iUnion_cls, integral_iUnion_fintype measurableSet_cls disjoint_cls
    (fun k => (integrableOn_const (hfin k)).congr_fun (hconst k) (measurableSet_cls k))]
  have hk : ∀ k : Fin 4, ∫ u in cls K k, psiLocal K (placeTwo K) (z₂ K * u) *
      charExt (localChar (cmChar K) (placeTwo K))⁻¹ u ∂(selfDualHaarAt K (placeTwo K)) =
      (1 / 16 : ℂ) * (psiLocal K (placeTwo K) (z₂ K * toCompl K (placeTwo K) (unitPow K k)) *
        ((((sigmaU K (unitPow K k))⁻¹ : ℂˣ)) : ℂ)) := by
    intro k
    rw [← setIntegral_congr_fun (measurableSet_cls k) (hconst k), setIntegral_const, real_cls,
      Complex.real_smul]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun k _ => hk k, ← Finset.mul_sum, gauss_sum_two]

end CMPoints
