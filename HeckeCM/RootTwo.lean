import HeckeCM.RootInt

/-!
# `ε_{v₂}(cmChar) = −i`

* `cmChar_pi2`: on the uniformizer `1 + i` at `v₂`, `cmChar` equals
  `(1 + J)/|1 + J|`, with `J = σ(i)`;
* `charExt_cmChar_z₂`: the same value at `z₂ = (1 + i)/8`;
* `stdRootNumberAt_cmChar_two`: the local root number at `v₂` is `−i`.
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

lemma two_ne_zero_two : (2 : K₂) ≠ 0 := fun h => by
  have := valued_two (K := K)
  rw [h, map_zero] at this
  exact exp_ne_zero this.symm

variable (K) in
/-- The uniformizer `1 + i` in the completion at 2. -/
def pi2 : (K₂)ˣ := Units.mk0 (toCompl K (placeTwo K) (1 + gaussI K)) (fun h => by
  have := valued_toCompl_one_add_gaussI (K := K)
  rw [h, map_zero] at this
  exact exp_ne_zero this.symm)

variable (K) in
/-- The unit `i` in the completion at 2. -/
def iu2 : (K₂)ˣ := Units.map ((toCompl K (placeTwo K) : 𝓞 K →+* K₂) : 𝓞 K →* K₂) (gaussIUnit K)

/-- On `1 + i` at `v₂`, `cmChar` equals `(1 + J)/|1 + J|`. -/
theorem cmChar_pi2 :
    ((cmChar K (locIdele K (placeTwo K) (pi2 K)) : ℂˣ) : ℂ) =
      (1 + sigJ K) / ((‖1 + sigJ K‖ : ℝ) : ℂ) := by
  have ht : Valued.v ((pi2 K : (K₂)ˣ) : K₂) = exp (-1 : ℤ) := valued_toCompl_one_add_gaussI
  have hρ := ρ_localUnit_uniformizer (placeTwo K) (pi2 K) ht
  have hg : genK K (placeTwo K) = algebraMap (𝓞 K) K (1 + gaussI K) := by
    unfold genK
    rw [gen_of_two_mem two_mem_placeTwo]
  have hroot : rootHom K (locIdele K (placeTwo K) (pi2 K)) = 1 := by
    rw [rootHom_apply]
    have h2 : unit2 K (locIdele K (placeTwo K) (pi2 K)) = 1 := by
      unfold unit2
      rw [hρ, Units.coe_map, finIncl_apply_snd, localUnit_apply_self, hg]
      exact mul_inv_cancel₀ (pi2 K).ne_zero
    rw [h2, root2_one]
  have hθ : ((thetaHom K (locIdele K (placeTwo K) (pi2 K)) : ℂˣ) : ℂ) =
      (sigma K (genK K (placeTwo K)))⁻¹ := by
    rw [thetaHom_val, hρ, Units.coe_map, archHom_finIncl, one_mul]
  have hs : sigma K (genK K (placeTwo K)) = 1 + sigJ K := by
    rw [hg, ← gaussOf_one_one, sigma_gaussOf]
    simp
  rw [cmChar_apply, hroot, map_one, mul_one, Units.val_inv_eq_inv_val, unitDir_val, hθ, norm_inv,
    Complex.ofReal_inv, inv_div, inv_div_inv, hs]

/-- On `i` at `v₂`, `cmChar` equals `J`. -/
theorem cmChar_iu2 : ((cmChar K (locIdele K (placeTwo K) (iu2 K)) : ℂˣ) : ℂ) = sigJ K := by
  have h1 : Valued.v ((iu2 K : (K₂)ˣ) : K₂) = 1 := valued_toCompl_unit _ (gaussIUnit K)
  rw [cmChar_locIdele_two_unit (iu2 K) h1]
  have : root2 K ((iu2 K : (K₂)ˣ) : K₂) = gaussIUnit K := root2_toCompl_unit (gaussIUnit K)
  rw [this, sigmaU_val, gaussIUnit_val]
  rfl

lemma z₂_mul :
    z₂ K * (toCompl K (placeTwo K) (1 + gaussI K) ^ 5 * toCompl K (placeTwo K) (gaussI K)) = 1 := by
  have h8 : (2 : K₂) ^ 3 = toCompl K (placeTwo K) ((1 + gaussI K) ^ 6 * gaussI K) := by
    rw [show ((1 + gaussI K) ^ 6 * gaussI K : 𝓞 K) = 2 ^ 3 by
      linear_combination (gaussI K ^ 5 + 6 * gaussI K ^ 4 + 14 * gaussI K ^ 3 + 14 * gaussI K ^ 2 +
        gaussI K - 8) * gaussI_sq K, map_pow, map_ofNat]
  unfold z₂ zK
  rw [map_div₀, map_pow, map_ofNat, gaussOf_one_one, div_mul_eq_mul_div,
    div_eq_one_iff_eq (pow_ne_zero 3 two_ne_zero_two), h8, map_mul, map_pow]
  show toCompl K (placeTwo K) (1 + gaussI K) * _ = _
  ring

lemma norm_one_add_sigJ : ‖1 + sigJ K‖ = Real.sqrt 2 := by
  have h := norm_add_mul_of_sq (sigJ_sq (K := K)) 1 1
  have e : ((1 : ℤ) : ℂ) + ((1 : ℤ) : ℂ) * sigJ K = 1 + sigJ K := by push_cast; ring
  rw [e] at h
  rw [h]
  norm_num

/-- The value of `cmChar` at `z₂ = (1 + i)/8`. -/
theorem charExt_cmChar_z₂ :
    charExt (localChar (cmChar K) (placeTwo K)) (z₂ K) =
      (1 + sigJ K) / ((Real.sqrt 2 : ℝ) : ℂ) := by
  have hJ := sigJ_sq (K := K)
  have hn2 : (((Real.sqrt 2 : ℝ)) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  set η : ℂ := (1 + sigJ K) / ((Real.sqrt 2 : ℝ) : ℂ) with hη
  have hη2 : η ^ 2 = sigJ K := by
    rw [hη, div_pow, hn2]
    linear_combination (1 / 2) * hJ
  have hunit : Units.mk0 (z₂ K) z₂_ne_zero * (pi2 K ^ 5 * iu2 K) = 1 :=
    Units.ext (by
      rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      exact z₂_mul)
  have hχ := congrArg (fun t => ((localChar (cmChar K) (placeTwo K) t : ℂˣ) : ℂ)) hunit
  simp only [map_mul, map_pow, map_one, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one]
    at hχ
  have hp : ((localChar (cmChar K) (placeTwo K) (pi2 K) : ℂˣ) : ℂ) = η := by
    rw [hη, ← norm_one_add_sigJ (K := K)]
    exact cmChar_pi2
  have hi : ((localChar (cmChar K) (placeTwo K) (iu2 K) : ℂˣ) : ℂ) = sigJ K := cmChar_iu2
  rw [hp, hi] at hχ
  rw [charExt_of_ne_zero _ z₂_ne_zero]
  have h6 : η * (η ^ 5 * sigJ K) = 1 := by
    have : η * (η ^ 5 * sigJ K) = (η ^ 2) ^ 3 * sigJ K := by ring
    rw [this, hη2]
    linear_combination (sigJ K ^ 2 - 1) * hJ
  calc ((localChar (cmChar K) (placeTwo K) (Units.mk0 (z₂ K) z₂_ne_zero) : ℂˣ) : ℂ)
      = ((localChar (cmChar K) (placeTwo K) (Units.mk0 (z₂ K) z₂_ne_zero) : ℂˣ) : ℂ) *
          (η * (η ^ 5 * sigJ K)) := by rw [h6, mul_one]
    _ = η * (((localChar (cmChar K) (placeTwo K) (Units.mk0 (z₂ K) z₂_ne_zero) : ℂˣ) : ℂ) *
          (η ^ 5 * sigJ K)) := by ring
    _ = η := by rw [hχ, mul_one]

lemma two_cpow_five_half :
    ((2 : ℕ) : ℂ) ^ ((((2 : ℤ) + ((3 : ℕ) : ℤ) : ℤ) : ℂ) / 2) = 4 * ((Real.sqrt 2 : ℝ) : ℂ) := by
  have e : ((2 : ℕ) : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  have e2 : ((((2 : ℤ) + ((3 : ℕ) : ℤ) : ℤ) : ℂ) / 2) = (((5 / 2 : ℝ)) : ℂ) := by
    push_cast
    norm_num
  have hreal : (2 : ℝ) ^ (5 / 2 : ℝ) = 4 * Real.sqrt 2 := by
    rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add (by norm_num), Real.sqrt_eq_rpow,
      Real.rpow_two]
    norm_num
  rw [e, e2, ← Complex.ofReal_cpow (by norm_num), hreal]
  push_cast
  ring

/-- **The local root number of `cmChar` at the place above 2 is `−i`.** -/
theorem stdRootNumberAt_cmChar_two :
    stdRootNumberAt K (placeTwo K) (localChar (cmChar K) (placeTwo K)) = -Complex.I := by
  have hJ := sigJ_sq (K := K)
  have hn2 : (((Real.sqrt 2 : ℝ)) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hn0 : (((Real.sqrt 2 : ℝ)) : ℂ) ≠ 0 := fun h => by
    rw [h] at hn2
    norm_num at hn2
  have h1J : (1 + sigJ K) ≠ 0 := fun h => by
    have : sigJ K = -1 := by linear_combination h
    rw [this] at hJ
    norm_num at hJ
  have hz : Valued.v (z₂ K) =
      exp (addCharLevel (psiLocal K (placeTwo K)) + ((3 : ℕ) : ℤ)) := by
    rw [addCharLevel_psiLocal_placeTwo, valued_z₂]
    norm_num
  have H := setIntegral_psiLocal_mul_charExt_inv_mul_cpow_eq_charExt_mul_stdRootNumberAt K
    (placeTwo K) (localChar (cmChar K) (placeTwo K)) 3 (by norm_num)
    hasConductorExponentAt_cmChar_two (isUnitaryChar_cmChar K _) (z₂ K) hz
  rw [gauss_integral_two, absNorm_placeTwo, addCharLevel_psiLocal_placeTwo, two_cpow_five_half,
    charExt_cmChar_z₂] at H
  have H3 : (1 + sigJ K) * stdRootNumberAt K (placeTwo K) (localChar (cmChar K) (placeTwo K)) =
      (1 + sigJ K) * -Complex.I := by
    have e : (1 + sigJ K) / ((Real.sqrt 2 : ℝ) : ℂ) *
        stdRootNumberAt K (placeTwo K) (localChar (cmChar K) (placeTwo K)) *
          ((Real.sqrt 2 : ℝ) : ℂ) =
        (1 + sigJ K) * stdRootNumberAt K (placeTwo K) (localChar (cmChar K) (placeTwo K)) := by
      field_simp
    rw [← e, ← H]
    linear_combination (-(1 / 2) * Complex.I * (1 + sigJ K)) * hn2
  exact mul_left_cancel₀ h1J H3

end CMPoints
