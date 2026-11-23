import HeckeCM.RootEvenTwo
import HeckeCM.TwistEven

/-!
# `ε_{v₂}(cmCharEv) = −i`

The character `cmCharEv = cmChar · twC · tw8C` (for `d = 2e`) at the place above 2:

* `hasConductorExponentAt_cmCharEv_two`: conductor exponent 4;
* `gauss_sum_even_two`: the sum over the eight classes equals `−4i`;
* `stdRootNumberAt_cmCharEv_two`: the local root number is `−i`.
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

/-! ## The character modulo 8 on the units -/

lemma chi8_of_four_dvd_sub_one {α : 𝓞 K} (h : (4 : 𝓞 K) ∣ α - 1) : chi8 K α = 1 := by
  obtain ⟨γ, hγ⟩ := h
  obtain ⟨c, d, rfl⟩ := exists_coords γ
  have hα : α = gaussOf K (1 + 4 * c) (4 * d) := by
    have : α = 1 + 4 * ((c : 𝓞 K) + (d : 𝓞 K) * gaussI K) := by rw [← hγ]; ring
    rw [this]
    unfold gaussOf
    push_cast
    ring
  rw [chi8, hα, nrm_gaussOf]
  have : (((1 + 4 * c) ^ 2 + (4 * d) ^ 2 : ℤ) : ZMod 8) = 1 := by
    have e : ((1 + 4 * c) ^ 2 + (4 * d) ^ 2 : ℤ) = 1 + 8 * (c + 2 * c ^ 2 + 2 * d ^ 2) := by ring
    rw [e]
    push_cast
    rw [show (8 : ZMod 8) = 0 from rfl]
    ring
  rw [this, map_one]

lemma chi8_gEl : chi8 K (gEl K) = -1 := by
  unfold chi8 gEl
  rw [nrm_gaussOf, show ((3 : ℤ) ^ 2 + 2 ^ 2) = 13 by norm_num]
  decide

lemma chi8_rep8 (i : Fin 4 × Fin 2) : chi8 K (rep8 K i) = (-1) ^ (i.2 : ℕ) := by
  obtain ⟨k, j⟩ := i
  unfold rep8
  rw [chi8_mul, chi8_unit, one_mul]
  fin_cases j
  · simp [chi8_one]
  · simp [chi8_gEl]

lemma gEl_notMem : gEl K ∉ (placeTwo K).asIdeal := by
  have h := rep8_notMem (K := K) (0, 1)
  have e : rep8 K (0, 1) = gEl K := by simp [rep8_one, unitPow]
  rwa [e] at h

lemma tw8C_locIdele_two_unit (t : (K₂)ˣ) (ht : Valued.v (t : K₂) = 1) {α : 𝓞 K}
    (hα : Valued.v ((t : K₂) - toCompl K (placeTwo K) α) ≤ exp (-6 : ℤ)) :
    ((tw8C K (locIdele K (placeTwo K) t) : ℂˣ) : ℂ) = ((chi8 K α : ℤ) : ℂ) := by
  have hc : IsClose8 (locIdele K (placeTwo K) t) α := by
    unfold IsClose8
    rw [unitAt_locIdele_self, ρ_localUnit_unit _ t ht, map_one, inv_one, mul_one]
    exact hα
  rw [tw8C_val, tw8_eq hc]

/-! ## The representatives in coordinates -/

/-- Real part of `i^k · g^j`. -/
def repA (i : Fin 4 × Fin 2) : ℤ := if i.2 = 0 then uA i.1 else 3 * uA i.1 - 2 * uB i.1

/-- Imaginary part of `i^k · g^j`. -/
def repB (i : Fin 4 × Fin 2) : ℤ := if i.2 = 0 then uB i.1 else 2 * uA i.1 + 3 * uB i.1

lemma rep8_coords (i : Fin 4 × Fin 2) : rep8 K i = gaussOf K (repA i) (repB i) := by
  obtain ⟨k, j⟩ := i
  fin_cases j
  · have h1 : repA (k, 0) = uA k := rfl
    have h2 : repB (k, 0) = uB k := rfl
    show rep8 K (k, 0) = gaussOf K (repA (k, 0)) (repB (k, 0))
    rw [h1, h2, rep8_zero, unitPow_val]
  · have h1 : repA (k, 1) = 3 * uA k - 2 * uB k := rfl
    have h2 : repB (k, 1) = 2 * uA k + 3 * uB k := rfl
    show rep8 K (k, 1) = gaussOf K (repA (k, 1)) (repB (k, 1))
    rw [h1, h2, rep8_one, unitPow_val]
    unfold gEl gaussOf
    push_cast
    linear_combination (2 * (uB k : 𝓞 K)) * gaussI_sq K

variable (K) in
/-- The test element `1/8` in the completion at 2. -/
def z₈ : K₂ := ((2 : K₂) ^ 3)⁻¹

lemma valued_z₈ : Valued.v (z₈ K) = exp (6 : ℤ) := by
  unfold z₈
  rw [map_inv₀, map_pow, valued_two, exp_neg_two_pow, ← exp_neg]
  norm_num

lemma psi_z₈_rep8 (i : Fin 4 × Fin 2) :
    psiLocal K (placeTwo K) (z₈ K * toCompl K (placeTwo K) (rep8 K i)) =
      (-Complex.I) ^ (repA i) := by
  have e : z₈ K * toCompl K (placeTwo K) (rep8 K i) =
      algebraMap K K₂ (algebraMap (𝓞 K) K (gaussOf K (repA i) (repB i)) / 2 ^ 3) := by
    unfold z₈
    rw [rep8_coords, map_div₀, map_pow, map_ofNat, div_eq_inv_mul]
    rfl
  rw [e, psi_half, ← exp_quarter_int]
  congr 1
  push_cast
  ring

lemma sinv0 : ((((sigmaU K (unitPow K 0))⁻¹ : ℂˣ)) : ℂ) = 1 := by
  rw [sigmaU_unitPow_inv, show uA 0 = 1 from rfl, show uB 0 = 0 from rfl]
  simp

lemma sinv1 : ((((sigmaU K (unitPow K 1))⁻¹ : ℂˣ)) : ℂ) = -sigJ K := by
  have hJ := sigJ_sq (K := K)
  rw [sigmaU_unitPow_inv, show uA 1 = 0 from rfl, show uB 1 = 1 from rfl, Int.cast_zero,
    Int.cast_one, zero_add, one_mul]
  exact inv_eq_of_mul_eq_one_right (by linear_combination (-1) * hJ)

lemma sinv2 : ((((sigmaU K (unitPow K 2))⁻¹ : ℂˣ)) : ℂ) = -1 := by
  rw [sigmaU_unitPow_inv, show uA 2 = -1 from rfl, show uB 2 = 0 from rfl]
  simp

lemma sinv3 : ((((sigmaU K (unitPow K 3))⁻¹ : ℂˣ)) : ℂ) = sigJ K := by
  have hJ := sigJ_sq (K := K)
  rw [sigmaU_unitPow_inv, show uA 3 = 0 from rfl, show uB 3 = -1 from rfl, Int.cast_zero,
    Int.cast_neg, Int.cast_one, zero_add, neg_one_mul]
  exact inv_eq_of_mul_eq_one_right (by linear_combination (-1) * hJ)

/-- The Gauss sum over the eight classes. -/
theorem gauss_sum_even_two :
    ∑ i : Fin 4 × Fin 2, (-Complex.I) ^ (repA i) *
        (((((sigmaU K (unitPow K i.1))⁻¹ : ℂˣ)) : ℂ) * (-1 : ℂ) ^ (i.2 : ℕ)) =
      -(4 * Complex.I) := by
  have t00 : (-Complex.I) ^ (repA (0, 0)) * (((((sigmaU K (unitPow K 0))⁻¹ : ℂˣ)) : ℂ) *
      (-1 : ℂ) ^ ((0 : Fin 2) : ℕ)) = -Complex.I := by
    rw [show repA (0, 0) = 1 from rfl, sinv0, zpow_one]
    simp
  have t01 : (-Complex.I) ^ (repA (0, 1)) * (((((sigmaU K (unitPow K 0))⁻¹ : ℂˣ)) : ℂ) *
      (-1 : ℂ) ^ ((1 : Fin 2) : ℕ)) = -Complex.I := by
    rw [show repA (0, 1) = 3 from rfl, sinv0, negI_zpow_three]
    simp
  have t10 : (-Complex.I) ^ (repA (1, 0)) * (((((sigmaU K (unitPow K 1))⁻¹ : ℂˣ)) : ℂ) *
      (-1 : ℂ) ^ ((0 : Fin 2) : ℕ)) = -sigJ K := by
    rw [show repA (1, 0) = 0 from rfl, sinv1, zpow_zero]
    simp
  have t11 : (-Complex.I) ^ (repA (1, 1)) * (((((sigmaU K (unitPow K 1))⁻¹ : ℂˣ)) : ℂ) *
      (-1 : ℂ) ^ ((1 : Fin 2) : ℕ)) = -sigJ K := by
    rw [show repA (1, 1) = -2 from rfl, sinv1, negI_zpow_neg_two]
    simp
  have t20 : (-Complex.I) ^ (repA (2, 0)) * (((((sigmaU K (unitPow K 2))⁻¹ : ℂˣ)) : ℂ) *
      (-1 : ℂ) ^ ((0 : Fin 2) : ℕ)) = -Complex.I := by
    rw [show repA (2, 0) = -1 from rfl, sinv2, negI_zpow_neg_one]
    simp
  have t21 : (-Complex.I) ^ (repA (2, 1)) * (((((sigmaU K (unitPow K 2))⁻¹ : ℂˣ)) : ℂ) *
      (-1 : ℂ) ^ ((1 : Fin 2) : ℕ)) = -Complex.I := by
    rw [show repA (2, 1) = -3 from rfl, sinv2, negI_zpow_neg_three]
    simp
  have t30 : (-Complex.I) ^ (repA (3, 0)) * (((((sigmaU K (unitPow K 3))⁻¹ : ℂˣ)) : ℂ) *
      (-1 : ℂ) ^ ((0 : Fin 2) : ℕ)) = sigJ K := by
    rw [show repA (3, 0) = 0 from rfl, sinv3, zpow_zero]
    simp
  have t31 : (-Complex.I) ^ (repA (3, 1)) * (((((sigmaU K (unitPow K 3))⁻¹ : ℂˣ)) : ℂ) *
      (-1 : ℂ) ^ ((1 : Fin 2) : ℕ)) = sigJ K := by
    rw [show repA (3, 1) = 2 from rfl, sinv3, negI_zpow_two]
    simp
  rw [Fintype.sum_prod_type, Fin.sum_univ_four]
  simp only [Fin.sum_univ_two]
  rw [t00, t01, t10, t11, t20, t21, t30, t31]
  ring

variable {e : ℕ} (hodd : e % 2 = 1) (hsq : Squarefree e) (he : e ≠ 0)
include hodd hsq

/-- The character `cmCharEv` on a local unit at 2. -/
lemma evChar_unit (t : (K₂)ˣ) (ht : Valued.v (t : K₂) = 1) :
    ((localChar (cmCharEv K hodd hsq he) (placeTwo K) t : ℂˣ) : ℂ) =
      ((sigmaU K (root2 K t) : ℂˣ) : ℂ) * ((tw8C K (locIdele K (placeTwo K) t) : ℂˣ) : ℂ) := by
  show ((cmCharEv K hodd hsq he (locIdele K (placeTwo K) t) : ℂˣ) : ℂ) = _
  rw [cmCharEv_apply, cmCharTw_apply, cmChar_locIdele_two_unit t ht,
    twC_locIdele_unit hodd hsq he (natCast_notMem_placeTwo hodd) t ht, mul_one, Units.val_mul]

/-- **The conductor exponent of `cmCharEv` at 2 is 4.** -/
theorem hasConductorExponentAt_cmCharEv_two :
    HasConductorExponentAt K (placeTwo K) (localChar (cmCharEv K hodd hsq he) (placeTwo K)) 4 := by
  constructor
  · intro u hu
    obtain ⟨h1, h4⟩ := hu
    have h4' : Valued.v ((u : K₂) - 1) ≤ exp (-((4 : ℕ) : ℤ)) := by
      rcases h4 with h | h
      · exact absurd h (by norm_num)
      · exact h
    have hmem : (u : K₂) ∈ (placeTwo K).adicCompletionIntegers K :=
      (mem_adicCompletionIntegers (𝓞 K) K _).2 h1.le
    obtain ⟨a, ha⟩ := exists_adicValued_sub_lt_of_adicCompletionInteger K (placeTwo K)
      ⟨(u : K₂), hmem⟩ (Units.mk0 (exp (-6 : ℤ)) exp_ne_zero)
    have ha' : Valued.v (toCompl K (placeTwo K) a - (u : K₂)) < exp (-6 : ℤ) := ha
    have h4a : (4 : 𝓞 K) ∣ a - 1 := by
      rw [← valued_toCompl_two_le_four_iff, map_sub, map_one,
        show toCompl K (placeTwo K) a - 1 = (toCompl K (placeTwo K) a - (u : K₂)) +
          ((u : K₂) - 1) by ring]
      exact Valuation.map_add_le _ (le_trans ha'.le (exp_le_exp.2 (by norm_num))) h4'
    refine Units.ext ?_
    rw [evChar_unit hodd hsq he u h1,
      root2_of_sub_one_le (le_trans h4' (exp_le_exp.2 (by norm_num))), map_one, Units.val_one,
      one_mul, tw8C_locIdele_two_unit u h1 (α := a) (by rw [Valuation.map_sub_swap]; exact ha'.le),
      chi8_of_four_dvd_sub_one h4a, Int.cast_one]
  · intro m hm
    have hg1 : Valued.v (toCompl K (placeTwo K) (gEl K)) = 1 :=
      (valued_toCompl_eq_one_iff _ _).2 gEl_notMem
    have hne : toCompl K (placeTwo K) (gEl K) ≠ 0 := fun h => by
      rw [h, map_zero] at hg1
      exact zero_ne_one hg1
    have hsub : Valued.v (toCompl K (placeTwo K) (gEl K) - 1) ≤ exp (-3 : ℤ) := by
      rw [← map_one (toCompl K (placeTwo K)), ← map_sub, gEl_eq, add_sub_cancel_left]
      exact (valued_toCompl_two_le_iff _).2 dvd_rfl
    refine ⟨Units.mk0 _ hne, ⟨hg1, Or.inr ?_⟩, fun h => ?_⟩
    · rw [Units.val_mk0]
      exact le_trans hsub (exp_le_exp.2 (by omega))
    · have h' := congrArg Units.val h
      rw [evChar_unit hodd hsq he (Units.mk0 _ hne) hg1, Units.val_mk0,
        root2_of_sub_one_le hsub, map_one,
        Units.val_one, one_mul,
        tw8C_locIdele_two_unit (Units.mk0 _ hne) hg1 (α := gEl K)
          (by rw [Units.val_mk0, sub_self, map_zero]; exact zero_le), chi8_gEl] at h'
      norm_num at h'

/-- The value of the character on the representatives. -/
lemma charExt_cmCharEv_rep8 (i : Fin 4 × Fin 2) :
    charExt (localChar (cmCharEv K hodd hsq he) (placeTwo K))⁻¹
        (toCompl K (placeTwo K) (rep8 K i)) =
      ((((sigmaU K (unitPow K i.1))⁻¹ : ℂˣ)) : ℂ) * (-1 : ℂ) ^ (i.2 : ℕ) := by
  have hρ1 : Valued.v (toCompl K (placeTwo K) (rep8 K i)) = 1 :=
    (valued_toCompl_eq_one_iff _ _).2 (rep8_notMem i)
  have hρ : toCompl K (placeTwo K) (rep8 K i) ≠ 0 := fun h => by
    rw [h, map_zero] at hρ1
    exact zero_ne_one hρ1
  have hroot : root2 K (toCompl K (placeTwo K) (rep8 K i)) = unitPow K i.1 :=
    root2_eq (by
      rw [← map_sub]
      exact (valued_toCompl_two_le_iff _).2 (rep8_sub i))
  have hval := evChar_unit hodd hsq he (Units.mk0 _ hρ) hρ1
  rw [Units.val_mk0, hroot,
    tw8C_locIdele_two_unit (Units.mk0 _ hρ) hρ1 (α := rep8 K i)
      (by rw [Units.val_mk0, sub_self, map_zero]; exact zero_le), chi8_rep8] at hval
  rw [charExt_of_ne_zero _ hρ, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, hval, mul_inv,
    Units.val_inv_eq_inv_val]
  congr 1
  push_cast
  rw [← inv_pow]
  norm_num

/-- The character equals 1 on the test element `1/8`. -/
lemma charExt_cmCharEv_z₈ :
    charExt (localChar (cmCharEv K hodd hsq he) (placeTwo K)) (z₈ K) = 1 := by
  have hw := natCast_notMem_placeTwo (K := K) hodd
  have hJ := sigJ_sq (K := K)
  have hz0 : z₈ K ≠ 0 := fun h => by
    have := valued_z₈ (K := K)
    rw [h, map_zero] at this
    exact exp_ne_zero this.symm
  have hpi : Valued.v ((pi2 K : (K₂)ˣ) : K₂) = exp (-1 : ℤ) := valued_toCompl_one_add_gaussI
  have hiu : Valued.v ((iu2 K : (K₂)ˣ) : K₂) = 1 := valued_toCompl_unit _ (gaussIUnit K)
  have hunit : Units.mk0 (z₈ K) hz0 = (pi2 K ^ 6 * iu2 K)⁻¹ := by
    refine Units.ext ?_
    rw [Units.val_mk0, Units.val_inv_eq_inv_val, Units.val_mul, Units.val_pow_eq_pow_val]
    show ((2 : K₂) ^ 3)⁻¹ = (toCompl K (placeTwo K) (1 + gaussI K) ^ 6 *
      toCompl K (placeTwo K) (gaussIUnit K))⁻¹
    congr 1
    have h8 : (2 : K₂) ^ 3 = toCompl K (placeTwo K) (8 : 𝓞 K) := by
      rw [map_ofNat]
      norm_num
    rw [h8, eight_eq, map_mul, map_pow, gaussIUnit_val, mul_comm]
  -- the three characters on the uniformizer `1 + i`
  have hgK : genK K (placeTwo K) = algebraMap (𝓞 K) K (1 + gaussI K) := by
    unfold genK
    rw [gen_of_two_mem two_mem_placeTwo]
  have h8pi : tw8C K (locIdele K (placeTwo K) (pi2 K)) = 1 := by
    refine tw8C_eq_one_of_isClose8_one ?_
    unfold IsClose8
    rw [unitAt_locIdele_self, ρ_localUnit_uniformizer (placeTwo K) (pi2 K) hpi, hgK]
    have e : ((pi2 K : (K₂)ˣ) : K₂) *
        (algebraMap K K₂ (algebraMap (𝓞 K) K (1 + gaussI K)))⁻¹ = 1 :=
      mul_inv_cancel₀ (pi2 K).ne_zero
    rw [e, map_one, sub_self, map_zero]
    exact zero_le
  have hs : (((tw K e he (locIdele K (placeTwo K) (pi2 K)) : ℤ)) : ℂ) ^ 2 = 1 := by
    rw [sq, ← Int.cast_mul, tw_mul_self he, Int.cast_one]
  have hn2 : (((‖1 + sigJ K‖ : ℝ)) : ℂ) ^ 2 = 2 := by
    rw [norm_one_add_sigJ, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hη2 : ((1 + sigJ K) / ((‖1 + sigJ K‖ : ℝ) : ℂ)) ^ 2 = sigJ K := by
    rw [div_pow, hn2]
    linear_combination (1 / 2) * hJ
  have hpiv : ((localChar (cmCharEv K hodd hsq he) (placeTwo K) (pi2 K) : ℂˣ) : ℂ) =
      (1 + sigJ K) / ((‖1 + sigJ K‖ : ℝ) : ℂ) *
        (((tw K e he (locIdele K (placeTwo K) (pi2 K)) : ℤ)) : ℂ) := by
    show ((cmCharEv K hodd hsq he (locIdele K (placeTwo K) (pi2 K)) : ℂˣ) : ℂ) = _
    rw [cmCharEv_apply, cmCharTw_apply, h8pi, mul_one, Units.val_mul, cmChar_pi2, twC_val]
  have hiuv : ((localChar (cmCharEv K hodd hsq he) (placeTwo K) (iu2 K) : ℂˣ) : ℂ) = sigJ K := by
    show ((cmCharEv K hodd hsq he (locIdele K (placeTwo K) (iu2 K)) : ℂˣ) : ℂ) = _
    have h8 : tw8C K (locIdele K (placeTwo K) (iu2 K)) = 1 := tw8C_locIdele_two_gaussI
    rw [cmCharEv_apply, cmCharTw_apply, h8, mul_one,
      twC_locIdele_unit hodd hsq he hw (iu2 K) hiu, mul_one, cmChar_iu2]
  rw [charExt_of_ne_zero _ hz0, hunit, map_inv, Units.val_inv_eq_inv_val, map_mul, map_pow,
    Units.val_mul, Units.val_pow_eq_pow_val, hpiv, hiuv]
  have key : ((1 + sigJ K) / ((‖1 + sigJ K‖ : ℝ) : ℂ) *
      (((tw K e he (locIdele K (placeTwo K) (pi2 K)) : ℤ)) : ℂ)) ^ 6 * sigJ K = 1 := by
    have e1 : ((1 + sigJ K) / ((‖1 + sigJ K‖ : ℝ) : ℂ) *
        (((tw K e he (locIdele K (placeTwo K) (pi2 K)) : ℤ)) : ℂ)) ^ 6 * sigJ K =
        (((1 + sigJ K) / ((‖1 + sigJ K‖ : ℝ) : ℂ)) ^ 2) ^ 3 *
          ((((tw K e he (locIdele K (placeTwo K) (pi2 K)) : ℤ)) : ℂ) ^ 2) ^ 3 * sigJ K := by ring
    rw [e1, hη2, hs]
    linear_combination (sigJ K ^ 2 - 1) * hJ
  rw [key, inv_one]

/-- **The local root number of `cmCharEv` at the place above 2 is `−i`.** -/
theorem stdRootNumberAt_cmCharEv_two :
    stdRootNumberAt K (placeTwo K) (localChar (cmCharEv K hodd hsq he) (placeTwo K)) =
      -Complex.I := by
  have hcond := hasConductorExponentAt_cmCharEv_two (K := K) hodd hsq he
  have hz : Valued.v (z₈ K) =
      exp (addCharLevel (psiLocal K (placeTwo K)) + ((4 : ℕ) : ℤ)) := by
    rw [addCharLevel_psiLocal_placeTwo, valued_z₈]
    norm_num
  have hz' : Valued.v (z₈ K) ≤ exp ((2 : ℤ) + ((4 : ℕ) : ℤ)) := by
    rw [valued_z₈]
    norm_num
  have H := setIntegral_psiLocal_mul_charExt_inv_mul_cpow_eq_charExt_mul_stdRootNumberAt K
    (placeTwo K) (localChar (cmCharEv K hodd hsq he) (placeTwo K)) 4 (by norm_num) hcond
    (isUnitaryChar_cmCharEv hodd hsq he _) (z₈ K) hz
  have hS : ∑ i : Fin 4 × Fin 2, psiLocal K (placeTwo K) (z₈ K * toCompl K (placeTwo K) (rep8 K i)) *
      charExt (localChar (cmCharEv K hodd hsq he) (placeTwo K))⁻¹
        (toCompl K (placeTwo K) (rep8 K i)) = -(4 * Complex.I) := by
    rw [← gauss_sum_even_two (K := K)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [psi_z₈_rep8, charExt_cmCharEv_rep8 hodd hsq he]
  have hc : (((2 : ℕ) : ℝ)) ^ (-((4 : ℕ) : ℤ)) * (((2 : ℕ) : ℝ)) ^ (-((2 : ℤ) : ℝ) / 2) =
      1 / 32 := by
    rw [show (-((2 : ℤ) : ℝ) / 2) = -1 by norm_num, Real.rpow_neg_one]
    norm_num
  have hpow : ((2 : ℕ) : ℂ) ^ ((((2 : ℤ) + ((4 : ℕ) : ℤ) : ℤ) : ℂ) / 2) = 8 := by
    have e3 : ((((2 : ℤ) + ((4 : ℕ) : ℤ) : ℤ) : ℂ) / 2) = ((3 : ℕ) : ℂ) := by
      push_cast
      norm_num
    rw [e3, Complex.cpow_natCast]
    norm_num
  rw [gauss_integral_eq_sum_N (placeTwo K) 4 (rep8 K) (by norm_num) rep8_notMem rep8_cover rep8_inj
      _ hcond.1 (l := 2) (fun x hx => psiLocal_two_eq_one_of_valued_le hx) (z₈ K) hz',
    hS, absNorm_placeTwo, addCharLevel_psiLocal_placeTwo, hc, hpow,
    charExt_cmCharEv_z₈ hodd hsq he] at H
  push_cast at H
  linear_combination (-1) * H

end CMPoints
