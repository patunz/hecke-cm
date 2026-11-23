import HeckeCM.Character
import HeckeCM.GenPlaces
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction

/-!
# The local values of the Hecke character of `ℚ(i)`

* `isUnramifiedCharAt_cmChar_iff`: `cmChar` is unramified at `v` if and only
  if `v` is not the place above 2;
* `cmChar_uniformizerIdele`: outside 2, the value on the uniformizer is
  `σ(π_v) / |σ(π_v)|`, with `π_v` the primary generator;
* `isGenEulerDatum_cmChar`: the local values satisfy `IsGenEulerDatum`, that is,
  they are those of the Dirichlet series of `cmCoeff`.
-/

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open NumberField.AdelicLevel AutomorphicForm NumberField.TateGlobal
open scoped Classical

namespace CMPoints

variable (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

local notation "𝔸" => AdeleRing (𝓞 K) K

variable {K}

theorem root2_inv_toCompl_primary {c d : ℤ} (h : IsPrimaryPair c d) :
    root2 K (toCompl K (placeTwo K) (gaussOf K c d))⁻¹ = 1 := by
  have hclose : Valued.v (toCompl K (placeTwo K) (gaussOf K c d) -
      toCompl K (placeTwo K) ((1 : (𝓞 K)ˣ) : 𝓞 K)) ≤ exp (-3 : ℤ) := by
    rw [Units.val_one, ← map_sub]
    exact (valued_toCompl_two_le_iff _).2 (two_add_two_dvd_of_isPrimaryPair h)
  have hv1 := valued_eq_one_of_sub_le hclose
  have hne : toCompl K (placeTwo K) (gaussOf K c d) ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hv1
    exact zero_ne_one hv1
  have hvinv : Valued.v (toCompl K (placeTwo K) (gaussOf K c d))⁻¹ = 1 := by
    rw [map_inv₀, hv1, inv_one]
  have := root2_mul hv1 hvinv
  rw [mul_inv_cancel₀ hne, root2_one, root2_toCompl_primary h, one_mul] at this
  exact this.symm

/-! ## The character on idèles concentrated at one place -/

/-- A local unit outside 2 maps to 1. -/
theorem cmChar_localUnit_of_ne {v : HeightOneSpectrum (𝓞 K)} (hv : v ≠ placeTwo K)
    (t : (v.adicCompletion K)ˣ) (ht : Valued.v (t : v.adicCompletion K) = 1) :
    cmChar K (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t)) = 1 := by
  have hρ := ρ_localUnit_unit v t ht
  have h2 : unit2 K (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t)) = 1 := by
    unfold unit2
    rw [hρ, map_one, inv_one, mul_one, Units.coe_map, finIncl_apply_snd,
      localUnit_apply_of_ne (𝓞 K) K v t hv.symm]
  have hθ : thetaHom K (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t)) = 1 :=
    Units.ext (by
      rw [thetaHom_val, hρ, map_one, inv_one, mul_one, Units.coe_map]
      exact archHom_finIncl K _)
  rw [cmChar_apply, hθ, rootHom_apply, h2, root2_one, map_one, map_one, inv_one, one_mul]

/-- A uniformizer outside 2 maps to `σ(π_v) / |σ(π_v)|`. -/
theorem cmChar_localUnit_uniformizer {v : HeightOneSpectrum (𝓞 K)} (hv : v ≠ placeTwo K)
    (t : (v.adicCompletion K)ˣ) (ht : Valued.v (t : v.adicCompletion K) = exp (-1 : ℤ)) :
    ((cmChar K (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t)) : ℂˣ) : ℂ) =
      sigma K (genK K v) / ((‖sigma K (genK K v)‖ : ℝ) : ℂ) := by
  have hρ := ρ_localUnit_uniformizer v t ht
  have h2v : (2 : 𝓞 K) ∉ v.asIdeal := fun h => hv (eq_placeTwo_of_two_mem h)
  obtain ⟨a, b, hab, hg, -⟩ := gen_spec h2v
  have hroot : rootHom K (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t)) = 1 := by
    rw [rootHom_apply]
    have h2 : unit2 K (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t)) =
        (toCompl K (placeTwo K) (gaussOf K a b))⁻¹ := by
      unfold unit2
      rw [hρ, Units.coe_map, finIncl_apply_snd, localUnit_apply_of_ne (𝓞 K) K v t hv.symm,
        one_mul]
      unfold genK toCompl
      rw [hg]
      rfl
    rw [h2]
    exact root2_inv_toCompl_primary hab
  have hθ : ((thetaHom K (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t)) : ℂˣ) : ℂ) =
      (sigma K (genK K v))⁻¹ := by
    rw [thetaHom_val, hρ, Units.coe_map, archHom_finIncl, one_mul]
  rw [cmChar_apply, hroot, map_one, mul_one, Units.val_inv_eq_inv_val, unitDir_val, hθ, norm_inv,
    Complex.ofReal_inv, inv_div, inv_div_inv]

variable (K) in
/-- The unit `i` of `𝓞 K`. -/
def gaussIUnit : (𝓞 K)ˣ := isUnit_gaussI.unit

/-- At 2 the character is ramified: on the local unit `i` it takes the value `σ(i) ≠ 1`. -/
theorem cmChar_localUnit_two_ne_one :
    cmChar K (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K (placeTwo K)
      (Units.map ((toCompl K (placeTwo K) : 𝓞 K →+* _) : 𝓞 K →* _) (gaussIUnit K)))) ≠ 1 := by
  set t : ((placeTwo K).adicCompletion K)ˣ :=
    Units.map ((toCompl K (placeTwo K) : 𝓞 K →+* _) : 𝓞 K →* _) (gaussIUnit K) with ht
  have htv : (t : (placeTwo K).adicCompletion K) = toCompl K (placeTwo K) (gaussIUnit K) := rfl
  have ht1 : Valued.v (t : (placeTwo K).adicCompletion K) = 1 := by
    rw [htv, valued_toCompl_unit]
  have hρ := ρ_localUnit_unit (placeTwo K) t ht1
  have h2 : unit2 K (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K (placeTwo K) t)) =
      toCompl K (placeTwo K) (gaussIUnit K) := by
    unfold unit2
    rw [hρ, map_one, inv_one, mul_one, Units.coe_map, finIncl_apply_snd, localUnit_apply_self, htv]
  have hθ : thetaHom K (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K (placeTwo K) t)) = 1 :=
    Units.ext (by
      rw [thetaHom_val, hρ, map_one, inv_one, mul_one, Units.coe_map]
      exact archHom_finIncl K _)
  rw [cmChar_apply, hθ, rootHom_apply, h2, root2_toCompl_unit, map_one, inv_one, one_mul]
  intro h1
  have hval : sigma K (algebraMap (𝓞 K) K (gaussI K)) = 1 := by
    have := congrArg Units.val h1
    rwa [sigmaU_val, Units.val_one] at this
  have hsq : sigma K (algebraMap (𝓞 K) K (gaussI K)) ^ 2 = -1 := by
    rw [← map_pow, ← map_pow, gaussI_sq, map_neg, map_neg, map_one, map_one]
  rw [hval] at hsq
  norm_num at hsq

/-- **`cmChar` is unramified exactly outside 2.** -/
theorem isUnramifiedCharAt_cmChar_iff (v : HeightOneSpectrum (𝓞 K)) :
    IsUnramifiedCharAt (cmChar K) v ↔ v ≠ placeTwo K := by
  constructor
  · rintro h rfl
    refine cmChar_localUnit_two_ne_one (K := K) (h _ ?_ ?_)
    · exact (mem_adicCompletionIntegers (𝓞 K) K _).2 (valued_toCompl_unit _ _).le
    · rw [← map_inv]
      exact (mem_adicCompletionIntegers (𝓞 K) K _).2 (valued_toCompl_unit _ _).le
  · intro hv t ht hti
    have h1 := (mem_adicCompletionIntegers (𝓞 K) K v).1 ht
    have h2 := (mem_adicCompletionIntegers (𝓞 K) K v).1 hti
    have hmul : Valued.v (t : v.adicCompletion K) *
        Valued.v ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    have hone : Valued.v (t : v.adicCompletion K) = 1 := le_antisymm h1 (by
      calc (1 : ℤᵐ⁰) = Valued.v (t : v.adicCompletion K) *
            Valued.v ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) := hmul.symm
        _ ≤ Valued.v (t : v.adicCompletion K) * 1 := mul_le_mul_right h2 _
        _ = Valued.v (t : v.adicCompletion K) := mul_one _)
    exact cmChar_localUnit_of_ne hv t hone

/-- Outside 2, the value on the uniformizing idèle. -/
theorem cmChar_uniformizerIdele {v : HeightOneSpectrum (𝓞 K)} (hv : v ≠ placeTwo K) :
    ((cmChar K (uniformizerIdele K v) : ℂˣ) : ℂ) =
      sigma K (genK K v) / ((‖sigma K (genK K v)‖ : ℝ) : ℂ) :=
  cmChar_localUnit_uniformizer hv (uniformizerUnit K v) (valued_uniformizerUnit K v)

/-! ## Computations in `ℂ` -/

variable (K) in
/-- The image of `i` in `ℂ`: a square root of `−1`. -/
def sigJ : ℂ := sigma K (algebraMap (𝓞 K) K (gaussI K))

lemma sigJ_sq : sigJ K ^ 2 = -1 := by
  unfold sigJ
  rw [← map_pow, ← map_pow, gaussI_sq, map_neg, map_neg, map_one, map_one]

lemma sigma_gaussOf (a b : ℤ) :
    sigma K (algebraMap (𝓞 K) K (gaussOf K a b)) = (a : ℂ) + (b : ℂ) * sigJ K := by
  unfold gaussOf sigJ
  rw [map_add, map_add, map_mul, map_mul, map_intCast, map_intCast, map_intCast, map_intCast]

lemma norm_add_mul_of_sq {j : ℂ} (hj : j ^ 2 = -1) (a b : ℤ) :
    ‖(a : ℂ) + (b : ℂ) * j‖ = Real.sqrt (((a ^ 2 + b ^ 2 : ℤ) : ℝ)) := by
  have hcases : j = Complex.I ∨ j = -Complex.I := by
    have h : (j - Complex.I) * (j + Complex.I) = 0 := by
      linear_combination hj - Complex.I_sq
    rcases mul_eq_zero.1 h with h | h
    · left; linear_combination h
    · right; linear_combination h
  rcases hcases with rfl | rfl
  · rw [show (a : ℂ) + (b : ℂ) * Complex.I = ((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.norm_add_mul_I]
    congr 1
    push_cast
    ring
  · rw [show (a : ℂ) + (b : ℂ) * -Complex.I = ((a : ℝ) : ℂ) + ((-b : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.norm_add_mul_I]
    congr 1
    push_cast
    ring

lemma natCast_cpow_neg_half (p : ℕ) :
    (p : ℂ) ^ (-(1 / 2 : ℂ)) = (((Real.sqrt p : ℝ) : ℂ))⁻¹ := by
  have h := Complex.ofReal_cpow (Nat.cast_nonneg p : (0 : ℝ) ≤ p) (-(1 / 2 : ℝ))
  rw [Real.rpow_neg (Nat.cast_nonneg p), ← Real.sqrt_eq_rpow] at h
  push_cast at h
  rw [← h]

lemma gen_eq_of_primary {v : HeightOneSpectrum (𝓞 K)} (h2v : (2 : 𝓞 K) ∉ v.asIdeal) {a b : ℤ}
    (hab : IsPrimaryPair a b) (hv : v.asIdeal = Ideal.span {gaussOf K a b}) :
    gen K v = gaussOf K a b := by
  obtain ⟨a', b', hab', hg, hv'⟩ := gen_spec h2v
  obtain ⟨rfl, rfl⟩ := primary_unique hab' hab (hv'.symm.trans hv)
  exact hg

/-! ## The theorem -/

/-- **The local values of `cmChar` are those of the series of `cmCoeff`.** -/
theorem isGenEulerDatum_cmChar :
    IsGenEulerDatum K (· = 2) cmPrime fun v =>
      if IsUnramifiedCharAt (cmChar K) v then ((cmChar K (uniformizerIdele K v) : ℂˣ) : ℂ)
      else 0 := by
  refine ⟨fun v => ?_, fun p _ hp2 v hv => ?_, fun p hp _ h3 => ?_, fun p hp _ h1 => ?_⟩
  · split_ifs
    · exact (isUnitaryChar_cmChar K _).le
    · rw [norm_zero]; exact zero_le_one
  · obtain rfl : p = 2 := hp2
    have h2 : (2 : 𝓞 K) ∈ v.asIdeal := by simpa using hv
    rw [if_neg]
    rw [isUnramifiedCharAt_cmChar_iff, not_not]
    exact eq_placeTwo_of_two_mem h2
  · haveI := Fact.mk hp
    obtain ⟨v, hmem, hN, hprim, hv⟩ := exists_primary_inert (K := K) p h3
    refine ⟨v, hmem, hN, ?_⟩
    have h2v : (2 : 𝓞 K) ∉ v.asIdeal := two_not_mem v (by omega) ((hmem v).2 rfl)
    have hne : v ≠ placeTwo K := fun h => h2v (h ▸ two_mem_placeTwo)
    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    rw [if_pos ((isUnramifiedCharAt_cmChar_iff v).2 hne), cmChar_uniformizerIdele hne]
    unfold genK
    rw [gen_eq_of_primary h2v hprim hv, sigma_gaussOf]
    push_cast
    rw [zero_mul, add_zero, norm_neg, Complex.norm_natCast, Complex.ofReal_natCast, neg_div,
      div_self hp0]
  · haveI := Fact.mk hp
    obtain ⟨v, w, a, b, hvw, hmem, hNv, hNw, hab, hab', hn, hv, hw⟩ :=
      exists_primary_split (K := K) p h1
    refine ⟨v, w, hvw, hmem, hNv, hNw, ?_, ?_⟩
    all_goals
      have hodd : p % 2 = 1 := by omega
      have h2v : (2 : 𝓞 K) ∉ v.asIdeal := two_not_mem v hodd ((hmem v).2 (Or.inl rfl))
      have h2w : (2 : 𝓞 K) ∉ w.asIdeal := two_not_mem w hodd ((hmem w).2 (Or.inr rfl))
      have hnev : v ≠ placeTwo K := fun h => h2v (h ▸ two_mem_placeTwo)
      have hnew : w ≠ placeTwo K := fun h => h2w (h ▸ two_mem_placeTwo)
      have hj := sigJ_sq (K := K)
      have hs0 : ((Real.sqrt p : ℝ) : ℂ) ≠ 0 := by
        rw [Ne, Complex.ofReal_eq_zero, Real.sqrt_eq_zero (Nat.cast_nonneg p)]
        exact Nat.cast_ne_zero.2 hp.ne_zero
      have hss : ((Real.sqrt p : ℝ) : ℂ) ^ 2 = p := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg p), Complex.ofReal_natCast]
      have hnC : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = p := by exact_mod_cast congrArg (Int.cast : ℤ → ℂ) hn
      have hnv : ‖(a : ℂ) + (b : ℂ) * sigJ K‖ = Real.sqrt p := by
        rw [norm_add_mul_of_sq hj, hn, Int.cast_natCast]
      have hnw : ‖(a : ℂ) + ((-b : ℤ) : ℂ) * sigJ K‖ = Real.sqrt p := by
        rw [norm_add_mul_of_sq hj, show a ^ 2 + (-b) ^ 2 = (p : ℤ) by rw [neg_sq]; exact hn,
          Int.cast_natCast]
      rw [if_pos ((isUnramifiedCharAt_cmChar_iff v).2 hnev),
        if_pos ((isUnramifiedCharAt_cmChar_iff w).2 hnew), cmChar_uniformizerIdele hnev,
        cmChar_uniformizerIdele hnew]
      unfold genK
      rw [gen_eq_of_primary h2v hab hv, gen_eq_of_primary h2w hab' hw, sigma_gaussOf,
        sigma_gaussOf, hnv, hnw]
    · have hcm : cmPrime p = 2 * a := by
        unfold cmPrime
        rw [if_pos h1, cmA_eq hp hn hab]
      rw [hcm, natCast_cpow_neg_half, ← add_div, div_eq_mul_inv]
      push_cast
      ring
    · rw [div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero hs0 hs0)]
      push_cast
      linear_combination hnC - hss - (b : ℂ) ^ 2 * hj

end CMPoints
