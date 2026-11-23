import HeckeCM.Values
import HeckeCM.GenConditional
import Definitions.Def_NumberField_NormPowChar

/-!
# The entire continuation of the Dirichlet series of `cmCoeff`

Here the last hypotheses of the conditional theorem
`exists_entire_lseries_of_hasProd_places` are discharged for the character
`cmChar`:

* `continuous_cmChar`: it is continuous. Near 1 it coincides with the
  archimedean part alone, which is continuous; a homomorphism continuous at 1
  is continuous;
* `cmChar_ne_normPowChar`: it is not an imaginary power of the norm, because
  on the idèle of order 4 concentrated at 2 it takes the value `σ(i) ≠ 1`.

The final theorem, with no hypotheses, is `entire_lseries_cmCoeff`.
-/

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open NumberField.AdelicLevel AutomorphicForm NumberField.TateGlobal
open scoped Classical Topology

namespace CMPoints

variable (K : Type) [Field K] [NumberField K]

local notation "𝔸" => AdeleRing (𝓞 K) K

/-! ## Continuity -/

/-- The archimedean coordinate on the idèles. -/
def archU : (𝔸)ˣ →* ℂˣ := Units.map (archHom K : 𝔸 →* ℂ)

theorem continuous_archHom : Continuous (archHom K) :=
  (InfinitePlace.Completion.isometry_extensionEmbedding (archPlace K)).continuous.comp
    ((continuous_archEval K (archPlace K)).comp (continuous_adeleArch (𝓞 K) K))

theorem continuous_archU : Continuous (archU K) :=
  Continuous.units_map _ (continuous_archHom K)

theorem continuous_unitDir : Continuous unitDir := by
  have hval : Continuous fun z : ℂˣ => ((unitDir z : ℂˣ) : ℂ) := by
    show Continuous fun z : ℂˣ => (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ)
    exact Units.continuous_val.div
      (Complex.continuous_ofReal.comp (continuous_norm.comp Units.continuous_val))
      (fun z => by exact_mod_cast norm_ne_zero_iff.2 z.ne_zero)
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  exact (hval.inv₀ fun z => (unitDir z).ne_zero).congr fun z =>
    (Units.val_inv_eq_inv_val _).symm

variable [IsCyclotomicExtension {4} ℚ K]

/-- An open neighbourhood of 1 on which the character is the archimedean part alone. -/
def nhdOne : Set (𝔸)ˣ :=
  {x | (x : 𝔸).2 ∈ integralFiniteAdeles (𝓞 K) K ∧
    ((x⁻¹ : (𝔸)ˣ) : 𝔸).2 ∈ integralFiniteAdeles (𝓞 K) K ∧
    Valued.v ((x : 𝔸).2 (placeTwo K) - 1) ≤
      Valued.v (toCompl K (placeTwo K) (gaussOf K 2 2))}

variable {K} in
lemma toCompl_two_add_two_ne_zero : toCompl K (placeTwo K) (gaussOf K 2 2) ≠ 0 := by
  have h0 : gaussOf K 2 2 ≠ 0 := by
    intro h
    have := coords_unique (K := K) (a := 2) (b := 2) (c := 0) (d := 0) (by
      rw [Int.cast_zero, zero_mul, add_zero]; exact h)
    omega
  intro h
  have hv := valued_toCompl (placeTwo K) (gaussOf K 2 2)
  rw [h, map_zero] at hv
  exact (placeTwo K).intValuation_ne_zero _ h0 hv.symm

theorem isOpen_nhdOne : IsOpen (nhdOne K) := by
  refine ((isOpen_integralFiniteAdeles (𝓞 K) K).preimage
    ((continuous_adeleFin (𝓞 K) K).comp Units.continuous_val)).inter
    (((isOpen_integralFiniteAdeles (𝓞 K) K).preimage
      ((continuous_adeleFin (𝓞 K) K).comp Units.continuous_coe_inv)).inter ?_)
  have hopen : IsOpen {y : (placeTwo K).adicCompletion K |
      Valued.v (y - 1) ≤ Valued.v (toCompl K (placeTwo K) (gaussOf K 2 2))} :=
    (isOpen_setOf_valued_le (placeTwo K) _ toCompl_two_add_two_ne_zero).preimage
      (continuous_id.sub continuous_const)
  exact hopen.preimage (((continuous_finAdeleEval (𝓞 K) K (placeTwo K)).comp
    (continuous_adeleFin (𝓞 K) K)).comp Units.continuous_val)

theorem one_mem_nhdOne : (1 : (𝔸)ˣ) ∈ nhdOne K := by
  refine ⟨fun v => one_mem _, ?_, ?_⟩
  · rw [inv_one]
    exact fun v => one_mem _
  · rw [show ((1 : (𝔸)ˣ) : 𝔸).2 (placeTwo K) = 1 from rfl, sub_self, map_zero]
    exact zero_le

variable {K} in
theorem cmChar_eq_of_mem_nhdOne {x : (𝔸)ˣ} (hx : x ∈ nhdOne K) :
    cmChar K x = (unitDir (archU K x))⁻¹ := by
  obtain ⟨h1, h2, h3'⟩ := hx
  have h3 : Valued.v ((x : 𝔸).2 (placeTwo K) - 1) ≤ exp (-3 : ℤ) :=
    h3'.trans ((valued_toCompl_two_le_iff _).2 dvd_rfl)
  have hord : ∀ v : HeightOneSpectrum (𝓞 K), ordAt v x = 0 := fun v =>
    ordAt_eq_zero_of_le_one ((mem_adicCompletionIntegers (𝓞 K) K v).mp (h1 v))
      ((mem_adicCompletionIntegers (𝓞 K) K v).mp (h2 v))
  have hρ : ρ K x = 1 := by
    unfold ρ
    exact finprod_eq_one_of_forall_eq_one fun v => by rw [hord v, zpow_zero]
  have hu2 : unit2 K x = (x : 𝔸).2 (placeTwo K) := by
    unfold unit2
    rw [hρ, map_one, inv_one, mul_one]
  have hθ : thetaHom K x = archU K x :=
    Units.ext (by rw [thetaHom_val, hρ, map_one, inv_one, mul_one]; rfl)
  rw [cmChar_apply, hθ, rootHom_apply, hu2, root2_of_sub_one_le h3, map_one, mul_one]

/-- **`cmChar` is continuous.** -/
theorem continuous_cmChar : Continuous (cmChar K) := by
  refine continuous_of_continuousAt_one (cmChar K) ?_
  have hg : Continuous fun x : (𝔸)ˣ => (unitDir (archU K x))⁻¹ :=
    (continuous_unitDir.comp (continuous_archU K)).inv
  refine hg.continuousAt.congr ?_
  exact Filter.eventually_of_mem ((isOpen_nhdOne K).mem_nhds (one_mem_nhdOne K)) fun x hx =>
    (cmChar_eq_of_mem_nhdOne hx).symm

/-! ## It is not a power of the norm -/

/-- **`cmChar` is not an imaginary power of the norm.** -/
theorem cmChar_ne_normPowChar (τ : ℝ) : cmChar K ≠ normPowChar K τ := by
  intro h
  set x₀ : (𝔸)ˣ := Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K (placeTwo K)
    (Units.map ((toCompl K (placeTwo K) : 𝓞 K →+* _) : 𝓞 K →* _) (gaussIUnit K))) with hx₀
  have hpow : x₀ ^ 4 = 1 := by
    rw [hx₀, ← map_pow, ← map_pow, ← map_pow, unit_pow_four, map_one, map_one, map_one]
  have hnorm : ideleNorm K x₀ = 1 := by
    have h4 : ideleNorm K x₀ ^ 4 = 1 := by
      have : ideleNorm K (x₀ ^ 4) = ideleNorm K x₀ ^ 4 := by
        simp only [pow_succ, pow_zero, one_mul, ideleNorm_mul]
      rw [← this, hpow, ideleNorm_one K]
    exact (pow_eq_one_iff_of_nonneg (ideleNorm_pos x₀).le (by norm_num)).1 h4
  apply cmChar_localUnit_two_ne_one (K := K)
  show cmChar K x₀ = 1
  rw [h]
  refine Units.ext ?_
  show ((ideleNorm K x₀ : ℝ) : ℂ) ^ (Complex.I * τ) = 1
  rw [hnorm, Complex.ofReal_one, Complex.one_cpow]

/-! ## The theorem -/

/-- The Dirichlet series of `cmCoeff` has an entire continuation: version
for any model `K` of `ℚ(i)`. -/
theorem exists_entire_lseries_cmCoeff_of_cyclotomic (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {4} ℚ K] :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      ∀ s : ℂ, 3 / 2 < s.re → F s = LSeries (fun n => ((cmCoeff n : ℤ) : ℂ)) s :=
  exists_entire_lseries_of_hasProd_places K (cmChar K)
    (Units.continuous_val.comp (continuous_cmChar K))
    (isUnitaryChar_cmChar K) (isIdeleClassChar_cmChar K) {placeTwo K}
    (fun v hv => (isUnramifiedCharAt_cmChar_iff v).2 (by simpa using hv))
    (cmChar_ne_normPowChar K) _ fun _ hs => by
      rw [cmCoeff_eq_gCoeff]
      exact hasProd_places_of_isGenEulerDatum isGenEulerDatum_cmChar rfl
        (fun p _ h3 => by rw [cmPrime, if_neg (by omega)]) (fun p hp => cmPrime_sq_le hp) hs

end CMPoints

/-- **The Dirichlet series of `cmCoeff` has an entire continuation to all of
`ℂ`.** No hypotheses. -/
theorem CMPoints.entire_lseries_cmCoeff :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      ∀ s : ℂ, 3 / 2 < s.re → F s = LSeries (fun n => ((CMPoints.cmCoeff n : ℤ) : ℂ)) s := by
  haveI : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  exact CMPoints.exists_entire_lseries_cmCoeff_of_cyclotomic (CyclotomicField 4 ℚ)
