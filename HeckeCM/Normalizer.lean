import Definitions.Def_NumberField_AdelicLevel
import HeckeCM.GaussPrimary

/-!
# The normalizer of the idèles of `ℚ(i)`

For an idèle `x` of `K = ℚ(i)` we define the order `ordAt v x` at every finite
place and the normalizer
`ρ x = ∏ gen v ^ ordAt v x ∈ Kˣ`, where `gen v` is the primary generator of `v`
(and `1 + i` above 2). By construction `ρ x` has the same valuation as `x` at
every place.

* `valuation_ρ`, `ρ_mul`, `ρ_one`;
* `ρ_localUnit_uniformizer`: on a uniformizer at `v`, `ρ = gen v`;
* `ρ_localUnit_unit`: on a local unit, `ρ = 1`;
* `exists_unit_mul_ρ_principal`: on a principal idèle `α`, `α = u · ρ α` with
  `u` a unit of `𝓞 K`.

The section on the order is the copy, for `K` in place of `ℚ`, of the section
`Order` of `Definitions/Def_RatIdele_Normalizer.lean` of the Fermat repository
`anthropics/fermats-last-theorem` (Apache 2.0); the outline of the normalizer
comes from the same file.
-/

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open NumberField.AdelicLevel

namespace CMPoints

variable (K : Type) [Field K] [NumberField K]

local notation "𝔸" => AdeleRing (𝓞 K) K
local notation "𝔸f" => FiniteAdeleRing (𝓞 K) K

section Order

variable {K}

theorem valued_snd_mul (x y : (𝔸)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((((x * y : (𝔸)ˣ)) : 𝔸).2 v) = Valued.v ((x : 𝔸).2 v) * Valued.v ((y : 𝔸).2 v) := by
  rw [← map_mul]
  rfl

theorem valued_snd_ne_zero (x : (𝔸)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((x : 𝔸).2 v) ≠ 0 := by
  rw [ne_eq, map_eq_zero]
  intro h
  have h1 : (((x * x⁻¹ : (𝔸)ˣ)) : 𝔸).2 v = 1 := by
    rw [mul_inv_cancel]
    rfl
  rw [show (((x * x⁻¹ : (𝔸)ˣ)) : 𝔸).2 v = (x : 𝔸).2 v * (((x⁻¹ : (𝔸)ˣ)) : 𝔸).2 v from rfl, h,
    zero_mul] at h1
  exact zero_ne_one h1

theorem snd_ne_zero (x : (𝔸)ˣ) (v : HeightOneSpectrum (𝓞 K)) : (x : 𝔸).2 v ≠ 0 := fun h =>
  valued_snd_ne_zero x v (by rw [h, map_zero])

theorem valued_snd_inv_mul (x : (𝔸)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((((x⁻¹ : (𝔸)ˣ)) : 𝔸).2 v) * Valued.v ((x : 𝔸).2 v) = 1 := by
  rw [← valued_snd_mul, inv_mul_cancel]
  show Valued.v ((1 : 𝔸f) v) = 1
  rw [show ((1 : 𝔸f)) v = 1 from rfl, map_one]

/-- The order of an idèle at the place `v`. -/
def ordAt (v : HeightOneSpectrum (𝓞 K)) (x : (𝔸)ˣ) : ℤ := -log (Valued.v ((x : 𝔸).2 v))

theorem valued_snd_eq (v : HeightOneSpectrum (𝓞 K)) (x : (𝔸)ˣ) :
    Valued.v ((x : 𝔸).2 v) = exp (-ordAt v x) := by
  rw [ordAt, neg_neg, exp_log (valued_snd_ne_zero x v)]

theorem ordAt_mul (v : HeightOneSpectrum (𝓞 K)) (x y : (𝔸)ˣ) :
    ordAt v (x * y) = ordAt v x + ordAt v y := by
  unfold ordAt
  rw [valued_snd_mul, log_mul (valued_snd_ne_zero x v) (valued_snd_ne_zero y v), neg_add]

theorem ordAt_one (v : HeightOneSpectrum (𝓞 K)) : ordAt v (1 : (𝔸)ˣ) = 0 := by
  unfold ordAt
  rw [show ((1 : (𝔸)ˣ) : 𝔸).2 v = 1 from rfl, map_one, log_one, neg_zero]

theorem ordAt_eq_zero_of_valued_eq_one {v : HeightOneSpectrum (𝓞 K)} {x : (𝔸)ˣ}
    (h1 : Valued.v ((x : 𝔸).2 v) = 1) : ordAt v x = 0 := by
  unfold ordAt
  rw [h1, log_one, neg_zero]

theorem ordAt_eq_zero_of_le_one {v : HeightOneSpectrum (𝓞 K)} {x : (𝔸)ˣ}
    (hx : Valued.v ((x : 𝔸).2 v) ≤ 1)
    (hxi : Valued.v ((((x⁻¹ : (𝔸)ˣ)) : 𝔸).2 v) ≤ 1) : ordAt v x = 0 := by
  have hmul := valued_snd_inv_mul x v
  have h1 : Valued.v ((x : 𝔸).2 v) = 1 := le_antisymm hx (by
    calc (1 : ℤᵐ⁰) = Valued.v ((((x⁻¹ : (𝔸)ˣ)) : 𝔸).2 v) * Valued.v ((x : 𝔸).2 v) := hmul.symm
      _ ≤ 1 * Valued.v ((x : 𝔸).2 v) := mul_le_mul_left hxi _
      _ = Valued.v ((x : 𝔸).2 v) := one_mul _)
  exact ordAt_eq_zero_of_valued_eq_one h1

theorem finite_setOf_ordAt_ne_zero (x : (𝔸)ˣ) :
    {v : HeightOneSpectrum (𝓞 K) | ordAt v x ≠ 0}.Finite := by
  have hx : ∀ᶠ v in Filter.cofinite, ((x : 𝔸).2 : 𝔸f) v ∈ v.adicCompletionIntegers K :=
    ((x : 𝔸).2).2
  have hxi : ∀ᶠ v in Filter.cofinite,
      ((((x⁻¹ : (𝔸)ˣ)) : 𝔸).2 : 𝔸f) v ∈ v.adicCompletionIntegers K :=
    ((((x⁻¹ : (𝔸)ˣ)) : 𝔸).2).2
  have hboth := hx.and hxi
  rw [Filter.eventually_cofinite] at hboth
  refine hboth.subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv ⊢
  intro hcon
  exact hv (ordAt_eq_zero_of_le_one ((mem_adicCompletionIntegers (𝓞 K) K v).mp hcon.1)
    ((mem_adicCompletionIntegers (𝓞 K) K v).mp hcon.2))

theorem valued_algebraMap (v : HeightOneSpectrum (𝓞 K)) (q : K) :
    Valued.v (algebraMap K (v.adicCompletion K) q) = v.valuation K q := by
  rw [algebraMap_adicCompletion]
  exact valuedAdicCompletion_eq_valuation' v q

theorem algebraMap_adeleRing_snd (q : K) (v : HeightOneSpectrum (𝓞 K)) :
    (algebraMap K 𝔸 q).2 v = algebraMap K (v.adicCompletion K) q := by
  rw [AdeleRing.algebraMap_snd_apply, algebraMap_adicCompletion]
  rfl

end Order

section Gen

variable [IsCyclotomicExtension {4} ℚ K]

open Classical in
/-- The chosen generator of the place `v`: `1 + i` above 2, the primary
generator otherwise. -/
def gen (v : HeightOneSpectrum (𝓞 K)) : 𝓞 K :=
  if h : (2 : 𝓞 K) ∈ v.asIdeal then 1 + gaussI K
  else gaussOf K (Classical.choose (exists_primary_generator v h))
    (Classical.choose (Classical.choose_spec (exists_primary_generator v h)))

variable {K}

theorem gen_of_two_mem {v : HeightOneSpectrum (𝓞 K)} (h : (2 : 𝓞 K) ∈ v.asIdeal) :
    gen K v = 1 + gaussI K := by
  unfold gen
  rw [dif_pos h]

/-- Away from 2 the chosen generator is primary. -/
theorem gen_spec {v : HeightOneSpectrum (𝓞 K)} (h : (2 : 𝓞 K) ∉ v.asIdeal) :
    ∃ a b : ℤ, IsPrimaryPair a b ∧ gen K v = gaussOf K a b ∧ v.asIdeal = Ideal.span {gaussOf K a b} := by
  have hs := Classical.choose_spec (Classical.choose_spec (exists_primary_generator v h))
  refine ⟨_, _, hs.1, ?_, hs.2⟩
  unfold gen
  rw [dif_neg h]

theorem asIdeal_eq_span_gen (v : HeightOneSpectrum (𝓞 K)) : v.asIdeal = Ideal.span {gen K v} := by
  by_cases h : (2 : 𝓞 K) ∈ v.asIdeal
  · rw [gen_of_two_mem h]
    exact asIdeal_eq_span_one_add_gaussI v h
  · obtain ⟨a, b, -, hg, hv⟩ := gen_spec h
    rw [hg]
    exact hv

theorem gen_ne_zero (v : HeightOneSpectrum (𝓞 K)) : gen K v ≠ 0 := by
  intro h0
  have := asIdeal_eq_span_gen v
  rw [h0, Ideal.span_singleton_eq_bot.2 rfl] at this
  exact v.ne_bot this

variable (K) in
/-- The chosen generator, viewed in `K`. -/
def genK (v : HeightOneSpectrum (𝓞 K)) : K := algebraMap (𝓞 K) K (gen K v)

theorem genK_ne_zero (v : HeightOneSpectrum (𝓞 K)) : genK K v ≠ 0 := by
  unfold genK
  rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
  exact gen_ne_zero v

theorem valuation_genK_self (v : HeightOneSpectrum (𝓞 K)) :
    v.valuation K (genK K v) = exp (-1 : ℤ) := by
  unfold genK
  rw [valuation_of_algebraMap]
  exact intValuation_singleton v (gen_ne_zero v) (asIdeal_eq_span_gen v)

theorem valuation_genK_of_ne {v w : HeightOneSpectrum (𝓞 K)} (h : v ≠ w) :
    w.valuation K (genK K v) = 1 := by
  unfold genK
  rw [valuation_of_algebraMap]
  refine intValuation_eq_one_iff.mpr fun hmem => h ?_
  have hle : v.asIdeal ≤ w.asIdeal := by
    rw [asIdeal_eq_span_gen v]
    exact (Ideal.span_singleton_le_iff_mem _).2 hmem
  exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hle)

end Gen

section Rho

variable [IsCyclotomicExtension {4} ℚ K]

/-- The normalizer: the element of `Kˣ` with the same valuations as `x`. -/
def ρ (x : (𝔸)ˣ) : K := ∏ᶠ v : HeightOneSpectrum (𝓞 K), genK K v ^ ordAt v x

variable {K}

theorem mulSupport_ρ_finite (x : (𝔸)ˣ) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => genK K v ^ ordAt v x).Finite := by
  refine (finite_setOf_ordAt_ne_zero x).subset fun v hv => ?_
  rw [Set.mem_setOf_eq]
  intro h0
  rw [Function.mem_mulSupport, h0, zpow_zero] at hv
  exact hv rfl

theorem ρ_ne_zero (x : (𝔸)ˣ) : ρ K x ≠ 0 :=
  finprod_induction (fun r : K => r ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero)
    fun v => zpow_ne_zero _ (genK_ne_zero v)

theorem valuation_ρ (w : HeightOneSpectrum (𝓞 K)) (x : (𝔸)ˣ) :
    w.valuation K (ρ K x) = Valued.v ((x : 𝔸).2 w) := by
  classical
  rw [ρ, finprod_eq_prod_of_mulSupport_subset _
    (show (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) => genK K v ^ ordAt v x) ⊆
      ((mulSupport_ρ_finite x).toFinset : Set (HeightOneSpectrum (𝓞 K))) by
      rw [Set.Finite.coe_toFinset]),
    map_prod, valued_snd_eq, Finset.prod_eq_single w]
  · rw [map_zpow₀, valuation_genK_self, ← exp_zsmul, smul_eq_mul, mul_neg_one]
  · intro v _ hvw
    rw [map_zpow₀, valuation_genK_of_ne hvw, one_zpow]
  · intro hw
    have h0 : genK K w ^ ordAt w x = 1 := by
      by_contra h0
      exact hw ((Set.Finite.mem_toFinset _).mpr h0)
    rw [h0, map_one]

theorem ρ_mul (x y : (𝔸)ˣ) : ρ K (x * y) = ρ K x * ρ K y := by
  unfold ρ
  rw [← finprod_mul_distrib (mulSupport_ρ_finite x) (mulSupport_ρ_finite y)]
  refine finprod_congr fun v => ?_
  rw [ordAt_mul, zpow_add₀ (genK_ne_zero v)]

theorem ρ_one : ρ K (1 : (𝔸)ˣ) = 1 := by
  unfold ρ
  refine finprod_eq_one_of_forall_eq_one fun v => ?_
  rw [ordAt_one, zpow_zero]

theorem ρ_localUnit_uniformizer (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ)
    (ht : Valued.v (t : v.adicCompletion K) = exp (-1 : ℤ)) :
    ρ K (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t)) = genK K v := by
  unfold ρ
  rw [finprod_eq_single _ v]
  · have : ordAt v (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t)) = 1 := by
      unfold ordAt
      rw [Units.coe_map, finIncl_apply_snd, localUnit_apply_self, ht, log_exp, neg_neg]
    rw [this, zpow_one]
  · intro w hw
    have : ordAt w (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t)) = 0 := by
      refine ordAt_eq_zero_of_valued_eq_one ?_
      rw [Units.coe_map, finIncl_apply_snd, localUnit_apply_of_ne (𝓞 K) K v t hw, map_one]
    rw [this, zpow_zero]

theorem ρ_localUnit_unit (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ)
    (ht : Valued.v (t : v.adicCompletion K) = 1) :
    ρ K (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t)) = 1 := by
  unfold ρ
  refine finprod_eq_one_of_forall_eq_one fun w => ?_
  have : ordAt w (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t)) = 0 := by
    refine ordAt_eq_zero_of_valued_eq_one ?_
    rw [Units.coe_map, finIncl_apply_snd]
    by_cases hw : w = v
    · subst hw
      rw [localUnit_apply_self, ht]
    · rw [localUnit_apply_of_ne (𝓞 K) K v t hw, map_one]
  rw [this, zpow_zero]

/-- On a principal idèle `α` the normalizer equals `α` up to a unit. -/
theorem exists_unit_mul_ρ_principal (α : Kˣ) :
    ∃ u : (𝓞 K)ˣ, (α : K) =
      algebraMap (𝓞 K) K u * ρ K (Units.map (algebraMap K 𝔸 : K →* 𝔸) α) := by
  set r := ρ K (Units.map (algebraMap K 𝔸 : K →* 𝔸) α) with hr
  have hr0 : r ≠ 0 := ρ_ne_zero _
  have hval : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K ((α : K) / r) = 1 := fun v => by
    rw [map_div₀, hr, valuation_ρ, Units.coe_map, MonoidHom.coe_coe, algebraMap_adeleRing_snd,
      valued_algebraMap, div_self]
    exact (map_ne_zero _).2 α.ne_zero
  obtain ⟨z, hz⟩ := mem_integers_of_valuation_le_one K ((α : K) / r) fun v => (hval v).le
  obtain ⟨z', hz'⟩ := mem_integers_of_valuation_le_one K ((α : K) / r)⁻¹ fun v => by
    rw [map_inv₀, hval v, inv_one]
  have hq0 : (α : K) / r ≠ 0 := div_ne_zero α.ne_zero hr0
  have hzz' : z * z' = 1 :=
    IsFractionRing.injective (𝓞 K) K (by rw [map_mul, hz, hz', map_one, mul_inv_cancel₀ hq0])
  refine ⟨Units.mkOfMulEqOne z z' hzz', ?_⟩
  rw [Units.val_mkOfMulEqOne, hz, div_mul_cancel₀ _ hr0]

end Rho

end CMPoints
