import HeckeCM.GaussLocal
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_of_hasConductorExponentAt_zero

/-!
# The twisting character at the places dividing `d`

For `d` odd and squarefree and `v` a place with `d ∈ v`:

* `hasConductorExponentAt_twC`: the local component of `twC` has conductor
  exponent 1;
* `twC_locIdele_toCompl`, `twC_locIdele_gen`: the values of `twC` on a global
  unit and on the primary generator, via an explicit approximant;
* `stdRootNumberAt_cmCharTw_of_mem`: the local root number of `cmCharTw` is
  `σ(π)/|σ(π)|` times that of `twC`;
* `gauss_sum_twC`: the Gauss sum computing the root number of `twC`.
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

attribute [local instance] localBorel borelSpace_localBorel

lemma valued_toCompl_gen (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v (toCompl K v (gen K v)) = exp (-1 : ℤ) := by
  rw [valued_toCompl]
  exact intValuation_singleton v (gen_ne_zero v) (asIdeal_eq_span_gen v)

lemma toCompl_gen_ne_zero' (v : HeightOneSpectrum (𝓞 K)) : toCompl K v (gen K v) ≠ 0 := fun h => by
  have := valued_toCompl_gen v
  rw [h, map_zero] at this
  exact exp_ne_zero this.symm

variable {d : ℕ} (hodd : d % 2 = 1) (hsq : Squarefree d) (hd : d ≠ 0)
include hodd hsq

theorem twC_locIdele_of_sub_one_lt (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ)
    (ht : Valued.v (t : v.adicCompletion K) = 1)
    (h : Valued.v ((t : v.adicCompletion K) - 1) < 1) :
    twC K hodd hsq hd (locIdele K v t) = 1 := by
  refine twC_eq_one_of_isClose_one hodd hsq hd fun v' _ => ?_
  by_cases hv : v' = v
  · subst hv
    rw [unitAt_locIdele_self, ρ_localUnit_unit v' t ht, map_one, inv_one, mul_one, map_one]
    exact h
  · rw [unitAt_locIdele_of_ne hv, ρ_localUnit_unit v t ht, map_one, inv_one, map_one, sub_self,
      map_zero]
    exact zero_lt_one

/-- **At a place dividing `d` the conductor exponent of `twC` is 1.** -/
theorem hasConductorExponentAt_twC {v : HeightOneSpectrum (𝓞 K)}
    (hv : ((d : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    HasConductorExponentAt K v (localChar (twC K hodd hsq hd) v) 1 := by
  constructor
  · intro u hu
    obtain ⟨h1, h2⟩ := hu
    have h2' : Valued.v ((u : v.adicCompletion K) - 1) < 1 := by
      rcases h2 with h | h
      · exact absurd h one_ne_zero
      · exact (lt_one_iff_le_exp _).2 (by exact_mod_cast h)
    exact twC_locIdele_of_sub_one_lt hodd hsq hd v u h1 h2'
  · intro m hm
    obtain rfl : m = 0 := by omega
    obtain ⟨t, ht, hval⟩ := exists_twC_locIdele_eq_neg_one hodd hsq hd hv
    refine ⟨t, ⟨ht, Or.inl rfl⟩, fun h => ?_⟩
    have h' : twC K hodd hsq hd (locIdele K v t) = 1 := h
    rw [h', Units.val_one] at hval
    norm_num at hval

/-- The value of `twC` on a global unit at `v`, with an approximant `β`. -/
theorem twC_locIdele_toCompl {v : HeightOneSpectrum (𝓞 K)} {α β : 𝓞 K}
    (hα : toCompl K v α ≠ 0) (hαv : α ∉ v.asIdeal) (h1 : β - α ∈ v.asIdeal)
    (h2 : ∀ v' : HeightOneSpectrum (𝓞 K), v' ≠ v → ((d : ℕ) : 𝓞 K) ∈ v'.asIdeal →
      β - 1 ∈ v'.asIdeal) :
    ((twC K hodd hsq hd (locIdele K v (Units.mk0 (toCompl K v α) hα)) : ℂˣ) : ℂ) =
      ((tau K d β : ℤ) : ℂ) := by
  have ht : Valued.v ((Units.mk0 (toCompl K v α) hα : (v.adicCompletion K)ˣ) :
      v.adicCompletion K) = 1 := (valued_toCompl_eq_one_iff v α).2 hαv
  have hc : IsClose d (locIdele K v (Units.mk0 (toCompl K v α) hα)) β := by
    intro v' hv'
    by_cases hv : v' = v
    · subst hv
      rw [unitAt_locIdele_self, ρ_localUnit_unit v' _ ht, map_one, inv_one, mul_one,
        Units.val_mk0, ← map_sub, valued_toCompl_lt_one_iff]
      have := v'.asIdeal.neg_mem h1
      rwa [neg_sub] at this
    · rw [unitAt_locIdele_of_ne hv, ρ_localUnit_unit v _ ht, map_one, inv_one,
        ← map_one (toCompl K v'), ← map_sub, valued_toCompl_lt_one_iff]
      have := v'.asIdeal.neg_mem (h2 v' hv hv')
      rwa [neg_sub] at this
  rw [twC_val, tw_eq hodd hsq hd hc]

/-- The value of `twC` on the primary generator of `v`, with an approximant `β`. -/
theorem twC_locIdele_gen {v : HeightOneSpectrum (𝓞 K)} {β : 𝓞 K} (h1 : β - 1 ∈ v.asIdeal)
    (h2 : ∀ v' : HeightOneSpectrum (𝓞 K), v' ≠ v → ((d : ℕ) : 𝓞 K) ∈ v'.asIdeal →
      β * gen K v - 1 ∈ v'.asIdeal) :
    ((twC K hodd hsq hd (locIdele K v (Units.mk0 (toCompl K v (gen K v))
      (toCompl_gen_ne_zero' v))) : ℂˣ) : ℂ) = ((tau K d β : ℤ) : ℂ) := by
  have ht : Valued.v ((Units.mk0 (toCompl K v (gen K v)) (toCompl_gen_ne_zero' v) :
      (v.adicCompletion K)ˣ) : v.adicCompletion K) = exp (-1 : ℤ) := valued_toCompl_gen v
  have hρ := ρ_localUnit_uniformizer v _ ht
  have hc : IsClose d (locIdele K v (Units.mk0 (toCompl K v (gen K v))
      (toCompl_gen_ne_zero' v))) β := by
    intro v' hv'
    by_cases hv : v' = v
    · subst hv
      rw [unitAt_locIdele_self, hρ, Units.val_mk0]
      have e : toCompl K v' (gen K v') * (algebraMap K (v'.adicCompletion K) (genK K v'))⁻¹ = 1 :=
        mul_inv_cancel₀ (toCompl_gen_ne_zero' v')
      rw [e, ← map_one (toCompl K v'), ← map_sub, valued_toCompl_lt_one_iff]
      have := v'.asIdeal.neg_mem h1
      rwa [neg_sub] at this
    · rw [unitAt_locIdele_of_ne hv, hρ]
      have hg1 : Valued.v (algebraMap K (v'.adicCompletion K) (genK K v)) = 1 := by
        rw [valued_algebraMap, valuation_genK_of_ne (Ne.symm hv)]
      have hg0 : algebraMap K (v'.adicCompletion K) (genK K v) ≠ 0 := fun h => by
        rw [h, map_zero] at hg1
        exact zero_ne_one hg1
      have e : (algebraMap K (v'.adicCompletion K) (genK K v))⁻¹ - toCompl K v' β =
          (algebraMap K (v'.adicCompletion K) (genK K v))⁻¹ *
            -(toCompl K v' (β * gen K v - 1)) := by
        have : toCompl K v' (β * gen K v - 1) =
            toCompl K v' β * algebraMap K (v'.adicCompletion K) (genK K v) - 1 := by
          rw [map_sub, map_mul, map_one]
          rfl
        rw [this]
        field_simp
        ring
      rw [e, map_mul, map_inv₀, hg1, inv_one, one_mul, Valuation.map_neg,
        valued_toCompl_lt_one_iff]
      exact h2 v' hv hv'
  rw [twC_val, tw_eq hodd hsq hd hc]

/-- **The local root number of `cmCharTw` at a place dividing `d`.** -/
theorem stdRootNumberAt_cmCharTw_of_mem {v : HeightOneSpectrum (𝓞 K)}
    (hv : ((d : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    stdRootNumberAt K v (localChar (cmCharTw K hodd hsq hd) v) =
      sigma K (genK K v) / ((‖sigma K (genK K v)‖ : ℝ) : ℂ) *
        stdRootNumberAt K v (localChar (twC K hodd hsq hd) v) := by
  have hv2 : v ≠ placeTwo K := by
    rintro rfl
    exact natCast_notMem_placeTwo hodd hv
  have hloc : localChar (cmCharTw K hodd hsq hd) v =
      localChar (twC K hodd hsq hd) v * localChar (cmChar K) v :=
    MonoidHom.ext fun t => mul_comm _ _
  have h := stdRootNumberAt_mul_of_hasConductorExponentAt_zero K v
    (localChar (twC K hodd hsq hd) v) (localChar (cmChar K) v) 1
    (hasConductorExponentAt_twC hodd hsq hd hv) (hasConductorExponentAt_cmChar_of_ne hv2)
    (norm_twC hodd hsq hd _) (isUnitaryChar_cmChar K _) (psiLocal_ne_one K v)
  rw [hloc, h, addCharLevel_psiLocal_of_ne hv2, show (((1 : ℕ) : ℤ)) + 0 = 1 by norm_num,
    zpow_one, ← cmChar_localUnit_uniformizer hv2 (uniformizerUnit K v) (valued_uniformizerUnit K v)]
  rfl

/-- **The Gauss sum computing the local root number of `twC`.** -/
theorem gauss_sum_twC {v : HeightOneSpectrum (𝓞 K)} (hv : ((d : ℕ) : 𝓞 K) ∈ v.asIdeal)
    {ι : Type} [Fintype ι] (r : ι → 𝓞 K) (hcover : ∀ α : 𝓞 K, ∃ i, α - r i ∈ v.asIdeal)
    (hinj : ∀ i j, r i - r j ∈ v.asIdeal → i = j) :
    ((Ideal.absNorm v.asIdeal : ℂ))⁻¹ * (∑ i : {i // r i ∉ v.asIdeal},
        psiLocal K v ((toCompl K v (gen K v))⁻¹ * toCompl K v (r i)) *
          charExt (localChar (twC K hodd hsq hd) v)⁻¹ (toCompl K v (r i))) *
        (Ideal.absNorm v.asIdeal : ℂ) ^ ((1 : ℂ) / 2) =
      charExt (localChar (twC K hodd hsq hd) v) (toCompl K v (gen K v))⁻¹ *
        stdRootNumberAt K v (localChar (twC K hodd hsq hd) v) := by
  have hv2 : v ≠ placeTwo K := by
    rintro rfl
    exact natCast_notMem_placeTwo hodd hv
  have hlev := addCharLevel_psiLocal_of_ne hv2
  have hcond := hasConductorExponentAt_twC hodd hsq hd hv
  have hzv : Valued.v (toCompl K v (gen K v))⁻¹ = exp (1 : ℤ) := by
    rw [map_inv₀, valued_toCompl_gen, ← exp_neg, neg_neg]
  have hz : Valued.v (toCompl K v (gen K v))⁻¹ =
      exp (addCharLevel (psiLocal K v) + ((1 : ℕ) : ℤ)) := by
    rw [hlev, hzv]
    norm_num
  have H := setIntegral_psiLocal_mul_charExt_inv_mul_cpow_eq_charExt_mul_stdRootNumberAt K v
    (localChar (twC K hodd hsq hd) v) 1 le_rfl hcond (norm_twC hodd hsq hd _) _ hz
  rw [gauss_integral_eq_sum v r hlev hcover hinj _ hcond.1 _ hzv.le, hlev] at H
  rw [← H]
  congr 2
  push_cast
  norm_num

end CMPoints
