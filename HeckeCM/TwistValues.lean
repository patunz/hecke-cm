import HeckeCM.TwistChar
import HeckeCM.TwistRamified
import HeckeCM.GenPlaces
import HeckeCM.TwistCoeff

/-!
# The twisted Hecke character and its local values

For `d` odd and squarefree, `cmCharTw = cmChar · twC`:

* it is a continuous unitary character of the idèle class group;
* it is unramified exactly away from 2 and from the places containing `d`;
* on the uniformizer of a good place `w` it equals the value of `cmChar` times
  `(nrm π_w / d)`;
* its local values satisfy `IsGenEulerDatum` for the twisted sequence
  `cmCoeffTw d` (`isGenEulerDatum_cmCharTw`).
-/

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open NumberField.AdelicLevel AutomorphicForm NumberField.TateGlobal
open scoped Classical Topology

namespace CMPoints

variable (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

local notation "𝔸" => AdeleRing (𝓞 K) K

/-- The idèle concentrated at the place `v`. -/
abbrev locIdele (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) : (𝔸)ˣ :=
  Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t)

variable {K}

lemma unitAt_locIdele_of_ne {v w : HeightOneSpectrum (𝓞 K)} (h : v ≠ w)
    (t : (w.adicCompletion K)ˣ) :
    unitAt K v (locIdele K w t) =
      (algebraMap K (v.adicCompletion K) (ρ K (locIdele K w t)))⁻¹ := by
  unfold unitAt
  rw [Units.coe_map, finIncl_apply_snd, localUnit_apply_of_ne (𝓞 K) K w t h, one_mul]

lemma unitAt_locIdele_self (w : HeightOneSpectrum (𝓞 K)) (t : (w.adicCompletion K)ˣ) :
    unitAt K w (locIdele K w t) =
      (t : w.adicCompletion K) * (algebraMap K (w.adicCompletion K) (ρ K (locIdele K w t)))⁻¹ := by
  unfold unitAt
  rw [Units.coe_map, finIncl_apply_snd, localUnit_apply_self]

lemma natCast_notMem_placeTwo {d : ℕ} (hodd : d % 2 = 1) :
    ((d : ℕ) : 𝓞 K) ∉ (placeTwo K).asIdeal := fun h =>
  two_not_mem (placeTwo K) hodd h two_mem_placeTwo

lemma valued_eq_one_of_mem_integers {v : HeightOneSpectrum (𝓞 K)} (t : (v.adicCompletion K)ˣ)
    (ht : (t : v.adicCompletion K) ∈ v.adicCompletionIntegers K)
    (hti : ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K) :
    Valued.v (t : v.adicCompletion K) = 1 := by
  have h1 := (mem_adicCompletionIntegers (𝓞 K) K v).1 ht
  have h2 := (mem_adicCompletionIntegers (𝓞 K) K v).1 hti
  have hmul : Valued.v (t : v.adicCompletion K) *
      Valued.v ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  exact le_antisymm h1 (by
    calc (1 : ℤᵐ⁰) = Valued.v (t : v.adicCompletion K) *
          Valued.v ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) := hmul.symm
      _ ≤ Valued.v (t : v.adicCompletion K) * 1 := mul_le_mul_right h2 _
      _ = Valued.v (t : v.adicCompletion K) := mul_one _)

variable {d : ℕ} (hodd : d % 2 = 1) (hsq : Squarefree d) (hd : d ≠ 0)
include hodd hsq

/-! ## The twisting character on idèles concentrated at one place -/

/-- A local unit away from `d` maps to 1. -/
theorem twC_locIdele_unit {w : HeightOneSpectrum (𝓞 K)} (hw : ((d : ℕ) : 𝓞 K) ∉ w.asIdeal)
    (t : (w.adicCompletion K)ˣ) (ht : Valued.v (t : w.adicCompletion K) = 1) :
    twC K hodd hsq hd (locIdele K w t) = 1 := by
  refine twC_eq_one_of_isClose_one hodd hsq hd fun v hv => ?_
  have hvw : v ≠ w := by
    rintro rfl
    exact hw hv
  rw [unitAt_locIdele_of_ne hvw, ρ_localUnit_unit w t ht, map_one, inv_one, map_one, sub_self,
    map_zero]
  exact zero_lt_one

/-- On a uniformizer away from `d` the symbol equals `(nrm π_w / d)`. -/
theorem tw_locIdele_uniformizer {w : HeightOneSpectrum (𝓞 K)}
    (hw : ((d : ℕ) : 𝓞 K) ∉ w.asIdeal) (t : (w.adicCompletion K)ˣ)
    (ht : Valued.v (t : w.adicCompletion K) = exp (-1 : ℤ)) :
    tw K d hd (locIdele K w t) = tau K d (gen K w) := by
  have hρ := ρ_localUnit_uniformizer w t ht
  obtain ⟨α, hα⟩ := exists_isClose (K := K) hd (locIdele K w t)
  have hc : IsClose d (1 : (𝔸)ˣ) (α * gen K w) := by
    intro v hv
    have hvw : v ≠ w := by
      rintro rfl
      exact hw hv
    have hπ1 : Valued.v (toCompl K v (gen K w)) = 1 := by
      show Valued.v (algebraMap K (v.adicCompletion K) (genK K w)) = 1
      rw [valued_algebraMap, valuation_genK_of_ne (Ne.symm hvw)]
    have hπ0 : toCompl K v (gen K w) ≠ 0 := fun h0 => by
      rw [h0, map_zero] at hπ1
      exact zero_ne_one hπ1
    have hu : unitAt K v (locIdele K w t) = (toCompl K v (gen K w))⁻¹ := by
      rw [unitAt_locIdele_of_ne hvw, hρ]
      rfl
    have hαv := hα v hv
    rw [hu] at hαv
    have e : (1 : v.adicCompletion K) - toCompl K v α * toCompl K v (gen K w) =
        toCompl K v (gen K w) * ((toCompl K v (gen K w))⁻¹ - toCompl K v α) := by
      rw [mul_sub, mul_inv_cancel₀ hπ0]
      ring
    rw [unitAt_one, map_mul, e, map_mul, hπ1, one_mul]
    exact hαv
  have hdvd := (isClose_one (K := K) (d := d)).dvd_sub hodd hsq hc
  have h1 := tau_congr hdvd
  rw [tau_one, tau_mul] at h1
  rw [tw_eq hodd hsq hd hα]
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.1 h1.symm with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> rw [h2, h3]

/-- At every place containing `d` there is a local unit on which the symbol equals `−1`. -/
theorem exists_twC_locIdele_eq_neg_one {v : HeightOneSpectrum (𝓞 K)}
    (hv : ((d : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    ∃ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 ∧
      ((twC K hodd hsq hd (locIdele K v t) : ℂˣ) : ℂ) = -1 := by
  obtain ⟨α, hαv, hothers, htau⟩ := exists_tau_eq_neg_one hodd hsq v hv
  have hval : Valued.v (toCompl K v α) = 1 := by
    rw [valued_toCompl, intValuation_eq_one_iff]
    exact hαv
  have hne : toCompl K v α ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hval
    exact zero_ne_one hval
  refine ⟨Units.mk0 _ hne, hval, ?_⟩
  have hρ := ρ_localUnit_unit v (Units.mk0 _ hne) hval
  have hclose : IsClose d (locIdele K v (Units.mk0 _ hne)) α := by
    intro v' hv'
    by_cases h : v' = v
    · subst h
      rw [unitAt_locIdele_self, hρ, map_one, inv_one, mul_one, Units.val_mk0, sub_self, map_zero]
      exact zero_lt_one
    · rw [unitAt_locIdele_of_ne h, hρ, map_one, inv_one, Valuation.map_sub_swap,
        ← map_one (toCompl K v'), ← map_sub, valued_toCompl, intValuation_lt_one_iff_mem]
      exact hothers v' hv' h
  rw [twC_val, tw_eq hodd hsq hd hclose, htau]
  norm_num

/-! ## Continuity of the twisting character -/

/-- An open neighbourhood of 1 on which the twisting character equals 1. -/
def twNhd : Set (𝔸)ˣ :=
  {x | (x : 𝔸).2 ∈ integralFiniteAdeles (𝓞 K) K} ∩
    ({x | ((x⁻¹ : (𝔸)ˣ) : 𝔸).2 ∈ integralFiniteAdeles (𝓞 K) K} ∩
      ⋂ v ∈ (finite_setOf_natCast_mem (K := K) hd).toFinset,
        {x : (𝔸)ˣ | Valued.v ((x : 𝔸).2 v - 1) ≤ Valued.v (toCompl K v (gen K v))})

omit hodd hsq in
lemma valued_toCompl_gen_lt_one (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v (toCompl K v (gen K v)) < 1 := by
  rw [valued_toCompl, intValuation_lt_one_iff_mem, asIdeal_eq_span_gen v]
  exact Ideal.mem_span_singleton_self _

omit hodd hsq in
lemma toCompl_gen_ne_zero (v : HeightOneSpectrum (𝓞 K)) : toCompl K v (gen K v) ≠ 0 := by
  intro h
  have hv := valued_toCompl v (gen K v)
  rw [h, map_zero] at hv
  exact v.intValuation_ne_zero _ (gen_ne_zero v) hv.symm

omit hodd hsq in
theorem isOpen_twNhd : IsOpen (twNhd (K := K) hd) := by
  refine ((isOpen_integralFiniteAdeles (𝓞 K) K).preimage
    ((continuous_adeleFin (𝓞 K) K).comp Units.continuous_val)).inter
    (((isOpen_integralFiniteAdeles (𝓞 K) K).preimage
      ((continuous_adeleFin (𝓞 K) K).comp Units.continuous_coe_inv)).inter ?_)
  refine isOpen_biInter_finset fun v _ => ?_
  have hopen : IsOpen {y : v.adicCompletion K |
      Valued.v (y - 1) ≤ Valued.v (toCompl K v (gen K v))} :=
    (isOpen_setOf_valued_le v _ (toCompl_gen_ne_zero v)).preimage
      (continuous_id.sub continuous_const)
  exact hopen.preimage (((continuous_finAdeleEval (𝓞 K) K v).comp
    (continuous_adeleFin (𝓞 K) K)).comp Units.continuous_val)

omit hodd hsq in
theorem one_mem_twNhd : (1 : (𝔸)ˣ) ∈ twNhd (K := K) hd := by
  refine ⟨fun v => one_mem _, ?_, ?_⟩
  · show ((1⁻¹ : (𝔸)ˣ) : 𝔸).2 ∈ integralFiniteAdeles (𝓞 K) K
    rw [inv_one]
    exact fun v => one_mem _
  · refine Set.mem_iInter₂.2 fun v _ => ?_
    show Valued.v (((1 : (𝔸)ˣ) : 𝔸).2 v - 1) ≤ _
    rw [show ((1 : (𝔸)ˣ) : 𝔸).2 v = 1 from rfl, sub_self, map_zero]
    exact zero_le

theorem twC_eq_one_of_mem_twNhd {x : (𝔸)ˣ} (hx : x ∈ twNhd (K := K) hd) :
    twC K hodd hsq hd x = 1 := by
  obtain ⟨h1, h2, h3⟩ := hx
  have hord : ∀ v : HeightOneSpectrum (𝓞 K), ordAt v x = 0 := fun v =>
    ordAt_eq_zero_of_le_one ((mem_adicCompletionIntegers (𝓞 K) K v).mp (h1 v))
      ((mem_adicCompletionIntegers (𝓞 K) K v).mp (h2 v))
  have hρ : ρ K x = 1 := by
    unfold ρ
    exact finprod_eq_one_of_forall_eq_one fun v => by rw [hord v, zpow_zero]
  refine twC_eq_one_of_isClose_one hodd hsq hd fun v hv => ?_
  have hv3 := Set.mem_iInter₂.1 h3 v ((Set.Finite.mem_toFinset _).2 hv)
  have hu : unitAt K v x = (x : 𝔸).2 v := by
    unfold unitAt
    rw [hρ, map_one, inv_one, mul_one]
  rw [hu, map_one]
  exact lt_of_le_of_lt hv3 (valued_toCompl_gen_lt_one v)

theorem continuous_twC : Continuous (twC K hodd hsq hd) := by
  refine continuous_of_continuousAt_one (twC K hodd hsq hd) ?_
  have hc : ContinuousAt (fun _ : (𝔸)ˣ => (1 : ℂˣ)) 1 := continuousAt_const
  refine hc.congr ?_
  exact Filter.eventually_of_mem ((isOpen_twNhd hd).mem_nhds (one_mem_twNhd hd)) fun x hx =>
    (twC_eq_one_of_mem_twNhd hodd hsq hd hx).symm

/-! ## The twisted character -/

variable (K) in
/-- **The Hecke character of `y² = x³ − d²x`.** -/
def cmCharTw : (𝔸)ˣ →* ℂˣ := cmChar K * twC K hodd hsq hd

theorem cmCharTw_apply (x : (𝔸)ˣ) :
    cmCharTw K hodd hsq hd x = cmChar K x * twC K hodd hsq hd x := rfl

theorem isUnitaryChar_cmCharTw : IsUnitaryChar (𝓞 K) K (cmCharTw K hodd hsq hd) := by
  intro x
  rw [cmCharTw_apply, Units.val_mul, norm_mul, isUnitaryChar_cmChar K x, norm_twC, one_mul]

theorem isIdeleClassChar_cmCharTw : IsIdeleClassChar (𝓞 K) K (cmCharTw K hodd hsq hd) := by
  intro a
  rw [cmCharTw_apply, isIdeleClassChar_cmChar K a, twC_principal, one_mul]

theorem continuous_cmCharTw : Continuous (cmCharTw K hodd hsq hd) :=
  (continuous_cmChar K).mul (continuous_twC hodd hsq hd)

/-- Unramified away from 2 and `d`. -/
theorem isUnramifiedCharAt_cmCharTw {w : HeightOneSpectrum (𝓞 K)} (h2 : w ≠ placeTwo K)
    (hw : ((d : ℕ) : 𝓞 K) ∉ w.asIdeal) : IsUnramifiedCharAt (cmCharTw K hodd hsq hd) w := by
  intro t ht hti
  have hone := valued_eq_one_of_mem_integers t ht hti
  show cmCharTw K hodd hsq hd (locIdele K w t) = 1
  rw [cmCharTw_apply, cmChar_localUnit_of_ne h2 t hone, twC_locIdele_unit hodd hsq hd hw t hone,
    one_mul]

/-- Ramified at 2. -/
theorem not_isUnramifiedCharAt_cmCharTw_two :
    ¬ IsUnramifiedCharAt (cmCharTw K hodd hsq hd) (placeTwo K) := by
  intro h
  set t : ((placeTwo K).adicCompletion K)ˣ :=
    Units.map ((toCompl K (placeTwo K) : 𝓞 K →+* _) : 𝓞 K →* _) (gaussIUnit K) with ht
  have htv : (t : (placeTwo K).adicCompletion K) = toCompl K (placeTwo K) (gaussIUnit K) := rfl
  have ht1 : Valued.v (t : (placeTwo K).adicCompletion K) = 1 := by
    rw [htv, valued_toCompl_unit]
  have hti1 : Valued.v ((t⁻¹ : ((placeTwo K).adicCompletion K)ˣ) :
      (placeTwo K).adicCompletion K) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, ht1, inv_one]
  have key : cmCharTw K hodd hsq hd (locIdele K (placeTwo K) t) = 1 :=
    h t ((mem_adicCompletionIntegers (𝓞 K) K _).2 ht1.le)
      ((mem_adicCompletionIntegers (𝓞 K) K _).2 hti1.le)
  rw [cmCharTw_apply, twC_locIdele_unit hodd hsq hd (natCast_notMem_placeTwo hodd) t ht1,
    mul_one] at key
  exact cmChar_localUnit_two_ne_one (K := K) key

/-- Ramified at every place containing `d`. -/
theorem not_isUnramifiedCharAt_cmCharTw_of_mem {v : HeightOneSpectrum (𝓞 K)}
    (hv : ((d : ℕ) : 𝓞 K) ∈ v.asIdeal) : ¬ IsUnramifiedCharAt (cmCharTw K hodd hsq hd) v := by
  intro h
  obtain ⟨t, ht1, htw⟩ := exists_twC_locIdele_eq_neg_one hodd hsq hd hv
  have hv2 : v ≠ placeTwo K := by
    rintro rfl
    exact natCast_notMem_placeTwo hodd hv
  have hti1 : Valued.v ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, ht1, inv_one]
  have key : cmCharTw K hodd hsq hd (locIdele K v t) = 1 :=
    h t ((mem_adicCompletionIntegers (𝓞 K) K v).2 ht1.le)
      ((mem_adicCompletionIntegers (𝓞 K) K v).2 hti1.le)
  have hval := congrArg (fun z : ℂˣ => (z : ℂ)) key
  simp only [cmCharTw_apply, Units.val_mul, Units.val_one] at hval
  rw [cmChar_localUnit_of_ne hv2 t ht1, Units.val_one, one_mul, htw] at hval
  norm_num at hval

/-- The value on the uniformizer of a good place. -/
theorem cmCharTw_uniformizerIdele {w : HeightOneSpectrum (𝓞 K)} (h2 : w ≠ placeTwo K)
    (hw : ((d : ℕ) : 𝓞 K) ∉ w.asIdeal) :
    ((cmCharTw K hodd hsq hd (uniformizerIdele K w) : ℂˣ) : ℂ) =
      sigma K (genK K w) / ((‖sigma K (genK K w)‖ : ℝ) : ℂ) * ((tau K d (gen K w) : ℤ) : ℂ) := by
  have h1 : uniformizerIdele K w = locIdele K w (uniformizerUnit K w) := rfl
  rw [cmCharTw_apply, Units.val_mul, cmChar_uniformizerIdele h2, twC_val, h1,
    tw_locIdele_uniformizer hodd hsq hd hw _ (valued_uniformizerUnit K w)]

end CMPoints
