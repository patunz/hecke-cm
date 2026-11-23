import HeckeCM.TwistValues

/-!
# The quadratic character at 2

For an idèle `x` of `K = ℚ(i)`, `tw8 x = χ₈(nrm α)` where `α ∈ 𝓞 K` approximates
`x₂ / ρ x` modulo `8 = i (1 + i)⁶` at the place above 2. This is the character of
`K(√2)/K`: together with the twisting character of odd `e` it gives that of `2e`,
because `(2e / N) = χ₈(N) · (N / e)` for `N ≡ 1 (mod 4)`.

* `tw8C : 𝔸ˣ →* ℂˣ`, with values `±1`, trivial on principal idèles, continuous;
* it equals 1 on the local units away from 2, and `χ₈(nrm π_w)` on the uniformizer
  of a place `w` other than the one above 2.
-/

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open NumberField.AdelicLevel AutomorphicForm
open scoped Classical Topology

namespace CMPoints

variable (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

local notation "𝔸" => AdeleRing (𝓞 K) K

/-! ## Arithmetic modulo 8 -/

/-- `χ₈` of the norm. -/
def chi8 (z : 𝓞 K) : ℤ := ZMod.χ₈ ((nrm K z : ℤ) : ZMod 8)

variable {K}

lemma chi8_mul (z w : 𝓞 K) : chi8 K (z * w) = chi8 K z * chi8 K w := by
  rw [chi8, nrm_mul, Int.cast_mul, map_mul]
  rfl

lemma chi8_one : chi8 K (1 : 𝓞 K) = 1 := by
  rw [chi8, nrm_one, Int.cast_one, map_one]

lemma chi8_unit (u : (𝓞 K)ˣ) : chi8 K (u : 𝓞 K) = 1 := by
  rw [chi8, nrm_unit, Int.cast_one, map_one]

lemma chi8_congr {z w : 𝓞 K} (h : ((8 : ℤ) : 𝓞 K) ∣ z - w) : chi8 K z = chi8 K w := by
  have hd := intCast_dvd_nrm_sub h
  have : ((nrm K z : ℤ) : ZMod 8) = ((nrm K w : ℤ) : ZMod 8) := by
    rw [← sub_eq_zero, ← Int.cast_sub]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).2 (by exact_mod_cast hd)
  rw [chi8, chi8, this]

lemma chi8_sq_of_odd {n : ℤ} (h : ¬ (2 : ℤ) ∣ n) :
    ZMod.χ₈ ((n : ℤ) : ZMod 8) * ZMod.χ₈ ((n : ℤ) : ZMod 8) = 1 := by
  have h8 : ((n : ℤ) : ZMod 8) = (((n % 8 : ℤ)) : ZMod 8) := by
    simpa using (ZMod.intCast_mod n 8).symm
  have hc : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
  rcases hc with hc | hc | hc | hc <;> rw [h8, hc] <;> decide

lemma eight_eq : (8 : 𝓞 K) = gaussI K * (1 + gaussI K) ^ 6 := by
  linear_combination (-(gaussI K ^ 5 + 6 * gaussI K ^ 4 + 14 * gaussI K ^ 3 + 14 * gaussI K ^ 2
    + gaussI K - 8)) * gaussI_sq K

lemma span_eight : Ideal.span {(8 : 𝓞 K)} = (placeTwo K).asIdeal ^ 6 := by
  rw [placeTwo_asIdeal, Ideal.span_singleton_pow, eight_eq,
    Ideal.span_singleton_mul_left_unit isUnit_gaussI]

lemma valued_toCompl_two_le_six_iff (z : 𝓞 K) :
    Valued.v (toCompl K (placeTwo K) z) ≤ exp (-6 : ℤ) ↔ (8 : 𝓞 K) ∣ z := by
  rw [valued_toCompl, show (-6 : ℤ) = -((6 : ℕ) : ℤ) by norm_num, intValuation_le_pow_iff_mem,
    ← span_eight, Ideal.mem_span_singleton]

lemma exp_neg_six_lt_one : (exp (-6 : ℤ) : ℤᵐ⁰) < 1 := by
  rw [← exp_zero, exp_lt_exp]
  norm_num

/-! ## Approximation at the place above 2 -/

/-- `α` approximates the local unit of `x` at the place above 2, modulo 8. -/
def IsClose8 (x : (𝔸)ˣ) (α : 𝓞 K) : Prop :=
  Valued.v (unitAt K (placeTwo K) x - toCompl K (placeTwo K) α) ≤ exp (-6 : ℤ)

theorem exists_isClose8 (x : (𝔸)ˣ) : ∃ α : 𝓞 K, IsClose8 x α := by
  obtain ⟨a, ha⟩ := exists_adicValued_sub_lt_of_adicCompletionInteger K (placeTwo K)
    ⟨unitAt K (placeTwo K) x,
      (mem_adicCompletionIntegers (𝓞 K) K _).2 (valued_unitAt K (placeTwo K) x).le⟩
    (Units.mk0 (exp (-6 : ℤ)) exp_ne_zero)
  refine ⟨a, ?_⟩
  have h1 : Valued.v (toCompl K (placeTwo K) a - unitAt K (placeTwo K) x) < exp (-6 : ℤ) := ha
  unfold IsClose8
  rw [Valuation.map_sub_swap]
  exact h1.le

lemma IsClose8.notMem {x : (𝔸)ˣ} {α : 𝓞 K} (h : IsClose8 x α) : α ∉ (placeTwo K).asIdeal := by
  have h1 := Valuation.map_add_eq_of_lt_left (v := Valued.v) (x := unitAt K (placeTwo K) x)
    (y := toCompl K (placeTwo K) α - unitAt K (placeTwo K) x) (by
      rw [valued_unitAt, Valuation.map_sub_swap]
      exact lt_of_le_of_lt h exp_neg_six_lt_one)
  rw [add_sub_cancel, valued_unitAt, valued_toCompl, intValuation_eq_one_iff] at h1
  exact h1

lemma IsClose8.not_dvd_nrm {x : (𝔸)ˣ} {α : 𝓞 K} (h : IsClose8 x α) : ¬ (2 : ℤ) ∣ nrm K α := by
  have := not_dvd_nrm_of_forall_notMem (K := K) Nat.prime_two (z := α) (fun v hv => by
    have h2 : (2 : 𝓞 K) ∈ v.asIdeal := by simpa using hv
    rw [eq_placeTwo_of_two_mem h2]
    exact h.notMem)
  simpa using this

lemma IsClose8.mul {x y : (𝔸)ˣ} {α β : 𝓞 K} (h : IsClose8 x α) (h' : IsClose8 y β) :
    IsClose8 (x * y) (α * β) := by
  unfold IsClose8 at h h' ⊢
  have e : unitAt K (placeTwo K) (x * y) - toCompl K (placeTwo K) (α * β) =
      unitAt K (placeTwo K) x * (unitAt K (placeTwo K) y - toCompl K (placeTwo K) β) +
        toCompl K (placeTwo K) β * (unitAt K (placeTwo K) x - toCompl K (placeTwo K) α) := by
    rw [unitAt_mul, map_mul]
    ring
  rw [e]
  refine Valuation.map_add_le _ ?_ ?_
  · rw [map_mul, valued_unitAt, one_mul]
    exact h'
  · rw [map_mul]
    exact le_trans (mul_le_of_le_one_left' (valued_toCompl_le_one _ β)) h

lemma isClose8_one : IsClose8 (1 : (𝔸)ˣ) (1 : 𝓞 K) := by
  unfold IsClose8
  rw [unitAt_one, map_one, sub_self, map_zero]
  exact zero_le

lemma IsClose8.dvd_sub {x : (𝔸)ˣ} {α β : 𝓞 K} (h : IsClose8 x α) (h' : IsClose8 x β) :
    ((8 : ℤ) : 𝓞 K) ∣ α - β := by
  have : Valued.v (toCompl K (placeTwo K) (α - β)) ≤ exp (-6 : ℤ) := by
    rw [map_sub, show toCompl K (placeTwo K) α - toCompl K (placeTwo K) β =
      (unitAt K (placeTwo K) x - toCompl K (placeTwo K) β) +
        -(unitAt K (placeTwo K) x - toCompl K (placeTwo K) α) by ring]
    refine Valuation.map_add_le _ h' ?_
    rw [Valuation.map_neg]
    exact h
  have h8 := (valued_toCompl_two_le_six_iff _).1 this
  simpa using h8

/-! ## The character -/

variable (K) in
/-- `χ₈(nrm α)` for an approximant `α` modulo 8 at the place above 2. -/
def tw8 (x : (𝔸)ˣ) : ℤ := chi8 K (Classical.choose (exists_isClose8 x))

theorem tw8_eq {x : (𝔸)ˣ} {α : 𝓞 K} (h : IsClose8 x α) : tw8 K x = chi8 K α :=
  chi8_congr ((Classical.choose_spec (exists_isClose8 x)).dvd_sub h)

theorem tw8_mul (x y : (𝔸)ˣ) : tw8 K (x * y) = tw8 K x * tw8 K y := by
  have hx := Classical.choose_spec (exists_isClose8 (K := K) x)
  have hy := Classical.choose_spec (exists_isClose8 (K := K) y)
  rw [tw8_eq (hx.mul hy), chi8_mul, ← tw8_eq hx, ← tw8_eq hy]

theorem tw8_one : tw8 K (1 : (𝔸)ˣ) = 1 := by
  rw [tw8_eq (isClose8_one (K := K)), chi8_one]

theorem tw8_mul_self (x : (𝔸)ˣ) : tw8 K x * tw8 K x = 1 :=
  chi8_sq_of_odd (Classical.choose_spec (exists_isClose8 (K := K) x)).not_dvd_nrm

theorem tw8_eq_one_or (x : (𝔸)ˣ) : tw8 K x = 1 ∨ tw8 K x = -1 := by
  have h := tw8_mul_self (K := K) x
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.1 h with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact Or.inl h1
  · exact Or.inr h1

variable (K) in
/-- The `ℤˣ`-valued character. -/
def tw8Unit : (𝔸)ˣ →* ℤˣ where
  toFun x := Units.mkOfMulEqOne (tw8 K x) (tw8 K x) (tw8_mul_self x)
  map_one' := Units.ext tw8_one
  map_mul' x y := Units.ext (tw8_mul x y)

variable (K) in
/-- **The quadratic character at 2**, with values in `ℂˣ`. -/
def tw8C : (𝔸)ˣ →* ℂˣ :=
  (Units.map ((Int.castRingHom ℂ : ℤ →+* ℂ) : ℤ →* ℂ)).comp (tw8Unit K)

theorem tw8C_val (x : (𝔸)ˣ) : ((tw8C K x : ℂˣ) : ℂ) = ((tw8 K x : ℤ) : ℂ) := rfl

theorem norm_tw8C (x : (𝔸)ˣ) : ‖((tw8C K x : ℂˣ) : ℂ)‖ = 1 := by
  rw [tw8C_val]
  rcases tw8_eq_one_or (K := K) x with h | h <;> rw [h] <;> simp

theorem tw8C_eq_one_of_isClose8_one {x : (𝔸)ˣ} (h : IsClose8 x (1 : 𝓞 K)) : tw8C K x = 1 :=
  Units.ext (by rw [tw8C_val, tw8_eq h, chi8_one, Int.cast_one, Units.val_one])

/-- **`tw8C` is trivial on principal idèles.** -/
theorem tw8C_principal (a : Kˣ) : tw8C K (Units.map (algebraMap K 𝔸 : K →* 𝔸) a) = 1 := by
  obtain ⟨u, hu⟩ := exists_unit_mul_ρ_principal a
  have hclose : IsClose8 (Units.map (algebraMap K 𝔸 : K →* 𝔸) a) (u : 𝓞 K) := by
    have hρ0 : ρ K (Units.map (algebraMap K 𝔸 : K →* 𝔸) a) ≠ 0 := ρ_ne_zero _
    have h2 : unitAt K (placeTwo K) (Units.map (algebraMap K 𝔸 : K →* 𝔸) a) =
        toCompl K (placeTwo K) u := by
      unfold unitAt toCompl
      rw [Units.coe_map, MonoidHom.coe_coe, algebraMap_adeleRing_snd]
      conv_lhs => rw [hu]
      rw [map_mul, RingHom.comp_apply, mul_inv_cancel_right₀ ((_root_.map_ne_zero _).2 hρ0)]
    unfold IsClose8
    rw [h2, sub_self, map_zero]
    exact zero_le
  refine Units.ext ?_
  rw [tw8C_val, tw8_eq hclose, chi8_unit, Int.cast_one, Units.val_one]

/-! ## Values on idèles concentrated at one place -/

/-- A local unit away from 2 maps to 1. -/
theorem tw8C_locIdele_unit {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ placeTwo K)
    (t : (w.adicCompletion K)ˣ) (ht : Valued.v (t : w.adicCompletion K) = 1) :
    tw8C K (locIdele K w t) = 1 := by
  refine tw8C_eq_one_of_isClose8_one ?_
  unfold IsClose8
  rw [unitAt_locIdele_of_ne (Ne.symm hw), ρ_localUnit_unit w t ht, map_one, inv_one, map_one,
    sub_self, map_zero]
  exact zero_le

/-- On the local unit `i` at the place above 2 it equals 1. -/
theorem tw8C_locIdele_two_gaussI :
    tw8C K (locIdele K (placeTwo K)
      (Units.map ((toCompl K (placeTwo K) : 𝓞 K →+* _) : 𝓞 K →* _) (gaussIUnit K))) = 1 := by
  set t : ((placeTwo K).adicCompletion K)ˣ :=
    Units.map ((toCompl K (placeTwo K) : 𝓞 K →+* _) : 𝓞 K →* _) (gaussIUnit K) with ht
  have htv : (t : (placeTwo K).adicCompletion K) = toCompl K (placeTwo K) (gaussIUnit K) := rfl
  have ht1 : Valued.v (t : (placeTwo K).adicCompletion K) = 1 := by
    rw [htv, valued_toCompl_unit]
  have hclose : IsClose8 (locIdele K (placeTwo K) t) ((gaussIUnit K : (𝓞 K)ˣ) : 𝓞 K) := by
    unfold IsClose8
    rw [unitAt_locIdele_self, ρ_localUnit_unit _ t ht1, map_one, inv_one, mul_one, htv, sub_self,
      map_zero]
    exact zero_le
  refine Units.ext ?_
  rw [tw8C_val, tw8_eq hclose, chi8_unit, Int.cast_one, Units.val_one]

/-- On the uniformizer of a place away from 2 it equals `χ₈(nrm π_w)`. -/
theorem tw8_locIdele_uniformizer {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ placeTwo K)
    (t : (w.adicCompletion K)ˣ) (ht : Valued.v (t : w.adicCompletion K) = exp (-1 : ℤ)) :
    tw8 K (locIdele K w t) = chi8 K (gen K w) := by
  have hρ := ρ_localUnit_uniformizer w t ht
  obtain ⟨α, hα⟩ := exists_isClose8 (K := K) (locIdele K w t)
  have hπ1 : Valued.v (toCompl K (placeTwo K) (gen K w)) = 1 := by
    show Valued.v (algebraMap K ((placeTwo K).adicCompletion K) (genK K w)) = 1
    rw [valued_algebraMap, valuation_genK_of_ne hw]
  have hπ0 : toCompl K (placeTwo K) (gen K w) ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hπ1
    exact zero_ne_one hπ1
  have hu : unitAt K (placeTwo K) (locIdele K w t) = (toCompl K (placeTwo K) (gen K w))⁻¹ := by
    rw [unitAt_locIdele_of_ne (Ne.symm hw), hρ]
    rfl
  have hc : IsClose8 (1 : (𝔸)ˣ) (α * gen K w) := by
    unfold IsClose8 at hα ⊢
    rw [hu] at hα
    have e : (1 : (placeTwo K).adicCompletion K) -
        toCompl K (placeTwo K) α * toCompl K (placeTwo K) (gen K w) =
        toCompl K (placeTwo K) (gen K w) *
          ((toCompl K (placeTwo K) (gen K w))⁻¹ - toCompl K (placeTwo K) α) := by
      rw [mul_sub, mul_inv_cancel₀ hπ0]
      ring
    rw [unitAt_one, map_mul, e, map_mul, hπ1, one_mul]
    exact hα
  have hdvd := (isClose8_one (K := K)).dvd_sub hc
  have h1 := chi8_congr hdvd
  rw [chi8_one, chi8_mul] at h1
  rw [tw8_eq hα]
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.1 h1.symm with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> rw [h2, h3]

/-! ## Continuity -/

lemma toCompl_eight_ne_zero : toCompl K (placeTwo K) (8 : 𝓞 K) ≠ 0 := by
  intro h
  have hv := valued_toCompl (placeTwo K) (8 : 𝓞 K)
  rw [h, map_zero] at hv
  have h8 : (8 : 𝓞 K) ≠ 0 := by
    have : (8 : 𝓞 K) = ((8 : ℕ) : 𝓞 K) := by norm_num
    rw [this]
    exact Nat.cast_ne_zero.2 (by norm_num)
  exact (placeTwo K).intValuation_ne_zero _ h8 hv.symm

variable (K) in
/-- An open neighbourhood of 1 on which `tw8C` equals 1. -/
def tw8Nhd : Set (𝔸)ˣ :=
  {x | (x : 𝔸).2 ∈ integralFiniteAdeles (𝓞 K) K ∧
    ((x⁻¹ : (𝔸)ˣ) : 𝔸).2 ∈ integralFiniteAdeles (𝓞 K) K ∧
    Valued.v ((x : 𝔸).2 (placeTwo K) - 1) ≤ Valued.v (toCompl K (placeTwo K) (8 : 𝓞 K))}

theorem isOpen_tw8Nhd : IsOpen (tw8Nhd K) := by
  refine ((isOpen_integralFiniteAdeles (𝓞 K) K).preimage
    ((continuous_adeleFin (𝓞 K) K).comp Units.continuous_val)).inter
    (((isOpen_integralFiniteAdeles (𝓞 K) K).preimage
      ((continuous_adeleFin (𝓞 K) K).comp Units.continuous_coe_inv)).inter ?_)
  have hopen : IsOpen {y : (placeTwo K).adicCompletion K |
      Valued.v (y - 1) ≤ Valued.v (toCompl K (placeTwo K) (8 : 𝓞 K))} :=
    (isOpen_setOf_valued_le (placeTwo K) _ toCompl_eight_ne_zero).preimage
      (continuous_id.sub continuous_const)
  exact hopen.preimage (((continuous_finAdeleEval (𝓞 K) K (placeTwo K)).comp
    (continuous_adeleFin (𝓞 K) K)).comp Units.continuous_val)

theorem one_mem_tw8Nhd : (1 : (𝔸)ˣ) ∈ tw8Nhd K := by
  refine ⟨fun v => one_mem _, ?_, ?_⟩
  · rw [inv_one]
    exact fun v => one_mem _
  · rw [show ((1 : (𝔸)ˣ) : 𝔸).2 (placeTwo K) = 1 from rfl, sub_self, map_zero]
    exact zero_le

theorem tw8C_eq_one_of_mem_tw8Nhd {x : (𝔸)ˣ} (hx : x ∈ tw8Nhd K) : tw8C K x = 1 := by
  obtain ⟨h1, h2, h3⟩ := hx
  have hord : ∀ v : HeightOneSpectrum (𝓞 K), ordAt v x = 0 := fun v =>
    ordAt_eq_zero_of_le_one ((mem_adicCompletionIntegers (𝓞 K) K v).mp (h1 v))
      ((mem_adicCompletionIntegers (𝓞 K) K v).mp (h2 v))
  have hρ : ρ K x = 1 := by
    unfold ρ
    exact finprod_eq_one_of_forall_eq_one fun v => by rw [hord v, zpow_zero]
  refine tw8C_eq_one_of_isClose8_one ?_
  have hu : unitAt K (placeTwo K) x = (x : 𝔸).2 (placeTwo K) := by
    unfold unitAt
    rw [hρ, map_one, inv_one, mul_one]
  unfold IsClose8
  rw [hu, map_one]
  exact le_trans h3 ((valued_toCompl_two_le_six_iff _).2 dvd_rfl)

theorem continuous_tw8C : Continuous (tw8C K) := by
  refine continuous_of_continuousAt_one (tw8C K) ?_
  have hc : ContinuousAt (fun _ : (𝔸)ˣ => (1 : ℂˣ)) 1 := continuousAt_const
  refine hc.congr ?_
  exact Filter.eventually_of_mem (isOpen_tw8Nhd.mem_nhds one_mem_tw8Nhd) fun x hx =>
    (tw8C_eq_one_of_mem_tw8Nhd hx).symm

end CMPoints
