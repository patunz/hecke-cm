import HeckeCM.RootTwist

/-!
# The local Gauss integral as a finite sum, for arbitrary conductor

Version of `gauss_integral_eq_sum` for a character `ξ` trivial on `1 + 𝔭ⁿ`,
`n ≥ 1`, at a place of arbitrary level. The representatives `r : ι → 𝓞 K`
cover the units modulo `𝔭ⁿ`; the local units are the disjoint union of the balls
`ballN v n (r i)`, on which the integrand is constant.
-/

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero MeasureTheory
open NumberField.AdelicLevel AutomorphicForm NumberField.TateGlobal
open NumberField.StandardAddChar LanglandsTunnell.TateLocal
open scoped Classical

namespace CMPoints

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

attribute [local instance] localBorel borelSpace_localBorel

variable (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)

/-- The closed ball of radius `exp (−n)` around `α`. -/
def ballN (α : 𝓞 K) : Set (v.adicCompletion K) :=
  {u | Valued.v (u - toCompl K v α) ≤ exp (-(n : ℤ))}

lemma measurableSet_ballN (α : 𝓞 K) : MeasurableSet (ballN v n α) :=
  ((NumberField.AdelicTrace.isClosed_setOf_valued_le (F := K) v (exp (-(n : ℤ)))).preimage
    (continuous_id.sub continuous_const)).measurableSet

lemma exp_neg_natCast_lt_one (hn : 1 ≤ n) : (exp (-(n : ℤ)) : ℤᵐ⁰) < 1 := by
  rw [← exp_zero, exp_lt_exp]
  omega

lemma mem_ballN_valued_eq_one (hn : 1 ≤ n) {α : 𝓞 K} (hα : α ∉ v.asIdeal)
    {u : v.adicCompletion K} (hu : u ∈ ballN v n α) : Valued.v u = 1 := by
  have h1 := (valued_toCompl_eq_one_iff v α).2 hα
  have hu' : Valued.v (u - toCompl K v α) ≤ exp (-(n : ℤ)) := hu
  have := Valuation.map_add_eq_of_lt_left (v := Valued.v) (x := toCompl K v α)
    (y := u - toCompl K v α) (by rw [h1]; exact lt_of_le_of_lt hu' (exp_neg_natCast_lt_one n hn))
  rwa [add_sub_cancel, h1] at this

lemma ballN_one_eq_image (hn : 1 ≤ n) :
    ballN v n 1 = ((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) '' higherUnitsAt K v n := by
  ext u
  constructor
  · intro hu
    have h1 : Valued.v u = 1 :=
      mem_ballN_valued_eq_one v n hn (fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)) hu
    have hu' : Valued.v (u - toCompl K v 1) ≤ exp (-(n : ℤ)) := hu
    rw [map_one] at hu'
    have hne : u ≠ 0 := fun h => by
      rw [h, map_zero] at h1
      exact zero_ne_one h1
    exact ⟨Units.mk0 u hne, ⟨h1, Or.inr hu'⟩, rfl⟩
  · rintro ⟨t, ⟨-, h3⟩, rfl⟩
    rcases h3 with h | h
    · omega
    · show Valued.v ((t : v.adicCompletion K) - toCompl K v 1) ≤ exp (-(n : ℤ))
      rw [map_one]
      exact h

lemma real_ballN (hn : 1 ≤ n) (α : 𝓞 K) :
    (selfDualHaarAt K v).real (ballN v n α) =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-(n : ℤ)) *
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-(addCharLevel (psiLocal K v) : ℝ) / 2) := by
  have hpre : (fun h : v.adicCompletion K => (toCompl K v α - 1) + h) ⁻¹' ballN v n α =
      ballN v n 1 := by
    ext u
    show Valued.v (toCompl K v α - 1 + u - toCompl K v α) ≤ _ ↔ Valued.v (u - toCompl K v 1) ≤ _
    rw [map_one, show toCompl K v α - 1 + u - toCompl K v α = u - 1 by ring]
  have hm : (selfDualHaarAt K v) (ballN v n α) = (selfDualHaarAt K v) (ballN v n 1) := by
    rw [← hpre, measure_preimage_add]
  have h := selfDualHaarAt_real_image_higherUnitsAt K v n hn
  rw [← ballN_one_eq_image v n hn] at h
  unfold Measure.real
  rw [hm]
  exact h

variable {ι : Type} [Fintype ι] (r : ι → 𝓞 K)

theorem setOf_valued_eq_one_eq_iUnion_N (hn : 1 ≤ n) (hr : ∀ i, r i ∉ v.asIdeal)
    (hcover : ∀ α : 𝓞 K, α ∉ v.asIdeal →
      ∃ i, Valued.v (toCompl K v (α - r i)) ≤ exp (-(n : ℤ))) :
    {u : v.adicCompletion K | Valued.v u = 1} = ⋃ i, ballN v n (r i) := by
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro hu
    have hmem : u ∈ v.adicCompletionIntegers K := (mem_adicCompletionIntegers (𝓞 K) K v).2 hu.le
    obtain ⟨a, ha⟩ := exists_adicValued_sub_lt_of_adicCompletionInteger K v ⟨u, hmem⟩
      (Units.mk0 (exp (-(n : ℤ))) exp_ne_zero)
    have ha' : Valued.v (toCompl K v a - u) < exp (-(n : ℤ)) := ha
    have hav : a ∉ v.asIdeal := by
      rw [← valued_toCompl_eq_one_iff]
      have := Valuation.map_add_eq_of_lt_left (v := Valued.v) (x := u) (y := toCompl K v a - u)
        (by rw [hu]; exact lt_trans ha' (exp_neg_natCast_lt_one n hn))
      rwa [add_sub_cancel, hu] at this
    obtain ⟨i, hi⟩ := hcover a hav
    refine ⟨i, ?_⟩
    show Valued.v (u - toCompl K v (r i)) ≤ exp (-(n : ℤ))
    have e : u - toCompl K v (r i) = (u - toCompl K v a) + toCompl K v (a - r i) := by
      rw [map_sub]
      ring
    rw [e]
    refine Valuation.map_add_le _ ?_ hi
    rw [Valuation.map_sub_swap]
    exact ha'.le
  · rintro ⟨i, hi⟩
    exact mem_ballN_valued_eq_one v n hn (hr i) hi

lemma disjoint_ballN
    (hinj : ∀ i j, Valued.v (toCompl K v (r i - r j)) ≤ exp (-(n : ℤ)) → i = j) :
    Pairwise (Function.onFun Disjoint fun i : ι => ballN v n (r i)) := by
  intro i j hij
  refine Set.disjoint_left.2 fun u hi hj => hij (hinj _ _ ?_)
  rw [map_sub, show toCompl K v (r i) - toCompl K v (r j) =
    (u - toCompl K v (r j)) + -(u - toCompl K v (r i)) by ring]
  refine Valuation.map_add_le _ hj ?_
  rw [Valuation.map_neg]
  exact hi

lemma integrand_ballN (hn : 1 ≤ n) (ξ : (v.adicCompletion K)ˣ →* ℂˣ)
    (hξ : ∀ u ∈ higherUnitsAt K v n, ξ u = 1) {l : ℤ}
    (hψ : ∀ x : v.adicCompletion K, Valued.v x ≤ exp l → psiLocal K v x = 1)
    (z : v.adicCompletion K) (hz : Valued.v z ≤ exp (l + n)) {α : 𝓞 K} (hα : α ∉ v.asIdeal)
    {u : v.adicCompletion K} (hu : u ∈ ballN v n α) :
    psiLocal K v (z * u) * charExt ξ⁻¹ u =
      psiLocal K v (z * toCompl K v α) * charExt ξ⁻¹ (toCompl K v α) := by
  have hρ1 := (valued_toCompl_eq_one_iff v α).2 hα
  have hu1 := mem_ballN_valued_eq_one v n hn hα hu
  have hρ : toCompl K v α ≠ 0 := fun h => by
    rw [h, map_zero] at hρ1
    exact zero_ne_one hρ1
  have hne : u ≠ 0 := fun h => by
    rw [h, map_zero] at hu1
    exact zero_ne_one hu1
  have hu' : Valued.v (u - toCompl K v α) ≤ exp (-(n : ℤ)) := hu
  have h1 : psiLocal K v (z * (u - toCompl K v α)) = 1 := by
    refine hψ _ ?_
    rw [map_mul]
    calc Valued.v z * Valued.v (u - toCompl K v α)
        ≤ exp (l + n) * exp (-(n : ℤ)) := mul_le_mul' hz hu'
      _ = exp l := by rw [← exp_add]; congr 1; ring
  have hψ' : psiLocal K v (z * u) = psiLocal K v (z * toCompl K v α) := by
    rw [show z * u = z * toCompl K v α + z * (u - toCompl K v α) by ring, AddChar.map_add_eq_mul,
      h1, mul_one]
  have hw : (Units.mk0 (toCompl K v α) hρ)⁻¹ * Units.mk0 u hne ∈ higherUnitsAt K v n := by
    refine ⟨?_, Or.inr ?_⟩
    · rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0, map_mul,
        map_inv₀, hρ1, hu1, inv_one, one_mul]
    · have e : (((Units.mk0 (toCompl K v α) hρ)⁻¹ * Units.mk0 u hne : (v.adicCompletion K)ˣ) :
          v.adicCompletion K) - 1 = (toCompl K v α)⁻¹ * (u - toCompl K v α) := by
        rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0]
        field_simp
      rw [e, map_mul, map_inv₀, hρ1, inv_one, one_mul]
      exact hu'
  have hξu : ξ (Units.mk0 u hne) = ξ (Units.mk0 (toCompl K v α) hρ) := by
    have e : Units.mk0 u hne = Units.mk0 (toCompl K v α) hρ *
        ((Units.mk0 (toCompl K v α) hρ)⁻¹ * Units.mk0 u hne) := by
      rw [mul_inv_cancel_left]
    rw [e, map_mul, hξ _ hw, mul_one]
  rw [hψ', charExt_of_ne_zero _ hne, charExt_of_ne_zero _ hρ, MonoidHom.inv_apply,
    MonoidHom.inv_apply, hξu]

/-- **The local Gauss integral as a finite sum.** -/
theorem gauss_integral_eq_sum_N (hn : 1 ≤ n) (hr : ∀ i, r i ∉ v.asIdeal)
    (hcover : ∀ α : 𝓞 K, α ∉ v.asIdeal →
      ∃ i, Valued.v (toCompl K v (α - r i)) ≤ exp (-(n : ℤ)))
    (hinj : ∀ i j, Valued.v (toCompl K v (r i - r j)) ≤ exp (-(n : ℤ)) → i = j)
    (ξ : (v.adicCompletion K)ˣ →* ℂˣ) (hξ : ∀ u ∈ higherUnitsAt K v n, ξ u = 1) {l : ℤ}
    (hψ : ∀ x : v.adicCompletion K, Valued.v x ≤ exp l → psiLocal K v x = 1)
    (z : v.adicCompletion K) (hz : Valued.v z ≤ exp (l + n)) :
    ∫ u in {u : v.adicCompletion K | Valued.v u = 1},
        psiLocal K v (z * u) * charExt ξ⁻¹ u ∂(selfDualHaarAt K v) =
      (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(n : ℤ)) *
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-(addCharLevel (psiLocal K v) : ℝ) / 2) : ℝ) : ℂ) *
      ∑ i, psiLocal K v (z * toCompl K v (r i)) * charExt ξ⁻¹ (toCompl K v (r i)) := by
  have hN0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  have hfin : ∀ α : 𝓞 K, (selfDualHaarAt K v) (ballN v n α) ≠ ⊤ := fun α h => by
    have := real_ballN v n hn α
    unfold Measure.real at this
    rw [h, ENNReal.toReal_top] at this
    have hpos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) ^ (-(n : ℤ)) *
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-(addCharLevel (psiLocal K v) : ℝ) / 2) :=
      mul_pos (zpow_pos hN0 _) (Real.rpow_pos_of_pos hN0 _)
    rw [← this] at hpos
    exact lt_irrefl _ hpos
  have hconst : ∀ i : ι, Set.EqOn
      (fun _ : v.adicCompletion K => psiLocal K v (z * toCompl K v (r i)) *
        charExt ξ⁻¹ (toCompl K v (r i)))
      (fun u : v.adicCompletion K => psiLocal K v (z * u) * charExt ξ⁻¹ u) (ballN v n (r i)) :=
    fun i u hu => (integrand_ballN v n hn ξ hξ hψ z hz (hr i) hu).symm
  have hmeas : ∀ i : ι, MeasurableSet (ballN v n (r i)) := fun i => measurableSet_ballN v n _
  rw [setOf_valued_eq_one_eq_iUnion_N v n r hn hr hcover,
    integral_iUnion_fintype (s := fun i : ι => ballN v n (r i)) hmeas (disjoint_ballN v n r hinj)
      (fun i => (integrableOn_const (hfin _)).congr_fun (hconst i) (hmeas i)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← setIntegral_congr_fun (hmeas i) (hconst i), setIntegral_const, real_ballN v n hn,
    Complex.real_smul]

end CMPoints
