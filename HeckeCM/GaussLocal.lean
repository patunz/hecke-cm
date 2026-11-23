import HeckeCM.RootGlobal

/-!
# The local Gauss integral as a sum over residue classes

Let `v` be a place of `K = ℚ(i)` at which the standard additive character has level
0, and let `r : ι → 𝓞 K` be a system of representatives of `𝓞 K / v`. For a
character `ξ` of `K_v^×` trivial on `1 + 𝔭_v` and for `z` of valuation at most
`exp 1`,

`∫_{|u| = 1} ψ(z u) ξ⁻¹(u) du = N(v)⁻¹ · Σ_{r i ∉ v} ψ(z · r i) ξ⁻¹(r i)`.

The local units are the disjoint union of the balls `ball v (r i)`, of measure
`N(v)⁻¹`, on which the integrand is constant.
-/

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero MeasureTheory
open NumberField.AdelicLevel AutomorphicForm NumberField.TateGlobal
open NumberField.StandardAddChar LanglandsTunnell.TateLocal
open scoped Classical

namespace CMPoints

lemma lt_one_iff_le_exp (x : ℤᵐ⁰) : x < 1 ↔ x ≤ exp (-1 : ℤ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · obtain ⟨n, rfl⟩ : ∃ n : ℤ, x = exp n := ⟨log x, (exp_log hx).symm⟩
    rw [← exp_zero, exp_lt_exp, exp_le_exp]
    omega

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

attribute [local instance] localBorel borelSpace_localBorel

variable (v : HeightOneSpectrum (𝓞 K))

lemma valued_toCompl_lt_one_iff (α : 𝓞 K) : Valued.v (toCompl K v α) < 1 ↔ α ∈ v.asIdeal := by
  rw [valued_toCompl, intValuation_lt_one_iff_mem]

lemma valued_toCompl_eq_one_iff (α : 𝓞 K) : Valued.v (toCompl K v α) = 1 ↔ α ∉ v.asIdeal := by
  rw [valued_toCompl, intValuation_eq_one_iff]

instance isAddLeftInvariant_selfDualHaarAt : (selfDualHaarAt K v).IsAddLeftInvariant := by
  unfold selfDualHaarAt
  infer_instance

/-- The open ball of radius 1 around `α`. -/
def ball (α : 𝓞 K) : Set (v.adicCompletion K) := {u | Valued.v (u - toCompl K v α) < 1}

lemma measurableSet_ball (α : 𝓞 K) : MeasurableSet (ball v α) := by
  have h : ball v α = (fun u => u - toCompl K v α) ⁻¹'
      {y : v.adicCompletion K | Valued.v y ≤ exp (-1 : ℤ)} := by
    ext u
    exact lt_one_iff_le_exp _
  rw [h]
  exact ((NumberField.AdelicTrace.isClosed_setOf_valued_le (F := K) v (exp (-1 : ℤ))).preimage
    (continuous_id.sub continuous_const)).measurableSet

lemma ball_one_eq_image :
    ball v 1 = ((↑) : (v.adicCompletion K)ˣ → v.adicCompletion K) '' higherUnitsAt K v 1 := by
  ext u
  constructor
  · intro hu
    have hu' : Valued.v (u - toCompl K v 1) < 1 := hu
    rw [map_one] at hu'
    have h1 : Valued.v u = 1 := by
      have := Valuation.map_add_eq_of_lt_left (v := Valued.v) (x := (1 : v.adicCompletion K))
        (y := u - 1) (by rw [map_one]; exact hu')
      rwa [add_sub_cancel, map_one] at this
    have hne : u ≠ 0 := fun h => by
      rw [h, map_zero] at h1
      exact zero_ne_one h1
    exact ⟨Units.mk0 u hne, ⟨h1, Or.inr (by exact_mod_cast (lt_one_iff_le_exp _).1 hu')⟩, rfl⟩
  · rintro ⟨t, ⟨-, h3⟩, rfl⟩
    rcases h3 with h | h
    · exact absurd h (by norm_num)
    · show Valued.v ((t : v.adicCompletion K) - toCompl K v 1) < 1
      rw [map_one]
      exact (lt_one_iff_le_exp _).2 (by exact_mod_cast h)

lemma real_ball (hlev : addCharLevel (psiLocal K v) = 0) (α : 𝓞 K) :
    (selfDualHaarAt K v).real (ball v α) = ((Ideal.absNorm v.asIdeal : ℝ))⁻¹ := by
  have hpre : (fun h : v.adicCompletion K => (toCompl K v α - 1) + h) ⁻¹' ball v α = ball v 1 := by
    ext u
    show Valued.v (toCompl K v α - 1 + u - toCompl K v α) < 1 ↔ Valued.v (u - toCompl K v 1) < 1
    rw [map_one, show toCompl K v α - 1 + u - toCompl K v α = u - 1 by ring]
  have hm : (selfDualHaarAt K v) (ball v α) = (selfDualHaarAt K v) (ball v 1) := by
    rw [← hpre, measure_preimage_add]
  have h := selfDualHaarAt_real_image_higherUnitsAt K v 1 le_rfl
  rw [← ball_one_eq_image, hlev] at h
  unfold Measure.real
  rw [hm]
  unfold Measure.real at h
  rw [h]
  simp

variable {ι : Type} [Fintype ι] (r : ι → 𝓞 K)

lemma mem_ball_valued_eq_one {α : 𝓞 K} (hα : α ∉ v.asIdeal) {u : v.adicCompletion K}
    (hu : u ∈ ball v α) : Valued.v u = 1 := by
  have h1 := (valued_toCompl_eq_one_iff v α).2 hα
  have := Valuation.map_add_eq_of_lt_left (v := Valued.v) (x := toCompl K v α)
    (y := u - toCompl K v α) (by rw [h1]; exact hu)
  rwa [add_sub_cancel, h1] at this

theorem setOf_valued_eq_one_eq_iUnion (hcover : ∀ α : 𝓞 K, ∃ i, α - r i ∈ v.asIdeal) :
    {u : v.adicCompletion K | Valued.v u = 1} =
      ⋃ i : {i // r i ∉ v.asIdeal}, ball v (r i) := by
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro hu
    have hmem : u ∈ v.adicCompletionIntegers K := (mem_adicCompletionIntegers (𝓞 K) K v).2 hu.le
    obtain ⟨a, ha⟩ := exists_adicValued_sub_lt_of_adicCompletionInteger K v ⟨u, hmem⟩ 1
    have ha' : Valued.v (toCompl K v a - u) < 1 := ha
    obtain ⟨i, hi⟩ := hcover a
    have hball : Valued.v (u - toCompl K v (r i)) < 1 := by
      have e : u - toCompl K v (r i) = (u - toCompl K v a) + toCompl K v (a - r i) := by
        rw [map_sub]
        ring
      rw [e]
      refine Valuation.map_add_lt _ ?_ ((valued_toCompl_lt_one_iff v _).2 hi)
      rw [Valuation.map_sub_swap]
      exact ha'
    refine ⟨⟨i, fun hri => ?_⟩, hball⟩
    have e : u = (u - toCompl K v (r i)) + toCompl K v (r i) := by ring
    have hlt : Valued.v u < 1 := by
      rw [e]
      exact Valuation.map_add_lt _ hball ((valued_toCompl_lt_one_iff v _).2 hri)
    rw [hu] at hlt
    exact lt_irrefl _ hlt
  · rintro ⟨i, hi⟩
    exact mem_ball_valued_eq_one v i.2 hi

lemma disjoint_ball (hinj : ∀ i j, r i - r j ∈ v.asIdeal → i = j) :
    Pairwise (Function.onFun Disjoint fun i : {i // r i ∉ v.asIdeal} => ball v (r i)) := by
  intro i j hij
  refine Set.disjoint_left.2 fun u hi hj => hij (Subtype.ext (hinj _ _ ?_))
  rw [← valued_toCompl_lt_one_iff, map_sub, show toCompl K v (r i) - toCompl K v (r j) =
    (u - toCompl K v (r j)) + -(u - toCompl K v (r i)) by ring]
  refine Valuation.map_add_lt _ hj ?_
  rw [Valuation.map_neg]
  exact hi

lemma integrand_ball (ξ : (v.adicCompletion K)ˣ →* ℂˣ)
    (hξ : ∀ u ∈ higherUnitsAt K v 1, ξ u = 1) (z : v.adicCompletion K)
    (hz : Valued.v z ≤ exp (1 : ℤ)) {α : 𝓞 K} (hα : α ∉ v.asIdeal) {u : v.adicCompletion K}
    (hu : u ∈ ball v α) :
    psiLocal K v (z * u) * charExt ξ⁻¹ u =
      psiLocal K v (z * toCompl K v α) * charExt ξ⁻¹ (toCompl K v α) := by
  have hρ1 := (valued_toCompl_eq_one_iff v α).2 hα
  have hu1 := mem_ball_valued_eq_one v hα hu
  have hρ : toCompl K v α ≠ 0 := fun h => by
    rw [h, map_zero] at hρ1
    exact zero_ne_one hρ1
  have hne : u ≠ 0 := fun h => by
    rw [h, map_zero] at hu1
    exact zero_ne_one hu1
  have hu' : Valued.v (u - toCompl K v α) < 1 := hu
  have h1 : psiLocal K v (z * (u - toCompl K v α)) = 1 := by
    refine psiLocal_eq_one_of_mem_integers K v _ ?_
    rw [mem_adicCompletionIntegers, map_mul]
    calc Valued.v z * Valued.v (u - toCompl K v α)
        ≤ exp (1 : ℤ) * exp (-1 : ℤ) := mul_le_mul' hz ((lt_one_iff_le_exp _).1 hu')
      _ = 1 := by rw [← exp_add]; norm_num
  have hψ : psiLocal K v (z * u) = psiLocal K v (z * toCompl K v α) := by
    rw [show z * u = z * toCompl K v α + z * (u - toCompl K v α) by ring, AddChar.map_add_eq_mul,
      h1, mul_one]
  have hw : (Units.mk0 (toCompl K v α) hρ)⁻¹ * Units.mk0 u hne ∈ higherUnitsAt K v 1 := by
    refine ⟨?_, Or.inr ?_⟩
    · rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0, map_mul,
        map_inv₀, hρ1, hu1, inv_one, one_mul]
    · have e : (((Units.mk0 (toCompl K v α) hρ)⁻¹ * Units.mk0 u hne : (v.adicCompletion K)ˣ) :
          v.adicCompletion K) - 1 = (toCompl K v α)⁻¹ * (u - toCompl K v α) := by
        rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0]
        field_simp
      rw [e, map_mul, map_inv₀, hρ1, inv_one, one_mul]
      exact_mod_cast (lt_one_iff_le_exp _).1 hu'
  have hξu : ξ (Units.mk0 u hne) = ξ (Units.mk0 (toCompl K v α) hρ) := by
    have e : Units.mk0 u hne = Units.mk0 (toCompl K v α) hρ *
        ((Units.mk0 (toCompl K v α) hρ)⁻¹ * Units.mk0 u hne) := by
      rw [mul_inv_cancel_left]
    rw [e, map_mul, hξ _ hw, mul_one]
  rw [hψ, charExt_of_ne_zero _ hne, charExt_of_ne_zero _ hρ, MonoidHom.inv_apply,
    MonoidHom.inv_apply, hξu]

/-- **The local Gauss integral as a sum over residue classes.** -/
theorem gauss_integral_eq_sum (hlev : addCharLevel (psiLocal K v) = 0)
    (hcover : ∀ α : 𝓞 K, ∃ i, α - r i ∈ v.asIdeal)
    (hinj : ∀ i j, r i - r j ∈ v.asIdeal → i = j)
    (ξ : (v.adicCompletion K)ˣ →* ℂˣ) (hξ : ∀ u ∈ higherUnitsAt K v 1, ξ u = 1)
    (z : v.adicCompletion K) (hz : Valued.v z ≤ exp (1 : ℤ)) :
    ∫ u in {u : v.adicCompletion K | Valued.v u = 1},
        psiLocal K v (z * u) * charExt ξ⁻¹ u ∂(selfDualHaarAt K v) =
      ((Ideal.absNorm v.asIdeal : ℂ))⁻¹ * ∑ i : {i // r i ∉ v.asIdeal},
        psiLocal K v (z * toCompl K v (r i)) * charExt ξ⁻¹ (toCompl K v (r i)) := by
  have hN0 : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
    exact_mod_cast this
  have hfin : ∀ α : 𝓞 K, (selfDualHaarAt K v) (ball v α) ≠ ⊤ := fun α h => by
    have := real_ball v hlev α
    unfold Measure.real at this
    rw [h, ENNReal.toReal_top] at this
    exact inv_ne_zero hN0 this.symm
  have hconst : ∀ i : {i // r i ∉ v.asIdeal}, Set.EqOn
      (fun _ : v.adicCompletion K => psiLocal K v (z * toCompl K v (r i)) *
        charExt ξ⁻¹ (toCompl K v (r i)))
      (fun u : v.adicCompletion K => psiLocal K v (z * u) * charExt ξ⁻¹ u) (ball v (r i)) :=
    fun i u hu => (integrand_ball v ξ hξ z hz i.2 hu).symm
  have hmeas : ∀ i : {i // r i ∉ v.asIdeal}, MeasurableSet (ball v (r i)) :=
    fun i => measurableSet_ball v _
  rw [setOf_valued_eq_one_eq_iUnion v r hcover,
    integral_iUnion_fintype (s := fun i : {i // r i ∉ v.asIdeal} => ball v (r i)) hmeas
      (disjoint_ball v r hinj)
      (fun i => (integrableOn_const (hfin _)).congr_fun (hconst i) (hmeas i)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← setIntegral_congr_fun (measurableSet_ball v _) (hconst i), setIntegral_const,
    real_ball v hlev, Complex.real_smul]
  push_cast
  ring

end CMPoints
