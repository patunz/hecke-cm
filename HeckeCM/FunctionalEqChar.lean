import HeckeCM.FunctionalEq
import HeckeCM.TwistEven

/-!
# The functional equation of the L-series of `y² = x³ − d²x`

* `ℚ(i)` has a single place at infinity, which is complex;
* our characters (`cmChar`, `cmCharTw`, `cmCharEv`) have archimedean component
  `x ↦ (x/|x|)⁻¹` and are nontrivial on the idèles of norm 1;
* the local values of the inverse character satisfy the same conditions
  (`IsGenEulerDatum.inv`), because at the split primes the two values are inverse
  to each other;
* hence `Λ(s) = Γ_ℂ(s) L(s)` is entire and `Λ(s) = ε N^{1−s} Λ(2 − s)` with
  `ε = ±1` (`functional_equation_of_datum`);
* `functional_equation_curveD`: for every `d ≠ 0`, for the Mathlib L-series of
  `y² = x³ − d²x`; in particular if the sign is `−1` the entire continuation
  vanishes at `s = 1`.

The sign is not computed: it is the root number `heckeRootNumber` of the Fermat
repository, a product of local root numbers.
-/

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open NumberField.AdelicLevel AutomorphicForm NumberField.TateGlobal
open LanglandsTunnell LanglandsTunnell.HeckeTate LanglandsTunnell.Converse
open scoped Classical

namespace CMPoints

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

local notation "𝔸" => AdeleRing (𝓞 K) K

/-! ## The places at infinity of `ℚ(i)` -/

lemma card_infinitePlace : Fintype.card (InfinitePlace K) = 1 := by
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (n := 4) K (by decide), zero_add,
    IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two (n := 4)]
  rfl

instance subsingleton_infinitePlace : Subsingleton (InfinitePlace K) :=
  Fintype.card_le_one_iff_subsingleton.1 card_infinitePlace.le

lemma not_isReal_infinitePlace (w : InfinitePlace K) : ¬ w.IsReal := by
  intro hw
  have h := IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (n := 4) K (by decide)
  have he : IsEmpty {w : InfinitePlace K // w.IsReal} := Fintype.card_eq_zero_iff.1 h
  exact he.false ⟨w, hw⟩

/-! ## The archimedean idèles -/

section Arch

variable (w : InfinitePlace K) (x : (w.Completion)ˣ)

lemma ordAt_archUnitHom (v : HeightOneSpectrum (𝓞 K)) : ordAt v (archUnitHom w x) = 0 := by
  refine ordAt_eq_zero_of_valued_eq_one ?_
  show Valued.v ((1 : FiniteAdeleRing (𝓞 K) K) v) = 1
  rw [show (1 : FiniteAdeleRing (𝓞 K) K) v = 1 from rfl, map_one]

lemma ρ_archUnitHom : ρ K (archUnitHom w x) = 1 := by
  unfold ρ
  exact finprod_eq_one_of_forall_eq_one fun v => by rw [ordAt_archUnitHom, zpow_zero]

lemma unitAt_archUnitHom (v : HeightOneSpectrum (𝓞 K)) : unitAt K v (archUnitHom w x) = 1 := by
  unfold unitAt
  rw [ρ_archUnitHom, map_one, inv_one, mul_one]
  rfl

lemma archHom_archUnitHom :
    archHom K ((archUnitHom w x : (𝔸)ˣ) : 𝔸) =
      InfinitePlace.Completion.extensionEmbedding w (x : w.Completion) := by
  obtain rfl : w = archPlace K := Subsingleton.elim _ _
  show InfinitePlace.Completion.extensionEmbedding (archPlace K)
    (Function.update (1 : InfiniteAdeleRing K) (archPlace K) (x : (archPlace K).Completion)
      (archPlace K)) = _
  rw [Function.update_self]

/-- On the archimedean idèles `cmChar` equals `(x/|x|)⁻¹`. -/
theorem cmChar_archUnitHom :
    ((cmChar K (archUnitHom w x) : ℂˣ) : ℂ) =
      (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion) /
        ((‖InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)‖ : ℝ) : ℂ))⁻¹ := by
  have hroot : rootHom K (archUnitHom w x) = 1 := by
    rw [rootHom_apply]
    have : unit2 K (archUnitHom w x) = 1 := unitAt_archUnitHom w x (placeTwo K)
    rw [this, root2_one]
  have hθ : ((thetaHom K (archUnitHom w x) : ℂˣ) : ℂ) =
      InfinitePlace.Completion.extensionEmbedding w (x : w.Completion) := by
    rw [thetaHom_val, ρ_archUnitHom, map_one, inv_one, mul_one, archHom_archUnitHom]
  rw [cmChar_apply, hroot, map_one, mul_one, Units.val_inv_eq_inv_val, unitDir_val, hθ]

variable {d : ℕ} (hodd : d % 2 = 1) (hsq : Squarefree d) (hd : d ≠ 0)

include hodd hsq in
theorem twC_archUnitHom : twC K hodd hsq hd (archUnitHom w x) = 1 := by
  refine twC_eq_one_of_isClose_one hodd hsq hd fun v _ => ?_
  rw [unitAt_archUnitHom, map_one, sub_self, map_zero]
  exact zero_lt_one

theorem tw8C_archUnitHom : tw8C K (archUnitHom w x) = 1 := by
  refine tw8C_eq_one_of_isClose8_one ?_
  unfold IsClose8
  rw [unitAt_archUnitHom, map_one, sub_self, map_zero]
  exact zero_le

end Arch

/-- The archimedean component required by Tate's theorem, starting from the
value on the archimedean idèles. -/
theorem isArchCompAt_of_apply {χ : (𝔸)ˣ →* ℂˣ}
    (h : ∀ (w : InfinitePlace K) (x : (w.Completion)ˣ), ((χ (archUnitHom w x) : ℂˣ) : ℂ) =
      (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion) /
        ((‖InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)‖ : ℝ) : ℂ))⁻¹)
    (w : InfinitePlace K) : IsArchCompAt K χ w 0 (-1) := by
  intro x
  have hnorm : ‖InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)‖ =
      ‖(x : w.Completion)‖ :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _
  show ((χ (archUnitHom w x) : ℂˣ) : ℂ) = _
  rw [h w x, hnorm, mul_zero, Complex.cpow_zero, one_mul, zpow_neg_one]

/-! ## The idèle of order 4 at the place above 2 -/

variable (K) in
/-- The idèle concentrated at the place above 2, with component `i`. -/
def x₀ : (𝔸)ˣ := locIdele K (placeTwo K)
  (Units.map ((toCompl K (placeTwo K) : 𝓞 K →+* _) : 𝓞 K →* _) (gaussIUnit K))

lemma x₀_mem_normOneIdeles : x₀ K ∈ normOneIdeles K := by
  rw [mem_normOneIdeles_iff]
  have hpow : x₀ K ^ 4 = 1 := by
    unfold x₀
    rw [← map_pow, ← map_pow, ← map_pow, unit_pow_four, map_one, map_one, map_one]
  have h4 : ideleNorm K (x₀ K) ^ 4 = 1 := by
    have : ideleNorm K (x₀ K ^ 4) = ideleNorm K (x₀ K) ^ 4 := by
      simp only [pow_succ, pow_zero, one_mul, ideleNorm_mul]
    rw [← this, hpow, ideleNorm_one K]
  exact (pow_eq_one_iff_of_nonneg (ideleNorm_pos (x₀ K)).le (by norm_num)).1 h4

/-! ## The local values of the inverse character -/

omit [IsCyclotomicExtension {4} ℚ K] in
theorem IsGenEulerDatum.inv {B : ℕ → Prop} {a : ℕ → ℤ} {c : HeightOneSpectrum (𝓞 K) → ℂ}
    (hc : IsGenEulerDatum K B a c) (hn : ∀ v, c v = 0 ∨ ‖c v‖ = 1) :
    IsGenEulerDatum K B a fun v => (c v)⁻¹ := by
  refine ⟨fun v => ?_, fun p hp hb v hv => ?_, fun p hp hb h3 => ?_, fun p hp hb h1 => ?_⟩
  · rcases hn v with h | h
    · simp [h]
    · rw [norm_inv, h, inv_one]
  · show (c v)⁻¹ = 0
    rw [hc.bad p hp hb v hv, inv_zero]
  · obtain ⟨v, hmem, hN, hcv⟩ := hc.inert p hp hb h3
    exact ⟨v, hmem, hN, by show (c v)⁻¹ = -1; rw [hcv]; norm_num⟩
  · obtain ⟨v, w, hvw, hmem, hNv, hNw, hsum, hprod⟩ := hc.split p hp hb h1
    have e1 : (c v)⁻¹ = c w := inv_eq_of_mul_eq_one_right hprod
    have e2 : (c w)⁻¹ = c v := inv_eq_of_mul_eq_one_left hprod
    refine ⟨v, w, hvw, hmem, hNv, hNw, ?_, ?_⟩
    · show (c v)⁻¹ + (c w)⁻¹ = _
      rw [e1, e2, add_comm]
      exact hsum
    · show (c v)⁻¹ * (c w)⁻¹ = 1
      rw [e1, e2, mul_comm]
      exact hprod

/-! ## The functional equation, starting from the local values -/

/-- **Functional equation** for a character whose local values are those of a
sequence of CM type. -/
theorem functional_equation_of_datum (χ : (𝔸)ˣ →* ℂˣ) (hcont : Continuous χ)
    (hu : IsUnitaryChar (𝓞 K) K χ) (hF : IsIdeleClassChar (𝓞 K) K χ) (hx : χ (x₀ K) ≠ 1)
    (harch : ∀ (w : InfinitePlace K) (x : (w.Completion)ˣ), ((χ (archUnitHom w x) : ℂˣ) : ℂ) =
      (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion) /
        ((‖InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)‖ : ℝ) : ℂ))⁻¹)
    {B : ℕ → Prop} [DecidablePred B] {a : ℕ → ℤ}
    (hdat : IsGenEulerDatum K B a fun v =>
      if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0)
    (hB2 : B 2) (ha3 : ∀ p : ℕ, p.Prime → p % 4 = 3 → a p = 0)
    (ha : ∀ p : ℕ, p.Prime → a p ^ 2 ≤ 4 * p) :
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      (∀ s : ℂ, 3 / 2 < s.re →
        Λ s = Complex.Gammaℂ s * LSeries (fun n => ((gCoeff B a n : ℤ) : ℂ)) s) ∧
      (∀ s : ℂ, Λ s = heckeRootNumber K χ (fun _ _ => 0) (fun _ _ => -1) *
        ((heckeConductor K χ : ℝ) : ℂ) ^ (1 - s) * Λ (2 - s)) ∧
      0 < heckeConductor K χ ∧
      (heckeRootNumber K χ (fun _ _ => 0) (fun _ _ => -1) = 1 ∨
        heckeRootNumber K χ (fun _ _ => 0) (fun _ _ => -1) = -1) := by
  have hn : ∀ v : HeightOneSpectrum (𝓞 K),
      (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) = 0 ∨
      ‖(if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0)‖ = 1 := by
    intro v
    split_ifs
    · exact Or.inr (hu _)
    · exact Or.inl rfl
  have hdat' := hdat.inv hn
  have hinv : (fun v : HeightOneSpectrum (𝓞 K) =>
      (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0)⁻¹) =
      fun v => if IsUnramifiedCharAt χ v then (((χ (uniformizerIdele K v))⁻¹ : ℂˣ) : ℂ) else 0 := by
    funext v
    split_ifs
    · rw [Units.val_inv_eq_inv_val]
    · rw [inv_zero]
  rw [hinv] at hdat'
  exact exists_functional_equation K χ ⟨hF, hcont, hu⟩ ⟨x₀ K, x₀_mem_normOneIdeles, hx⟩
    not_isReal_infinitePlace (isArchCompAt_of_apply harch) _
    (fun s hs => hasProd_places_of_isGenEulerDatum hdat hB2 ha3 ha hs)
    (fun s hs => hasProd_places_of_isGenEulerDatum hdat' hB2 ha3 ha hs)

end CMPoints
