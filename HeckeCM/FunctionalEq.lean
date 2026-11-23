import HeckeCM.GenPlaces
import Theorems.Thm_LanglandsTunnell_HeckeTate_isNicePinned_heckeDatum

/-!
# The functional equation, given the product over places

`exists_functional_equation`: let `K` be a number field with no real places and
with a single place at infinity (for example `ℚ(i)`), and let `χ` be a continuous
unitary character of the idèle class group, nontrivial on the idèles of norm 1, with
archimedean component `x ↦ (x/|x|)⁻¹`. If the Euler product of `χ` and that
of `χ⁻¹` over the places both give the Dirichlet series of `f` at `s + 1/2`,
then `Λ(s) = Γ_ℂ(s) · L(f, s)` extends to an entire function with

`Λ(s) = ε · N^{1 − s} · Λ(2 − s)`,

where `ε = heckeRootNumber` is the product of the local root numbers and
`N = heckeConductor` the conductor, as defined in the Fermat repository
`anthropics/fermats-last-theorem`. Moreover `ε = ±1`.

We use `LanglandsTunnell.HeckeTate.isNicePinned_heckeDatum` from that repository.
-/

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal
open LanglandsTunnell LanglandsTunnell.HeckeTate LanglandsTunnell.Converse Polynomial
open scoped Classical

namespace CMPoints

variable (K : Type) [Field K] [NumberField K]

/-- **Functional equation with explicit root number and conductor.** -/
theorem exists_functional_equation (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hadm : IsAdmissibleTwist K χ) (hx : ∃ x ∈ normOneIdeles K, χ x ≠ 1)
    (hreal : ∀ w : InfinitePlace K, ¬ w.IsReal) [Subsingleton (InfinitePlace K)]
    (harch : ∀ w : InfinitePlace K, IsArchCompAt K χ w 0 (-1))
    (f : ℕ → ℂ)
    (hP : ∀ s : ℂ, 1 < s.re → HasProd (fun v : HeightOneSpectrum (𝓞 K) =>
        (1 - (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) (LSeries f (s + 1 / 2)))
    (hP' : ∀ s : ℂ, 1 < s.re → HasProd (fun v : HeightOneSpectrum (𝓞 K) =>
        (1 - (if IsUnramifiedCharAt χ v then (((χ (uniformizerIdele K v))⁻¹ : ℂˣ) : ℂ) else 0) *
          ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) (LSeries f (s + 1 / 2))) :
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      (∀ s : ℂ, 3 / 2 < s.re → Λ s = Complex.Gammaℂ s * LSeries f s) ∧
      (∀ s : ℂ, Λ s = heckeRootNumber K χ (fun _ _ => 0) (fun _ _ => -1) *
        ((heckeConductor K χ : ℝ) : ℂ) ^ (1 - s) * Λ (2 - s)) ∧
      0 < heckeConductor K χ ∧
      (heckeRootNumber K χ (fun _ _ => 0) (fun _ _ => -1) = 1 ∨
        heckeRootNumber K χ (fun _ _ => 0) (fun _ _ => -1) = -1) := by
  have hcomplex : ∀ w : InfinitePlace K, w.IsComplex := fun w =>
    (InfinitePlace.not_isReal_iff_isComplex).1 (hreal w)
  obtain ⟨-, hconv, hN, Λ, Λd, hΛ, hΛd, -, -, hΛeq, hΛdeq, hfe⟩ :=
    isNicePinned_heckeDatum K χ hadm hx (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
      (fun _ _ => -1) (fun w hw => absurd hw (hreal w)) (fun w _ => harch w)
  set ε := heckeRootNumber K χ (fun _ _ => 0) (fun _ _ => -1) with hε
  set N := heckeConductor K χ with hNdef
  set D := heckeDatum K χ (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => -1) with hD
  -- the L-function of the datum and of its dual
  have hL : ∀ s : ℂ, 1 < s.re → D.LFun s = LSeries f (s + 1 / 2) := by
    intro s hs
    rw [← (hP s hs).tprod_eq]
    unfold LDatum.LFun
    refine tprod_congr fun v => ?_
    show ((if IsUnramifiedCharAt χ v then
        (C 1 - C ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) * X : ℂ[X]) else C 1).eval
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ = _
    split_ifs <;> simp
  have hLd : ∀ s : ℂ, 1 < s.re → D.LFunDual s = LSeries f (s + 1 / 2) := by
    intro s hs
    rw [← (hP' s hs).tprod_eq]
    unfold LDatum.LFunDual
    refine tprod_congr fun v => ?_
    show ((if IsUnramifiedCharAt χ v then
        (C 1 - C (((χ (uniformizerIdele K v))⁻¹ : ℂˣ) : ℂ) * X : ℂ[X]) else C 1).eval
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ = _
    split_ifs <;> simp
  -- the archimedean factor
  haveI : IsEmpty {w : InfinitePlace K // w.IsReal} := ⟨fun w => hreal w.1 w.2⟩
  haveI : Nonempty {w : InfinitePlace K // w.IsComplex} :=
    ⟨⟨Classical.arbitrary _, hcomplex _⟩⟩
  haveI : Unique {w : InfinitePlace K // w.IsComplex} :=
    ⟨⟨⟨Classical.arbitrary _, hcomplex _⟩⟩, fun a => Subsingleton.elim _ _⟩
  have hA : ∀ s : ℂ, D.archFactor s = Complex.Gammaℂ (s + 1 / 2) := by
    intro s
    simp [LDatum.archFactor, hD, heckeDatum, Finset.univ_unique]
  have hAd : ∀ s : ℂ, D.archFactorDual s = Complex.Gammaℂ (s + 1 / 2) := by
    intro s
    simp [LDatum.archFactorDual, hD, heckeDatum, Finset.univ_unique]
  -- `Λ = Λd`
  have habs : D.abscissa = 1 := rfl
  have hcen : D.center = 1 / 2 := rfl
  have heq : Λ = Λd := by
    have hU : {s : ℂ | 1 < s.re} ∈ nhds (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    have hev : Λ =ᶠ[nhds (2 : ℂ)] Λd :=
      Filter.mem_of_superset hU fun s hs => by
        have hs' : D.abscissa < s.re := by rw [habs]; exact hs
        show Λ s = Λd s
        rw [hΛeq s hs', hΛdeq s hs', hA, hAd, hL s hs, hLd s hs]
    funext z
    exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr hΛ).eqOn_of_preconnected_of_eventuallyEq
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hΛd) isPreconnected_univ
      (Set.mem_univ 2) hev (Set.mem_univ z)
  have hN0 : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hval : ∀ s : ℂ, 3 / 2 < s.re → Λ (s - 1 / 2) = Complex.Gammaℂ s * LSeries f s := by
    intro s hs
    have hs1 : 1 < (s - 1 / 2).re := by
      simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
      linarith
    have hs' : D.abscissa < (s - 1 / 2).re := by rw [habs]; exact hs1
    rw [hΛeq _ hs', hA, hL _ hs1, one_mul, sub_add_cancel]
  have hFE : ∀ s : ℂ, Λ (s - 1 / 2) = ε * ((N : ℝ) : ℂ) ^ (1 - s) * Λ (2 - s - 1 / 2) := by
    intro s
    have h := hfe (s - 1 / 2)
    rw [← heq, hcen] at h
    have e1 : (((1 / 2 : ℝ)) : ℂ) - (s - 1 / 2) = 1 - s := by push_cast; ring
    have e2 : 2 * (((1 / 2 : ℝ)) : ℂ) - (s - 1 / 2) = 2 - s - 1 / 2 := by push_cast; ring
    rw [e1, e2] at h
    exact h
  refine ⟨fun s => Λ (s - 1 / 2), hΛ.comp (differentiable_id.sub_const _), hval, hFE, hN, ?_⟩
  -- `ε² = 1`, by applying the equation twice at `s = 2`
  have h2 := hFE 2
  have h0 := hFE 0
  have e20 : (2 : ℂ) - 2 - 1 / 2 = 0 - 1 / 2 := by ring
  have e02 : (2 : ℂ) - 0 - 1 / 2 = 2 - 1 / 2 := by ring
  rw [e20, h0, e02] at h2
  have hne : Λ ((2 : ℂ) - 1 / 2) ≠ 0 := by
    rw [hval 2 (by norm_num)]
    refine mul_ne_zero ?_ ?_
    · rw [Complex.Gammaℂ_def]
      exact mul_ne_zero (mul_ne_zero two_ne_zero (by simp [Real.pi_ne_zero]))
        (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
    · have h32 : (1 : ℝ) < ((3 / 2 : ℂ)).re := by norm_num
      have hc := (hconv (3 / 2) (by rw [habs]; exact h32)).2.2.1
      rw [hL _ h32] at hc
      have : (3 / 2 : ℂ) + 1 / 2 = 2 := by norm_num
      rwa [this] at hc
  have hNN : ((N : ℝ) : ℂ) ^ ((1 : ℂ) - 2) * ((N : ℝ) : ℂ) ^ ((1 : ℂ) - 0) = 1 := by
    rw [← Complex.cpow_add _ _ hN0]
    norm_num
  have hsq : ε * ε = 1 := by
    have h3 : Λ ((2 : ℂ) - 1 / 2) = ε * ε *
        (((N : ℝ) : ℂ) ^ ((1 : ℂ) - 2) * ((N : ℝ) : ℂ) ^ ((1 : ℂ) - 0)) * Λ ((2 : ℂ) - 1 / 2) := by
      conv_lhs => rw [h2]
      ring
    rw [hNN, mul_one] at h3
    exact mul_right_cancel₀ hne (by rw [one_mul]; exact h3.symm)
  exact mul_self_eq_one_iff.1 hsq

end CMPoints
