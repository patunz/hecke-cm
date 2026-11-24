import HeckeCM.FunctionalEqStrip
import Theorems.Thm_NumberField_TateGlobal_exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc

/-!
# Polynomial growth in vertical strips

The Fermat repository proves that an entire function which agrees with the
Euler product of a nontrivial unitary Hecke character for `Re s > 1` has at
most polynomial growth in every vertical strip. Applied to our characters:

* `growth_of_datum`: for a character whose local values are those of a
  sequence of CM type, every entire `F` that agrees with the Dirichlet series
  of the sequence for `Re s > 3/2` satisfies `‖F(w)‖ ≤ A (1 + |Im w|)^N` on
  `σ₁ ≤ Re w ≤ σ₂`;
* `growth_curveD_odd`: the same for every entire continuation of the Mathlib
  L-series of `y² = x³ − d²x`, `d` odd and squarefree.
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

/-- **Polynomial growth in vertical strips**, starting from the local values. -/
theorem growth_of_datum (χ : (𝔸)ˣ →* ℂˣ) (hcont : Continuous χ)
    (hu : IsUnitaryChar (𝓞 K) K χ) (hF : IsIdeleClassChar (𝓞 K) K χ) (hx : χ (x₀ K) ≠ 1)
    {B : ℕ → Prop} [DecidablePred B] {a : ℕ → ℤ}
    (hdat : IsGenEulerDatum K B a fun v =>
      if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0)
    (hB2 : B 2) (ha3 : ∀ p : ℕ, p.Prime → p % 4 = 3 → a p = 0)
    (ha : ∀ p : ℕ, p.Prime → a p ^ 2 ≤ 4 * p)
    (F : ℂ → ℂ) (hFd : Differentiable ℂ F)
    (hFv : ∀ s : ℂ, 3 / 2 < s.re → F s = LSeries (fun n => ((gCoeff B a n : ℤ) : ℂ)) s)
    (σ₁ σ₂ : ℝ) :
    ∃ (A : ℝ) (N : ℕ), ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ → ‖F w‖ ≤ A * (1 + |w.im|) ^ N := by
  obtain ⟨A, N, h⟩ :=
    NumberField.TateGlobal.exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc
      K χ hF hcont hu ⟨x₀ K, x₀_mem_normOneIdeles, hx⟩ ∅ (σ₁ - 1 / 2) (σ₂ - 1 / 2)
      (fun w => F (w + 1 / 2)) (hFd.comp (differentiable_id.add_const _)) (fun s hs => by
        have hs' : 3 / 2 < (s + 1 / 2).re := by
          simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
          linarith
        have hP := (hasProd_places_of_isGenEulerDatum hdat hB2 ha3 ha hs).tprod_eq
        show F (s + 1 / 2) = _
        rw [hFv _ hs', ← hP]
        exact ((Equiv.subtypeUnivEquiv (fun v : HeightOneSpectrum (𝓞 K) =>
          Finset.notMem_empty v)).tprod_eq (fun v : HeightOneSpectrum (𝓞 K) =>
            (1 - (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
              (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)).symm)
  refine ⟨A, N, fun w h1 h2 => ?_⟩
  have hre : (w - 1 / 2).re = w.re - 1 / 2 := by
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
  have him : (w - 1 / 2).im = w.im := by
    simp
  have := h (w - 1 / 2) (by rw [hre]; linarith) (by rw [hre]; linarith)
  rw [him] at this
  simpa using this

end CMPoints

/-- **Polynomial growth in vertical strips** of every entire continuation of the
Mathlib L-series of `y² = x³ − d²x`, `d` odd and squarefree. -/
theorem CMPoints.growth_curveD_odd {d : ℕ} (hodd : d % 2 = 1) (hsq : Squarefree d) (F : ℂ → ℂ)
    (hF : CMPoints.IsEntireContinuation (⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ) F)
    (σ₁ σ₂ : ℝ) :
    ∃ (A : ℝ) (N : ℕ), ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ → ‖F w‖ ≤ A * (1 + |w.im|) ^ N := by
  haveI : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  have hd : d ≠ 0 := by
    rintro rfl
    omega
  have hoddZ : Odd (d : ℤ) := by exact_mod_cast Nat.odd_iff.2 hodd
  have hsqZ : Squarefree (d : ℤ) := Int.squarefree_natCast.2 hsq
  refine CMPoints.growth_of_datum (CMPoints.cmCharTw (CyclotomicField 4 ℚ) hodd hsq hd)
    (CMPoints.continuous_cmCharTw hodd hsq hd)
    (CMPoints.isUnitaryChar_cmCharTw hodd hsq hd) (CMPoints.isIdeleClassChar_cmCharTw hodd hsq hd)
    (CMPoints.cmCharTw_x₀_ne_one hodd hsq hd)
    (CMPoints.isGenEulerDatum_cmCharTw hodd hsq hd) ⟨(d : ℤ), by norm_num⟩
    (fun p _ h => CMPoints.twCoeff_eq_zero _ p h) (CMPoints.twCoeff_sq_le _) F hF.1
    (fun s hs => ?_) σ₁ σ₂
  rw [hF.2 s hs, ← CMPoints.cmCoeffTw_eq_gCoeff,
    CMPoints.curve_eq (Int.cast_natCast d).symm, WeierstrassCurve.LSeries]
  congr 1
  funext n
  show (((CMPoints.curveD ℚ ((d : ℤ) : ℚ)).LFunction n : ℤ) : ℂ) =
    ((CMPoints.cmCoeffTw (d : ℤ) n : ℤ) : ℂ)
  rw [CMPoints.LFunction_curveD_eq_cmCoeffTw_of_odd_squarefree hoddZ hsqZ n]
