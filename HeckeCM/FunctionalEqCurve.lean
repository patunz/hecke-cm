import HeckeCM.FunctionalEqChar

/-!
# The functional equation of the L-series of `y² = x³ − d²x`, for every `d ≠ 0`

`CMPoints.functional_equation_curveD`: there exist entire `F` and `Λ`, a sign
`w = ±1` and `N > 0` such that

* `F` extends the Mathlib L-series of the curve;
* `F(s) = Γ_ℂ(s)⁻¹ · Λ(s)`;
* `Λ(s) = w · N^{1 − s} · Λ(2 − s)`;
* if `w = −1` then `F(1) = 0`.

The sign and the conductor are `heckeRootNumber` and `heckeConductor` of the
Hecke character of the curve, but here they appear only existentially quantified:
they are not computed.
-/

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField.AdelicLevel AutomorphicForm NumberField.TateGlobal
open LanglandsTunnell LanglandsTunnell.HeckeTate LanglandsTunnell.Converse
open scoped Classical

namespace CMPoints

lemma Gammaℂ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : Complex.Gammaℂ s ≠ 0 := by
  rw [Complex.Gammaℂ_def]
  exact mul_ne_zero (mul_ne_zero two_ne_zero (by simp [Real.pi_ne_zero]))
    (Complex.Gamma_ne_zero_of_re_pos hs)

/-- From the functional equation of `Λ = Γ_ℂ · L` to the package for `L`. -/
theorem exists_package {f : ℕ → ℂ} {ε : ℂ} {N : ℝ} {Λ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ)
    (hval : ∀ s : ℂ, 3 / 2 < s.re → Λ s = Complex.Gammaℂ s * LSeries f s)
    (hfe : ∀ s : ℂ, Λ s = ε * ((N : ℝ) : ℂ) ^ (1 - s) * Λ (2 - s)) (hN : 0 < N)
    (hε : ε = 1 ∨ ε = -1) :
    ∃ (F Λ : ℂ → ℂ) (w : ℂ) (N : ℝ), Differentiable ℂ F ∧ Differentiable ℂ Λ ∧
      (w = 1 ∨ w = -1) ∧ 0 < N ∧
      (∀ s : ℂ, 3 / 2 < s.re → F s = LSeries f s) ∧
      (∀ s : ℂ, F s = (Complex.Gammaℂ s)⁻¹ * Λ s) ∧
      (∀ s : ℂ, Λ s = w * ((N : ℝ) : ℂ) ^ (1 - s) * Λ (2 - s)) ∧
      (w = -1 → F 1 = 0) := by
  refine ⟨fun s => (Complex.Gammaℂ s)⁻¹ * Λ s, Λ, ε, N, Complex.differentiable_Gammaℂ_inv.mul hΛ,
    hΛ, hε, hN, fun s hs => ?_, fun s => rfl, hfe, fun hw => ?_⟩
  · show (Complex.Gammaℂ s)⁻¹ * Λ s = LSeries f s
    rw [hval s hs, inv_mul_cancel_left₀ (Gammaℂ_ne_zero_of_re_pos (by linarith))]
  · have h1 := hfe 1
    rw [hw, sub_self, Complex.cpow_zero, show (2 : ℂ) - 1 = 1 by norm_num] at h1
    have h0 : Λ 1 = 0 := by linear_combination (1 / 2 : ℂ) * h1
    show (Complex.Gammaℂ 1)⁻¹ * Λ 1 = 0
    rw [h0, mul_zero]

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

local notation "𝔸" => AdeleRing (𝓞 K) K

section Odd

variable {d : ℕ} (hodd : d % 2 = 1) (hsq : Squarefree d) (hd : d ≠ 0)
include hodd hsq

lemma valued_x₀_unit :
    Valued.v (((Units.map ((toCompl K (placeTwo K) : 𝓞 K →+* _) : 𝓞 K →* _) (gaussIUnit K) :
      ((placeTwo K).adicCompletion K)ˣ) : (placeTwo K).adicCompletion K)) = 1 := by
  show Valued.v (toCompl K (placeTwo K) (gaussIUnit K)) = 1
  rw [valued_toCompl_unit]

theorem cmCharTw_x₀_ne_one : cmCharTw K hodd hsq hd (x₀ K) ≠ 1 := by
  intro key
  unfold x₀ at key
  rw [cmCharTw_apply, twC_locIdele_unit hodd hsq hd (natCast_notMem_placeTwo hodd) _
    (valued_x₀_unit hodd hsq), mul_one] at key
  exact cmChar_localUnit_two_ne_one (K := K) key

theorem cmCharTw_archUnitHom (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    ((cmCharTw K hodd hsq hd (archUnitHom w x) : ℂˣ) : ℂ) =
      (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion) /
        ((‖InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)‖ : ℝ) : ℂ))⁻¹ := by
  rw [cmCharTw_apply, twC_archUnitHom w x hodd hsq hd, mul_one, cmChar_archUnitHom]

theorem cmCharEv_archUnitHom (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    ((cmCharEv K hodd hsq hd (archUnitHom w x) : ℂˣ) : ℂ) =
      (InfinitePlace.Completion.extensionEmbedding w (x : w.Completion) /
        ((‖InfinitePlace.Completion.extensionEmbedding w (x : w.Completion)‖ : ℝ) : ℂ))⁻¹ := by
  rw [cmCharEv_apply, tw8C_archUnitHom, mul_one, cmCharTw_archUnitHom hodd hsq hd]

end Odd

end CMPoints

/-- Functional equation for the Dirichlet series of `cmCoeffTw d`, `d` odd and
squarefree. -/
theorem CMPoints.exists_package_cmCoeffTw (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {4} ℚ K] {d : ℕ} (hodd : d % 2 = 1) (hsq : Squarefree d) :
    ∃ (F Λ : ℂ → ℂ) (w : ℂ) (N : ℝ), Differentiable ℂ F ∧ Differentiable ℂ Λ ∧
      (w = 1 ∨ w = -1) ∧ 0 < N ∧
      (∀ s : ℂ, 3 / 2 < s.re →
        F s = LSeries (fun n => ((CMPoints.cmCoeffTw (d : ℤ) n : ℤ) : ℂ)) s) ∧
      (∀ s : ℂ, F s = (Complex.Gammaℂ s)⁻¹ * Λ s) ∧
      (∀ s : ℂ, Λ s = w * ((N : ℝ) : ℂ) ^ (1 - s) * Λ (2 - s)) ∧
      (w = -1 → F 1 = 0) := by
  have hd : d ≠ 0 := by
    rintro rfl
    simp at hodd
  obtain ⟨Λ, hΛ, hval, hfe, hN, hε⟩ := CMPoints.functional_equation_of_datum
    (CMPoints.cmCharTw K hodd hsq hd) (CMPoints.continuous_cmCharTw hodd hsq hd)
    (CMPoints.isUnitaryChar_cmCharTw hodd hsq hd) (CMPoints.isIdeleClassChar_cmCharTw hodd hsq hd)
    (CMPoints.cmCharTw_x₀_ne_one hodd hsq hd) (CMPoints.cmCharTw_archUnitHom hodd hsq hd)
    (CMPoints.isGenEulerDatum_cmCharTw hodd hsq hd) ⟨(d : ℤ), by norm_num⟩
    (fun p _ h => CMPoints.twCoeff_eq_zero _ p h) (CMPoints.twCoeff_sq_le _)
  rw [← CMPoints.cmCoeffTw_eq_gCoeff] at hval
  exact CMPoints.exists_package hΛ hval hfe hN hε

/-- Functional equation for the Dirichlet series of `cmCoeffTw (2e)`, `e`
odd and squarefree. -/
theorem CMPoints.exists_package_cmCoeffTw_two_mul (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {4} ℚ K] {e : ℕ} (hodd : e % 2 = 1) (hsq : Squarefree e) :
    ∃ (F Λ : ℂ → ℂ) (w : ℂ) (N : ℝ), Differentiable ℂ F ∧ Differentiable ℂ Λ ∧
      (w = 1 ∨ w = -1) ∧ 0 < N ∧
      (∀ s : ℂ, 3 / 2 < s.re →
        F s = LSeries (fun n => ((CMPoints.cmCoeffTw (2 * (e : ℤ)) n : ℤ) : ℂ)) s) ∧
      (∀ s : ℂ, F s = (Complex.Gammaℂ s)⁻¹ * Λ s) ∧
      (∀ s : ℂ, Λ s = w * ((N : ℝ) : ℂ) ^ (1 - s) * Λ (2 - s)) ∧
      (w = -1 → F 1 = 0) := by
  have he : e ≠ 0 := by
    rintro rfl
    simp at hodd
  obtain ⟨Λ, hΛ, hval, hfe, hN, hε⟩ := CMPoints.functional_equation_of_datum
    (CMPoints.cmCharEv K hodd hsq he) (CMPoints.continuous_cmCharEv hodd hsq he)
    (CMPoints.isUnitaryChar_cmCharEv hodd hsq he) (CMPoints.isIdeleClassChar_cmCharEv hodd hsq he)
    (CMPoints.cmCharEv_locIdele_two_ne_one hodd hsq he) (CMPoints.cmCharEv_archUnitHom hodd hsq he)
    (CMPoints.isGenEulerDatum_cmCharEv hodd hsq he) ⟨2 * (e : ℤ), by norm_num⟩
    (fun p _ h => CMPoints.twCoeff_eq_zero _ p h) (CMPoints.twCoeff_sq_le _)
  rw [← CMPoints.cmCoeffTw_eq_gCoeff] at hval
  exact CMPoints.exists_package hΛ hval hfe hN hε

/-- **Functional equation of the Mathlib L-series of `y² = x³ − d²x`**, for
every nonzero natural number `d`. If the sign is `−1`, the entire continuation
vanishes at `s = 1`. -/
theorem CMPoints.functional_equation_curveD {d : ℕ} (hd : d ≠ 0) :
    ∃ (F Λ : ℂ → ℂ) (w : ℂ) (N : ℝ), Differentiable ℂ F ∧ Differentiable ℂ Λ ∧
      (w = 1 ∨ w = -1) ∧ 0 < N ∧
      (∀ s : ℂ, 3 / 2 < s.re →
        F s = (⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ).LSeries s) ∧
      (∀ s : ℂ, F s = (Complex.Gammaℂ s)⁻¹ * Λ s) ∧
      (∀ s : ℂ, Λ s = w * ((N : ℝ) : ℂ) ^ (1 - s) * Λ (2 - s)) ∧
      (w = -1 → F 1 = 0) := by
  haveI : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  obtain ⟨d', m, hmd, hsq⟩ := Nat.sq_mul_squarefree d
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hmd
    exact hd hmd.symm
  have hmZ : (m : ℤ) ≠ 0 := by exact_mod_cast hm0
  by_cases hpar : d' % 2 = 1
  · obtain ⟨F, Λ, w, N, hF, hΛ, hw, hN, hval, hrel, hfe, hzero⟩ :=
      CMPoints.exists_package_cmCoeffTw (CyclotomicField 4 ℚ) hpar hsq
    refine ⟨F, Λ, w, N, hF, hΛ, hw, hN, fun s hs => ?_, hrel, hfe, hzero⟩
    rw [hval s hs]
    have e1 : (⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ) =
        CMPoints.curveD ℚ ((((d' : ℤ) * (m : ℤ) ^ 2 : ℤ)) : ℚ) := by
      have hq : (d : ℚ) = ((((d' : ℤ) * (m : ℤ) ^ 2 : ℤ)) : ℚ) := by
        rw [← hmd]
        push_cast
        ring
      rw [hq]
      rfl
    have hoddZ : Odd (d' : ℤ) := by exact_mod_cast Nat.odd_iff.2 hpar
    have hsqZ : Squarefree (d' : ℤ) := Int.squarefree_natCast.2 hsq
    rw [e1, WeierstrassCurve.LSeries, CMPoints.LFunction_curveD_mul_sq hoddZ hsqZ hmZ]
    congr 1
    funext n
    show ((CMPoints.cmCoeffTw (d' : ℤ) n : ℤ) : ℂ) =
      (((CMPoints.curveD ℚ ((d' : ℤ) : ℚ)).LFunction n : ℤ) : ℂ)
    rw [CMPoints.LFunction_curveD_eq_cmCoeffTw_of_odd_squarefree hoddZ hsqZ n]
  · obtain ⟨e, he⟩ : ∃ e, d' = 2 * e := ⟨d' / 2, by omega⟩
    subst he
    have hesq : Squarefree e := hsq.of_mul_right
    have heodd : e % 2 = 1 := by
      by_contra h
      obtain ⟨f, hf⟩ : ∃ f, e = 2 * f := ⟨e / 2, by omega⟩
      have h22 : (2 : ℕ) * 2 ∣ 2 * e := ⟨f, by rw [hf]; ring⟩
      exact absurd (hsq 2 h22) (by decide)
    have heoddZ : Odd (e : ℤ) := by exact_mod_cast Nat.odd_iff.2 heodd
    have hesqZ : Squarefree (e : ℤ) := Int.squarefree_natCast.2 hesq
    obtain ⟨F, Λ, w, N, hF, hΛ, hw, hN, hval, hrel, hfe, hzero⟩ :=
      CMPoints.exists_package_cmCoeffTw_two_mul (CyclotomicField 4 ℚ) heodd hesq
    refine ⟨F, Λ, w, N, hF, hΛ, hw, hN, fun s hs => ?_, hrel, hfe, hzero⟩
    have e1 : (⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ) =
        CMPoints.curveD ℚ (((2 * (e : ℤ) * (m : ℤ) ^ 2 : ℤ)) : ℚ) := by
      have hq : (d : ℚ) = (((2 * (e : ℤ) * (m : ℤ) ^ 2 : ℤ)) : ℚ) := by
        rw [← hmd]
        push_cast
        ring
      rw [hq]
      rfl
    rw [hval s hs, e1, WeierstrassCurve.LSeries,
      CMPoints.LFunction_curveD_two_mul_sq heoddZ hesqZ hmZ]
    congr 1
    funext n
    show ((CMPoints.cmCoeffTw (2 * (e : ℤ)) n : ℤ) : ℂ) =
      (((CMPoints.curveD ℚ (((2 * (e : ℤ) : ℤ)) : ℚ)).LFunction n : ℤ) : ℂ)
    rw [CMPoints.LFunction_curveD_two_mul_eq_cmCoeffTw heoddZ hesqZ n]
