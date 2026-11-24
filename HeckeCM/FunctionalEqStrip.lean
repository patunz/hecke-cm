import HeckeCM.Bridge

/-!
# The functional equation in classical form, for every entire continuation

`functional_equation_curveD_odd` gives *one* entire continuation `F` of the
L-series of `y² = x³ − d²x` (`d` odd and squarefree) together with
`Λ = Γ_ℂ · F` and `Λ(s) = w · N^{1−s} · Λ(2−s)`, `N = 32 d²`.

Here the same statement is written in the classical normalisation

`Λ*(s) = N^{s/2} (2π)^{−s} Γ(s) F(s)`,   `Λ*(s) = w · Λ*(2 − s)`,

for *every* entire continuation `F`, and for `0 < Re s < 2`. The restriction to
the strip is needed because Mathlib's `Complex.Gamma` takes the value `0` at
the nonpositive integers, where the true `Γ` has poles: on the strip both
`Γ(s)` and `Γ(2 − s)` are the true values.

* `functional_equation_strip_odd`: `d` odd and squarefree, sign `χ₈(d)·χ₄(d)`;
* `functional_equation_strip_five`: `d ≡ 5 (mod 8)` squarefree, sign `−1`, with
  the conductor written as the natural number `32 * d ^ 2`.
-/

set_option autoImplicit false

noncomputable section

namespace CMPoints

/-- `(2π)^{−t} Γ(t) = Γ_ℂ(t) / 2`. -/
lemma two_pi_cpow_mul_Gamma (t : ℂ) :
    (2 * Real.pi : ℂ) ^ (-t) * Complex.Gamma t = Complex.Gammaℂ t / 2 := by
  rw [Complex.Gammaℂ_def]
  ring

/-- **Functional equation on the strip, `d` odd and squarefree.** For every
entire continuation `F` of the Mathlib L-series of `y² = x³ − d²x` and every
`s` with `0 < Re s < 2`, the completed function
`N^{s/2} (2π)^{−s} Γ(s) F(s)`, `N = 32 d²`, takes at `s` the value
`χ₈(d)·χ₄(d)` times its value at `2 − s`. -/
theorem functional_equation_strip_odd {d : ℕ} (hodd : d % 2 = 1) (hsq : Squarefree d)
    (F : ℂ → ℂ)
    (hF : IsEntireContinuation (⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ) F)
    (s : ℂ) (h0 : 0 < s.re) (h2 : s.re < 2) :
    (32 * (d : ℂ) ^ 2) ^ (s / 2) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s * F s =
      ((ZMod.χ₈ (d : ZMod 8) * ZMod.χ₄ (d : ZMod 4) : ℤ) : ℂ) *
        ((32 * (d : ℂ) ^ 2) ^ ((2 - s) / 2) * (2 * Real.pi : ℂ) ^ (-(2 - s)) *
          Complex.Gamma (2 - s) * F (2 - s)) := by
  obtain ⟨F₀, Λ, hF₀, -, hval, hrel, hfe⟩ := functional_equation_curveD_odd hodd hsq
  -- the constructed continuation is `F`
  have hopen : IsOpen {t : ℂ | 3 / 2 < t.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : F₀ =ᶠ[nhds (2 : ℂ)] F :=
    Filter.eventually_of_mem (hopen.mem_nhds (by norm_num : (3 / 2 : ℝ) < (2 : ℂ).re))
      fun t ht => (hval t ht).trans (hF.2 t ht).symm
  have heq := (hF₀.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
    (hF.1.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (Set.mem_univ 2) hev
  -- `(2π)^{−t} Γ(t) F(t) = Λ(t) / 2` for `Re t > 0`
  have key : ∀ t : ℂ, 0 < t.re →
      (2 * Real.pi : ℂ) ^ (-t) * Complex.Gamma t * F t = Λ t / 2 := by
    intro t ht
    have hne : Complex.Gammaℂ t ≠ 0 := Gammaℂ_ne_zero_of_re_pos ht
    rw [← heq (Set.mem_univ t), hrel t, two_pi_cpow_mul_Gamma]
    field_simp
  have hre : (2 - s).re = 2 - s.re := by simp
  have k1 := key s h0
  have k2 := key (2 - s) (by rw [hre]; linarith)
  have hd0 : (d : ℂ) ≠ 0 := by
    have : d ≠ 0 := by
      rintro rfl
      omega
    exact_mod_cast this
  have hN0 : (32 * (d : ℂ) ^ 2) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hd0)
  have hp : (32 * (d : ℂ) ^ 2) ^ ((2 - s) / 2) =
      (32 * (d : ℂ) ^ 2) ^ (s / 2) * (32 * (d : ℂ) ^ 2) ^ (1 - s) := by
    rw [← Complex.cpow_add _ _ hN0]
    congr 1
    ring
  have e1 : (32 * (d : ℂ) ^ 2) ^ (s / 2) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s * F s =
      (32 * (d : ℂ) ^ 2) ^ (s / 2) * (Λ s / 2) := by
    rw [← k1]
    ring
  have e2 : (32 * (d : ℂ) ^ 2) ^ ((2 - s) / 2) * (2 * Real.pi : ℂ) ^ (-(2 - s)) *
      Complex.Gamma (2 - s) * F (2 - s) =
      (32 * (d : ℂ) ^ 2) ^ ((2 - s) / 2) * (Λ (2 - s) / 2) := by
    rw [← k2]
    ring
  rw [e1, e2, hp]
  linear_combination ((32 * (d : ℂ) ^ 2) ^ (s / 2) / 2) * hfe s

/-- **Functional equation on the strip, `d ≡ 5 (mod 8)` squarefree**:
`Λ*(2 − s) = −Λ*(s)` for `0 < Re s < 2`, where
`Λ*(s) = N^{s/2} (2π)^{−s} Γ(s) F(s)`, `N = 32 d²`, and `F` is any entire
continuation of the Mathlib L-series of `y² = x³ − d²x`. -/
theorem functional_equation_strip_five {d : ℕ} (h5 : d % 8 = 5) (hsq : Squarefree d)
    (F : ℂ → ℂ)
    (hF : IsEntireContinuation (⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ) F)
    (s : ℂ) (h0 : 0 < s.re) (h2 : s.re < 2) :
    ((32 * d ^ 2 : ℕ) : ℂ) ^ ((2 - s) / 2) * (2 * Real.pi : ℂ) ^ (-(2 - s)) *
        Complex.Gamma (2 - s) * F (2 - s) =
      -(((32 * d ^ 2 : ℕ) : ℂ) ^ (s / 2) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s * F s) := by
  have hodd : d % 2 = 1 := by omega
  have h4 : d % 4 = 1 := by omega
  have hsign : ZMod.χ₈ (d : ZMod 8) * ZMod.χ₄ (d : ZMod 4) = -1 := by
    rw [ZMod.χ₈_nat_eq_if_mod_eight, ZMod.χ₄_nat_eq_if_mod_four]
    simp [h5, hodd, h4]
  have hgen := functional_equation_strip_odd hodd hsq F hF s h0 h2
  rw [hsign] at hgen
  have hN : ((32 * d ^ 2 : ℕ) : ℂ) = 32 * (d : ℂ) ^ 2 := by push_cast; ring
  rw [hN]
  push_cast at hgen
  linear_combination hgen

end CMPoints
