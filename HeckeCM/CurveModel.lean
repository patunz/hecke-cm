/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang
-/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/- The notices above are reproduced from the original files. This file is a modified copy:
see the module docstring below and `THIRD_PARTY.md`. The license text is in
`LICENSE-APACHE-2.0`. -/
import Mathlib

/-!
# Minimal models, point counting and the curve `y² = x³ − x`, in Lean 4.33.1

This file ports to Lean 4.33.1 (Mathlib `0df444a3`) the declarations we need
that are not available in that version. **It is not our work**:

* the `UIntegral` section is copied from Mathlib,
  `Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean` at commit `31ce06ea`
  (Apache 2.0, Mathlib authors);
* everything else is copied from Tau Ceti (`TauCetiProject/TauCeti`, commit
  `b608709b`, Apache 2.0, "The Tau Ceti contributors"), from the files
  `AlgebraicGeometry/EllipticCurve/` `Affine/Formula/VariableChange.lean`,
  `PointCount.lean`, `IntegralModel.lean`, `MinimalModel/Basic.lean`,
  `CurveX3SubX.lean`.

Modifications: the module system was removed (`public`, `@[expose]`), names were
adapted where Mathlib changed, and the curve lives in the namespace
`CMPoints.CurveX3SubX` instead of `TauCeti.CurveX3SubX`.
-/

set_option autoImplicit false

open Polynomial

namespace WeierstrassCurve

/-! ## From Mathlib `31ce06ea`: descent of a change of variables -/

section UIntegral

open Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K] {W W' : WeierstrassCurve K} [IsIntegral R W] [IsIntegral R W']
  {CK : VariableChange K} (hCK : CK • W = W') {u : Rˣ} (hu : algebraMap R K u = CK.u)

include hCK hu

lemma r_integral_of_u_integral : ∃ r : R, algebraMap R K r = CK.r := by
  refine IsIntegrallyClosed.isIntegral_iff.mp ⟨X ^ 4 - C (integralModel R W).b₄ * X ^ 2 -
    C (u ^ 6 * (integralModel R W').b₆ + 2 * (integralModel R W).b₆) * X -
    C ((integralModel R W).b₈ - u ^ 8 * (integralModel R W').b₈), by monicity!, ?_⟩
  simp [map_ofNat, hu, ← hCK, integralModel_b₄_eq, integralModel_b₆_eq,
    integralModel_b₈_eq, variableChange_b₆, variableChange_b₈]
  ring1

lemma s_integral_of_u_integral : ∃ s : R, algebraMap R K s = CK.s := by
  rcases r_integral_of_u_integral hCK hu with ⟨r, hr⟩
  refine IsIntegrallyClosed.isIntegral_iff.mp ⟨X ^ 2 + C (integralModel R W).a₁ * X +
    C (u ^ 2 * (integralModel R W').a₂ - (integralModel R W).a₂ - 3 * r), by monicity!, ?_⟩
  simp [map_ofNat, hu, hr, ← hCK, integralModel_a₁_eq, integralModel_a₂_eq,
    variableChange_a₂]
  ring1

lemma t_integral_of_u_integral : ∃ t : R, algebraMap R K t = CK.t := by
  rcases r_integral_of_u_integral hCK hu with ⟨r, hr⟩
  refine IsIntegrallyClosed.isIntegral_iff.mp ⟨X ^ 2 +
    C ((integralModel R W).a₃ + r * (integralModel R W).a₁) * X +
    C (u ^ 6 * (integralModel R W').a₆ - (integralModel R W).a₆ - r * (integralModel R W).a₄
      - r ^ 2 * (integralModel R W).a₂ - r ^ 3), by monicity!, ?_⟩
  simp [hu, hr, ← hCK, integralModel_a₁_eq, integralModel_a₂_eq, integralModel_a₃_eq,
    integralModel_a₄_eq, integralModel_a₆_eq, variableChange_a₆]
  ring1

/-- A variable change over the fraction field between integral Weierstrass equations descends to the
base ring if its `u` coefficient descends to a unit of the base ring. -/
theorem variableChange_integral_of_u_integral : ∃ CR : VariableChange R, CR.baseChange K = CK := by
  rcases r_integral_of_u_integral hCK hu, s_integral_of_u_integral hCK hu,
    t_integral_of_u_integral hCK hu with ⟨⟨r, hr⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩
  exact ⟨⟨u, r, s, t⟩, by ext <;> simpa⟩

end UIntegral

end WeierstrassCurve

/-! ## From Tau Ceti: the equation under a change of variables -/

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (C : VariableChange R)

-- Mathlib's `variableChange_aᵢ` state the coefficients of `C • W` with a factor of `u⁻¹ ^ i`.
-- These five clear that factor, and are the only place `u⁻¹` is mentioned in this half of the
-- file: every identity below is a `linear_combination` of them over `R`, with `(C • W).aᵢ` left
-- as an atom. They are `private` because the `variableChange_aᵢ` themselves are the public way to
-- ask what the coefficients are.
private lemma u_mul_variableChange_a₁ : (C.u : R) * (C • W).a₁ = W.a₁ + 2 * C.s := by
  simp only [variableChange_a₁, Units.mul_inv_cancel_left]

private lemma u_pow_mul_variableChange_a₂ :
    (C.u : R) ^ 2 * (C • W).a₂ = W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2 := by
  simp only [variableChange_a₂, ← Units.val_pow_eq_pow_val, inv_pow, Units.mul_inv_cancel_left]

private lemma u_pow_mul_variableChange_a₃ :
    (C.u : R) ^ 3 * (C • W).a₃ = W.a₃ + C.r * W.a₁ + 2 * C.t := by
  simp only [variableChange_a₃, ← Units.val_pow_eq_pow_val, inv_pow, Units.mul_inv_cancel_left]

private lemma u_pow_mul_variableChange_a₄ :
    (C.u : R) ^ 4 * (C • W).a₄ = W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂
      - (C.t + C.r * C.s) * W.a₁ + 3 * C.r ^ 2 - 2 * C.s * C.t := by
  simp only [variableChange_a₄, ← Units.val_pow_eq_pow_val, inv_pow, Units.mul_inv_cancel_left]

private lemma u_pow_mul_variableChange_a₆ :
    (C.u : R) ^ 6 * (C • W).a₆ = W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3
      - C.t * W.a₃ - C.t ^ 2 - C.r * C.t * W.a₁ := by
  simp only [variableChange_a₆, ← Units.val_pow_eq_pow_val, inv_pow, Units.mul_inv_cancel_left]

/-- A point `(x, y)` lies on `C • W` if and only if `(u²x + r, u³y + u²sx + t)` lies on `W`: the
change of variables scales the Weierstrass polynomial by `u⁶`, and `u` is a unit. -/
@[simp] lemma variableChange_equation (x y : R) :
    W.toAffine.Equation ((C.u : R) ^ 2 * x + C.r)
        ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
      ↔ (C • W).toAffine.Equation x y := by
  rw [equation_iff', equation_iff']
  refine (Eq.congr_left ?_).trans (C.u.isUnit.pow 6).mul_right_eq_zero
  linear_combination -(C.u : R) ^ 5 * x * y * u_mul_variableChange_a₁ W C
    + (C.u : R) ^ 4 * x ^ 2 * u_pow_mul_variableChange_a₂ W C
    - (C.u : R) ^ 3 * y * u_pow_mul_variableChange_a₃ W C
    + (C.u : R) ^ 2 * x * u_pow_mul_variableChange_a₄ W C + u_pow_mul_variableChange_a₆ W C

end WeierstrassCurve.Affine

/-! ## From Tau Ceti: point counting and the Frobenius trace -/

namespace WeierstrassCurve

section PointCount

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- **The number of `F`-points of the projective Weierstrass model**, the singular point included
when there is one: `Nat.card` of the solutions of the affine equation, singular or not, plus one
for the point at infinity. It is the honest count whenever that solution type is finite. -/
noncomputable def pointCount : ℕ :=
  Nat.card {p : F × F // W.toAffine.Equation p.1 p.2} + 1

/-- The defining equation of `pointCount`. -/
@[simp]
-- Needed as a lemma rather than left to unfolding: `pointCount`'s body is not exposed across a
-- module boundary, so `rfl` for this equation fails in a downstream file.
theorem pointCount_def :
    W.pointCount = Nat.card {p : F × F // W.toAffine.Equation p.1 p.2} + 1 := rfl

/-- **On an elliptic model the projective count is the cardinality of Mathlib's point type.**
An elliptic model has no singular point to include, so the solutions of the equation are exactly
the nonsingular ones, and the point at infinity is the one Mathlib's type adjoins. -/
theorem pointCount_eq_card_point
    [Finite {p : F × F // W.toAffine.Equation p.1 p.2}] [W.IsElliptic] :
    W.pointCount = Nat.card W.toAffine.Point := by
  rw [WeierstrassCurve.pointCount_def, Nat.card_congr W.toAffine.pointEquiv]
  -- `WithZero` is the `Option` the cardinality lemma is stated for
  exact Finite.card_option.symm

/-- **The Frobenius trace** `a_q = q + 1 − #W(F)` of a Weierstrass model over a finite field of
`q` elements, measured against `pointCount`.

Taken against that count the formula returns the classical local invariant at *every* Weierstrass
model: `a_q` at an elliptic one, and `1`, `−1`, `0` at split multiplicative, nonsplit
multiplicative and additive reduction. That is why it carries no ellipticity hypothesis. It is
elliptic-specific only in its reading as a *trace*, which rests on the identity
`deg (1 − π_q) = #E(𝔽_q)`. -/
noncomputable def frobeniusTrace [Finite F] : ℤ :=
  -- `q` is a number only because the base is finite, so the count is taken through that
  -- finiteness; `frobeniusTrace_def` restates it with `Nat.card`, the form the API is phrased in
  have : Fintype F := Fintype.ofFinite F
  (Fintype.card F : ℤ) + 1 - W.pointCount

/-- The defining equation of `frobeniusTrace`. -/
@[simp]
theorem frobeniusTrace_def [Finite F] :
    W.frobeniusTrace = (Nat.card F : ℤ) + 1 - W.pointCount := by
  simp only [WeierstrassCurve.frobeniusTrace, @Nat.card_eq_fintype_card F (Fintype.ofFinite F)]

/-- **Over a finite field, on an elliptic model the trace is measured against Mathlib's point
type**, which is the classical `a_q`. -/
theorem frobeniusTrace_eq_card_point [Finite F] [W.IsElliptic] :
    W.frobeniusTrace = (Nat.card F : ℤ) + 1 - Nat.card W.toAffine.Point := by
  rw [WeierstrassCurve.frobeniusTrace_def, WeierstrassCurve.pointCount_eq_card_point]

/-- **The point count is invariant under a change of variables**, singular models included: the
affine substitution `(x, y) ↦ (u² x + r, u³ y + u² s x + t)` is a bijection of `F × F` carrying the
solutions of the equation of `C • W` onto those of `W`. -/
@[simp 1100]
theorem variableChange_pointCount (C : WeierstrassCurve.VariableChange F) :
    (C • W).pointCount = W.pointCount := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  let e : F × F ≃ F × F :=
    { toFun p := ((C.u : F) ^ 2 * p.1 + C.r, (C.u : F) ^ 3 * p.2 + (C.u : F) ^ 2 * C.s * p.1 + C.t)
      invFun q := (((C.u : F) ^ 2)⁻¹ * (q.1 - C.r),
        ((C.u : F) ^ 3)⁻¹ * (q.2 - C.s * (q.1 - C.r) - C.t))
      left_inv p := by ext <;> field_simp <;> ring
      right_inv q := by ext <;> field_simp <;> ring }
  rw [WeierstrassCurve.pointCount_def, WeierstrassCurve.pointCount_def,
    Nat.card_congr (e.subtypeEquiv (q := fun p : F × F ↦ W.toAffine.Equation p.1 p.2) fun p ↦
      (WeierstrassCurve.Affine.variableChange_equation W C p.1 p.2).symm)]

/-- **The Frobenius trace is invariant under a change of variables.** -/
@[simp 1100]
theorem variableChange_frobeniusTrace [Finite F]
    (C : WeierstrassCurve.VariableChange F) :
    (C • W).frobeniusTrace = W.frobeniusTrace := by
  rw [WeierstrassCurve.frobeniusTrace_def, WeierstrassCurve.frobeniusTrace_def,
    WeierstrassCurve.variableChange_pointCount]

end PointCount

/-! ## From Tau Ceti: integral model and minimal model -/

/-- **The integral model is determined by its base change.** When `R → K` is injective, an
equation over `R` whose base change to `K` is `W` is the integral model of `W`. -/
theorem integralModel_eq_of_baseChange_eq {R : Type*} [CommRing R] {K : Type*} [Field K]
    [Algebra R K] [FaithfulSMul R K] {W : WeierstrassCurve K} [IsIntegral R W]
    {W₀ : WeierstrassCurve R} (h : W₀.baseChange K = W) : integralModel R W = W₀ :=
  map_injective (FaithfulSMul.algebraMap_injective R K)
    ((baseChange_integralModel_eq R W).trans h.symm)

open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **An integral Weierstrass equation whose discriminant has additive valuation less than `12` is
minimal.** This is the discriminant case of Silverman, *AEC*, Remark VII.1.1.

The hypothesis is stated multiplicatively, through the adic valuation of `W.Δ : K` with values in
`ℤᵐ⁰`: the inequality `exp (-12) < v (Δ)` says exactly that the additive valuation of `Δ` (its
order at the place) is less than `12`. For an equation with coefficients in `R`,
`isMinimal_baseChange_of_not_pow_twelve_dvd_Δ` reads the same condition as `¬ ϖ ^ 12 ∣ Δ`. -/
theorem isMinimal_of_exp_neg_twelve_lt_valuation_Δ (W : WeierstrassCurve K) [IsIntegral R W]
    (hΔ : WithZero.exp (-12) < valuation K (maximalIdeal R) W.Δ) : IsMinimal R W := by
  refine ⟨⟨by simpa using ‹IsIntegral R W›, ?_⟩⟩
  intro C hC _
  simp only [one_smul, ← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral R (C • W),
    valuation_Δ_aux_eq_of_isIntegral R W]
  have hint : valuation K (maximalIdeal R) (C • W).Δ ≤ 1 := by
    simpa [← integralModel_Δ_eq R (C • W)] using valuation_le_one _ _
  rw [variableChange_Δ, map_mul, map_pow] at hint ⊢
  refine mul_le_of_le_one_left' (pow_le_one' (not_lt.1 fun hu ↦ hint.not_gt ?_) 12)
  -- A valuation in `ℤᵐ⁰` greater than `1` is at least `exp 1`.
  have hu := (WithZero.lt_mul_exp_iff_le one_ne_zero).not.2 hu.not_ge
  rw [one_mul, not_lt] at hu
  calc 1 = WithZero.exp 1 ^ 12 * WithZero.exp (-12) := by
        rw [← WithZero.exp_nsmul, ← WithZero.exp_add]; norm_num
    _ < WithZero.exp 1 ^ 12 * valuation K (maximalIdeal R) W.Δ :=
        mul_lt_mul_of_pos_left hΔ (by simp)
    _ ≤ _ := mul_le_mul_left (pow_le_pow_left₀ zero_le hu 12) _

/-- **An equation over `R` whose discriminant is not divisible by `ϖ ^ 12` is minimal over `R`.**
This is `isMinimal_of_exp_neg_twelve_lt_valuation_Δ` for an equation whose coefficients are given
in `R`, with the valuation condition read as a divisibility. -/
theorem isMinimal_baseChange_of_not_pow_twelve_dvd_Δ (W : WeierstrassCurve R) {ϖ : R}
    (hϖ : Irreducible ϖ) (h : ¬ ϖ ^ 12 ∣ W.Δ) : IsMinimal R (W.baseChange K) := by
  have : IsIntegral R (W.baseChange K) := ⟨⟨W, rfl⟩⟩
  refine isMinimal_of_exp_neg_twelve_lt_valuation_Δ R _ ?_
  have hΔ : W.Δ ≠ 0 := fun h₀ ↦ h (h₀ ▸ dvd_zero _)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (addVal_eq_top_iff.not.2 hΔ)
  have hn12 : n < 12 := by
    by_contra h'
    refine h (addVal_le_iff_dvd.1 ?_)
    rw [addVal_pow, addVal_uniformizer hϖ, ← hn, nsmul_one]
    exact_mod_cast not_lt.1 h'
  rw [baseChange, map_Δ, valuation_of_algebraMap, intValuation_maximalIdeal, ← hn,
    ENat.recTopCoe_natCast, ← WithZero.exp_eq_coe_ofAdd, ← WithZero.exp_neg, WithZero.exp_lt_exp]
  omega

/-- **Mathlib's chosen minimal equation lies in the variable-change orbit.** The equation
`W.minimal R` is obtained from `W` by a change of variables. -/
theorem exists_smul_eq_minimal (W : WeierstrassCurve K) :
    ∃ C : VariableChange K, C • W = W.minimal R :=
  ⟨_, rfl⟩

/-- **A minimal model maximises the discriminant valuation in its orbit**: every integral model
obtained from it by a change of variables has discriminant of at most that valuation. This is the
`valuation`-level reading of Mathlib's `IsMinimal`, whose `MaximalFor` phrasing speaks of
`valuation_Δ_aux` and of the orbit of a fixed equation. -/
theorem valuation_Δ_le_of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K} [hm : IsMinimal R W₁]
    [IsIntegral R W₂] (D : VariableChange K) (hD : D • W₁ = W₂) :
    valuation K (maximalIdeal R) W₂.Δ ≤ valuation K (maximalIdeal R) W₁.Δ := by
  have hint : IsIntegral R (D • W₁) := by rw [hD]; infer_instance
  have h : valuation_Δ_aux R (D • W₁) ≤ valuation_Δ_aux R ((1 : VariableChange K) • W₁) :=
    (le_total (valuation_Δ_aux R ((1 : VariableChange K) • W₁)) (valuation_Δ_aux R (D • W₁))).elim
      (hm.val_Δ_maximal.2 hint) id
  rw [hD, one_smul] at h
  rw [← valuation_Δ_aux_eq_of_isIntegral R W₂, ← valuation_Δ_aux_eq_of_isIntegral R W₁,
    Subtype.coe_le_coe]
  exact h

/-- **Two minimal models related by a change of variables have the same discriminant valuation.**
So `v (Δ)` is an invariant of the curve at this place rather than of the chosen model: any two
minimal models of the same curve agree on it, and a consumer may read it off whichever model it
holds. -/
theorem valuation_Δ_eq_of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K} [IsMinimal R W₁]
    [IsMinimal R W₂] (D : VariableChange K) (hD : D • W₁ = W₂) :
    valuation K (maximalIdeal R) W₂.Δ = valuation K (maximalIdeal R) W₁.Δ :=
  -- Antisymmetry: `D` carries `W₁` to `W₂` and `D⁻¹` carries `W₂` back, and by minimality neither
  -- direction can increase the valuation.
  le_antisymm (valuation_Δ_le_of_isMinimal_smul R D hD)
    (valuation_Δ_le_of_isMinimal_smul R D⁻¹ (by rw [← hD, inv_smul_smul]))

/-- **The scaling factor of a change of variables between two minimal models of an elliptic curve
has valuation `1`.** Over a discrete valuation ring that says `u` is a **unit**: it and its inverse
are both integral, so such a change of variables is as integral as its coordinates allow. This is
the hypothesis `variableChange_integral_of_u_integral` asks for, and hence the step by
which a property of the reduction transfers between two minimal models of one curve. -/
theorem valuation_u_eq_one_of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K} [IsMinimal R W₁]
    [IsMinimal R W₂] [W₁.IsElliptic] (D : VariableChange K) (hD : D • W₁ = W₂) :
    valuation K (maximalIdeal R) ↑D.u = 1 := by
  -- A change of variables scales `Δ` by `u⁻¹²`. The two discriminant valuations agree and are
  -- nonzero, so `v (u)¹² = 1`, and the value group is torsion-free.
  have hΔ0 : valuation K (maximalIdeal R) W₁.Δ ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr W₁.isUnit_Δ.ne_zero
  have h12 : valuation K (maximalIdeal R) ↑D.u ^ 12 = 1 := by
    have key : valuation K (maximalIdeal R) W₁.Δ
        = (valuation K (maximalIdeal R) ↑D.u)⁻¹ ^ 12 * valuation K (maximalIdeal R) W₁.Δ := by
      conv_lhs => rw [← valuation_Δ_eq_of_isMinimal_smul R D hD, ← hD, variableChange_Δ]
      rw [map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀]
    have h1 : (valuation K (maximalIdeal R) ↑D.u)⁻¹ ^ 12 = 1 :=
      mul_right_cancel₀ hΔ0 (key.symm.trans (one_mul _).symm)
    rw [inv_pow] at h1
    exact inv_eq_one.mp h1
  exact (pow_eq_one_iff_of_nonneg zero_le (by norm_num)).mp h12

/-- **Two minimal models of an elliptic curve related by a change of variables have the same `c₄`
valuation**, since the change of variables scales `c₄` by `u⁻⁴` with `v (u) = 1`. -/
theorem valuation_c₄_eq_of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K} [IsMinimal R W₁]
    [IsMinimal R W₂] [W₁.IsElliptic] (D : VariableChange K) (hD : D • W₁ = W₂) :
    valuation K (maximalIdeal R) W₂.c₄ = valuation K (maximalIdeal R) W₁.c₄ := by
  rw [← hD, variableChange_c₄, map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀,
    valuation_u_eq_one_of_isMinimal_smul R D hD]
  simp

namespace VariableChange

/-- The scaling factor between two minimal elliptic equations is the image of a unit of the
discrete valuation ring. -/
theorem exists_unit_algebraMap_eq_u_of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K}
    [IsMinimal R W₁] [IsMinimal R W₂] [W₁.IsElliptic] (D : VariableChange K)
    (hD : D • W₁ = W₂) : ∃ u₀ : Rˣ, algebraMap R K u₀ = D.u := by
  obtain ⟨u₀, hau⟩ := associated_of_valuation_eq (A := R) 1 (↑D.u : K)
    (by rw [map_one]; exact (valuation_u_eq_one_of_isMinimal_smul R D hD).symm)
  rw [Units.smul_def, Algebra.smul_def, mul_one] at hau
  exact ⟨u₀, hau⟩

/-- **A change of variables between two minimal elliptic equations is defined over `R`, and it
carries one integral model to the other.** Its scaling factor is the image of a unit, so it
descends to a change of variables `C` over `R`, and since `R → K` is injective `C` relates the
integral models themselves. A property of integral models that is invariant under changes of
variables over `R`, such as one read off the reduction, is therefore shared by all minimal models
of an elliptic curve (Silverman, *AEC*, Proposition VII.1.3(b)). -/
theorem exists_baseChange_eq_and_smul_integralModel_eq_of_isMinimal_smul
    {W₁ W₂ : WeierstrassCurve K} [IsMinimal R W₁] [IsMinimal R W₂] [W₁.IsElliptic]
    (D : VariableChange K) (hD : D • W₁ = W₂) :
    ∃ C : VariableChange R, C.baseChange K = D ∧ C • W₁.integralModel R = W₂.integralModel R := by
  obtain ⟨u₀, hau⟩ := exists_unit_algebraMap_eq_u_of_isMinimal_smul R D hD
  obtain ⟨C, hC⟩ := variableChange_integral_of_u_integral hD hau
  refine ⟨C, hC, (integralModel_eq_of_baseChange_eq ?_).symm⟩
  rw [WeierstrassCurve.baseChange, ← map_variableChange]
  exact (congrArg₂ (· • ·) hC (baseChange_integralModel_eq R W₁)).trans hD

end VariableChange

/-- **The reductions of two minimal models of an elliptic curve are related by a change of
variables over the residue field**, namely the reduction of the integral change of variables
between their integral models. So every property of the reduction that is invariant under changes
of variables, such as being elliptic, ordinary or supersingular, depends only on the curve. -/
theorem exists_smul_reduction_eq_of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K}
    [IsMinimal R W₁] [IsMinimal R W₂] [W₁.IsElliptic] (D : VariableChange K) (hD : D • W₁ = W₂) :
    ∃ C : VariableChange (IsLocalRing.ResidueField R), C • W₁.reduction R = W₂.reduction R := by
  obtain ⟨C, -, hC⟩ :=
    VariableChange.exists_baseChange_eq_and_smul_integralModel_eq_of_isMinimal_smul R D hD
  exact ⟨C.map (IsLocalRing.residue R), by rw [reduction, reduction, ← hC, map_variableChange]⟩

end WeierstrassCurve

/-! ## From Tau Ceti: the curve `y² = x³ − x` -/

open WeierstrassCurve

namespace CMPoints.CurveX3SubX

/-- The Weierstrass curve `y² = x³ - x`. -/
def curve (R : Type*) [CommRing R] : WeierstrassCurve R := ⟨0, 0, 0, -1, 0⟩

section Coefficients

variable (R : Type*) [CommRing R]

/-- The coefficient `a₁` of `y² = x³ - x` is `0`. -/
@[simp]
theorem curve_a₁ : (curve R).a₁ = 0 :=
  (rfl)

/-- The coefficient `a₂` of `y² = x³ - x` is `0`. -/
@[simp]
theorem curve_a₂ : (curve R).a₂ = 0 :=
  (rfl)

/-- The coefficient `a₃` of `y² = x³ - x` is `0`. -/
@[simp]
theorem curve_a₃ : (curve R).a₃ = 0 :=
  (rfl)

/-- The coefficient `a₄` of `y² = x³ - x` is `-1`. -/
@[simp]
theorem curve_a₄ : (curve R).a₄ = -1 :=
  (rfl)

/-- The coefficient `a₆` of `y² = x³ - x` is `0`. -/
@[simp]
theorem curve_a₆ : (curve R).a₆ = 0 :=
  (rfl)

end Coefficients

/-- The discriminant of `y² = x³ - x` is `64`. -/
@[simp]
theorem Δ_curve (R : Type*) [CommRing R] : (curve R).Δ = 64 := by
  simp only [Δ, b₂, b₄, b₆, b₈, curve_a₁, curve_a₂, curve_a₃, curve_a₄, curve_a₆]
  ring

/-- `y² = x³ - x` is defined over `ℤ`, so it is preserved by every ring homomorphism. -/
@[simp]
theorem map_curve {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (curve R).map f = curve S := by
  ext <;> simp

/-- The affine points of `y² = x³ - x` are the solutions of `y² = x³ - x`. -/
@[simp]
theorem equation_iff {R : Type*} [CommRing R] (x y : R) :
    (curve R).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - x := by
  rw [Affine.equation_iff]
  simp only [curve_a₁, curve_a₂, curve_a₃, curve_a₄, curve_a₆]
  constructor <;> intro h <;> linear_combination h

end CMPoints.CurveX3SubX
