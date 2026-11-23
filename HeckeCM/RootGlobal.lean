import HeckeCM.RootTwo
import HeckeCM.FunctionalEqCurve
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_eq_one_of_hasConductorExponentAt_zero
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_ne_one

/-!
# The sign of the functional equation of `y² = x³ − x` is `+1`

* `addCharLevel_psiLocal_of_ne`: outside 2 the level of the standard additive
  character is 0;
* `stdRootNumberAt_cmChar_of_ne`: outside 2 the local root number of
  `cmChar` is 1;
* `heckeRootNumber_cmChar`: the global root number is `i · (−i) = 1`;
* `heckeConductor_cmChar`: the conductor is 32;
* `functional_equation_curve_one`: `Λ(s) = 32^{1−s} Λ(2 − s)` for the Mathlib
  L-series of `y² = x³ − x`.
-/

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open NumberField.AdelicLevel AutomorphicForm NumberField.TateGlobal
open NumberField.StandardAddChar LanglandsTunnell.TateLocal
open LanglandsTunnell LanglandsTunnell.HeckeTate
open scoped Classical

namespace CMPoints

lemma not_dvd_two_mul {a b : ℤ} (hab : IsPrimaryPair a b) (hN : a ^ 2 + b ^ 2 ≠ 1) :
    ¬ (a ^ 2 + b ^ 2) ∣ 2 * a := by
  intro hdvd
  obtain ⟨a', ha'⟩ : ∃ a', a = 2 * a' + 1 := ⟨a / 2, by unfold IsPrimaryPair at hab; omega⟩
  obtain ⟨b', hb'⟩ : ∃ b', b = 2 * b' := ⟨b / 2, by unfold IsPrimaryPair at hab; omega⟩
  have hcop : IsCoprime (a ^ 2 + b ^ 2) 2 :=
    ⟨1, -(2 * a' ^ 2 + 2 * a' + 2 * b' ^ 2), by rw [ha', hb']; ring⟩
  have ha0 : a ≠ 0 := by omega
  have hpos : 0 < a ^ 2 + b ^ 2 := by positivity
  obtain ⟨N, hNe⟩ : ∃ N, N = a ^ 2 + b ^ 2 := ⟨_, rfl⟩
  rw [← hNe] at hcop hpos hN hdvd
  obtain ⟨m, hm⟩ := hcop.dvd_of_dvd_mul_left hdvd
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact ha0 hm
  have hm2 : 1 ≤ m ^ 2 := by
    have := pow_pos (abs_pos.2 hm0) 2
    rw [sq_abs] at this
    omega
  have hsq : a ^ 2 = N ^ 2 * m ^ 2 := by
    rw [hm]
    ring
  have h1 : N ^ 2 ≤ N := by nlinarith [sq_nonneg b, sq_nonneg N]
  have h2 : N ≤ 1 := by nlinarith
  omega

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

local notation "𝔸" => AdeleRing (𝓞 K) K

/-- The trace of the inverse of the primary generator `a + b i`. -/
lemma trace_inv_gaussOf {a b : ℤ} (hN : (a ^ 2 + b ^ 2 : ℤ) ≠ 0) :
    Algebra.trace ℚ K (algebraMap (𝓞 K) K (gaussOf K a b))⁻¹ =
      (1 / ((a ^ 2 + b ^ 2 : ℤ) : ℚ)) * (2 * a) := by
  have hprod : gaussOf K a b * gaussOf K a (-b) = ((a ^ 2 + b ^ 2 : ℤ) : 𝓞 K) := by
    unfold gaussOf
    push_cast
    linear_combination (-(b : 𝓞 K) ^ 2) * gaussI_sq K
  have hK : algebraMap (𝓞 K) K (gaussOf K a b) * algebraMap (𝓞 K) K (gaussOf K a (-b)) =
      ((a ^ 2 + b ^ 2 : ℤ) : K) := by
    rw [← map_mul, hprod, map_intCast]
  have hNK : ((a ^ 2 + b ^ 2 : ℤ) : K) ≠ 0 := by exact_mod_cast hN
  have hy : (algebraMap (𝓞 K) K (gaussOf K a b))⁻¹ =
      (1 / ((a ^ 2 + b ^ 2 : ℤ) : ℚ)) • algebraMap (𝓞 K) K (gaussOf K a (-b)) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [Algebra.smul_def, mul_left_comm, hK, map_div₀, map_one, map_intCast, one_div,
      inv_mul_cancel₀ hNK]
  rw [hy, map_smul, trace_gaussOf, smul_eq_mul]

/-- **Outside 2 the level of the standard additive character is 0.** -/
theorem addCharLevel_psiLocal_of_ne {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ placeTwo K) :
    addCharLevel (psiLocal K w) = 0 := by
  have h2w : (2 : 𝓞 K) ∉ w.asIdeal := fun h => hw (eq_placeTwo_of_two_mem h)
  obtain ⟨a, b, hab, hg, hspan⟩ := gen_spec h2w
  have hN1 : a ^ 2 + b ^ 2 ≠ 1 := fun h => by
    have hu : IsUnit (gaussOf K a b) := (isUnit_coords_iff a b).2 h
    exact w.isPrime.ne_top (hspan ▸ Ideal.span_singleton_eq_top.2 hu)
  have hN0 : (a ^ 2 + b ^ 2 : ℤ) ≠ 0 := by
    have : a ≠ 0 := by unfold IsPrimaryPair at hab; omega
    positivity
  rw [addCharLevel_def]
  refine IsGreatest.csSup_eq ⟨fun x hx => psiLocal_eq_one_of_mem_integers K w x ?_, fun n hn => ?_⟩
  · rw [mem_adicCompletionIntegers]
    have hx' : Valued.v x ≤ exp (0 : ℤ) := hx
    rwa [exp_zero] at hx'
  · by_contra hlt
    have hval : Valued.v (algebraMap K (w.adicCompletion K) (genK K w)⁻¹) ≤ exp n := by
      rw [valued_algebraMap, map_inv₀, valuation_genK_self, ← exp_neg, neg_neg, exp_le_exp]
      omega
    have h1 := hn _ hval
    rw [psiLocal_algebraMap_of_integral_away K w _ (fun w' hw' => by
      rw [map_inv₀, valuation_genK_of_ne hw'.symm, inv_one])] at h1
    have hgK : genK K w = algebraMap (𝓞 K) K (gaussOf K a b) := by
      unfold genK
      rw [hg]
    rw [hgK, trace_inv_gaussOf hN0, Complex.exp_eq_one_iff] at h1
    obtain ⟨k, hk⟩ := h1
    have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
    have h0 : (2 * (Real.pi : ℂ) * Complex.I) *
        ((((1 / ((a ^ 2 + b ^ 2 : ℤ) : ℚ)) * (2 * a) + (k : ℚ) : ℚ)) : ℂ) = 0 := by
      push_cast
      push_cast at hk
      linear_combination (-1) * hk
    have h3 : ((((1 / ((a ^ 2 + b ^ 2 : ℤ) : ℚ)) * (2 * a) + (k : ℚ) : ℚ)) : ℂ) = 0 :=
      (mul_eq_zero.1 h0).resolve_left h2pi
    have h4 : (1 / ((a ^ 2 + b ^ 2 : ℤ) : ℚ)) * (2 * a) + (k : ℚ) = 0 := by exact_mod_cast h3
    have hNQ : (((a ^ 2 + b ^ 2 : ℤ)) : ℚ) ≠ 0 := by exact_mod_cast hN0
    have h5 : (2 * a : ℚ) = ((a ^ 2 + b ^ 2 : ℤ) : ℚ) * (-k) := by
      field_simp at h4
      linear_combination h4
    have h6 : 2 * a = (a ^ 2 + b ^ 2) * (-k) := by exact_mod_cast h5
    exact not_dvd_two_mul hab hN1 ⟨-k, h6⟩

lemma hasConductorExponentAt_cmChar_of_ne {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ placeTwo K) :
    HasConductorExponentAt K w (localChar (cmChar K) w) 0 :=
  ⟨fun u hu => cmChar_localUnit_of_ne hw u hu.1, fun m hm => absurd hm (Nat.not_lt_zero m)⟩

/-- **Outside 2 the local root number of `cmChar` is 1.** -/
theorem stdRootNumberAt_cmChar_of_ne {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ placeTwo K) :
    stdRootNumberAt K w (localChar (cmChar K) w) = 1 :=
  stdRootNumberAt_eq_one_of_hasConductorExponentAt_zero K w _
    (hasConductorExponentAt_cmChar_of_ne hw)
    (isUnitaryChar_cmChar K _) (addCharLevel_psiLocal_of_ne hw) (psiLocal_ne_one K w)

/-- **The conductor of `cmChar` is 32.** -/
theorem heckeConductor_cmChar : heckeConductor K (cmChar K) = 32 := by
  unfold heckeConductor
  refine (finprod_eq_single _ (placeTwo K) fun w hw => ?_).trans ?_
  · unfold LanglandsTunnell.Converse.pinnedExp
    rw [conductorExponentAt_eq_of_hasConductorExponentAt _ _
      (hasConductorExponentAt_cmChar_of_ne hw), addCharLevel_psiLocal_of_ne hw]
    simp
  · unfold LanglandsTunnell.Converse.pinnedExp
    rw [conductorExponentAt_eq_of_hasConductorExponentAt _ _ hasConductorExponentAt_cmChar_two,
      addCharLevel_psiLocal_placeTwo, absNorm_placeTwo]
    norm_num

/-- **The global root number of `cmChar` is `+1`.** -/
theorem heckeRootNumber_cmChar :
    heckeRootNumber K (cmChar K) (fun _ _ => 0) (fun _ _ => -1) = 1 := by
  unfold heckeRootNumber
  haveI : IsEmpty {w : InfinitePlace K // w.IsReal} := ⟨fun w => not_isReal_infinitePlace w.1 w.2⟩
  have hfin : ∏ᶠ v : HeightOneSpectrum (𝓞 K), stdRootNumberAt K v (localChar (cmChar K) v) =
      -Complex.I := by
    rw [finprod_eq_single _ (placeTwo K) fun w hw => stdRootNumberAt_cmChar_of_ne hw]
    exact stdRootNumberAt_cmChar_two
  have hc : (archPlace K).IsComplex :=
    InfinitePlace.not_isReal_iff_isComplex.1 (not_isReal_infinitePlace _)
  rw [hfin, Finset.univ_eq_empty, Finset.prod_empty,
    Fintype.prod_subsingleton _ (⟨archPlace K, hc⟩ : {w : InfinitePlace K // w.IsComplex})]
  simp

end CMPoints

/-- **Functional equation of the Mathlib L-series of `y² = x³ − x`, with sign
`+1` and conductor 32.** -/
theorem CMPoints.functional_equation_curve_one :
    ∃ F Λ : ℂ → ℂ, Differentiable ℂ F ∧ Differentiable ℂ Λ ∧
      (∀ s : ℂ, 3 / 2 < s.re →
        F s = (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ).LSeries s) ∧
      (∀ s : ℂ, F s = (Complex.Gammaℂ s)⁻¹ * Λ s) ∧
      (∀ s : ℂ, Λ s = (32 : ℂ) ^ (1 - s) * Λ (2 - s)) := by
  haveI : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  have hodd : (1 : ℕ) % 2 = 1 := rfl
  have hsq : Squarefree (1 : ℕ) := squarefree_one
  have hd : (1 : ℕ) ≠ 0 := one_ne_zero
  have hchar : CMPoints.cmCharTw (CyclotomicField 4 ℚ) hodd hsq hd =
      CMPoints.cmChar (CyclotomicField 4 ℚ) := by
    refine MonoidHom.ext fun x => ?_
    rw [CMPoints.cmCharTw_apply, CMPoints.twC_eq_one_of_isClose_one hodd hsq hd (fun v hv =>
      absurd ((Ideal.eq_top_iff_one _).2 (by simpa using hv)) v.isPrime.ne_top), mul_one]
  obtain ⟨Λ, hΛ, hval, hfe, hN, -⟩ := CMPoints.functional_equation_of_datum
    (CMPoints.cmCharTw (CyclotomicField 4 ℚ) hodd hsq hd)
    (CMPoints.continuous_cmCharTw hodd hsq hd)
    (CMPoints.isUnitaryChar_cmCharTw hodd hsq hd) (CMPoints.isIdeleClassChar_cmCharTw hodd hsq hd)
    (CMPoints.cmCharTw_x₀_ne_one hodd hsq hd) (CMPoints.cmCharTw_archUnitHom hodd hsq hd)
    (CMPoints.isGenEulerDatum_cmCharTw hodd hsq hd) ⟨((1 : ℕ) : ℤ), by norm_num⟩
    (fun p _ h => CMPoints.twCoeff_eq_zero _ p h) (CMPoints.twCoeff_sq_le _)
  rw [← CMPoints.cmCoeffTw_eq_gCoeff] at hval
  simp only [hchar, CMPoints.heckeRootNumber_cmChar, CMPoints.heckeConductor_cmChar, one_mul,
    Complex.ofReal_ofNat] at hfe
  refine ⟨fun s => (Complex.Gammaℂ s)⁻¹ * Λ s, Λ, Complex.differentiable_Gammaℂ_inv.mul hΛ,
    hΛ, fun s hs => ?_, fun s => rfl, hfe⟩
  show (Complex.Gammaℂ s)⁻¹ * Λ s = _
  rw [hval s hs, inv_mul_cancel_left₀ (CMPoints.Gammaℂ_ne_zero_of_re_pos (by linarith))]
  have e1 : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve ℚ) =
      CMPoints.curveD ℚ ((((1 : ℕ) : ℤ)) : ℚ) := by
    simp [CMPoints.curveD]
  have hoddZ : Odd (((1 : ℕ) : ℤ)) := by norm_num
  have hsqZ : Squarefree (((1 : ℕ) : ℤ)) := Int.squarefree_natCast.2 hsq
  rw [e1, WeierstrassCurve.LSeries]
  congr 1
  funext n
  show ((CMPoints.cmCoeffTw (((1 : ℕ) : ℤ)) n : ℤ) : ℂ) =
    (((CMPoints.curveD ℚ ((((1 : ℕ) : ℤ)) : ℚ)).LFunction n : ℤ) : ℂ)
  rw [CMPoints.LFunction_curveD_eq_cmCoeffTw_of_odd_squarefree hoddZ hsqZ n]
