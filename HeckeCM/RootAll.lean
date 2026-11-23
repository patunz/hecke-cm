import HeckeCM.RootEven

/-!
# Final statements: sign, conductor, vanishing

* `heckeConductor_cmCharTw`, `heckeConductor_cmCharEv`: the conductors are
  `32 d²` (for `d` odd) and `64 e²` (for `d = 2e`);
* `CMPoints.functional_equation_curveD_odd`, `…_two_mul`: functional equation
  with explicit sign and conductor;
* `CMPoints.vanishing_curveD_all`: vanishing at `s = 1` for
  `d ≡ 5, 6, 7 (mod 8)` squarefree;
* `CMPoints.vanishing_curveD_sq_mul`: the same for `d · m²`.
-/

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open NumberField.AdelicLevel AutomorphicForm NumberField.TateGlobal
open NumberField.StandardAddChar LanglandsTunnell.TateLocal
open LanglandsTunnell LanglandsTunnell.HeckeTate
open scoped Classical

namespace CMPoints

lemma curve_eq {x y : ℚ} (h : x = y) :
    (⟨0, 0, 0, -x ^ 2, 0⟩ : WeierstrassCurve ℚ) = curveD ℚ y := by
  rw [h]
  rfl

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

local notation "𝔸" => AdeleRing (𝓞 K) K

/-- The product with a character trivial on the units does not change the exponent of the
conductor. -/
lemma hasConductorExponentAt_mul_unram {v : HeightOneSpectrum (𝓞 K)}
    {χ ω : (v.adicCompletion K)ˣ →* ℂˣ} {c : ℕ} (h : HasConductorExponentAt K v χ c)
    (hω : ∀ u ∈ higherUnitsAt K v 0, ω u = 1) : HasConductorExponentAt K v (χ * ω) c := by
  refine ⟨fun u hu => ?_, fun m hm => ?_⟩
  · rw [MonoidHom.mul_apply, h.1 u hu, hω u ⟨hu.1, Or.inl rfl⟩, one_mul]
  · obtain ⟨u, hu, hne⟩ := h.2 m hm
    refine ⟨u, hu, ?_⟩
    rw [MonoidHom.mul_apply, hω u ⟨hu.1, Or.inl rfl⟩, mul_one]
    exact hne

/-- **The conductor**, given the local exponents. -/
theorem heckeConductor_eq {d : ℕ} (hodd : d % 2 = 1) (hsq : Squarefree d) (hd : d ≠ 0)
    (χ : (𝔸)ˣ →* ℂˣ) {c₂ : ℕ}
    (h2 : HasConductorExponentAt K (placeTwo K) (localChar χ (placeTwo K)) c₂)
    (hmem : ∀ v : HeightOneSpectrum (𝓞 K), ((d : ℕ) : 𝓞 K) ∈ v.asIdeal →
      HasConductorExponentAt K v (localChar χ v) 1)
    (hun : ∀ v : HeightOneSpectrum (𝓞 K), v ≠ placeTwo K → ((d : ℕ) : 𝓞 K) ∉ v.asIdeal →
      HasConductorExponentAt K v (localChar χ v) 0) :
    heckeConductor K χ = (2 : ℝ) ^ (c₂ + 2) * (d : ℝ) ^ 2 := by
  unfold heckeConductor
  have hpin1 : ∀ v : HeightOneSpectrum (𝓞 K), ((d : ℕ) : 𝓞 K) ∈ v.asIdeal →
      LanglandsTunnell.Converse.pinnedExp K χ v = 1 := by
    intro v hv
    have hv2 : v ≠ placeTwo K := by
      rintro rfl
      exact natCast_notMem_placeTwo hodd hv
    unfold LanglandsTunnell.Converse.pinnedExp
    rw [conductorExponentAt_eq_of_hasConductorExponentAt _ _ (hmem v hv),
      addCharLevel_psiLocal_of_ne hv2]
    norm_num
  rw [finprod_eq_of_fibres hodd hd _ (fun v hv2 hw => by
      unfold LanglandsTunnell.Converse.pinnedExp
      rw [conductorExponentAt_eq_of_hasConductorExponentAt _ _ (hun v hv2 hw),
        addCharLevel_psiLocal_of_ne hv2]
      simp) (fun q => (q : ℝ) ^ 2) (fun q hq hqd => ?_)]
  · unfold LanglandsTunnell.Converse.pinnedExp
    rw [conductorExponentAt_eq_of_hasConductorExponentAt _ _ h2, addCharLevel_psiLocal_placeTwo,
      absNorm_placeTwo, Finset.prod_pow, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
    norm_cast
  · obtain ⟨m, rfl⟩ := hqd
    haveI := Fact.mk hq
    have hq2 : q % 2 = 1 := Nat.odd_iff.1 (Nat.odd_mul.1 (Nat.odd_iff.2 hodd)).1
    have hqdvd : q ∣ 2 * (q * m) := ⟨2 * m, by ring⟩
    have hmemd : ∀ u : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∈ u.asIdeal →
        (((q * m : ℕ)) : 𝓞 K) ∈ u.asIdeal := fun u hu => by
      rw [Nat.cast_mul]
      exact u.asIdeal.mul_mem_right _ hu
    rcases (by omega : q % 4 = 3 ∨ q % 4 = 1) with h3 | h1
    · obtain ⟨v, hmemv, hN, -, -⟩ := exists_primary_inert (K := K) q h3
      have hf : (badPlaces K hd).filter (fun u => ((under K u : ℕ)) = q) = {v} := by
        ext u
        rw [Finset.mem_filter, Finset.mem_singleton, under_val_eq_iff u hq, hmemv u]
        constructor
        · exact fun h => h.2
        · rintro rfl
          exact ⟨mem_badPlaces_of_dvd hd hqdvd ((hmemv u).2 rfl), rfl⟩
      rw [hf, Finset.prod_singleton, hpin1 v (hmemd v ((hmemv v).2 rfl)), hN, zpow_one]
      norm_cast
    · obtain ⟨v, w, a, b, hvw, hmemv, hNv, hNw, -, -, -, -, -⟩ :=
        exists_primary_split (K := K) q h1
      have hf : (badPlaces K hd).filter (fun u => ((under K u : ℕ)) = q) = {v, w} := by
        ext u
        rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, under_val_eq_iff u hq,
          hmemv u]
        constructor
        · exact fun h => h.2
        · intro h
          exact ⟨mem_badPlaces_of_dvd hd hqdvd ((hmemv u).2 h), h⟩
      rw [hf, Finset.prod_pair hvw, hpin1 v (hmemd v ((hmemv v).2 (Or.inl rfl))),
        hpin1 w (hmemd w ((hmemv w).2 (Or.inr rfl))), hNv, hNw, zpow_one]
      ring

variable {d : ℕ} (hodd : d % 2 = 1) (hsq : Squarefree d) (hd : d ≠ 0)
include hodd hsq

/-- **The conductor of the character of `y² = x³ − d²x`, `d` odd, is `32 d²`.** -/
theorem heckeConductor_cmCharTw :
    heckeConductor K (cmCharTw K hodd hsq hd) = 32 * (d : ℝ) ^ 2 := by
  have hw := natCast_notMem_placeTwo (K := K) hodd
  have hloc : localChar (cmCharTw K hodd hsq hd) (placeTwo K) =
      localChar (cmChar K) (placeTwo K) * localChar (twC K hodd hsq hd) (placeTwo K) :=
    MonoidHom.ext fun t => rfl
  have h2 : HasConductorExponentAt K (placeTwo K)
      (localChar (cmCharTw K hodd hsq hd) (placeTwo K)) 3 := by
    rw [hloc]
    exact hasConductorExponentAt_mul_unram hasConductorExponentAt_cmChar_two
      (fun u hu => twC_locIdele_unit hodd hsq hd hw u hu.1)
  rw [heckeConductor_eq hodd hsq hd _ h2
    (fun v hv => hasConductorExponentAt_cmCharTw_of_mem hodd hsq hd hv)
    (fun v hv2 hv => ⟨fun u hu => by
        show cmCharTw K hodd hsq hd (locIdele K v u) = 1
        rw [cmCharTw_apply, cmChar_localUnit_of_ne hv2 u hu.1,
          twC_locIdele_unit hodd hsq hd hv u hu.1, one_mul],
      fun m hm => absurd hm (Nat.not_lt_zero m)⟩)]
  norm_num

/-- **The conductor of the character of `y² = x³ − (2e)²x`, `e` odd, is `64 e²`.** -/
theorem heckeConductor_cmCharEv :
    heckeConductor K (cmCharEv K hodd hsq hd) = 64 * (d : ℝ) ^ 2 := by
  have hloc : ∀ v : HeightOneSpectrum (𝓞 K), localChar (cmCharEv K hodd hsq hd) v =
      localChar (cmCharTw K hodd hsq hd) v * localChar (tw8C K) v :=
    fun v => MonoidHom.ext fun t => rfl
  rw [heckeConductor_eq hodd hsq hd _ (hasConductorExponentAt_cmCharEv_two hodd hsq hd)
    (fun v hv => by
      have hv2 : v ≠ placeTwo K := by
        rintro rfl
        exact natCast_notMem_placeTwo hodd hv
      rw [hloc v]
      exact hasConductorExponentAt_mul_unram
        (hasConductorExponentAt_cmCharTw_of_mem hodd hsq hd hv)
        (fun u hu => tw8C_locIdele_unit hv2 u hu.1))
    (fun v hv2 hv => ⟨fun u hu => by
        show cmCharEv K hodd hsq hd (locIdele K v u) = 1
        rw [cmCharEv_apply, cmCharTw_apply, cmChar_localUnit_of_ne hv2 u hu.1,
          twC_locIdele_unit hodd hsq hd hv u hu.1, tw8C_locIdele_unit hv2 u hu.1, one_mul,
          one_mul],
      fun m hm => absurd hm (Nat.not_lt_zero m)⟩)]
  norm_num

end CMPoints

/-- **Explicit functional equation for `d` odd and squarefree**: sign
`χ₈(d)·χ₄(d)`, conductor `32 d²`. -/
theorem CMPoints.functional_equation_curveD_odd {d : ℕ} (hodd : d % 2 = 1) (hsq : Squarefree d) :
    ∃ F Λ : ℂ → ℂ, Differentiable ℂ F ∧ Differentiable ℂ Λ ∧
      (∀ s : ℂ, 3 / 2 < s.re →
        F s = (⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ).LSeries s) ∧
      (∀ s : ℂ, F s = (Complex.Gammaℂ s)⁻¹ * Λ s) ∧
      (∀ s : ℂ, Λ s = ((ZMod.χ₈ (d : ZMod 8) * ZMod.χ₄ (d : ZMod 4) : ℤ) : ℂ) *
        (32 * (d : ℂ) ^ 2) ^ (1 - s) * Λ (2 - s)) := by
  haveI : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  have hd : d ≠ 0 := by
    rintro rfl
    omega
  obtain ⟨Λ, hΛ, hval, hfe, hN, -⟩ := CMPoints.functional_equation_of_datum
    (CMPoints.cmCharTw (CyclotomicField 4 ℚ) hodd hsq hd)
    (CMPoints.continuous_cmCharTw hodd hsq hd)
    (CMPoints.isUnitaryChar_cmCharTw hodd hsq hd) (CMPoints.isIdeleClassChar_cmCharTw hodd hsq hd)
    (CMPoints.cmCharTw_x₀_ne_one hodd hsq hd) (CMPoints.cmCharTw_archUnitHom hodd hsq hd)
    (CMPoints.isGenEulerDatum_cmCharTw hodd hsq hd) ⟨(d : ℤ), by norm_num⟩
    (fun p _ h => CMPoints.twCoeff_eq_zero _ p h) (CMPoints.twCoeff_sq_le _)
  rw [← CMPoints.cmCoeffTw_eq_gCoeff] at hval
  have hoddZ : Odd (d : ℤ) := by exact_mod_cast Nat.odd_iff.2 hodd
  have hsqZ : Squarefree (d : ℤ) := Int.squarefree_natCast.2 hsq
  refine ⟨fun s => (Complex.Gammaℂ s)⁻¹ * Λ s, Λ, Complex.differentiable_Gammaℂ_inv.mul hΛ, hΛ,
    fun s hs => ?_, fun s => rfl, fun s => ?_⟩
  · show (Complex.Gammaℂ s)⁻¹ * Λ s = _
    rw [hval s hs, inv_mul_cancel_left₀ (CMPoints.Gammaℂ_ne_zero_of_re_pos (by linarith)),
      CMPoints.curve_eq (Int.cast_natCast d).symm, WeierstrassCurve.LSeries]
    congr 1
    funext n
    show ((CMPoints.cmCoeffTw (d : ℤ) n : ℤ) : ℂ) =
      (((CMPoints.curveD ℚ ((d : ℤ) : ℚ)).LFunction n : ℤ) : ℂ)
    rw [CMPoints.LFunction_curveD_eq_cmCoeffTw_of_odd_squarefree hoddZ hsqZ n]
  · have h := hfe s
    rw [CMPoints.heckeRootNumber_cmCharTw hodd hsq hd, CMPoints.heckeConductor_cmCharTw hodd hsq hd]
      at h
    rw [h]
    push_cast
    rfl

/-- **Explicit functional equation for `d = 2e`, `e` odd and squarefree**:
sign `χ₄(e)`, conductor `64 e² = 16 d²`. -/
theorem CMPoints.functional_equation_curveD_two_mul {e : ℕ} (hodd : e % 2 = 1)
    (hsq : Squarefree e) :
    ∃ F Λ : ℂ → ℂ, Differentiable ℂ F ∧ Differentiable ℂ Λ ∧
      (∀ s : ℂ, 3 / 2 < s.re →
        F s = (⟨0, 0, 0, -((2 * e : ℕ) : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ).LSeries s) ∧
      (∀ s : ℂ, F s = (Complex.Gammaℂ s)⁻¹ * Λ s) ∧
      (∀ s : ℂ, Λ s = ((ZMod.χ₄ (e : ZMod 4) : ℤ) : ℂ) *
        (64 * (e : ℂ) ^ 2) ^ (1 - s) * Λ (2 - s)) := by
  haveI : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  have he : e ≠ 0 := by
    rintro rfl
    omega
  obtain ⟨Λ, hΛ, hval, hfe, hN, -⟩ := CMPoints.functional_equation_of_datum
    (CMPoints.cmCharEv (CyclotomicField 4 ℚ) hodd hsq he) (CMPoints.continuous_cmCharEv hodd hsq he)
    (CMPoints.isUnitaryChar_cmCharEv hodd hsq he) (CMPoints.isIdeleClassChar_cmCharEv hodd hsq he)
    (CMPoints.cmCharEv_locIdele_two_ne_one hodd hsq he) (CMPoints.cmCharEv_archUnitHom hodd hsq he)
    (CMPoints.isGenEulerDatum_cmCharEv hodd hsq he) ⟨2 * (e : ℤ), by norm_num⟩
    (fun p _ h => CMPoints.twCoeff_eq_zero _ p h) (CMPoints.twCoeff_sq_le _)
  rw [← CMPoints.cmCoeffTw_eq_gCoeff] at hval
  have hoddZ : Odd (e : ℤ) := by exact_mod_cast Nat.odd_iff.2 hodd
  have hsqZ : Squarefree (e : ℤ) := Int.squarefree_natCast.2 hsq
  refine ⟨fun s => (Complex.Gammaℂ s)⁻¹ * Λ s, Λ, Complex.differentiable_Gammaℂ_inv.mul hΛ, hΛ,
    fun s hs => ?_, fun s => rfl, fun s => ?_⟩
  · show (Complex.Gammaℂ s)⁻¹ * Λ s = _
    rw [hval s hs, inv_mul_cancel_left₀ (CMPoints.Gammaℂ_ne_zero_of_re_pos (by linarith)),
      CMPoints.curve_eq (y := (((2 * (e : ℤ) : ℤ)) : ℚ)) (by push_cast; ring),
      WeierstrassCurve.LSeries]
    congr 1
    funext n
    show ((CMPoints.cmCoeffTw (2 * (e : ℤ)) n : ℤ) : ℂ) =
      (((CMPoints.curveD ℚ (((2 * (e : ℤ) : ℤ)) : ℚ)).LFunction n : ℤ) : ℂ)
    rw [CMPoints.LFunction_curveD_two_mul_eq_cmCoeffTw hoddZ hsqZ n]
  · have h := hfe s
    rw [CMPoints.heckeRootNumber_cmCharEv hodd hsq he, CMPoints.heckeConductor_cmCharEv hodd hsq he]
      at h
    rw [h]
    push_cast
    rfl

/-- **Vanishing at `s = 1`.** For `d ≡ 5, 6, 7 (mod 8)` squarefree, every
entire continuation of the Mathlib L-series of `y² = x³ − d²x` vanishes at
`s = 1`. -/
theorem CMPoints.vanishing_curveD_all {d : ℕ} (hsq : Squarefree d)
    (h8 : d % 8 = 5 ∨ d % 8 = 6 ∨ d % 8 = 7) (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hFval : ∀ s : ℂ, 3 / 2 < s.re →
      F s = (⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ).LSeries s) :
    F 1 = 0 := by
  rcases h8 with h | h | h
  · exact CMPoints.vanishing_curveD hsq (Or.inl h) F hF hFval
  · obtain ⟨e, rfl⟩ : ∃ e, d = 2 * e := ⟨d / 2, by omega⟩
    refine CMPoints.vanishing_curveD_two_mul hsq.of_mul_right (by omega) F hF fun s hs => ?_
    rw [hFval s hs, CMPoints.curve_eq (y := (((2 * (e : ℤ) : ℤ)) : ℚ)) (by push_cast; ring)]
  · exact CMPoints.vanishing_curveD hsq (Or.inr h) F hF hFval

/-- **Vanishing at `s = 1`, with squares.** For `d ≡ 5, 6, 7 (mod 8)` squarefree
and `m ≠ 0`, every entire continuation of the Mathlib L-series of
`y² = x³ − (d m²)² x` vanishes at `s = 1`. -/
theorem CMPoints.vanishing_curveD_sq_mul {d m : ℕ} (hsq : Squarefree d)
    (h8 : d % 8 = 5 ∨ d % 8 = 6 ∨ d % 8 = 7) (hm : m ≠ 0) (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hFval : ∀ s : ℂ, 3 / 2 < s.re →
      F s = (⟨0, 0, 0, -((d * m ^ 2 : ℕ) : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ).LSeries s) :
    F 1 = 0 := by
  have hmZ : (m : ℤ) ≠ 0 := by exact_mod_cast hm
  refine CMPoints.vanishing_curveD_all hsq h8 F hF fun s hs => ?_
  rw [hFval s hs]
  rcases (by omega : d % 2 = 1 ∨ d % 2 = 0) with hpar | hpar
  · have hoddZ : Odd (d : ℤ) := by exact_mod_cast Nat.odd_iff.2 hpar
    have hsqZ : Squarefree (d : ℤ) := Int.squarefree_natCast.2 hsq
    rw [CMPoints.curve_eq (y := ((((d : ℤ) * (m : ℤ) ^ 2 : ℤ)) : ℚ)) (by push_cast; ring),
      CMPoints.curve_eq (Int.cast_natCast d).symm, WeierstrassCurve.LSeries,
      WeierstrassCurve.LSeries, CMPoints.LFunction_curveD_mul_sq hoddZ hsqZ hmZ]
  · obtain ⟨e, rfl⟩ : ∃ e, d = 2 * e := ⟨d / 2, by omega⟩
    have hesq : Squarefree e := hsq.of_mul_right
    have heodd : e % 2 = 1 := by omega
    have heoddZ : Odd (e : ℤ) := by exact_mod_cast Nat.odd_iff.2 heodd
    have hesqZ : Squarefree (e : ℤ) := Int.squarefree_natCast.2 hesq
    rw [CMPoints.curve_eq (y := (((2 * (e : ℤ) * (m : ℤ) ^ 2 : ℤ)) : ℚ)) (by push_cast; ring),
      CMPoints.curve_eq (x := ((2 * e : ℕ) : ℚ)) (y := (((2 * (e : ℤ) : ℤ)) : ℚ))
        (by push_cast; ring),
      WeierstrassCurve.LSeries, WeierstrassCurve.LSeries,
      CMPoints.LFunction_curveD_two_mul_sq heoddZ hesqZ hmZ]
