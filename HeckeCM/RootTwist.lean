import HeckeCM.RootPair

/-!
# The sign of the functional equation of `y² = x³ − d²x`, `d` odd and squarefree

* `stdRootNumberAt_cmCharTw_two`: at the place above 2 the local root number
  is `χ₈(d) · (−i)`;
* `stdRootNumberAt_cmCharTw_unram`: away from `2d` it is 1;
* `prod_fibre_cmCharTw`: above a prime `q` dividing `d` the product of the
  local root numbers is `χ₄(q)`;
* `heckeRootNumber_cmCharTw`: the global root number is `χ₈(d) · χ₄(d)`,
  that is `+1` for `d ≡ 1, 3 (mod 8)` and `−1` for `d ≡ 5, 7 (mod 8)`;
* `CMPoints.vanishing_curveD`: for squarefree `d ≡ 5, 7 (mod 8)`, every
  entire continuation of the Mathlib L-series of `y² = x³ − d²x` vanishes
  at `s = 1`.
-/

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open NumberField.AdelicLevel AutomorphicForm NumberField.TateGlobal
open NumberField.StandardAddChar LanglandsTunnell.TateLocal
open LanglandsTunnell LanglandsTunnell.HeckeTate
open scoped Classical

namespace CMPoints

lemma prod_χ₄_primeFactors {d : ℕ} (hsq : Squarefree d) :
    ∏ q ∈ d.primeFactors, ZMod.χ₄ (q : ZMod 4) = ZMod.χ₄ (d : ZMod 4) := by
  rw [← map_prod, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

local notation "𝔸" => AdeleRing (𝓞 K) K

section Bad

variable {d : ℕ} (hd : d ≠ 0)

variable (K) in
/-- The places containing `2d`. -/
def badPlaces : Finset (HeightOneSpectrum (𝓞 K)) :=
  (finite_setOf_natCast_mem (K := K) (d := 2 * d) (by omega)).toFinset

lemma mem_badPlaces (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ badPlaces K hd ↔ (((2 * d : ℕ)) : 𝓞 K) ∈ v.asIdeal := by
  unfold badPlaces
  rw [Set.Finite.mem_toFinset]
  rfl

lemma mem_badPlaces_of_dvd {v : HeightOneSpectrum (𝓞 K)} {q : ℕ} (hq : q ∣ 2 * d)
    (hv : ((q : ℕ) : 𝓞 K) ∈ v.asIdeal) : v ∈ badPlaces K hd := by
  rw [mem_badPlaces]
  obtain ⟨c, hc⟩ := hq
  have e : (((2 * d : ℕ)) : 𝓞 K) = ((q : ℕ) : 𝓞 K) * ((c : ℕ) : 𝓞 K) := by
    rw [hc, Nat.cast_mul]
  rw [e]
  exact v.asIdeal.mul_mem_right _ hv

omit hd in
lemma under_val_eq_iff (v : HeightOneSpectrum (𝓞 K)) {q : ℕ} (hq : q.Prime) :
    ((under K v : ℕ)) = q ↔ ((q : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  constructor
  · intro h
    exact (under_eq_iff K v ⟨q, hq⟩).1 (Nat.Primes.coe_nat_injective h)
  · intro h
    exact congrArg (fun r : Nat.Primes => (r : ℕ)) ((under_eq_iff K v ⟨q, hq⟩).2 h)

end Bad

variable {d : ℕ} (hodd : d % 2 = 1) (hsq : Squarefree d) (hd : d ≠ 0)
include hodd hsq

/-- **At the place above 2 the local root number is `χ₈(d) · (−i)`.** -/
theorem stdRootNumberAt_cmCharTw_two :
    stdRootNumberAt K (placeTwo K) (localChar (cmCharTw K hodd hsq hd) (placeTwo K)) =
      ((ZMod.χ₈ (d : ZMod 8) : ℤ) : ℂ) * -Complex.I := by
  have hw := natCast_notMem_placeTwo (K := K) hodd
  have hloc : localChar (cmCharTw K hodd hsq hd) (placeTwo K) =
      localChar (cmChar K) (placeTwo K) * localChar (twC K hodd hsq hd) (placeTwo K) :=
    MonoidHom.ext fun t => rfl
  have hω : HasConductorExponentAt K (placeTwo K)
      (localChar (twC K hodd hsq hd) (placeTwo K)) 0 :=
    ⟨fun u hu => twC_locIdele_unit hodd hsq hd hw u hu.1,
      fun m hm => absurd hm (Nat.not_lt_zero m)⟩
  have h := stdRootNumberAt_mul_of_hasConductorExponentAt_zero K (placeTwo K) _ _ 3
    hasConductorExponentAt_cmChar_two hω (isUnitaryChar_cmChar K _) (norm_twC hodd hsq hd _)
    (psiLocal_ne_one K _)
  have hval : ((localChar (twC K hodd hsq hd) (placeTwo K) (uniformizerUnit K (placeTwo K)) :
      ℂˣ) : ℂ) = ((ZMod.χ₈ (d : ZMod 8) : ℤ) : ℂ) := by
    show ((twC K hodd hsq hd (locIdele K (placeTwo K) (uniformizerUnit K (placeTwo K))) : ℂˣ) :
      ℂ) = _
    rw [twC_val, tw_locIdele_uniformizer hodd hsq hd hw _ (valued_uniformizerUnit K (placeTwo K)),
      gen_of_two_mem two_mem_placeTwo, tau, ← gaussOf_one_one, nrm_gaussOf,
      show ((1 : ℤ) ^ 2 + 1 ^ 2) = 2 by norm_num, jacobiSym.at_two (Nat.odd_iff.2 hodd)]
  have hsq' : (((ZMod.χ₈ (d : ZMod 8) : ℤ)) : ℂ) ^ 2 = 1 := by
    rw [ZMod.χ₈_nat_eq_if_mod_eight, if_neg (by omega)]
    split_ifs <;> norm_num
  have e5 : (((3 : ℕ) : ℤ) + 2) = ((5 : ℕ) : ℤ) := by norm_num
  rw [hloc, h, addCharLevel_psiLocal_placeTwo, stdRootNumberAt_cmChar_two, hval, e5, zpow_natCast]
  linear_combination (-Complex.I * ((((ZMod.χ₈ (d : ZMod 8) : ℤ)) : ℂ) ^ 3 +
    (((ZMod.χ₈ (d : ZMod 8) : ℤ)) : ℂ))) * hsq'

/-- **Away from `2d` the local root number is 1.** -/
theorem stdRootNumberAt_cmCharTw_unram {v : HeightOneSpectrum (𝓞 K)} (h2 : v ≠ placeTwo K)
    (hw : ((d : ℕ) : 𝓞 K) ∉ v.asIdeal) :
    stdRootNumberAt K v (localChar (cmCharTw K hodd hsq hd) v) = 1 :=
  stdRootNumberAt_eq_one_of_hasConductorExponentAt_zero K v _
    ⟨fun u hu => by
        show cmCharTw K hodd hsq hd (locIdele K v u) = 1
        rw [cmCharTw_apply, cmChar_localUnit_of_ne h2 u hu.1,
          twC_locIdele_unit hodd hsq hd hw u hu.1, one_mul],
      fun m hm => absurd hm (Nat.not_lt_zero m)⟩
    (isUnitaryChar_cmCharTw hodd hsq hd _) (addCharLevel_psiLocal_of_ne h2) (psiLocal_ne_one K v)

/-- Above 2 there is only `placeTwo`. -/
lemma prod_fibre_two :
    ∏ v ∈ (badPlaces K hd).filter (fun v => ((under K v : ℕ)) = 2),
        stdRootNumberAt K v (localChar (cmCharTw K hodd hsq hd) v) =
      ((ZMod.χ₈ (d : ZMod 8) : ℤ) : ℂ) * -Complex.I := by
  have hf : (badPlaces K hd).filter (fun v => ((under K v : ℕ)) = 2) = {placeTwo K} := by
    ext u
    rw [Finset.mem_filter, Finset.mem_singleton, under_val_eq_iff u Nat.prime_two]
    constructor
    · rintro ⟨-, h⟩
      exact eq_placeTwo_of_two_mem (by simpa using h)
    · rintro rfl
      have h2 : (((2 : ℕ)) : 𝓞 K) ∈ (placeTwo K).asIdeal := by simpa using two_mem_placeTwo (K := K)
      exact ⟨mem_badPlaces_of_dvd hd (dvd_mul_right 2 d) h2, h2⟩
  rw [hf, Finset.prod_singleton, stdRootNumberAt_cmCharTw_two hodd hsq hd]

/-- **Above a prime `q` dividing `d` the product of the local root numbers
is `χ₄(q)`.** -/
theorem prod_fibre_cmCharTw {q : ℕ} (hq : q.Prime) (hqd : q ∣ d) :
    ∏ v ∈ (badPlaces K hd).filter (fun v => ((under K v : ℕ)) = q),
        stdRootNumberAt K v (localChar (cmCharTw K hodd hsq hd) v) =
      ((ZMod.χ₄ (q : ZMod 4) : ℤ) : ℂ) := by
  obtain ⟨m, rfl⟩ := hqd
  haveI := Fact.mk hq
  have hq2 : q % 2 = 1 := Nat.odd_iff.1 (Nat.odd_mul.1 (Nat.odd_iff.2 hodd)).1
  have hqdvd : q ∣ 2 * (q * m) := ⟨2 * m, by ring⟩
  rcases (by omega : q % 4 = 3 ∨ q % 4 = 1) with h3 | h1
  · obtain ⟨v, hmem, hN, hprim, hv⟩ := exists_primary_inert (K := K) q h3
    have hf : (badPlaces K hd).filter (fun u => ((under K u : ℕ)) = q) = {v} := by
      ext u
      rw [Finset.mem_filter, Finset.mem_singleton, under_val_eq_iff u hq, hmem u]
      constructor
      · exact fun h => h.2
      · rintro rfl
        exact ⟨mem_badPlaces_of_dvd hd hqdvd ((hmem u).2 rfl), rfl⟩
    rw [hf, Finset.prod_singleton, stdRootNumberAt_cmCharTw_inert hv hodd hsq hd hmem h3 hN hprim,
      ZMod.χ₄_nat_three_mod_four h3]
    norm_num
  · obtain ⟨v, w, a, b, hvw, hmem, hNv, hNw, hab, hab', hn, hv, hw⟩ :=
      exists_primary_split (K := K) q h1
    have hf : (badPlaces K hd).filter (fun u => ((under K u : ℕ)) = q) = {v, w} := by
      ext u
      rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, under_val_eq_iff u hq,
        hmem u]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨mem_badPlaces_of_dvd hd hqdvd ((hmem u).2 h), h⟩
    rw [hf, Finset.prod_pair hvw,
      stdRootNumberAt_cmCharTw_split h1 hab hn hodd hsq hd hab' hv hw hNv hNw,
      ZMod.χ₄_nat_one_mod_four h1]
    norm_num

/-- The product of all the local root numbers. -/
theorem finprod_stdRootNumberAt_cmCharTw :
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), stdRootNumberAt K v (localChar (cmCharTw K hodd hsq hd) v) =
      ((ZMod.χ₈ (d : ZMod 8) : ℤ) : ℂ) * -Complex.I * ((ZMod.χ₄ (d : ZMod 4) : ℤ) : ℂ) := by
  have hsupp : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) =>
      stdRootNumberAt K v (localChar (cmCharTw K hodd hsq hd) v)) ⊆ ↑(badPlaces K hd) := by
    intro v hv
    by_contra hnot
    apply hv
    have hnot' : v ∉ badPlaces K hd := hnot
    refine stdRootNumberAt_cmCharTw_unram hodd hsq hd (fun h2 => hnot' ?_) (fun hw => hnot' ?_)
    · subst h2
      exact mem_badPlaces_of_dvd hd (dvd_mul_right 2 d) (by simpa using two_mem_placeTwo (K := K))
    · exact mem_badPlaces_of_dvd hd (dvd_mul_left d 2) hw
  have hmaps : ∀ v ∈ badPlaces K hd, ((under K v : ℕ)) ∈ (2 * d).primeFactors := by
    intro v hv
    have hqv : (((under K v : ℕ)) : 𝓞 K) ∈ v.asIdeal := (under_eq_iff K v (under K v)).1 rfl
    have h2d : ((((2 * d : ℕ) : ℤ)) : 𝓞 K) ∈ v.asIdeal := by
      have := (mem_badPlaces hd v).1 hv
      exact_mod_cast this
    have hdvd := dvd_of_intCast_mem (under K v).2 hqv h2d
    rw [Nat.mem_primeFactors]
    exact ⟨(under K v).2, Int.natCast_dvd_natCast.1 hdvd, by omega⟩
  have h2nd : 2 ∉ d.primeFactors := fun h => by
    have := Nat.dvd_of_mem_primeFactors h
    omega
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp,
    ← Finset.prod_fiberwise_of_maps_to hmaps, Nat.primeFactors_mul two_ne_zero hd,
    Nat.prime_two.primeFactors, Finset.prod_union (Finset.disjoint_singleton_left.2 h2nd),
    Finset.prod_singleton, prod_fibre_two hodd hsq hd,
    Finset.prod_congr rfl (fun q hq => prod_fibre_cmCharTw hodd hsq hd
      (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq)),
    ← Int.cast_prod, prod_χ₄_primeFactors hsq]

/-- **The global root number of `cmCharTw` is `χ₈(d) · χ₄(d)`.** -/
theorem heckeRootNumber_cmCharTw :
    heckeRootNumber K (cmCharTw K hodd hsq hd) (fun _ _ => 0) (fun _ _ => -1) =
      ((ZMod.χ₈ (d : ZMod 8) : ℤ) : ℂ) * ((ZMod.χ₄ (d : ZMod 4) : ℤ) : ℂ) := by
  unfold heckeRootNumber
  have : IsEmpty {w : InfinitePlace K // w.IsReal} := ⟨fun w => not_isReal_infinitePlace w.1 w.2⟩
  have hc : (archPlace K).IsComplex :=
    InfinitePlace.not_isReal_iff_isComplex.1 (not_isReal_infinitePlace _)
  rw [finprod_stdRootNumberAt_cmCharTw hodd hsq hd, Finset.univ_eq_empty, Finset.prod_empty,
    Fintype.prod_subsingleton _ (⟨archPlace K, hc⟩ : {w : InfinitePlace K // w.IsComplex})]
  simp only [Int.reduceNeg, Int.natAbs_neg, Int.natAbs_one, pow_one, one_mul]
  linear_combination (-(((ZMod.χ₈ (d : ZMod 8) : ℤ)) : ℂ) * ((ZMod.χ₄ (d : ZMod 4) : ℤ) : ℂ)) *
    Complex.I_sq

end CMPoints

/-- **Vanishing at `s = 1`.** For squarefree `d ≡ 5, 7 (mod 8)`, every
entire continuation of the Mathlib L-series of `y² = x³ − d²x` vanishes at
`s = 1`. -/
theorem CMPoints.vanishing_curveD {d : ℕ} (hsq : Squarefree d) (h8 : d % 8 = 5 ∨ d % 8 = 7)
    (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hFval : ∀ s : ℂ, 3 / 2 < s.re →
      F s = (⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ).LSeries s) :
    F 1 = 0 := by
  haveI : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  have hodd : d % 2 = 1 := by omega
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
  have hsign : ((ZMod.χ₈ (d : ZMod 8) : ℤ) : ℂ) * ((ZMod.χ₄ (d : ZMod 4) : ℤ) : ℂ) = -1 := by
    rw [ZMod.χ₈_nat_eq_if_mod_eight, ZMod.χ₄_nat_eq_if_mod_four]
    rcases h8 with h | h
    · have h4 : d % 4 = 1 := by omega
      simp [h, hodd, h4]
    · have h4 : d % 4 = 3 := by omega
      simp [h, hodd, h4]
  -- `Λ(1) = 0`
  have h1 := hfe 1
  rw [CMPoints.heckeRootNumber_cmCharTw hodd hsq hd, hsign, sub_self, Complex.cpow_zero,
    show (2 : ℂ) - 1 = 1 by norm_num] at h1
  have h0 : Λ 1 = 0 := by linear_combination (1 / 2 : ℂ) * h1
  -- the constructed continuation coincides with `F`
  have hG : Differentiable ℂ fun s => (Complex.Gammaℂ s)⁻¹ * Λ s :=
    Complex.differentiable_Gammaℂ_inv.mul hΛ
  have hoddZ : Odd (d : ℤ) := by exact_mod_cast Nat.odd_iff.2 hodd
  have hsqZ : Squarefree (d : ℤ) := Int.squarefree_natCast.2 hsq
  have hGval : ∀ s : ℂ, 3 / 2 < s.re → (Complex.Gammaℂ s)⁻¹ * Λ s = F s := by
    intro s hs
    rw [hval s hs, inv_mul_cancel_left₀ (CMPoints.Gammaℂ_ne_zero_of_re_pos (by linarith)),
      hFval s hs]
    have e1 : (⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ) =
        CMPoints.curveD ℚ ((((d : ℤ))) : ℚ) := by
      rw [Int.cast_natCast]
      rfl
    rw [e1, WeierstrassCurve.LSeries]
    congr 1
    funext n
    show ((CMPoints.cmCoeffTw (d : ℤ) n : ℤ) : ℂ) =
      (((CMPoints.curveD ℚ ((d : ℤ) : ℚ)).LFunction n : ℤ) : ℂ)
    rw [CMPoints.LFunction_curveD_eq_cmCoeffTw_of_odd_squarefree hoddZ hsqZ n]
  have hopen : IsOpen {s : ℂ | 3 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : (fun s => (Complex.Gammaℂ s)⁻¹ * Λ s) =ᶠ[nhds (2 : ℂ)] F :=
    Filter.eventually_of_mem (hopen.mem_nhds (by norm_num : (3 / 2 : ℝ) < (2 : ℂ).re))
      fun s hs => hGval s hs
  have heq := (hG.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
    (hF.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (Set.mem_univ 2) hev
  rw [← heq (Set.mem_univ 1)]
  show (Complex.Gammaℂ 1)⁻¹ * Λ 1 = 0
  rw [h0, mul_zero]
