import HeckeCM.RootEvenChar

/-!
# The sign for `d = 2e` and the vanishing at `s = 1` for `d ≡ 5, 6, 7 (mod 8)`

* `finprod_eq_of_fibres`: a product over places, trivial outside `2d`, can be
  grouped by primes;
* `heckeRootNumber_cmCharEv`: for `e` odd and squarefree, the global root
  number of the character of `y² = x³ − (2e)²x` is `χ₄(e)`;
* `CMPoints.vanishing_curveD_all`: for `d ≡ 5, 6, 7 (mod 8)` squarefree,
  every entire continuation of the Mathlib L-series of `y² = x³ − d²x`
  vanishes at `s = 1`;
* `CMPoints.vanishing_curveD_sq_mul`: the same for `d·m²`.
-/

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open NumberField.AdelicLevel AutomorphicForm NumberField.TateGlobal
open NumberField.StandardAddChar LanglandsTunnell.TateLocal
open LanglandsTunnell LanglandsTunnell.HeckeTate
open scoped Classical

namespace CMPoints

/-- From the functional equation with sign `−1` to the vanishing at `s = 1` of
every entire continuation. -/
theorem vanishing_of_functional_equation {f : ℕ → ℂ} {N : ℝ} {Λ : ℂ → ℂ}
    (hΛ : Differentiable ℂ Λ)
    (hval : ∀ s : ℂ, 3 / 2 < s.re → Λ s = Complex.Gammaℂ s * LSeries f s)
    (hfe : ∀ s : ℂ, Λ s = -1 * ((N : ℝ) : ℂ) ^ (1 - s) * Λ (2 - s))
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) (hFval : ∀ s : ℂ, 3 / 2 < s.re → F s = LSeries f s) :
    F 1 = 0 := by
  have h1 := hfe 1
  rw [sub_self, Complex.cpow_zero, show (2 : ℂ) - 1 = 1 by norm_num] at h1
  have h0 : Λ 1 = 0 := by linear_combination (1 / 2 : ℂ) * h1
  have hG : Differentiable ℂ fun s => (Complex.Gammaℂ s)⁻¹ * Λ s :=
    Complex.differentiable_Gammaℂ_inv.mul hΛ
  have hopen : IsOpen {s : ℂ | 3 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : (fun s => (Complex.Gammaℂ s)⁻¹ * Λ s) =ᶠ[nhds (2 : ℂ)] F :=
    Filter.eventually_of_mem (hopen.mem_nhds (by norm_num : (3 / 2 : ℝ) < (2 : ℂ).re))
      fun s hs => by
        show (Complex.Gammaℂ s)⁻¹ * Λ s = F s
        rw [hval s hs, inv_mul_cancel_left₀ (Gammaℂ_ne_zero_of_re_pos (by
          have : (3 / 2 : ℝ) < s.re := hs
          linarith)), hFval s hs]
  have heq := (hG.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
    (hF.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (Set.mem_univ 2) hev
  rw [← heq (Set.mem_univ 1)]
  show (Complex.Gammaℂ 1)⁻¹ * Λ 1 = 0
  rw [h0, mul_zero]

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

local notation "𝔸" => AdeleRing (𝓞 K) K

/-- **Grouping by primes** of a product over places that is trivial outside `2d`. -/
theorem finprod_eq_of_fibres {M : Type*} [CommMonoid M] {d : ℕ} (hodd : d % 2 = 1) (hd : d ≠ 0)
    (f : HeightOneSpectrum (𝓞 K) → M)
    (hunr : ∀ v : HeightOneSpectrum (𝓞 K), v ≠ placeTwo K → ((d : ℕ) : 𝓞 K) ∉ v.asIdeal → f v = 1)
    (c : ℕ → M)
    (hfib : ∀ q : ℕ, q.Prime → q ∣ d →
      ∏ v ∈ (badPlaces K hd).filter (fun v => ((under K v : ℕ)) = q), f v = c q) :
    ∏ᶠ v, f v = f (placeTwo K) * ∏ q ∈ d.primeFactors, c q := by
  have hsupp : Function.mulSupport f ⊆ ↑(badPlaces K hd) := by
    intro v hv
    by_contra hnot
    apply hv
    have hnot' : v ∉ badPlaces K hd := hnot
    refine hunr v (fun h2 => hnot' ?_) (fun hw => hnot' ?_)
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
  have hf2 : (badPlaces K hd).filter (fun v => ((under K v : ℕ)) = 2) = {placeTwo K} := by
    ext u
    rw [Finset.mem_filter, Finset.mem_singleton, under_val_eq_iff u Nat.prime_two]
    constructor
    · rintro ⟨-, h⟩
      exact eq_placeTwo_of_two_mem (by simpa using h)
    · rintro rfl
      have h2 : (((2 : ℕ)) : 𝓞 K) ∈ (placeTwo K).asIdeal := by simpa using two_mem_placeTwo (K := K)
      exact ⟨mem_badPlaces_of_dvd hd (dvd_mul_right 2 d) h2, h2⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp,
    ← Finset.prod_fiberwise_of_maps_to hmaps, Nat.primeFactors_mul two_ne_zero hd,
    Nat.prime_two.primeFactors, Finset.prod_union (Finset.disjoint_singleton_left.2 h2nd),
    Finset.prod_singleton, hf2, Finset.prod_singleton,
    Finset.prod_congr rfl (fun q hq => hfib q (Nat.prime_of_mem_primeFactors hq)
      (Nat.dvd_of_mem_primeFactors hq))]

variable {e : ℕ} (hodd : e % 2 = 1) (hsq : Squarefree e) (he : e ≠ 0)
include hodd hsq

/-- At a place dividing `e`, `cmCharTw` has conductor exponent 1. -/
theorem hasConductorExponentAt_cmCharTw_of_mem {v : HeightOneSpectrum (𝓞 K)}
    (hv : ((e : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    HasConductorExponentAt K v (localChar (cmCharTw K hodd hsq he) v) 1 := by
  have hv2 : v ≠ placeTwo K := by
    rintro rfl
    exact natCast_notMem_placeTwo hodd hv
  constructor
  · intro u hu
    obtain ⟨h1, h2⟩ := hu
    have h2' : Valued.v ((u : v.adicCompletion K) - 1) < 1 := by
      rcases h2 with h | h
      · exact absurd h one_ne_zero
      · exact (lt_one_iff_le_exp _).2 (by exact_mod_cast h)
    show cmCharTw K hodd hsq he (locIdele K v u) = 1
    rw [cmCharTw_apply, cmChar_localUnit_of_ne hv2 u h1,
      twC_locIdele_of_sub_one_lt hodd hsq he v u h1 h2', one_mul]
  · intro m hm
    obtain rfl : m = 0 := by omega
    obtain ⟨t, ht, hval⟩ := exists_twC_locIdele_eq_neg_one hodd hsq he hv
    refine ⟨t, ⟨ht, Or.inl rfl⟩, fun h => ?_⟩
    have h' : cmCharTw K hodd hsq he (locIdele K v t) = 1 := h
    rw [cmCharTw_apply, cmChar_localUnit_of_ne hv2 t ht, one_mul] at h'
    rw [h', Units.val_one] at hval
    norm_num at hval

/-- Outside `2e` the local root number of `cmCharEv` is 1. -/
theorem stdRootNumberAt_cmCharEv_unram {v : HeightOneSpectrum (𝓞 K)} (h2 : v ≠ placeTwo K)
    (hw : ((e : ℕ) : 𝓞 K) ∉ v.asIdeal) :
    stdRootNumberAt K v (localChar (cmCharEv K hodd hsq he) v) = 1 :=
  stdRootNumberAt_eq_one_of_hasConductorExponentAt_zero K v _
    ⟨fun u hu => by
        show cmCharEv K hodd hsq he (locIdele K v u) = 1
        rw [cmCharEv_apply, cmCharTw_apply, cmChar_localUnit_of_ne h2 u hu.1,
          twC_locIdele_unit hodd hsq he hw u hu.1, tw8C_locIdele_unit h2 u hu.1, one_mul, one_mul],
      fun m hm => absurd hm (Nat.not_lt_zero m)⟩
    (isUnitaryChar_cmCharEv hodd hsq he _) (addCharLevel_psiLocal_of_ne h2) (psiLocal_ne_one K v)

/-- At a place dividing `e`: the root number of `cmCharEv` is `χ₈(N gen)`
times that of `cmCharTw`. -/
theorem stdRootNumberAt_cmCharEv_of_mem {v : HeightOneSpectrum (𝓞 K)}
    (hv : ((e : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    stdRootNumberAt K v (localChar (cmCharEv K hodd hsq he) v) =
      ((chi8 K (gen K v) : ℤ) : ℂ) *
        stdRootNumberAt K v (localChar (cmCharTw K hodd hsq he) v) := by
  have hv2 : v ≠ placeTwo K := by
    rintro rfl
    exact natCast_notMem_placeTwo hodd hv
  have hloc : localChar (cmCharEv K hodd hsq he) v =
      localChar (cmCharTw K hodd hsq he) v * localChar (tw8C K) v := MonoidHom.ext fun t => rfl
  have hω : HasConductorExponentAt K v (localChar (tw8C K) v) 0 :=
    ⟨fun u hu => tw8C_locIdele_unit hv2 u hu.1, fun m hm => absurd hm (Nat.not_lt_zero m)⟩
  have h := stdRootNumberAt_mul_of_hasConductorExponentAt_zero K v _ _ 1
    (hasConductorExponentAt_cmCharTw_of_mem hodd hsq he hv) hω
    (isUnitaryChar_cmCharTw hodd hsq he _) (norm_tw8C _) (psiLocal_ne_one K v)
  have hval : ((localChar (tw8C K) v (uniformizerUnit K v) : ℂˣ) : ℂ) =
      ((chi8 K (gen K v) : ℤ) : ℂ) := by
    show ((tw8C K (locIdele K v (uniformizerUnit K v)) : ℂˣ) : ℂ) = _
    rw [tw8C_val, tw8_locIdele_uniformizer hv2 _ (valued_uniformizerUnit K v)]
  rw [hloc, h, addCharLevel_psiLocal_of_ne hv2, show (((1 : ℕ) : ℤ)) + 0 = 1 by norm_num,
    zpow_one, hval]

omit hodd hsq in
lemma chi8_gaussOf_sq {a b : ℤ} (h : ¬ (2 : ℤ) ∣ a ^ 2 + b ^ 2) :
    ((chi8 K (gaussOf K a b) : ℤ) : ℂ) * ((chi8 K (gaussOf K a (-b)) : ℤ) : ℂ) = 1 := by
  rw [chi8, chi8, nrm_gaussOf, nrm_gaussOf, neg_sq, ← Int.cast_mul, chi8_sq_of_odd h,
    Int.cast_one]

/-- Above a prime `q` dividing `e`, the product of the local root numbers of
`cmCharEv` is `χ₄(q)`. -/
theorem prod_fibre_cmCharEv {q : ℕ} (hq : q.Prime) (hqe : q ∣ e) :
    ∏ v ∈ (badPlaces K he).filter (fun v => ((under K v : ℕ)) = q),
        stdRootNumberAt K v (localChar (cmCharEv K hodd hsq he) v) =
      ((ZMod.χ₄ (q : ZMod 4) : ℤ) : ℂ) := by
  obtain ⟨m, rfl⟩ := hqe
  haveI := Fact.mk hq
  have hq2 : q % 2 = 1 := Nat.odd_iff.1 (Nat.odd_mul.1 (Nat.odd_iff.2 hodd)).1
  have hqdvd : q ∣ 2 * (q * m) := ⟨2 * m, by ring⟩
  have hmemd : ∀ u : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∈ u.asIdeal →
      (((q * m : ℕ)) : 𝓞 K) ∈ u.asIdeal := fun u hu => by
    rw [Nat.cast_mul]
    exact u.asIdeal.mul_mem_right _ hu
  rcases (by omega : q % 4 = 3 ∨ q % 4 = 1) with h3 | h1
  · obtain ⟨v, hmem, hN, hprim, hv⟩ := exists_primary_inert (K := K) q h3
    have hqv : ((q : ℕ) : 𝓞 K) ∈ v.asIdeal := (hmem v).2 rfl
    have h2v : (2 : 𝓞 K) ∉ v.asIdeal := two_not_mem v hq2 hqv
    have hf : (badPlaces K he).filter (fun u => ((under K u : ℕ)) = q) = {v} := by
      ext u
      rw [Finset.mem_filter, Finset.mem_singleton, under_val_eq_iff u hq, hmem u]
      constructor
      · exact fun h => h.2
      · rintro rfl
        exact ⟨mem_badPlaces_of_dvd he hqdvd ((hmem u).2 rfl), rfl⟩
    have hc8 : ((chi8 K (gen K v) : ℤ) : ℂ) = 1 := by
      rw [gen_eq_of_primary h2v hprim hv, chi8, nrm_gaussOf]
      have hq' : ¬ (2 : ℤ) ∣ (q : ℤ) := by omega
      have := chi8_sq_of_odd hq'
      rw [show (-(q : ℤ)) ^ 2 + (0 : ℤ) ^ 2 = (q : ℤ) * q by ring, Int.cast_mul, map_mul, this,
        Int.cast_one]
    rw [hf, Finset.prod_singleton, stdRootNumberAt_cmCharEv_of_mem hodd hsq he (hmemd v hqv), hc8,
      one_mul, stdRootNumberAt_cmCharTw_inert hv hodd hsq he hmem h3 hN hprim,
      ZMod.χ₄_nat_three_mod_four h3]
    norm_num
  · obtain ⟨v, w, a, b, hvw, hmem, hNv, hNw, hab, hab', hn, hv, hw⟩ :=
      exists_primary_split (K := K) q h1
    have hqv : ((q : ℕ) : 𝓞 K) ∈ v.asIdeal := (hmem v).2 (Or.inl rfl)
    have hqw : ((q : ℕ) : 𝓞 K) ∈ w.asIdeal := (hmem w).2 (Or.inr rfl)
    have h2v : (2 : 𝓞 K) ∉ v.asIdeal := two_not_mem v hq2 hqv
    have h2w : (2 : 𝓞 K) ∉ w.asIdeal := two_not_mem w hq2 hqw
    have hf : (badPlaces K he).filter (fun u => ((under K u : ℕ)) = q) = {v, w} := by
      ext u
      rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, under_val_eq_iff u hq,
        hmem u]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨mem_badPlaces_of_dvd he hqdvd ((hmem u).2 h), h⟩
    have hc8 : ((chi8 K (gen K v) : ℤ) : ℂ) * ((chi8 K (gen K w) : ℤ) : ℂ) = 1 := by
      rw [gen_eq_of_primary h2v hab hv, gen_eq_of_primary h2w hab' hw]
      exact chi8_gaussOf_sq (by rw [hn]; omega)
    have hsplit := stdRootNumberAt_cmCharTw_split h1 hab hn hodd hsq he hab' hv hw hNv hNw
    rw [hf, Finset.prod_pair hvw, stdRootNumberAt_cmCharEv_of_mem hodd hsq he (hmemd v hqv),
      stdRootNumberAt_cmCharEv_of_mem hodd hsq he (hmemd w hqw), ZMod.χ₄_nat_one_mod_four h1]
    push_cast
    linear_combination
      (stdRootNumberAt K v (localChar (cmCharTw K hodd hsq he) v) *
        stdRootNumberAt K w (localChar (cmCharTw K hodd hsq he) w)) * hc8 + hsplit

/-- **The global root number of `cmCharEv` is `χ₄(e)`.** -/
theorem heckeRootNumber_cmCharEv :
    heckeRootNumber K (cmCharEv K hodd hsq he) (fun _ _ => 0) (fun _ _ => -1) =
      ((ZMod.χ₄ (e : ZMod 4) : ℤ) : ℂ) := by
  unfold heckeRootNumber
  have : IsEmpty {w : InfinitePlace K // w.IsReal} := ⟨fun w => not_isReal_infinitePlace w.1 w.2⟩
  have hc : (archPlace K).IsComplex :=
    InfinitePlace.not_isReal_iff_isComplex.1 (not_isReal_infinitePlace _)
  rw [finprod_eq_of_fibres hodd he _
      (fun v h2 hw => stdRootNumberAt_cmCharEv_unram hodd hsq he h2 hw) _
      (fun q hq hqe => prod_fibre_cmCharEv hodd hsq he hq hqe),
    stdRootNumberAt_cmCharEv_two hodd hsq he, ← Int.cast_prod, prod_χ₄_primeFactors hsq,
    Finset.univ_eq_empty, Finset.prod_empty,
    Fintype.prod_subsingleton _ (⟨archPlace K, hc⟩ : {w : InfinitePlace K // w.IsComplex})]
  simp only [Int.reduceNeg, Int.natAbs_neg, Int.natAbs_one, pow_one, one_mul]
  linear_combination (-((ZMod.χ₄ (e : ZMod 4) : ℤ) : ℂ)) * Complex.I_sq

end CMPoints

/-- Vanishing at `s = 1` for `d = 2e`, `e ≡ 3 (mod 4)` squarefree. -/
theorem CMPoints.vanishing_curveD_two_mul {e : ℕ} (hsq : Squarefree e) (h4 : e % 4 = 3)
    (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hFval : ∀ s : ℂ, 3 / 2 < s.re →
      F s = (CMPoints.curveD ℚ (((2 * (e : ℤ) : ℤ)) : ℚ)).LSeries s) :
    F 1 = 0 := by
  haveI : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  have hodd : e % 2 = 1 := by omega
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
  have hfe' : ∀ s : ℂ, Λ s = -1 * ((heckeConductor (CyclotomicField 4 ℚ)
      (CMPoints.cmCharEv (CyclotomicField 4 ℚ) hodd hsq he) : ℝ) : ℂ) ^ (1 - s) * Λ (2 - s) :=
    fun s => by
      have := hfe s
      rw [CMPoints.heckeRootNumber_cmCharEv hodd hsq he, ZMod.χ₄_nat_three_mod_four h4] at this
      simpa using this
  have hoddZ : Odd (e : ℤ) := by exact_mod_cast Nat.odd_iff.2 hodd
  have hsqZ : Squarefree (e : ℤ) := Int.squarefree_natCast.2 hsq
  refine CMPoints.vanishing_of_functional_equation hΛ hval hfe' F hF fun s hs => ?_
  rw [hFval s hs, WeierstrassCurve.LSeries]
  congr 1
  funext n
  show (((CMPoints.curveD ℚ (((2 * (e : ℤ) : ℤ)) : ℚ)).LFunction n : ℤ) : ℂ) =
    ((CMPoints.cmCoeffTw (2 * (e : ℤ)) n : ℤ) : ℂ)
  rw [CMPoints.LFunction_curveD_two_mul_eq_cmCoeffTw hoddZ hsqZ n]
