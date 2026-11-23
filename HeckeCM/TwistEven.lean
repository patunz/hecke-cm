import HeckeCM.TwistEight
import HeckeCM.TwistFinal
import HeckeCM.TwistOdd
import HeckeCM.CurveEven

/-!
# The L-series of `y² = x³ − d²x` has an entire continuation, for every `d ≠ 0`

For `e` odd and squarefree, `cmCharEv = cmChar · twC_e · tw8C` is the
Hecke character of `y² = x³ − (2e)²x`: its local values are those of
`cmCoeffTw (2e)`, because `(2e/p) = χ₈(p) · (p/e)` for `p ≡ 1 (mod 4)`.

* `exists_entire_lseries_cmCoeffTw_two_mul`: entire continuation of the
  Dirichlet series of `cmCoeffTw (2e)`;
* `entire_lseries_curveD_of_ne_zero`: **for every `d ≠ 0`**, the Mathlib
  L-series of `y² = x³ − d²x` has an entire continuation. Write `d = d' m²`
  with `d'` squarefree; `d'` is odd or `2e` with `e` odd.
-/

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open NumberField.AdelicLevel AutomorphicForm NumberField.TateGlobal
open scoped Classical

namespace CMPoints

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

local notation "𝔸" => AdeleRing (𝓞 K) K

lemma chi8_sq_natCast {p : ℕ} (hp : p % 2 = 1) :
    ZMod.χ₈ ((((p : ℤ) ^ 2 : ℤ)) : ZMod 8) = 1 := by
  rw [Int.cast_pow, sq, map_mul]
  exact chi8_sq_of_odd (by omega)

variable {e : ℕ} (hodd : e % 2 = 1) (hsq : Squarefree e) (he : e ≠ 0)
include hodd hsq

variable (K) in
/-- **The Hecke character of `y² = x³ − (2e)²x`.** -/
def cmCharEv : (𝔸)ˣ →* ℂˣ := cmCharTw K hodd hsq he * tw8C K

theorem cmCharEv_apply (x : (𝔸)ˣ) :
    cmCharEv K hodd hsq he x = cmCharTw K hodd hsq he x * tw8C K x := rfl

theorem isUnitaryChar_cmCharEv : IsUnitaryChar (𝓞 K) K (cmCharEv K hodd hsq he) := by
  intro x
  rw [cmCharEv_apply, Units.val_mul, norm_mul, isUnitaryChar_cmCharTw hodd hsq he x, norm_tw8C,
    one_mul]

theorem isIdeleClassChar_cmCharEv : IsIdeleClassChar (𝓞 K) K (cmCharEv K hodd hsq he) := by
  intro a
  rw [cmCharEv_apply, isIdeleClassChar_cmCharTw hodd hsq he a, tw8C_principal, one_mul]

theorem continuous_cmCharEv : Continuous (cmCharEv K hodd hsq he) :=
  (continuous_cmCharTw hodd hsq he).mul continuous_tw8C

theorem isUnramifiedCharAt_cmCharEv {w : HeightOneSpectrum (𝓞 K)} (h2 : w ≠ placeTwo K)
    (hw : ((e : ℕ) : 𝓞 K) ∉ w.asIdeal) : IsUnramifiedCharAt (cmCharEv K hodd hsq he) w := by
  intro t ht hti
  have hone := valued_eq_one_of_mem_integers t ht hti
  have h1 : cmCharTw K hodd hsq he (locIdele K w t) = 1 :=
    isUnramifiedCharAt_cmCharTw hodd hsq he h2 hw t ht hti
  show cmCharEv K hodd hsq he (locIdele K w t) = 1
  rw [cmCharEv_apply, h1, tw8C_locIdele_unit h2 t hone, one_mul]

/-- On the local unit `i` at the place above 2 the character is not 1. -/
theorem cmCharEv_locIdele_two_ne_one :
    cmCharEv K hodd hsq he (locIdele K (placeTwo K)
      (Units.map ((toCompl K (placeTwo K) : 𝓞 K →+* _) : 𝓞 K →* _) (gaussIUnit K))) ≠ 1 := by
  intro key
  set t : ((placeTwo K).adicCompletion K)ˣ :=
    Units.map ((toCompl K (placeTwo K) : 𝓞 K →+* _) : 𝓞 K →* _) (gaussIUnit K) with ht
  have htv : (t : (placeTwo K).adicCompletion K) = toCompl K (placeTwo K) (gaussIUnit K) := rfl
  have ht1 : Valued.v (t : (placeTwo K).adicCompletion K) = 1 := by
    rw [htv, valued_toCompl_unit]
  rw [cmCharEv_apply, cmCharTw_apply,
    twC_locIdele_unit hodd hsq he (natCast_notMem_placeTwo hodd) t ht1,
    tw8C_locIdele_two_gaussI, mul_one, mul_one] at key
  exact cmChar_localUnit_two_ne_one (K := K) key

theorem not_isUnramifiedCharAt_cmCharEv_two :
    ¬ IsUnramifiedCharAt (cmCharEv K hodd hsq he) (placeTwo K) := by
  intro h
  refine cmCharEv_locIdele_two_ne_one hodd hsq he (h _ ?_ ?_)
  · exact (mem_adicCompletionIntegers (𝓞 K) K _).2 (valued_toCompl_unit _ _).le
  · rw [← map_inv]
    exact (mem_adicCompletionIntegers (𝓞 K) K _).2 (valued_toCompl_unit _ _).le

theorem not_isUnramifiedCharAt_cmCharEv_of_mem {v : HeightOneSpectrum (𝓞 K)}
    (hv : ((e : ℕ) : 𝓞 K) ∈ v.asIdeal) : ¬ IsUnramifiedCharAt (cmCharEv K hodd hsq he) v := by
  intro h
  obtain ⟨t, ht1, htw⟩ := exists_twC_locIdele_eq_neg_one hodd hsq he hv
  have hv2 : v ≠ placeTwo K := by
    rintro rfl
    exact natCast_notMem_placeTwo hodd hv
  have hti1 : Valued.v ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, ht1, inv_one]
  have key : cmCharEv K hodd hsq he (locIdele K v t) = 1 :=
    h t ((mem_adicCompletionIntegers (𝓞 K) K v).2 ht1.le)
      ((mem_adicCompletionIntegers (𝓞 K) K v).2 hti1.le)
  have hval := congrArg (fun z : ℂˣ => (z : ℂ)) key
  simp only [cmCharEv_apply, cmCharTw_apply, Units.val_mul, Units.val_one] at hval
  rw [cmChar_localUnit_of_ne hv2 t ht1, tw8C_locIdele_unit hv2 t ht1, Units.val_one, one_mul,
    mul_one, htw] at hval
  norm_num at hval

theorem cmCharEv_uniformizerIdele {w : HeightOneSpectrum (𝓞 K)} (h2 : w ≠ placeTwo K)
    (hw : ((e : ℕ) : 𝓞 K) ∉ w.asIdeal) :
    ((cmCharEv K hodd hsq he (uniformizerIdele K w) : ℂˣ) : ℂ) =
      sigma K (genK K w) / ((‖sigma K (genK K w)‖ : ℝ) : ℂ) * ((tau K e (gen K w) : ℤ) : ℂ) *
        ((chi8 K (gen K w) : ℤ) : ℂ) := by
  have h1 : uniformizerIdele K w = locIdele K w (uniformizerUnit K w) := rfl
  rw [cmCharEv_apply, Units.val_mul, cmCharTw_uniformizerIdele hodd hsq he h2 hw, tw8C_val, h1,
    tw8_locIdele_uniformizer h2 _ (valued_uniformizerUnit K w)]

/-- **The local values of `cmCharEv` are those of `cmCoeffTw (2e)`.** -/
theorem isGenEulerDatum_cmCharEv :
    IsGenEulerDatum K (fun p : ℕ => (p : ℤ) ∣ 2 * (2 * (e : ℤ)))
      (fun p => jacobiSym (2 * (e : ℤ)) p * cmPrime p)
      (fun v => if IsUnramifiedCharAt (cmCharEv K hodd hsq he) v then
        ((cmCharEv K hodd hsq he (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) := by
  have hgood : ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ 2 * (2 * (e : ℤ)) →
      ∀ v : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ v.asIdeal →
        ((e : ℕ) : 𝓞 K) ∉ v.asIdeal := by
    intro p hp hb v hpv hdv
    have := dvd_of_intCast_mem hp hpv (N := (e : ℤ)) (by simpa using hdv)
    exact hb (Dvd.dvd.mul_left (Dvd.dvd.mul_left this 2) 2)
  refine ⟨fun v => ?_, fun p hp hb v hv => ?_, fun p hp hb h3 => ?_, fun p hp hb h1 => ?_⟩
  · split_ifs
    · exact (isUnitaryChar_cmCharEv hodd hsq he _).le
    · rw [norm_zero]
      exact zero_le_one
  · rw [if_neg]
    have hb' : p ∣ 2 * (2 * e) := by exact_mod_cast hb
    have hcase : p = 2 ∨ p ∣ e := by
      rcases (Nat.Prime.dvd_mul hp).1 hb' with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
      · rcases (Nat.Prime.dvd_mul hp).1 h with h' | h'
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
        · exact Or.inr h'
    rcases hcase with h | h
    · subst h
      have h2' : (2 : 𝓞 K) ∈ v.asIdeal := by simpa using hv
      rw [eq_placeTwo_of_two_mem h2']
      exact not_isUnramifiedCharAt_cmCharEv_two hodd hsq he
    · refine not_isUnramifiedCharAt_cmCharEv_of_mem hodd hsq he ?_
      obtain ⟨m, hm⟩ := h
      rw [hm, Nat.cast_mul]
      exact v.asIdeal.mul_mem_right _ hv
  · haveI := Fact.mk hp
    have hpe : ¬ p ∣ e := fun h =>
      hb (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Int.natCast_dvd_natCast.2 h) 2) 2)
    obtain ⟨v, hmem, hN, hprim, hv⟩ := exists_primary_inert (K := K) p h3
    refine ⟨v, hmem, hN, ?_⟩
    have hpv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal := (hmem v).2 rfl
    have h2v : (2 : 𝓞 K) ∉ v.asIdeal := two_not_mem v (by omega) hpv
    have hne : v ≠ placeTwo K := fun h => h2v (h ▸ two_mem_placeTwo)
    have hdv := hgood p hp hb v hpv
    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have hgcd : Int.gcd (p : ℤ) e = 1 := by
      rw [Int.gcd_natCast_natCast]
      exact (Nat.Prime.coprime_iff_not_dvd hp).2 hpe
    have hsqe : (-(p : ℤ)) ^ 2 + 0 ^ 2 = (p : ℤ) ^ 2 := by ring
    have htau : tau K e (gen K v) = 1 := by
      rw [gen_eq_of_primary h2v hprim hv, tau, nrm_gaussOf, hsqe, jacobiSym.sq_one' hgcd]
    have hchi : chi8 K (gen K v) = 1 := by
      rw [gen_eq_of_primary h2v hprim hv, chi8, nrm_gaussOf, hsqe]
      exact chi8_sq_natCast (by omega)
    rw [if_pos (isUnramifiedCharAt_cmCharEv hodd hsq he hne hdv),
      cmCharEv_uniformizerIdele hodd hsq he hne hdv, htau, hchi, Int.cast_one, mul_one, mul_one]
    unfold genK
    rw [gen_eq_of_primary h2v hprim hv, sigma_gaussOf]
    push_cast
    rw [zero_mul, add_zero, norm_neg, Complex.norm_natCast, Complex.ofReal_natCast, neg_div,
      div_self hp0]
  · haveI := Fact.mk hp
    have hpe : ¬ p ∣ e := fun h =>
      hb (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Int.natCast_dvd_natCast.2 h) 2) 2)
    obtain ⟨v, w, a, b, hvw, hmem, hNv, hNw, hab, hab', hn, hv, hw⟩ :=
      exists_primary_split (K := K) p h1
    refine ⟨v, w, hvw, hmem, hNv, hNw, ?_, ?_⟩
    all_goals
      have hpv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal := (hmem v).2 (Or.inl rfl)
      have hpw : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal := (hmem w).2 (Or.inr rfl)
      have hodd' : p % 2 = 1 := by omega
      have h2v : (2 : 𝓞 K) ∉ v.asIdeal := two_not_mem v hodd' hpv
      have h2w : (2 : 𝓞 K) ∉ w.asIdeal := two_not_mem w hodd' hpw
      have hnev : v ≠ placeTwo K := fun h => h2v (h ▸ two_mem_placeTwo)
      have hnew : w ≠ placeTwo K := fun h => h2w (h ▸ two_mem_placeTwo)
      have hdv := hgood p hp hb v hpv
      have hdw := hgood p hp hb w hpw
      have hj := sigJ_sq (K := K)
      have hs0 : ((Real.sqrt p : ℝ) : ℂ) ≠ 0 := by
        rw [Ne, Complex.ofReal_eq_zero, Real.sqrt_eq_zero (Nat.cast_nonneg p)]
        exact Nat.cast_ne_zero.2 hp.ne_zero
      have hss : ((Real.sqrt p : ℝ) : ℂ) ^ 2 = p := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg p), Complex.ofReal_natCast]
      have hnC : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = p := by exact_mod_cast congrArg (Int.cast : ℤ → ℂ) hn
      have hnv : ‖(a : ℂ) + (b : ℂ) * sigJ K‖ = Real.sqrt p := by
        rw [norm_add_mul_of_sq hj, hn, Int.cast_natCast]
      have hn' : a ^ 2 + (-b) ^ 2 = (p : ℤ) := by rw [neg_sq]; exact hn
      have hnw : ‖(a : ℂ) + ((-b : ℤ) : ℂ) * sigJ K‖ = Real.sqrt p := by
        rw [norm_add_mul_of_sq hj, hn', Int.cast_natCast]
      have hgcd : Int.gcd (p : ℤ) e = 1 := by
        rw [Int.gcd_natCast_natCast]
        exact (Nat.Prime.coprime_iff_not_dvd hp).2 hpe
      have hε1 := jacobiSym.eq_one_or_neg_one hgcd
      have htauv : tau K e (gen K v) = jacobiSym (p : ℤ) e := by
        rw [gen_eq_of_primary h2v hab hv, tau, nrm_gaussOf, hn]
      have htauw : tau K e (gen K w) = jacobiSym (p : ℤ) e := by
        rw [gen_eq_of_primary h2w hab' hw, tau, nrm_gaussOf, hn']
      have hchiv : chi8 K (gen K v) = ZMod.χ₈ ((p : ℕ) : ZMod 8) := by
        rw [gen_eq_of_primary h2v hab hv, chi8, nrm_gaussOf, hn, Int.cast_natCast]
      have hchiw : chi8 K (gen K w) = ZMod.χ₈ ((p : ℕ) : ZMod 8) := by
        rw [gen_eq_of_primary h2w hab' hw, chi8, nrm_gaussOf, hn', Int.cast_natCast]
      have hχsq : ZMod.χ₈ ((p : ℕ) : ZMod 8) * ZMod.χ₈ ((p : ℕ) : ZMod 8) = 1 := by
        have := chi8_sq_of_odd (n := (p : ℤ)) (by omega)
        rwa [Int.cast_natCast] at this
      have hε2 : ((jacobiSym (p : ℤ) e : ℤ) : ℂ) ^ 2 * ((ZMod.χ₈ ((p : ℕ) : ZMod 8) : ℤ) : ℂ) ^ 2
          = 1 := by
        have h1' : ((jacobiSym (p : ℤ) e : ℤ) : ℂ) ^ 2 = 1 := by
          rcases hε1 with h | h <;> rw [h] <;> norm_num
        have h2' : ((ZMod.χ₈ ((p : ℕ) : ZMod 8) : ℤ) : ℂ) ^ 2 = 1 := by
          rw [sq]
          exact_mod_cast congrArg (Int.cast : ℤ → ℂ) hχsq
        rw [h1', h2', one_mul]
      rw [if_pos (isUnramifiedCharAt_cmCharEv hodd hsq he hnev hdv),
        if_pos (isUnramifiedCharAt_cmCharEv hodd hsq he hnew hdw),
        cmCharEv_uniformizerIdele hodd hsq he hnev hdv,
        cmCharEv_uniformizerIdele hodd hsq he hnew hdw, htauv, htauw, hchiv, hchiw]
      unfold genK
      rw [gen_eq_of_primary h2v hab hv, gen_eq_of_primary h2w hab' hw, sigma_gaussOf,
        sigma_gaussOf, hnv, hnw]
    · have hcm : cmPrime p = 2 * a := by
        unfold cmPrime
        rw [if_pos h1, cmA_eq hp hn hab]
      have hrec : jacobiSym (2 * (e : ℤ)) p =
          jacobiSym (p : ℤ) e * ZMod.χ₈ ((p : ℕ) : ZMod 8) := by
        rw [jacobiSym.mul_left, jacobiSym.at_two (Nat.odd_iff.2 (by omega)),
          ← jacobiSym.quadratic_reciprocity_one_mod_four h1 (Nat.odd_iff.2 hodd), mul_comm]
      rw [hrec, hcm, natCast_cpow_neg_half, div_eq_mul_inv, div_eq_mul_inv]
      push_cast
      ring
    · have h1' : ((a : ℂ) + (b : ℂ) * sigJ K) / ((Real.sqrt p : ℝ) : ℂ) *
          (((a : ℂ) + ((-b : ℤ) : ℂ) * sigJ K) / ((Real.sqrt p : ℝ) : ℂ)) = 1 := by
        rw [div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero hs0 hs0)]
        push_cast
        linear_combination hnC - hss - (b : ℂ) ^ 2 * hj
      linear_combination ((jacobiSym (p : ℤ) e : ℤ) : ℂ) ^ 2 *
        ((ZMod.χ₈ ((p : ℕ) : ZMod 8) : ℤ) : ℂ) ^ 2 * h1' + hε2

theorem cmCharEv_ne_normPowChar (τ : ℝ) : cmCharEv K hodd hsq he ≠ normPowChar K τ := by
  intro h
  set t : ((placeTwo K).adicCompletion K)ˣ :=
    Units.map ((toCompl K (placeTwo K) : 𝓞 K →+* _) : 𝓞 K →* _) (gaussIUnit K) with ht
  set x₀ : (𝔸)ˣ := locIdele K (placeTwo K) t with hx₀
  have hpow : x₀ ^ 4 = 1 := by
    rw [hx₀, ht, ← map_pow, ← map_pow, ← map_pow, unit_pow_four, map_one, map_one, map_one]
  have hnorm : ideleNorm K x₀ = 1 := by
    have h4 : ideleNorm K x₀ ^ 4 = 1 := by
      have : ideleNorm K (x₀ ^ 4) = ideleNorm K x₀ ^ 4 := by
        simp only [pow_succ, pow_zero, one_mul, ideleNorm_mul]
      rw [← this, hpow, ideleNorm_one K]
    exact (pow_eq_one_iff_of_nonneg (ideleNorm_pos x₀).le (by norm_num)).1 h4
  have key : cmCharEv K hodd hsq he x₀ = 1 := by
    rw [h]
    refine Units.ext ?_
    show ((ideleNorm K x₀ : ℝ) : ℂ) ^ (Complex.I * τ) = 1
    rw [hnorm, Complex.ofReal_one, Complex.one_cpow]
  exact cmCharEv_locIdele_two_ne_one hodd hsq he key

end CMPoints

/-- **The Dirichlet series of `cmCoeffTw (2e)` has an entire continuation**,
for `e` odd and squarefree. -/
theorem CMPoints.exists_entire_lseries_cmCoeffTw_two_mul (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {4} ℚ K] {e : ℕ} (hodd : e % 2 = 1) (hsq : Squarefree e) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      ∀ s : ℂ, 3 / 2 < s.re →
        F s = LSeries (fun n => ((CMPoints.cmCoeffTw (2 * (e : ℤ)) n : ℤ) : ℂ)) s := by
  have he : e ≠ 0 := by
    rintro rfl
    simp at hodd
  refine CMPoints.exists_entire_lseries_of_hasProd_places K (CMPoints.cmCharEv K hodd hsq he)
    (Units.continuous_val.comp (CMPoints.continuous_cmCharEv hodd hsq he))
    (CMPoints.isUnitaryChar_cmCharEv hodd hsq he) (CMPoints.isIdeleClassChar_cmCharEv hodd hsq he)
    (insert (CMPoints.placeTwo K) (CMPoints.finite_setOf_natCast_mem (K := K) he).toFinset)
    (fun v hv => ?_) (CMPoints.cmCharEv_ne_normPowChar hodd hsq he) _ (fun s hs => ?_)
  · rw [Finset.mem_insert, not_or, Set.Finite.mem_toFinset] at hv
    exact CMPoints.isUnramifiedCharAt_cmCharEv hodd hsq he hv.1 hv.2
  · rw [CMPoints.cmCoeffTw_eq_gCoeff]
    exact CMPoints.hasProd_places_of_isGenEulerDatum
      (CMPoints.isGenEulerDatum_cmCharEv hodd hsq he) ⟨2 * (e : ℤ), by norm_num⟩
      (fun p _ h => CMPoints.twCoeff_eq_zero _ p h) (CMPoints.twCoeff_sq_le _) hs

/-- **The Mathlib L-series of `y² = x³ − d²x` over `ℚ` has an entire
continuation, for every nonzero natural `d`.** -/
theorem CMPoints.entire_lseries_curveD_of_ne_zero {d : ℕ} (hd : d ≠ 0) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      ∀ s : ℂ, 3 / 2 < s.re →
        F s = (⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ).LSeries s := by
  haveI : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  obtain ⟨d', m, hmd, hsq⟩ := Nat.sq_mul_squarefree d
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hmd
    exact hd hmd.symm
  have hmZ : (m : ℤ) ≠ 0 := by exact_mod_cast hm0
  by_cases hpar : d' % 2 = 1
  · -- odd squarefree part
    obtain ⟨F, hF, h⟩ := CMPoints.entire_lseries_curveD hpar hsq
    refine ⟨F, hF, fun s hs => ?_⟩
    rw [h s hs]
    have e1 : (⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ) =
        CMPoints.curveD ℚ ((((d' : ℤ) * (m : ℤ) ^ 2 : ℤ)) : ℚ) := by
      have hq : (d : ℚ) = ((((d' : ℤ) * (m : ℤ) ^ 2 : ℤ)) : ℚ) := by
        rw [← hmd]
        push_cast
        ring
      rw [hq]
      rfl
    have e2 : (⟨0, 0, 0, -(d' : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ) =
        CMPoints.curveD ℚ (((d' : ℤ) : ℤ) : ℚ) := by
      rw [Int.cast_natCast]
      rfl
    rw [e1, e2, WeierstrassCurve.LSeries, WeierstrassCurve.LSeries,
      CMPoints.LFunction_curveD_mul_sq (by exact_mod_cast Nat.odd_iff.2 hpar)
        (Int.squarefree_natCast.2 hsq) hmZ]
  · -- even squarefree part: `d' = 2 e` with `e` odd and squarefree
    obtain ⟨e, he⟩ : ∃ e, d' = 2 * e := ⟨d' / 2, by omega⟩
    subst he
    have hesq : Squarefree e := hsq.of_mul_right
    have heodd : e % 2 = 1 := by
      by_contra h
      obtain ⟨f, hf⟩ : ∃ f, e = 2 * f := ⟨e / 2, by omega⟩
      have h22 : (2 : ℕ) * 2 ∣ 2 * e := ⟨f, by rw [hf]; ring⟩
      exact absurd (hsq 2 h22) (by decide)
    have heoddZ : Odd (e : ℤ) := by exact_mod_cast Nat.odd_iff.2 heodd
    have hesqZ : Squarefree (e : ℤ) := Int.squarefree_natCast.2 hesq
    obtain ⟨F, hF, h⟩ :=
      CMPoints.exists_entire_lseries_cmCoeffTw_two_mul (CyclotomicField 4 ℚ) heodd hesq
    refine ⟨F, hF, fun s hs => ?_⟩
    have e1 : (⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ) =
        CMPoints.curveD ℚ (((2 * (e : ℤ) * (m : ℤ) ^ 2 : ℤ)) : ℚ) := by
      have hq : (d : ℚ) = (((2 * (e : ℤ) * (m : ℤ) ^ 2 : ℤ)) : ℚ) := by
        rw [← hmd]
        push_cast
        ring
      rw [hq]
      rfl
    rw [h s hs, e1, WeierstrassCurve.LSeries,
      CMPoints.LFunction_curveD_two_mul_sq heoddZ hesqZ hmZ]
    congr 1
    funext n
    show ((CMPoints.cmCoeffTw (2 * (e : ℤ)) n : ℤ) : ℂ) =
      (((CMPoints.curveD ℚ (((2 * (e : ℤ) : ℤ)) : ℚ)).LFunction n : ℤ) : ℂ)
    rw [CMPoints.LFunction_curveD_two_mul_eq_cmCoeffTw heoddZ hesqZ n]
