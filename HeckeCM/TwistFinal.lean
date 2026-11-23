import HeckeCM.TwistValues
import HeckeCM.GenConditional
import Definitions.Def_NumberField_NormPowChar

/-!
# The L-series of `y² = x³ − d²x` has an entire continuation, for `d` odd and squarefree

* `isGenEulerDatum_cmCharTw`: the local values of the twisted character are those
  of the sequence `cmCoeffTw d`;
* `cmCharTw_ne_normPowChar`: the twisted character is not a power of the norm;
* `exists_entire_lseries_cmCoeffTw`: the Dirichlet series of `cmCoeffTw d` has an
  entire continuation;
* `entire_lseries_curveD`: the Mathlib L-series of `y² = x³ − d²x` has an
  entire continuation.
-/

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open NumberField.AdelicLevel AutomorphicForm NumberField.TateGlobal
open scoped Classical

namespace CMPoints

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

local notation "𝔸" => AdeleRing (𝓞 K) K

variable {d : ℕ} (hodd : d % 2 = 1) (hsq : Squarefree d) (hd : d ≠ 0)
include hodd hsq

/-- **The local values of the twisted character are those of `cmCoeffTw d`.** -/
theorem isGenEulerDatum_cmCharTw :
    IsGenEulerDatum K (fun p : ℕ => (p : ℤ) ∣ 2 * (d : ℤ))
      (fun p => jacobiSym (d : ℤ) p * cmPrime p)
      (fun v => if IsUnramifiedCharAt (cmCharTw K hodd hsq hd) v then
        ((cmCharTw K hodd hsq hd (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) := by
  -- a place above a good prime does not contain `d`
  have hgood : ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ 2 * (d : ℤ) → ∀ v : HeightOneSpectrum (𝓞 K),
      ((p : ℕ) : 𝓞 K) ∈ v.asIdeal → ((d : ℕ) : 𝓞 K) ∉ v.asIdeal := by
    intro p hp hb v hpv hdv
    have := dvd_of_intCast_mem hp hpv (N := (d : ℤ)) (by simpa using hdv)
    exact hb (Dvd.dvd.mul_left this 2)
  refine ⟨fun v => ?_, fun p hp hb v hv => ?_, fun p hp hb h3 => ?_, fun p hp hb h1 => ?_⟩
  · split_ifs
    · exact (isUnitaryChar_cmCharTw hodd hsq hd _).le
    · rw [norm_zero]
      exact zero_le_one
  · rw [if_neg]
    have hb' : p ∣ 2 * d := by exact_mod_cast hb
    rcases (Nat.Prime.dvd_mul hp).1 hb' with h | h
    · have h2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h
      subst h2
      have h2' : (2 : 𝓞 K) ∈ v.asIdeal := by simpa using hv
      rw [eq_placeTwo_of_two_mem h2']
      exact not_isUnramifiedCharAt_cmCharTw_two hodd hsq hd
    · refine not_isUnramifiedCharAt_cmCharTw_of_mem hodd hsq hd ?_
      obtain ⟨m, hm⟩ := h
      rw [hm, Nat.cast_mul]
      exact v.asIdeal.mul_mem_right _ hv
  · haveI := Fact.mk hp
    have hpd : ¬ p ∣ d := fun h => hb (Dvd.dvd.mul_left (Int.natCast_dvd_natCast.2 h) 2)
    obtain ⟨v, hmem, hN, hprim, hv⟩ := exists_primary_inert (K := K) p h3
    refine ⟨v, hmem, hN, ?_⟩
    have hpv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal := (hmem v).2 rfl
    have h2v : (2 : 𝓞 K) ∉ v.asIdeal := two_not_mem v (by omega) hpv
    have hne : v ≠ placeTwo K := fun h => h2v (h ▸ two_mem_placeTwo)
    have hdv := hgood p hp hb v hpv
    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have hgcd : Int.gcd (p : ℤ) d = 1 := by
      rw [Int.gcd_natCast_natCast]
      exact (Nat.Prime.coprime_iff_not_dvd hp).2 hpd
    have htau : tau K d (gen K v) = 1 := by
      rw [gen_eq_of_primary h2v hprim hv, tau, nrm_gaussOf,
        show (-(p : ℤ)) ^ 2 + 0 ^ 2 = (p : ℤ) ^ 2 by ring, jacobiSym.sq_one' hgcd]
    rw [if_pos (isUnramifiedCharAt_cmCharTw hodd hsq hd hne hdv),
      cmCharTw_uniformizerIdele hodd hsq hd hne hdv, htau, Int.cast_one, mul_one]
    unfold genK
    rw [gen_eq_of_primary h2v hprim hv, sigma_gaussOf]
    push_cast
    rw [zero_mul, add_zero, norm_neg, Complex.norm_natCast, Complex.ofReal_natCast, neg_div,
      div_self hp0]
  · haveI := Fact.mk hp
    have hpd : ¬ p ∣ d := fun h => hb (Dvd.dvd.mul_left (Int.natCast_dvd_natCast.2 h) 2)
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
      have hnw : ‖(a : ℂ) + ((-b : ℤ) : ℂ) * sigJ K‖ = Real.sqrt p := by
        rw [norm_add_mul_of_sq hj, show a ^ 2 + (-b) ^ 2 = (p : ℤ) by rw [neg_sq]; exact hn,
          Int.cast_natCast]
      have hgcd : Int.gcd (p : ℤ) d = 1 := by
        rw [Int.gcd_natCast_natCast]
        exact (Nat.Prime.coprime_iff_not_dvd hp).2 hpd
      have hε1 := jacobiSym.eq_one_or_neg_one hgcd
      have htauv : tau K d (gen K v) = jacobiSym (p : ℤ) d := by
        rw [gen_eq_of_primary h2v hab hv, tau, nrm_gaussOf, hn]
      have htauw : tau K d (gen K w) = jacobiSym (p : ℤ) d := by
        rw [gen_eq_of_primary h2w hab' hw, tau, nrm_gaussOf,
          show a ^ 2 + (-b) ^ 2 = (p : ℤ) by rw [neg_sq]; exact hn]
      have hε2 : ((jacobiSym (p : ℤ) d : ℤ) : ℂ) ^ 2 = 1 := by
        rcases hε1 with h | h <;> rw [h] <;> norm_num
      rw [if_pos (isUnramifiedCharAt_cmCharTw hodd hsq hd hnev hdv),
        if_pos (isUnramifiedCharAt_cmCharTw hodd hsq hd hnew hdw),
        cmCharTw_uniformizerIdele hodd hsq hd hnev hdv,
        cmCharTw_uniformizerIdele hodd hsq hd hnew hdw, htauv, htauw]
      unfold genK
      rw [gen_eq_of_primary h2v hab hv, gen_eq_of_primary h2w hab' hw, sigma_gaussOf,
        sigma_gaussOf, hnv, hnw]
    · have hcm : cmPrime p = 2 * a := by
        unfold cmPrime
        rw [if_pos h1, cmA_eq hp hn hab]
      have hrec : jacobiSym (d : ℤ) p = jacobiSym (p : ℤ) d :=
        (jacobiSym.quadratic_reciprocity_one_mod_four h1 (Nat.odd_iff.2 hodd)).symm
      rw [hrec, hcm, natCast_cpow_neg_half, div_eq_mul_inv, div_eq_mul_inv]
      push_cast
      ring
    · have h1' : ((a : ℂ) + (b : ℂ) * sigJ K) / ((Real.sqrt p : ℝ) : ℂ) *
          (((a : ℂ) + ((-b : ℤ) : ℂ) * sigJ K) / ((Real.sqrt p : ℝ) : ℂ)) = 1 := by
        rw [div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero hs0 hs0)]
        push_cast
        linear_combination hnC - hss - (b : ℂ) ^ 2 * hj
      linear_combination ((jacobiSym (p : ℤ) d : ℤ) : ℂ) ^ 2 * h1' + hε2

/-- **The twisted character is not an imaginary power of the norm.** -/
theorem cmCharTw_ne_normPowChar (τ : ℝ) : cmCharTw K hodd hsq hd ≠ normPowChar K τ := by
  intro h
  set t : ((placeTwo K).adicCompletion K)ˣ :=
    Units.map ((toCompl K (placeTwo K) : 𝓞 K →+* _) : 𝓞 K →* _) (gaussIUnit K) with ht
  have htv : (t : (placeTwo K).adicCompletion K) = toCompl K (placeTwo K) (gaussIUnit K) := rfl
  have ht1 : Valued.v (t : (placeTwo K).adicCompletion K) = 1 := by
    rw [htv, valued_toCompl_unit]
  set x₀ : (𝔸)ˣ := locIdele K (placeTwo K) t with hx₀
  have hpow : x₀ ^ 4 = 1 := by
    rw [hx₀, ht, ← map_pow, ← map_pow, ← map_pow, unit_pow_four, map_one, map_one, map_one]
  have hnorm : ideleNorm K x₀ = 1 := by
    have h4 : ideleNorm K x₀ ^ 4 = 1 := by
      have : ideleNorm K (x₀ ^ 4) = ideleNorm K x₀ ^ 4 := by
        simp only [pow_succ, pow_zero, one_mul, ideleNorm_mul]
      rw [← this, hpow, ideleNorm_one K]
    exact (pow_eq_one_iff_of_nonneg (ideleNorm_pos x₀).le (by norm_num)).1 h4
  have key : cmCharTw K hodd hsq hd x₀ = 1 := by
    rw [h]
    refine Units.ext ?_
    show ((ideleNorm K x₀ : ℝ) : ℂ) ^ (Complex.I * τ) = 1
    rw [hnorm, Complex.ofReal_one, Complex.one_cpow]
  rw [cmCharTw_apply, twC_locIdele_unit hodd hsq hd (natCast_notMem_placeTwo hodd) t ht1,
    mul_one] at key
  exact cmChar_localUnit_two_ne_one (K := K) key

end CMPoints

/-- **The Dirichlet series of `cmCoeffTw d` has an entire continuation**, for
`d` odd and squarefree. -/
theorem CMPoints.exists_entire_lseries_cmCoeffTw (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {4} ℚ K] {d : ℕ} (hodd : d % 2 = 1) (hsq : Squarefree d) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      ∀ s : ℂ, 3 / 2 < s.re →
        F s = LSeries (fun n => ((CMPoints.cmCoeffTw (d : ℤ) n : ℤ) : ℂ)) s := by
  have hd : d ≠ 0 := by
    rintro rfl
    simp at hodd
  refine CMPoints.exists_entire_lseries_of_hasProd_places K (CMPoints.cmCharTw K hodd hsq hd)
    (Units.continuous_val.comp (CMPoints.continuous_cmCharTw hodd hsq hd))
    (CMPoints.isUnitaryChar_cmCharTw hodd hsq hd) (CMPoints.isIdeleClassChar_cmCharTw hodd hsq hd)
    (insert (CMPoints.placeTwo K) (CMPoints.finite_setOf_natCast_mem (K := K) hd).toFinset)
    (fun v hv => ?_) (CMPoints.cmCharTw_ne_normPowChar hodd hsq hd) _ (fun s hs => ?_)
  · rw [Finset.mem_insert, not_or, Set.Finite.mem_toFinset] at hv
    exact CMPoints.isUnramifiedCharAt_cmCharTw hodd hsq hd hv.1 hv.2
  · rw [CMPoints.cmCoeffTw_eq_gCoeff]
    exact CMPoints.hasProd_places_of_isGenEulerDatum
      (CMPoints.isGenEulerDatum_cmCharTw hodd hsq hd) ⟨(d : ℤ), by norm_num⟩
      (fun p _ h => CMPoints.twCoeff_eq_zero _ p h) (CMPoints.twCoeff_sq_le _) hs

/-- **The Mathlib L-series of `y² = x³ − d²x` over `ℚ` has an entire
continuation**, for every odd squarefree natural `d`. -/
theorem CMPoints.entire_lseries_curveD {d : ℕ} (hodd : d % 2 = 1) (hsq : Squarefree d) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      ∀ s : ℂ, 3 / 2 < s.re →
        F s = (⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ).LSeries s := by
  haveI : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
    CyclotomicField.isCyclotomicExtension 4 ℚ
  obtain ⟨F, hF, h⟩ := CMPoints.exists_entire_lseries_cmCoeffTw (CyclotomicField 4 ℚ) hodd hsq
  refine ⟨F, hF, fun s hs => ?_⟩
  have e : (⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ) =
      CMPoints.curveD ℚ (((d : ℤ) : ℤ) : ℚ) := by
    rw [Int.cast_natCast]
    rfl
  have hL := CMPoints.LFunction_curveD_eq_cmCoeffTw_of_odd_squarefree (d := (d : ℤ))
    (by exact_mod_cast Nat.odd_iff.2 hodd) (Int.squarefree_natCast.2 hsq)
  rw [h s hs, e, WeierstrassCurve.LSeries]
  congr 1
  funext n
  show ((CMPoints.cmCoeffTw (d : ℤ) n : ℤ) : ℂ) =
    (((CMPoints.curveD ℚ (((d : ℤ) : ℤ) : ℚ)).LFunction n : ℤ) : ℂ)
  rw [hL n]
