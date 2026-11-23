import HeckeCM.TwistLocal
import HeckeCM.QuadSums

/-!
# The local root number at an inert prime dividing `d`

Let `p ≡ 3 (mod 4)` be a prime, `d = p·m` odd and squarefree, and `v = (p)` the
place of `K = ℚ(i)` above `p`.

* `sum_inert`: `Σ_{x,y} e(2x/p) · χ(x² + y²) = p`;
* `stdRootNumberAt_twC_inert`: the local root number of `twC` at `v` is 1;
* `stdRootNumberAt_cmCharTw_inert`: that of `cmCharTw` is `−1`.
-/

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero MeasureTheory
open NumberField.AdelicLevel AutomorphicForm NumberField.TateGlobal
open NumberField.StandardAddChar LanglandsTunnell.TateLocal
open scoped Classical

namespace CMPoints

/-! ## Sums over `ZMod p` -/

section PureSums

variable {p : ℕ} [Fact p.Prime]

lemma two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)

lemma ringChar_zmod_ne_two (hp2 : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  exact hp2

lemma sum_stdAddChar_two_mul (hp2 : p ≠ 2) :
    ∑ x : ZMod p, (ZMod.stdAddChar (N := p)) (2 * x) = 0 := by
  have h := AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar p (two_ne_zero_zmod hp2))
  simpa [AddChar.mulShift_apply] using h

lemma inv_quadraticChar (a : ZMod p) :
    (((quadraticChar (ZMod p) a : ℤ)) : ℂ)⁻¹ = ((quadraticChar (ZMod p) a : ℤ) : ℂ) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rcases quadraticChar_dichotomy ha with h | h <;> rw [h] <;> norm_num

theorem sum_inert (hp2 : p ≠ 2) :
    ∑ i : ZMod p × ZMod p, (ZMod.stdAddChar (N := p)) (2 * i.1) *
      ((quadraticChar (ZMod p) (i.1 ^ 2 + i.2 ^ 2) : ℤ) : ℂ) = p := by
  have hc := ringChar_zmod_ne_two hp2
  rw [Fintype.sum_prod_type]
  have hin : ∀ x : ZMod p, ∑ y : ZMod p, (ZMod.stdAddChar (N := p)) (2 * x) *
      ((quadraticChar (ZMod p) (x ^ 2 + y ^ 2) : ℤ) : ℂ) =
      (ZMod.stdAddChar (N := p)) (2 * x) * ((if x = 0 then (p : ℂ) else 0) - 1) := by
    intro x
    rw [← Finset.mul_sum, ← Int.cast_sum]
    congr 1
    by_cases hx : x = 0
    · subst hx
      rw [if_pos rfl]
      have h := sum_quadraticChar_sq (p := p) hc
      have e : ∀ y : ZMod p, (0 : ZMod p) ^ 2 + y ^ 2 = y ^ 2 := fun y => by ring
      simp only [e]
      rw [h]
      push_cast
      ring
    · rw [if_neg hx]
      have h := sum_quadraticChar_sq_add (p := p) hc (c := x ^ 2) (pow_ne_zero 2 hx)
      have e : ∀ y : ZMod p, x ^ 2 + y ^ 2 = y ^ 2 + x ^ 2 := fun y => by ring
      simp only [e]
      rw [h]
      push_cast
      ring
  rw [Finset.sum_congr rfl fun x _ => hin x]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, mul_ite, mul_zero]
  rw [sum_stdAddChar_two_mul hp2, Finset.sum_ite_eq' Finset.univ (0 : ZMod p)]
  simp

lemma zmod_eq_of_dvd_val_sub {x y : ZMod p} (h : (p : ℤ) ∣ (x.val : ℤ) - y.val) : x = y := by
  have := (ZMod.intCast_eq_intCast_iff_dvd_sub (y.val : ℤ) (x.val : ℤ) p).2 h
  simpa using this.symm

lemma dvd_sub_val (A : ℤ) : (p : ℤ) ∣ A - (((A : ZMod p)).val : ℤ) := by
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
  simp

lemma natCast_sq_cpow_half (n : ℕ) : ((n ^ 2 : ℕ) : ℂ) ^ ((1 : ℂ) / 2) = n := by
  rw [Nat.cast_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_pow,
    show ((1 : ℂ) / 2) = (((1 / 2 : ℝ)) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq (Nat.cast_nonneg n)]

end PureSums

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

local notation "𝔸" => AdeleRing (𝓞 K) K

attribute [local instance] localBorel borelSpace_localBorel

/-- If `p ∉ v'` and `p·m ∈ v'`, then `m ∈ v'`. -/
lemma cofactor_mem {p m : ℕ} {v' : HeightOneSpectrum (𝓞 K)} (hp' : ((p : ℕ) : 𝓞 K) ∉ v'.asIdeal)
    (hd' : (((p * m : ℕ)) : 𝓞 K) ∈ v'.asIdeal) : ((m : ℤ) : 𝓞 K) ∈ v'.asIdeal := by
  have e : (((p * m : ℕ)) : 𝓞 K) = ((p : ℕ) : 𝓞 K) * ((m : ℤ) : 𝓞 K) := by
    push_cast
    ring
  rw [e] at hd'
  exact (v'.isPrime.mem_or_mem hd').resolve_left hp'

variable {p : ℕ} [hp : Fact p.Prime]

variable (K p) in
/-- The representatives `x + y i`, `0 ≤ x, y < p`. -/
def repI (i : ZMod p × ZMod p) : 𝓞 K := gaussOf K (i.1.val : ℤ) (i.2.val : ℤ)

section Place

variable {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal = Ideal.span {gaussOf K (-(p : ℤ)) 0})
include hv

lemma gaussOf_mem_inert_iff (a b : ℤ) :
    gaussOf K a b ∈ v.asIdeal ↔ (p : ℤ) ∣ a ∧ (p : ℤ) ∣ b := by
  have e : gaussOf K (-(p : ℤ)) 0 = ((-(p : ℤ) : ℤ) : 𝓞 K) := by simp [gaussOf]
  rw [hv, Ideal.mem_span_singleton, e, intCast_dvd_gaussOf_iff, neg_dvd, neg_dvd]

lemma repI_inj (i j : ZMod p × ZMod p) (h : repI K p i - repI K p j ∈ v.asIdeal) : i = j := by
  have e : repI K p i - repI K p j =
      gaussOf K ((i.1.val : ℤ) - j.1.val) ((i.2.val : ℤ) - j.2.val) := by
    unfold repI gaussOf
    push_cast
    ring
  rw [e, gaussOf_mem_inert_iff hv] at h
  exact Prod.ext (zmod_eq_of_dvd_val_sub h.1) (zmod_eq_of_dvd_val_sub h.2)

lemma repI_cover (α : 𝓞 K) : ∃ i, α - repI K p i ∈ v.asIdeal := by
  obtain ⟨A, B, rfl⟩ := exists_coords α
  refine ⟨((A : ZMod p), (B : ZMod p)), ?_⟩
  have e : (A : 𝓞 K) + (B : 𝓞 K) * gaussI K - repI K p ((A : ZMod p), (B : ZMod p)) =
      gaussOf K (A - ((A : ZMod p)).val) (B - ((B : ZMod p)).val) := by
    unfold repI gaussOf
    push_cast
    ring
  rw [e, gaussOf_mem_inert_iff hv]
  exact ⟨dvd_sub_val A, dvd_sub_val B⟩

lemma eq_zero_of_repI_mem {i : ZMod p × ZMod p} (h : repI K p i ∈ v.asIdeal) : i = 0 := by
  unfold repI at h
  rw [gaussOf_mem_inert_iff hv] at h
  refine Prod.ext (zmod_eq_of_dvd_val_sub ?_) (zmod_eq_of_dvd_val_sub ?_)
  · simpa using h.1
  · simpa using h.2

lemma psi_repI (hprim : IsPrimaryPair (-(p : ℤ)) 0) (h2v : (2 : 𝓞 K) ∉ v.asIdeal)
    (i : ZMod p × ZMod p) :
    psiLocal K v ((toCompl K v (gen K v))⁻¹ * toCompl K v (repI K p i)) =
      (ZMod.stdAddChar (N := p)) (2 * i.1) := by
  have hg := gen_eq_of_primary h2v hprim hv
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hgK : genK K v = algebraMap ℚ K (-(p : ℚ)) := by
    unfold genK
    rw [hg]
    simp [gaussOf]
  have e : (toCompl K v (gen K v))⁻¹ * toCompl K v (repI K p i) =
      algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K (repI K p i) / genK K v) := by
    rw [map_div₀, div_eq_inv_mul]
    rfl
  rw [e, psiLocal_algebraMap_of_integral_away K v _ (fun w hw => by
    rw [map_div₀, valuation_genK_of_ne hw.symm, div_one]
    exact valuation_le_one w _)]
  have htr : Algebra.trace ℚ K (algebraMap (𝓞 K) K (repI K p i) / genK K v) =
      -(2 * (i.1.val : ℚ)) / p := by
    have hs : algebraMap (𝓞 K) K (repI K p i) / genK K v =
        (-(p : ℚ))⁻¹ • algebraMap (𝓞 K) K (repI K p i) := by
      rw [hgK, Algebra.smul_def, map_inv₀, div_eq_inv_mul]
    rw [hs, map_smul, repI, trace_gaussOf, smul_eq_mul]
    push_cast
    field_simp
  rw [htr]
  have hz : (ZMod.stdAddChar (N := p)) (2 * i.1) =
      (ZMod.stdAddChar (N := p)) (((2 * (i.1.val : ℤ) : ℤ)) : ZMod p) := by
    congr 1
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [hz, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

variable {m : ℕ} (hodd : (p * m) % 2 = 1) (hsq : Squarefree (p * m)) (hd : p * m ≠ 0)
  (hmem : ∀ u : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ u.asIdeal ↔ u = v)
include hodd hsq hmem

lemma charExt_twC_repI (i : ZMod p × ZMod p) (hi : repI K p i ∉ v.asIdeal) :
    charExt (localChar (twC K hodd hsq hd) v)⁻¹ (toCompl K v (repI K p i)) =
      ((quadraticChar (ZMod p) (i.1 ^ 2 + i.2 ^ 2) : ℤ) : ℂ) := by
  have hρ1 := (valued_toCompl_eq_one_iff v _).2 hi
  have hρ : toCompl K v (repI K p i) ≠ 0 := fun h => by
    rw [h, map_zero] at hρ1
    exact zero_ne_one hρ1
  have hpm : p.Coprime m := Nat.coprime_of_squarefree_mul hsq
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hd
  obtain ⟨X, hX1, hX2⟩ := exists_int_modEq hpm hp.out.ne_zero hm0 (i.1.val : ℤ) 1
  obtain ⟨Y, hY1, hY2⟩ := exists_int_modEq hpm hp.out.ne_zero hm0 (i.2.val : ℤ) 0
  rw [sub_zero] at hY2
  have h1 : gaussOf K X Y - repI K p i ∈ v.asIdeal := by
    have e : gaussOf K X Y - repI K p i = gaussOf K (X - i.1.val) (Y - i.2.val) := by
      unfold repI gaussOf
      push_cast
      ring
    rw [e, gaussOf_mem_inert_iff hv]
    exact ⟨hX1, hY1⟩
  have h2 : ∀ v' : HeightOneSpectrum (𝓞 K), v' ≠ v → (((p * m : ℕ)) : 𝓞 K) ∈ v'.asIdeal →
      gaussOf K X Y - 1 ∈ v'.asIdeal := by
    intro v' hne hd'
    have hmv := cofactor_mem (fun h => hne ((hmem v').1 h)) hd'
    have e : gaussOf K X Y - 1 = gaussOf K (X - 1) Y := by
      unfold gaussOf
      push_cast
      ring
    obtain ⟨q, hq⟩ := (intCast_dvd_gaussOf_iff (K := K)).2 ⟨hX2, hY2⟩
    rw [e, hq]
    exact v'.asIdeal.mul_mem_right _ hmv
  have hval := twC_locIdele_toCompl hodd hsq hd hρ hi h1 h2
  have hloc : ((localChar (twC K hodd hsq hd) v (Units.mk0 _ hρ) : ℂˣ) : ℂ) =
      ((tau K (p * m) (gaussOf K X Y) : ℤ) : ℂ) := hval
  have hj1 : (p : ℤ) ∣ (X ^ 2 + Y ^ 2) - ((i.1.val : ℤ) ^ 2 + (i.2.val : ℤ) ^ 2) := by
    obtain ⟨k, hk⟩ := hX1
    obtain ⟨l, hl⟩ := hY1
    exact ⟨k * (X + i.1.val) + l * (Y + i.2.val), by
      linear_combination (X + i.1.val) * hk + (Y + i.2.val) * hl⟩
  have hj2 : (m : ℤ) ∣ (X ^ 2 + Y ^ 2) - 1 := by
    obtain ⟨k, hk⟩ := hX2
    obtain ⟨l, hl⟩ := hY2
    exact ⟨k * (X + 1) + l * Y, by linear_combination (X + 1) * hk + Y * hl⟩
  rw [charExt_of_ne_zero _ hρ, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, hloc, tau,
    nrm_gaussOf, jacobiSym_mul_eq hm0 hj1 hj2]
  have e : ((((i.1.val : ℤ) ^ 2 + (i.2.val : ℤ) ^ 2 : ℤ)) : ZMod p) = i.1 ^ 2 + i.2 ^ 2 := by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  show (((quadraticChar (ZMod p) ((((i.1.val : ℤ) ^ 2 + (i.2.val : ℤ) ^ 2 : ℤ)) : ZMod p) : ℤ)) :
    ℂ)⁻¹ = _
  rw [e, inv_quadraticChar]

lemma charExt_twC_gen_inv_inert (hprim : IsPrimaryPair (-(p : ℤ)) 0)
    (h2v : (2 : 𝓞 K) ∉ v.asIdeal) :
    charExt (localChar (twC K hodd hsq hd) v) (toCompl K v (gen K v))⁻¹ = 1 := by
  have hg := gen_eq_of_primary h2v hprim hv
  have hpm : p.Coprime m := Nat.coprime_of_squarefree_mul hsq
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hd
  obtain ⟨a, b, hab⟩ : IsCoprime (p : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.2 hpm
  obtain ⟨B, hB1, hB2⟩ := exists_int_modEq hpm hp.out.ne_zero hm0 1 (-a)
  obtain ⟨k1, hk1⟩ := hB1
  obtain ⟨k2, hk2⟩ := hB2
  have hprod : B * (-(p : ℤ)) - 1 = (m : ℤ) * (-b - k2 * p) := by
    linear_combination (-(p : ℤ)) * hk2 + hab
  have h1 : ((B : ℤ) : 𝓞 K) - 1 ∈ v.asIdeal := by
    have e : ((B : ℤ) : 𝓞 K) - 1 = gaussOf K (B - 1) 0 := by
      unfold gaussOf
      push_cast
      ring
    rw [e, gaussOf_mem_inert_iff hv]
    exact ⟨⟨k1, hk1⟩, dvd_zero _⟩
  have h2 : ∀ v' : HeightOneSpectrum (𝓞 K), v' ≠ v → (((p * m : ℕ)) : 𝓞 K) ∈ v'.asIdeal →
      ((B : ℤ) : 𝓞 K) * gen K v - 1 ∈ v'.asIdeal := by
    intro v' hne hd'
    have hmv := cofactor_mem (fun h => hne ((hmem v').1 h)) hd'
    have e : ((B : ℤ) : 𝓞 K) * gen K v - 1 = ((m : ℤ) : 𝓞 K) * (((-b - k2 * p : ℤ)) : 𝓞 K) := by
      rw [hg, ← Int.cast_mul, ← hprod]
      unfold gaussOf
      push_cast
      ring
    rw [e]
    exact v'.asIdeal.mul_mem_right _ hmv
  have hval := twC_locIdele_gen hodd hsq hd h1 h2
  have hgcd : Int.gcd B ((p * m : ℕ) : ℤ) = 1 := by
    have c1 : IsCoprime B (p : ℤ) := ⟨1, -k1, by linear_combination hk1⟩
    have c2 : IsCoprime B (m : ℤ) := ⟨-(p : ℤ), b + k2 * p, by linear_combination hprod⟩
    have := Int.isCoprime_iff_gcd_eq_one.1 (c1.mul_right c2)
    rw [Nat.cast_mul]
    exact this
  have htau : tau K (p * m) ((B : ℤ) : 𝓞 K) = 1 := by
    have e : ((B : ℤ) : 𝓞 K) = gaussOf K B 0 := by simp [gaussOf]
    rw [tau, e, nrm_gaussOf]
    have : B ^ 2 + (0 : ℤ) ^ 2 = B ^ 2 := by ring
    rw [this]
    exact jacobiSym.sq_one' hgcd
  have hz : (toCompl K v (gen K v))⁻¹ ≠ 0 := inv_ne_zero (toCompl_gen_ne_zero' v)
  have hu : Units.mk0 (toCompl K v (gen K v))⁻¹ hz =
      (Units.mk0 (toCompl K v (gen K v)) (toCompl_gen_ne_zero' v))⁻¹ :=
    Units.ext (by simp)
  have hloc : ((localChar (twC K hodd hsq hd) v (Units.mk0 (toCompl K v (gen K v))
      (toCompl_gen_ne_zero' v)) : ℂˣ) : ℂ) = ((tau K (p * m) ((B : ℤ) : 𝓞 K) : ℤ) : ℂ) := hval
  rw [charExt_of_ne_zero _ hz, hu, map_inv, Units.val_inv_eq_inv_val, hloc, htau]
  simp

/-- **The local root number of `twC` at an inert prime is 1.** -/
theorem stdRootNumberAt_twC_inert (hp3 : p % 4 = 3) (hN : Ideal.absNorm v.asIdeal = p ^ 2)
    (hprim : IsPrimaryPair (-(p : ℤ)) 0) :
    stdRootNumberAt K v (localChar (twC K hodd hsq hd) v) = 1 := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    omega
  have hpv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal := (hmem v).2 rfl
  have h2v : (2 : 𝓞 K) ∉ v.asIdeal := two_not_mem v (by omega) hpv
  have hdv : (((p * m : ℕ)) : 𝓞 K) ∈ v.asIdeal := by
    rw [Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ hpv
  have G := gauss_sum_twC hodd hsq hd hdv (repI K p) (repI_cover hv) (repI_inj hv)
  have hS : ∑ i : {i // repI K p i ∉ v.asIdeal},
      psiLocal K v ((toCompl K v (gen K v))⁻¹ * toCompl K v (repI K p i)) *
        charExt (localChar (twC K hodd hsq hd) v)⁻¹ (toCompl K v (repI K p i)) = (p : ℂ) := by
    rw [← sum_inert (p := p) hp2,
      ← Finset.sum_subtype (Finset.univ.filter fun i => repI K p i ∉ v.asIdeal) (fun i => by simp)
        (fun i => psiLocal K v ((toCompl K v (gen K v))⁻¹ * toCompl K v (repI K p i)) *
          charExt (localChar (twC K hodd hsq hd) v)⁻¹ (toCompl K v (repI K p i))),
      Finset.sum_congr rfl (fun i hi => by
        rw [psi_repI hv hprim h2v i,
          charExt_twC_repI hv hodd hsq hd hmem i (Finset.mem_filter.1 hi).2])]
    refine Finset.sum_filter_of_ne fun i _ hne hmemi => hne ?_
    rw [eq_zero_of_repI_mem hv hmemi]
    simp
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  rw [hS, charExt_twC_gen_inv_inert hv hodd hsq hd hmem hprim h2v, hN, natCast_sq_cpow_half,
    one_mul] at G
  rw [← G]
  push_cast
  field_simp

/-- **The local root number of `cmCharTw` at an inert prime is `−1`.** -/
theorem stdRootNumberAt_cmCharTw_inert (hp3 : p % 4 = 3) (hN : Ideal.absNorm v.asIdeal = p ^ 2)
    (hprim : IsPrimaryPair (-(p : ℤ)) 0) :
    stdRootNumberAt K v (localChar (cmCharTw K hodd hsq hd) v) = -1 := by
  have hpv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal := (hmem v).2 rfl
  have h2v : (2 : 𝓞 K) ∉ v.asIdeal := two_not_mem v (by omega) hpv
  have hdv : (((p * m : ℕ)) : 𝓞 K) ∈ v.asIdeal := by
    rw [Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ hpv
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  rw [stdRootNumberAt_cmCharTw_of_mem hodd hsq hd hdv,
    stdRootNumberAt_twC_inert hv hodd hsq hd hmem hp3 hN hprim, mul_one]
  unfold genK
  rw [gen_eq_of_primary h2v hprim hv, sigma_gaussOf]
  push_cast
  rw [zero_mul, add_zero, norm_neg, Complex.norm_natCast, Complex.ofReal_natCast, neg_div,
    div_self hp0]

end Place

end CMPoints
