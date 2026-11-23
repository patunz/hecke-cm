import HeckeCM.RootInert
import Theorems.Thm_LanglandsTunnell_TateLocal_stdRootNumberAt_mul_stdRootNumberAt_inv_eq_apply_neg_one

/-!
# The local root numbers at a split prime dividing `d`

Let `p ≡ 1 (mod 4)` be a prime, `p = a² + b²` with `(a, b)` primary, `d = p·m`
odd and squarefree, and `v = (a + bi)` and `w = (a − bi)` the two places above `p`.

* the Gauss sums computing the local root numbers of `twC` at `v` and at `w`
  are the same expression in `a` and `p`, and so is the value of `twC` at the
  test element: hence the two root numbers coincide;
* their square is `twC(−1) = (−1/p) = 1`;
* `stdRootNumberAt_cmCharTw_split`: the product of the local root numbers
  of `cmCharTw` at `v` and at `w` is 1.
-/

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero MeasureTheory
open NumberField.AdelicLevel AutomorphicForm NumberField.TateGlobal
open NumberField.StandardAddChar LanglandsTunnell.TateLocal
open scoped Classical

namespace CMPoints

/-! ## Ring identities -/

section RingIds

variable {R : Type*} [CommRing R] (P Q a n T e p E F e₁ e₂ e₃ f m : R)

lemma ring_id1 (hsum : P + Q = 2 * a) (hPQ : P * Q = p) (hT : 2 * a * T - 1 = p * e) :
    (1 + (n - 1) * T * Q) - n = P * ((n - 1) * (Q * e - T)) := by
  linear_combination (n - 1) * T * hsum + (n - 1) * hT - (n - 1) * e * hPQ

lemma ring_id2 (hsum : P + Q = 2 * a) (hPQ : P * Q = p) (hE : 2 * a * E - 1 = p * e₁) :
    (Q * E + P * F) - 1 = P * (Q * e₁ + F - E) := by
  linear_combination E * hsum + hE - e₁ * hPQ

lemma ring_id3 (hsum : P + Q = 2 * a) (hPQ : P * Q = p) (hF : 4 * a ^ 2 * F - 1 = p * e₂) :
    (Q * E + P * F) * P - 1 = Q * (P * E + P * e₂ + (Q - 4 * a) * F) := by
  linear_combination F * (P - Q + 2 * a) * hsum + hF - e₂ * hPQ

lemma ring_id4 (hPQ : P * Q = p) (hE3 : p * E - 1 = m * e₃) (hF3 : F = m * f) :
    (Q * E + P * F) * P - 1 = m * (e₃ + P ^ 2 * f) := by
  linear_combination E * hPQ + hE3 + P ^ 2 * hF3

end RingIds

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

local notation "𝔸" => AdeleRing (𝓞 K) K

attribute [local instance] localBorel borelSpace_localBorel

/-- An injective system of representatives of the right cardinality is a cover. -/
lemma cover_of_card (v : HeightOneSpectrum (𝓞 K)) {ι : Type} [Fintype ι] (r : ι → 𝓞 K)
    (hinj : ∀ i j, r i - r j ∈ v.asIdeal → i = j)
    (hcard : Fintype.card ι = Ideal.absNorm v.asIdeal) (α : 𝓞 K) :
    ∃ i, α - r i ∈ v.asIdeal := by
  have hN0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have hc : Nat.card (𝓞 K ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hc]; exact hN0)
  have hf : Function.Injective fun i => Ideal.Quotient.mk v.asIdeal (r i) :=
    fun i j h => hinj i j (Ideal.Quotient.eq.1 h)
  have hb := hf.bijective_of_nat_card_le (by rw [hc, Nat.card_eq_fintype_card, hcard])
  obtain ⟨i, hi⟩ := hb.2 (Ideal.Quotient.mk v.asIdeal α)
  exact ⟨i, Ideal.Quotient.eq.1 hi.symm⟩

variable {p : ℕ} [hp : Fact p.Prime]

variable (K p) in
/-- The integer representatives `0, …, p − 1`. -/
def repS (k : ZMod p) : 𝓞 K := ((k.val : ℤ) : 𝓞 K)

section Arith

variable {a b : ℤ} (hp1 : p % 4 = 1) (hn : a ^ 2 + b ^ 2 = p)
include hp1 hn

lemma not_dvd_two_a (hab : IsPrimaryPair a b) : ¬ (p : ℤ) ∣ 2 * a := by
  intro h
  have hp5 : 5 ≤ p := by
    have := hp.out.two_le
    omega
  have ha0 : a ≠ 0 := by unfold IsPrimaryPair at hab; omega
  rcases (Nat.prime_iff_prime_int.1 hp.out).dvd_or_dvd h with h2 | ⟨c, hc⟩
  · have := Int.le_of_dvd (by norm_num) h2
    omega
  · have hc0 : c ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hc
      exact ha0 hc
    have hc2 : 1 ≤ c ^ 2 := by
      have := pow_pos (abs_pos.2 hc0) 2
      rw [sq_abs] at this
      omega
    have hp5' : (5 : ℤ) ≤ p := by exact_mod_cast hp5
    have ha2 : a ^ 2 = (p : ℤ) ^ 2 * c ^ 2 := by rw [hc]; ring
    nlinarith [sq_nonneg b]

lemma exists_inv_two_a (hab : IsPrimaryPair a b) : ∃ s : ℤ, (p : ℤ) ∣ 2 * a * s - 1 := by
  obtain ⟨u, s, hus⟩ := (Nat.prime_iff_prime_int.1 hp.out).irreducible.coprime_iff_not_dvd.2
    (not_dvd_two_a hp1 hn hab)
  exact ⟨s, -u, by linear_combination hus⟩

lemma exists_EF (hab : IsPrimaryPair a b) {m : ℕ} (hpm : p.Coprime m) (hm0 : m ≠ 0) :
    ∃ E F : ℤ, (p : ℤ) ∣ 2 * a * E - 1 ∧ (m : ℤ) ∣ p * E - 1 ∧
      (p : ℤ) ∣ 4 * a ^ 2 * F - 1 ∧ (m : ℤ) ∣ F := by
  obtain ⟨s, k0, hs⟩ := exists_inv_two_a hp1 hn hab
  obtain ⟨a', b', hab'⟩ : IsCoprime (p : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.2 hpm
  obtain ⟨E, ⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ := exists_int_modEq hpm hp.out.ne_zero hm0 s a'
  obtain ⟨F, ⟨k3, hk3⟩, ⟨k4, hk4⟩⟩ := exists_int_modEq hpm hp.out.ne_zero hm0 (s ^ 2) 0
  refine ⟨E, F, ⟨2 * a * k1 + k0, by linear_combination 2 * a * hk1 + hs⟩,
    ⟨p * k2 - b', by linear_combination (p : ℤ) * hk2 + hab'⟩,
    ⟨4 * a ^ 2 * k3 + k0 * (2 * a * s + 1), by
      linear_combination 4 * a ^ 2 * hk3 + (2 * a * s + 1) * hs⟩,
    ⟨k4, by linear_combination hk4⟩⟩

end Arith

section Place

variable {a b : ℤ} (hp1 : p % 4 = 1) (hab : IsPrimaryPair a b) (hn : a ^ 2 + b ^ 2 = p)
  {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal = Ideal.span {gaussOf K a b})

omit hp in
lemma gaussOf_add_conj : gaussOf K a b + gaussOf K a (-b) = (2 : 𝓞 K) * (a : 𝓞 K) := by
  unfold gaussOf
  push_cast
  ring

omit hp in
include hn in
lemma gaussOf_mul_conj : gaussOf K a b * gaussOf K a (-b) = (p : 𝓞 K) := by
  have hnK : (a : 𝓞 K) ^ 2 + (b : 𝓞 K) ^ 2 = (p : 𝓞 K) := by
    have := congrArg (Int.cast : ℤ → 𝓞 K) hn
    push_cast at this
    exact this
  unfold gaussOf
  push_cast
  linear_combination hnK - (b : 𝓞 K) ^ 2 * gaussI_sq K

include hn hv

omit hp in
lemma natCast_mem_split : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  rw [hv, Ideal.mem_span_singleton]
  exact ⟨gaussOf K a (-b), (gaussOf_mul_conj hn).symm⟩

lemma intCast_mem_split_iff (N : ℤ) : ((N : ℤ) : 𝓞 K) ∈ v.asIdeal ↔ (p : ℤ) ∣ N := by
  constructor
  · exact fun h => dvd_of_intCast_mem hp.out (natCast_mem_split hn hv) h
  · rintro ⟨k, rfl⟩
    have e : (((p : ℤ) * k : ℤ) : 𝓞 K) = ((p : ℕ) : 𝓞 K) * ((k : ℤ) : 𝓞 K) := by push_cast; ring
    rw [e]
    exact v.asIdeal.mul_mem_right _ (natCast_mem_split hn hv)

lemma repS_inj (i j : ZMod p) (h : repS K p i - repS K p j ∈ v.asIdeal) : i = j := by
  have e : repS K p i - repS K p j = ((((i.val : ℤ) - j.val : ℤ)) : 𝓞 K) := by
    unfold repS
    push_cast
    ring
  rw [e, intCast_mem_split_iff hn hv] at h
  exact zmod_eq_of_dvd_val_sub h

lemma eq_zero_of_repS_mem {k : ZMod p} (h : repS K p k ∈ v.asIdeal) : k = 0 := by
  unfold repS at h
  rw [intCast_mem_split_iff hn hv] at h
  exact zmod_eq_of_dvd_val_sub (by simpa using h)

omit hp in
/-- A place other than `v` containing `p` contains the conjugate of the generator. -/
lemma conj_mem_of_ne {v' : HeightOneSpectrum (𝓞 K)} (hne : v' ≠ v)
    (hp' : ((p : ℕ) : 𝓞 K) ∈ v'.asIdeal) : gaussOf K a (-b) ∈ v'.asIdeal := by
  rw [← gaussOf_mul_conj (K := K) hn] at hp'
  rcases v'.isPrime.mem_or_mem hp' with h | h
  · exfalso
    have hle : v.asIdeal ≤ v'.asIdeal := by
      rw [hv, Ideal.span_singleton_le_iff_mem]
      exact h
    exact hne (HeightOneSpectrum.ext (v.isMaximal.eq_of_le v'.isPrime.ne_top hle)).symm
  · exact h

include hp1 hab

lemma psi_repS (k : ZMod p) :
    psiLocal K v ((toCompl K v (gen K v))⁻¹ * toCompl K v (repS K p k)) =
      (ZMod.stdAddChar (N := p)) ((((-2 * a * k.val : ℤ))) : ZMod p) := by
  have hpv := natCast_mem_split hn hv
  have h2v : (2 : 𝓞 K) ∉ v.asIdeal := two_not_mem v (by omega) hpv
  have hg := gen_eq_of_primary h2v hab hv
  have hN0 : (a ^ 2 + b ^ 2 : ℤ) ≠ 0 := by
    rw [hn]
    exact_mod_cast hp.out.ne_zero
  have e : (toCompl K v (gen K v))⁻¹ * toCompl K v (repS K p k) =
      algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K (repS K p k) / genK K v) := by
    rw [map_div₀, div_eq_inv_mul]
    rfl
  rw [e, psiLocal_algebraMap_of_integral_away K v _ (fun w hw => by
    rw [map_div₀, valuation_genK_of_ne hw.symm, div_one]
    exact valuation_le_one w _)]
  have htr : Algebra.trace ℚ K (algebraMap (𝓞 K) K (repS K p k) / genK K v) =
      (k.val : ℚ) * ((1 / ((a ^ 2 + b ^ 2 : ℤ) : ℚ)) * (2 * a)) := by
    have hs : algebraMap (𝓞 K) K (repS K p k) / genK K v =
        ((k.val : ℚ)) • (algebraMap (𝓞 K) K (gaussOf K a b))⁻¹ := by
      unfold genK repS
      rw [hg, Algebra.smul_def, div_eq_mul_inv]
      congr 1
      rw [map_intCast, map_natCast, Int.cast_natCast]
    rw [hs, map_smul, trace_inv_gaussOf hN0, smul_eq_mul]
  rw [htr, ZMod.stdAddChar_coe, hn]
  congr 1
  push_cast
  ring

variable {m : ℕ} (hodd : (p * m) % 2 = 1) (hsq : Squarefree (p * m)) (hd : p * m ≠ 0)
include hodd hsq

/-- The value of `twC` on an integer `N` coprime to `p`, at the place `v`. -/
lemma twC_locIdele_int (N : ℤ) (hρ : toCompl K v ((N : ℤ) : 𝓞 K) ≠ 0) (hN : ¬ (p : ℤ) ∣ N) :
    ((twC K hodd hsq hd (locIdele K v (Units.mk0 (toCompl K v ((N : ℤ) : 𝓞 K)) hρ)) : ℂˣ) : ℂ) =
      ((legendreSym p N : ℤ) : ℂ) := by
  have hNv : ((N : ℤ) : 𝓞 K) ∉ v.asIdeal := fun h => hN ((intCast_mem_split_iff hn hv N).1 h)
  have hpm : p.Coprime m := Nat.coprime_of_squarefree_mul hsq
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hd
  obtain ⟨s, k0, hs⟩ := exists_inv_two_a hp1 hn hab
  obtain ⟨T, ⟨k1, hk1⟩, ⟨t, ht⟩⟩ := exists_int_modEq hpm hp.out.ne_zero hm0 s 0
  rw [sub_zero] at ht
  have hT : 2 * a * T - 1 = (p : ℤ) * (2 * a * k1 + k0) := by
    linear_combination 2 * a * hk1 + hs
  have hTK : (2 : 𝓞 K) * (a : 𝓞 K) * (T : 𝓞 K) - 1 =
      (p : 𝓞 K) * (((2 * a * k1 + k0 : ℤ)) : 𝓞 K) := by
    have := congrArg (Int.cast : ℤ → 𝓞 K) hT
    push_cast at this
    push_cast
    exact this
  have hβ : gaussOf K (1 + (N - 1) * T * a) (-((N - 1) * T * b)) =
      1 + ((N : 𝓞 K) - 1) * (T : 𝓞 K) * gaussOf K a (-b) := by
    unfold gaussOf
    push_cast
    ring
  have h1 : gaussOf K (1 + (N - 1) * T * a) (-((N - 1) * T * b)) - ((N : ℤ) : 𝓞 K) ∈
      v.asIdeal := by
    rw [hβ, hv, Ideal.mem_span_singleton]
    exact ⟨_, ring_id1 (gaussOf K a b) (gaussOf K a (-b)) (a : 𝓞 K) (N : 𝓞 K) (T : 𝓞 K) _
      (p : 𝓞 K) gaussOf_add_conj (gaussOf_mul_conj hn) hTK⟩
  have h2 : ∀ v' : HeightOneSpectrum (𝓞 K), v' ≠ v → (((p * m : ℕ)) : 𝓞 K) ∈ v'.asIdeal →
      gaussOf K (1 + (N - 1) * T * a) (-((N - 1) * T * b)) - 1 ∈ v'.asIdeal := by
    intro v' hne hd'
    rw [hβ, add_sub_cancel_left]
    by_cases hp' : ((p : ℕ) : 𝓞 K) ∈ v'.asIdeal
    · exact v'.asIdeal.mul_mem_left _ (conj_mem_of_ne hn hv hne hp')
    · have hmv := cofactor_mem hp' hd'
      have e : ((N : 𝓞 K) - 1) * (T : 𝓞 K) * gaussOf K a (-b) =
          ((m : ℤ) : 𝓞 K) * (((N : 𝓞 K) - 1) * (t : 𝓞 K) * gaussOf K a (-b)) := by
        rw [ht]
        push_cast
        ring
      rw [e]
      exact v'.asIdeal.mul_mem_right _ hmv
  have hval := twC_locIdele_toCompl hodd hsq hd hρ hNv h1 h2
  have hj1 : (p : ℤ) ∣ ((1 + (N - 1) * T * a) ^ 2 + (-((N - 1) * T * b)) ^ 2) - N :=
    ⟨(N - 1) * (2 * a * k1 + k0) + ((N - 1) * T) ^ 2, by
      linear_combination (N - 1) * hT + ((N - 1) * T) ^ 2 * hn⟩
  have hj2 : (m : ℤ) ∣ ((1 + (N - 1) * T * a) ^ 2 + (-((N - 1) * T * b)) ^ 2) - 1 :=
    ⟨(N - 1) * t * (2 * a + (N - 1) * T * (a ^ 2 + b ^ 2)), by
      rw [ht]
      ring⟩
  rw [hval, tau, nrm_gaussOf, jacobiSym_mul_eq hm0 hj1 hj2]

lemma charExt_twC_repS (k : ZMod p) (hk : repS K p k ∉ v.asIdeal) :
    charExt (localChar (twC K hodd hsq hd) v)⁻¹ (toCompl K v (repS K p k)) =
      ((quadraticChar (ZMod p) k : ℤ) : ℂ) := by
  have hρ1 := (valued_toCompl_eq_one_iff v _).2 hk
  have hρ : toCompl K v (repS K p k) ≠ 0 := fun h => by
    rw [h, map_zero] at hρ1
    exact zero_ne_one hρ1
  have hN : ¬ (p : ℤ) ∣ (k.val : ℤ) := fun h => hk ((intCast_mem_split_iff hn hv _).2 h)
  have hval := twC_locIdele_int hp1 hab hn hv hodd hsq hd (k.val : ℤ) hρ hN
  have hloc : ((localChar (twC K hodd hsq hd) v (Units.mk0 _ hρ) : ℂˣ) : ℂ) =
      ((legendreSym p (k.val : ℤ) : ℤ) : ℂ) := hval
  rw [charExt_of_ne_zero _ hρ, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, hloc]
  show (((quadraticChar (ZMod p) (((k.val : ℤ)) : ZMod p) : ℤ)) : ℂ)⁻¹ = _
  have e : (((k.val : ℤ)) : ZMod p) = k := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [e, inv_quadraticChar]

/-- The value of `twC` at the test element, for given `E`, `F`. -/
lemma charExt_twC_gen_inv_split {E F : ℤ} (hE1 : (p : ℤ) ∣ 2 * a * E - 1)
    (hE2 : (m : ℤ) ∣ p * E - 1) (hF1 : (p : ℤ) ∣ 4 * a ^ 2 * F - 1) (hF2 : (m : ℤ) ∣ F) :
    charExt (localChar (twC K hodd hsq hd) v) (toCompl K v (gen K v))⁻¹ =
      (((tau K (p * m) (gaussOf K ((E + F) * a) ((F - E) * b)) : ℤ)) : ℂ)⁻¹ := by
  have hpv := natCast_mem_split hn hv
  have h2v : (2 : 𝓞 K) ∉ v.asIdeal := two_not_mem v (by omega) hpv
  have hg := gen_eq_of_primary h2v hab hv
  obtain ⟨e₁, he₁⟩ := hE1
  obtain ⟨e₃, he₃⟩ := hE2
  obtain ⟨e₂, he₂⟩ := hF1
  obtain ⟨f, hf⟩ := hF2
  have cast : ∀ {x y : ℤ}, x = y → ((x : ℤ) : 𝓞 K) = ((y : ℤ) : 𝓞 K) := fun h => by rw [h]
  have he₁K : (2 : 𝓞 K) * (a : 𝓞 K) * (E : 𝓞 K) - 1 = (p : 𝓞 K) * (e₁ : 𝓞 K) := by
    have := cast he₁
    push_cast at this
    exact this
  have he₂K : (4 : 𝓞 K) * (a : 𝓞 K) ^ 2 * (F : 𝓞 K) - 1 = (p : 𝓞 K) * (e₂ : 𝓞 K) := by
    have := cast he₂
    push_cast at this
    exact this
  have he₃K : (p : 𝓞 K) * (E : 𝓞 K) - 1 = ((m : ℤ) : 𝓞 K) * (e₃ : 𝓞 K) := by
    have := cast he₃
    push_cast at this
    push_cast
    exact this
  have hfK : (F : 𝓞 K) = ((m : ℤ) : 𝓞 K) * (f : 𝓞 K) := by
    have := cast hf
    push_cast at this
    push_cast
    exact this
  have hβ : gaussOf K ((E + F) * a) ((F - E) * b) =
      gaussOf K a (-b) * (E : 𝓞 K) + gaussOf K a b * (F : 𝓞 K) := by
    unfold gaussOf
    push_cast
    ring
  have h1 : gaussOf K ((E + F) * a) ((F - E) * b) - 1 ∈ v.asIdeal := by
    rw [hβ, hv, Ideal.mem_span_singleton]
    exact ⟨_, ring_id2 (gaussOf K a b) (gaussOf K a (-b)) (a : 𝓞 K) (p : 𝓞 K) (E : 𝓞 K)
      (F : 𝓞 K) (e₁ : 𝓞 K) gaussOf_add_conj (gaussOf_mul_conj hn) he₁K⟩
  have h2 : ∀ v' : HeightOneSpectrum (𝓞 K), v' ≠ v → (((p * m : ℕ)) : 𝓞 K) ∈ v'.asIdeal →
      gaussOf K ((E + F) * a) ((F - E) * b) * gen K v - 1 ∈ v'.asIdeal := by
    intro v' hne hd'
    rw [hβ, hg]
    by_cases hp' : ((p : ℕ) : 𝓞 K) ∈ v'.asIdeal
    · rw [ring_id3 (gaussOf K a b) (gaussOf K a (-b)) (a : 𝓞 K) (p : 𝓞 K) (E : 𝓞 K) (F : 𝓞 K)
        (e₂ : 𝓞 K) gaussOf_add_conj (gaussOf_mul_conj hn) he₂K]
      exact v'.asIdeal.mul_mem_right _ (conj_mem_of_ne hn hv hne hp')
    · rw [ring_id4 (gaussOf K a b) (gaussOf K a (-b)) (p : 𝓞 K) (E : 𝓞 K) (F : 𝓞 K) (e₃ : 𝓞 K)
        (f : 𝓞 K) ((m : ℤ) : 𝓞 K) (gaussOf_mul_conj hn) he₃K hfK]
      exact v'.asIdeal.mul_mem_right _ (cofactor_mem hp' hd')
  have hval := twC_locIdele_gen hodd hsq hd h1 h2
  have hz : (toCompl K v (gen K v))⁻¹ ≠ 0 := inv_ne_zero (toCompl_gen_ne_zero' v)
  have hu : Units.mk0 (toCompl K v (gen K v))⁻¹ hz =
      (Units.mk0 (toCompl K v (gen K v)) (toCompl_gen_ne_zero' v))⁻¹ :=
    Units.ext (by simp)
  have hloc : ((localChar (twC K hodd hsq hd) v (Units.mk0 (toCompl K v (gen K v))
      (toCompl_gen_ne_zero' v)) : ℂˣ) : ℂ) =
      ((tau K (p * m) (gaussOf K ((E + F) * a) ((F - E) * b)) : ℤ) : ℂ) := hval
  rw [charExt_of_ne_zero _ hz, hu, map_inv, Units.val_inv_eq_inv_val, hloc]

/-- The Gauss sum at `v`, as an expression in `a` and `p`. -/
lemma gauss_sum_split (hNv : Ideal.absNorm v.asIdeal = p) :
    ((p : ℂ))⁻¹ * (∑ k : ZMod p, (ZMod.stdAddChar (N := p)) ((((-2 * a * k.val : ℤ))) : ZMod p) *
        ((quadraticChar (ZMod p) k : ℤ) : ℂ)) * (p : ℂ) ^ ((1 : ℂ) / 2) =
      charExt (localChar (twC K hodd hsq hd) v) (toCompl K v (gen K v))⁻¹ *
        stdRootNumberAt K v (localChar (twC K hodd hsq hd) v) := by
  have hpv := natCast_mem_split hn hv
  have hdv : (((p * m : ℕ)) : 𝓞 K) ∈ v.asIdeal := by
    rw [Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ hpv
  have G := gauss_sum_twC hodd hsq hd hdv (repS K p)
    (cover_of_card v (repS K p) (repS_inj hn hv) (by rw [ZMod.card, hNv])) (repS_inj hn hv)
  have hS : ∑ i : {i // repS K p i ∉ v.asIdeal},
      psiLocal K v ((toCompl K v (gen K v))⁻¹ * toCompl K v (repS K p i)) *
        charExt (localChar (twC K hodd hsq hd) v)⁻¹ (toCompl K v (repS K p i)) =
      ∑ k : ZMod p, (ZMod.stdAddChar (N := p)) ((((-2 * a * k.val : ℤ))) : ZMod p) *
        ((quadraticChar (ZMod p) k : ℤ) : ℂ) := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun i => repS K p i ∉ v.asIdeal) (fun i => by simp)
        (fun i => psiLocal K v ((toCompl K v (gen K v))⁻¹ * toCompl K v (repS K p i)) *
          charExt (localChar (twC K hodd hsq hd) v)⁻¹ (toCompl K v (repS K p i))),
      Finset.sum_congr rfl (fun i hi => by
        rw [psi_repS hp1 hab hn hv i,
          charExt_twC_repS hp1 hab hn hv hodd hsq hd i (Finset.mem_filter.1 hi).2])]
    refine Finset.sum_filter_of_ne fun i _ hne hmemi => hne ?_
    rw [eq_zero_of_repS_mem hn hv hmemi]
    simp
  rw [hS, hNv] at G
  exact G

end Place

end CMPoints
