import HeckeCM.TwistArith

/-!
# An element on which the twisting symbol equals `−1`

`exists_tau_eq_neg_one`: for `d` odd and squarefree and a place `v`
containing `d`, there is `α ∈ 𝓞 K` outside `v`, congruent to `1` at all the other
places containing `d`, with `(nrm α / d) = −1`. It will be used to show that the
twisted character is ramified at `v`.

Let `p` be the rational prime below `v`, `d = p m`, and `n` a quadratic
non-residue modulo `p`.

* `p ≡ 3 (mod 4)`: `α = c + e i` with `c² + e² ≡ n (mod p)`, `c ≡ 1`, `e ≡ 0`
  modulo `m`;
* `p ≡ 1 (mod 4)`, `v = (π)`, `π = a + b i`: `α = 1 + h π̄` with `m ∣ h` and
  `2 a h ≡ n − 1 (mod p)`, because `nrm α = 1 + 2 a h + h² p`.
-/

open NumberField IsDedekindDomain Ideal

namespace CMPoints

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

/-- An integer lying in a place above `p` is divisible by `p`. -/
lemma dvd_of_intCast_mem {v : HeightOneSpectrum (𝓞 K)} {p : ℕ} (hp : p.Prime)
    (hpv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) {N : ℤ} (hN : ((N : ℤ) : 𝓞 K) ∈ v.asIdeal) :
    (p : ℤ) ∣ N := by
  by_contra hnd
  have hg : Int.gcd (p : ℤ) N = 1 := by
    have : Nat.Coprime p N.natAbs :=
      (Nat.Prime.coprime_iff_not_dvd hp).2 (by rwa [Int.natCast_dvd] at hnd)
    simpa [Int.gcd] using this
  have hcop : IsCoprime N (p : ℤ) := (Int.isCoprime_iff_gcd_eq_one.2 hg).symm
  obtain ⟨x, y, hxy⟩ := hcop
  have h1 : (1 : 𝓞 K) ∈ v.asIdeal := by
    have : ((x * N + y * (p : ℤ) : ℤ) : 𝓞 K) ∈ v.asIdeal := by
      push_cast
      exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hN) (v.asIdeal.mul_mem_left _ hpv)
    rw [hxy] at this
    simpa using this
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

/-- An element whose norm is not divisible by `p` lies in no place above `p`. -/
lemma notMem_of_not_dvd_nrm {v : HeightOneSpectrum (𝓞 K)} {p : ℕ} (hp : p.Prime)
    (hpv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) {α : 𝓞 K} (h : ¬ (p : ℤ) ∣ nrm K α) :
    α ∉ v.asIdeal := by
  intro hα
  refine h (dvd_of_intCast_mem hp hpv ?_)
  rw [nrm_eq_mul_conj]
  exact v.asIdeal.mul_mem_right _ hα

/-- Chinese remainder theorem for two coprime natural moduli, with integer residues. -/
lemma exists_int_modEq {p m : ℕ} (hpm : p.Coprime m) (hp0 : p ≠ 0) (hm0 : m ≠ 0) (r s : ℤ) :
    ∃ c : ℤ, (p : ℤ) ∣ c - r ∧ (m : ℤ) ∣ c - s := by
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hpm (r % p).toNat (s % m).toNat
  have hp' : (0 : ℤ) < p := by exact_mod_cast Nat.pos_of_ne_zero hp0
  have hm' : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  refine ⟨k, ?_, ?_⟩
  · have h1 : ((k : ℕ) : ℤ) ≡ ((r % p).toNat : ℤ) [ZMOD p] := (Int.natCast_modEq_iff).2 hk1
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hp'.ne')] at h1
    exact (Int.modEq_iff_dvd.1 (h1.trans (Int.mod_modEq r p)).symm)
  · have h1 : ((k : ℕ) : ℤ) ≡ ((s % m).toNat : ℤ) [ZMOD m] := (Int.natCast_modEq_iff).2 hk2
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hm'.ne')] at h1
    exact (Int.modEq_iff_dvd.1 (h1.trans (Int.mod_modEq s m)).symm)

/-- The Jacobi symbol modulo `p m` of an integer congruent to `n` modulo `p` and to `1`
modulo `m`. -/
lemma jacobiSym_mul_eq {p m : ℕ} [hp : Fact p.Prime] (hm0 : m ≠ 0) {N n : ℤ}
    (h1 : (p : ℤ) ∣ N - n) (h2 : (m : ℤ) ∣ N - 1) :
    jacobiSym N (p * m) = legendreSym p n := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  haveI : NeZero m := ⟨hm0⟩
  have e1 : N % (p : ℤ) = n % (p : ℤ) := (Int.modEq_iff_dvd.2 ((dvd_sub_comm).1 h1) : N ≡ n [ZMOD p])
  have e2 : N % (m : ℤ) = 1 % (m : ℤ) := (Int.modEq_iff_dvd.2 ((dvd_sub_comm).1 h2) : N ≡ 1 [ZMOD m])
  rw [jacobiSym.mul_right, jacobiSym.mod_left N m, e2, ← jacobiSym.mod_left, jacobiSym.one_left,
    mul_one, ← jacobiSym.legendreSym.to_jacobiSym, legendreSym.mod p N, e1, ← legendreSym.mod]

/-- A quadratic non-residue modulo an odd prime. -/
lemma exists_legendreSym_eq_neg_one (p : ℕ) [hp : Fact p.Prime] (hodd : p % 2 = 1) :
    ∃ n : ℤ, legendreSym p n = -1 := by
  have hF : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    rintro rfl
    omega
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hF
  refine ⟨(a.val : ℤ), (legendreSym.eq_neg_one_iff p).2 ?_⟩
  rwa [Int.cast_natCast, ZMod.natCast_zmod_val]

/-- **An element on which the twisting symbol equals `−1`.** -/
theorem exists_tau_eq_neg_one {d : ℕ} (hodd : d % 2 = 1) (hsq : Squarefree d)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ((d : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    ∃ α : 𝓞 K, α ∉ v.asIdeal ∧
      (∀ v' : HeightOneSpectrum (𝓞 K), ((d : ℕ) : 𝓞 K) ∈ v'.asIdeal → v' ≠ v →
        α - 1 ∈ v'.asIdeal) ∧ tau K d α = -1 := by
  -- the rational prime below `v`
  obtain ⟨p, hpf, hpv⟩ : ∃ p ∈ d.primeFactors, ((p : ℕ) : 𝓞 K) ∈ v.asIdeal := by
    have hprod : ((∏ p ∈ d.primeFactors, p : ℕ) : 𝓞 K) ∈ v.asIdeal := by
      rw [Nat.prod_primeFactors_of_squarefree hsq]
      exact hv
    rw [Nat.cast_prod] at hprod
    exact (v.isPrime.prod_mem_iff).1 hprod
  have hp := Nat.prime_of_mem_primeFactors hpf
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, rfl⟩ := Nat.dvd_of_mem_primeFactors hpf
  have hpm : p.Coprime m := (Nat.squarefree_mul_iff.1 hsq).1
  have hm0 : m ≠ 0 := by rintro rfl; simp at hodd
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h2 | h2
    · subst h2
      omega
    · exact h2
  obtain ⟨n, hn⟩ := exists_legendreSym_eq_neg_one p hpodd
  have hnp : ¬ (p : ℤ) ∣ n := by
    intro h
    have := (legendreSym.eq_zero_iff p n).2 ((ZMod.intCast_zmod_eq_zero_iff_dvd n p).2 h)
    rw [this] at hn
    norm_num at hn
  -- the other places above `d`: they contain either `p` or `m`
  have hsplit : ∀ v' : HeightOneSpectrum (𝓞 K), ((p * m : ℕ) : 𝓞 K) ∈ v'.asIdeal →
      ((p : ℕ) : 𝓞 K) ∈ v'.asIdeal ∨ ((m : ℕ) : 𝓞 K) ∈ v'.asIdeal := by
    intro v' h
    rw [Nat.cast_mul] at h
    exact v'.isPrime.mem_or_mem h
  -- common closing step: given `α` with `nrm α ≡ n (mod p)` and `≡ 1 (mod m)`
  have hfin : ∀ α : 𝓞 K, (p : ℤ) ∣ nrm K α - n → (m : ℤ) ∣ nrm K α - 1 →
      α ∉ v.asIdeal ∧ tau K (p * m) α = -1 := by
    intro α h1 h2
    refine ⟨notMem_of_not_dvd_nrm hp hpv fun hdv => hnp ?_, ?_⟩
    · have := dvd_sub hdv h1
      rwa [sub_sub_cancel] at this
    · rw [tau, jacobiSym_mul_eq hm0 h1 h2, hn]
  rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h4 | h4
  · -- `p` splits
    obtain ⟨v₁, v₂, a, b, hv12, hmem, -, -, -, -, hab, hv₁, hv₂⟩ :=
      exists_primary_split (K := K) p h4
    have hpa : ¬ (p : ℤ) ∣ 2 * a := by
      intro h
      have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
      rcases hpZ.dvd_or_dvd h with h' | h'
      · have : (p : ℤ) ∣ 2 := h'
        have h2 : p ∣ 2 := by exact_mod_cast this
        have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
        omega
      · obtain ⟨k, rfl⟩ := h'
        have hb : (p : ℤ) ∣ b ^ 2 := ⟨1 - p * k ^ 2, by linear_combination hab⟩
        obtain ⟨l, rfl⟩ := hpZ.dvd_of_dvd_pow hb
        have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
        have h1 : (p : ℤ) * (k ^ 2 + l ^ 2) = 1 := by
          apply mul_left_cancel₀ hp0
          linear_combination hab
        have := Int.eq_one_or_neg_one_of_mul_eq_one h1
        have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
        omega
    -- `h` with `m ∣ h` and `2 a h ≡ n − 1 (mod p)`
    have hunit : IsUnit (((2 * a : ℤ)) : ZMod p) := by
      rw [isUnit_iff_ne_zero, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hpa
    obtain ⟨u, hu⟩ := hunit
    set h₀ : ℤ := ((((n - 1 : ℤ) : ZMod p) * ((u⁻¹ : (ZMod p)ˣ) : ZMod p)).val : ℤ) with hh₀
    obtain ⟨h, hh1, hh2⟩ := exists_int_modEq hpm hp.ne_zero hm0 h₀ 0
    rw [sub_zero] at hh2
    have hcong : (p : ℤ) ∣ 2 * a * h - (n - 1) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have e1 : ((h : ℤ) : ZMod p) = ((h₀ : ℤ) : ZMod p) := by
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd (h - h₀) p).2 hh1
        rw [Int.cast_sub, sub_eq_zero] at this
        exact this
      have e2 : ((h₀ : ℤ) : ZMod p) = ((n - 1 : ℤ) : ZMod p) * ((u⁻¹ : (ZMod p)ˣ) : ZMod p) := by
        rw [hh₀, Int.cast_natCast, ZMod.natCast_zmod_val]
      push_cast
      have e3 : ((2 : ZMod p) * (a : ZMod p)) = (u : ZMod p) := by
        rw [hu]
        push_cast
        ring
      rw [e1, e2, e3]
      push_cast
      have hui : (u : ZMod p) * (u : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ u.ne_zero
      linear_combination ((n : ZMod p) - 1) * hui
    have hnrm : ∀ s : ℤ, s ^ 2 = b ^ 2 →
        ((p : ℤ) ∣ nrm K (gaussOf K (1 + h * a) (h * s)) - n) ∧
        ((m : ℤ) ∣ nrm K (gaussOf K (1 + h * a) (h * s)) - 1) := by
      intro s hs
      rw [nrm_gaussOf]
      have e : (1 + h * a) ^ 2 + (h * s) ^ 2 = 1 + 2 * a * h + h ^ 2 * p := by
        rw [mul_pow, hs]
        linear_combination h ^ 2 * hab
      rw [e]
      obtain ⟨k, hk⟩ := hcong
      obtain ⟨l, hl⟩ := hh2
      exact ⟨⟨k + h ^ 2, by linear_combination hk⟩, ⟨l * (2 * a + h * p), by rw [hl]; ring⟩⟩
    have hvcase : v = v₁ ∨ v = v₂ := (hmem v).1 hpv
    -- `α = 1 + h · (generator of the other place)`
    have hgen : ∀ (s : ℤ) (w w' : HeightOneSpectrum (𝓞 K)), s ^ 2 = b ^ 2 →
        w'.asIdeal = span {gaussOf K a s} → v = w →
        (∀ u : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ u.asIdeal → u = w ∨ u = w') →
        ∃ α : 𝓞 K, α ∉ v.asIdeal ∧
          (∀ v' : HeightOneSpectrum (𝓞 K), ((p * m : ℕ) : 𝓞 K) ∈ v'.asIdeal → v' ≠ v →
            α - 1 ∈ v'.asIdeal) ∧ tau K (p * m) α = -1 := by
      intro s w w' hs hw' hvw hall
      have hα : gaussOf K (1 + h * a) (h * s) - 1 = (h : 𝓞 K) * gaussOf K a s := by
        unfold gaussOf
        push_cast
        ring
      obtain ⟨hn1, hn2⟩ := hnrm s hs
      obtain ⟨hnot, htau⟩ := hfin _ hn1 hn2
      refine ⟨gaussOf K (1 + h * a) (h * s), hnot, fun v' hv' hne => ?_, htau⟩
      rw [hα]
      rcases hsplit v' hv' with hp' | hm'
      · have : v' = w' := by
          rcases hall v' hp' with h1 | h1
          · exact absurd (h1.trans hvw.symm) hne
          · exact h1
        rw [this, hw']
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
      · obtain ⟨l, hl⟩ := hh2
        rw [hl]
        push_cast
        rw [mul_assoc]
        exact v'.asIdeal.mul_mem_right _ hm'
    rcases hvcase with hv1 | hv2
    · exact hgen (-b) v₁ v₂ (neg_sq b) hv₂ hv1 fun u hu => (hmem u).1 hu
    · exact hgen b v₂ v₁ rfl hv₁ hv2 fun u hu => ((hmem u).1 hu).symm
  · -- `p` is inert
    obtain ⟨v₀, hmem, -, -, -⟩ := exists_primary_inert (K := K) p h4
    have hvv₀ : v = v₀ := (hmem v).1 hpv
    obtain ⟨c₀, e₀, hce⟩ := ZMod.sq_add_sq p ((n : ℤ) : ZMod p)
    obtain ⟨c, hc1, hc2⟩ := exists_int_modEq hpm hp.ne_zero hm0 (c₀.val : ℤ) 1
    obtain ⟨e, he1, he2⟩ := exists_int_modEq hpm hp.ne_zero hm0 (e₀.val : ℤ) 0
    rw [sub_zero] at he2
    have hcz : ((c : ℤ) : ZMod p) = c₀ := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (c - (c₀.val : ℤ)) p).2 hc1
      rw [Int.cast_sub, sub_eq_zero, Int.cast_natCast, ZMod.natCast_zmod_val] at this
      exact this
    have hez : ((e : ℤ) : ZMod p) = e₀ := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (e - (e₀.val : ℤ)) p).2 he1
      rw [Int.cast_sub, sub_eq_zero, Int.cast_natCast, ZMod.natCast_zmod_val] at this
      exact this
    have hn1 : (p : ℤ) ∣ nrm K (gaussOf K c e) - n := by
      rw [nrm_gaussOf, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hcz, hez, hce]
      ring
    have hn2 : (m : ℤ) ∣ nrm K (gaussOf K c e) - 1 := by
      rw [nrm_gaussOf]
      obtain ⟨k, hk⟩ := hc2
      obtain ⟨l, hl⟩ := he2
      exact ⟨k * (c + 1) + l * e, by linear_combination (c + 1) * hk + e * hl⟩
    obtain ⟨hnot, htau⟩ := hfin _ hn1 hn2
    refine ⟨gaussOf K c e, hnot, fun v' hv' hne => ?_, htau⟩
    rcases hsplit v' hv' with hp' | hm'
    · exact absurd (((hmem v').1 hp').trans hvv₀.symm) hne
    · have hα : gaussOf K c e - 1 = gaussOf K (c - 1) e := by
        unfold gaussOf
        push_cast
        ring
      rw [hα]
      have hdvd : ((m : ℤ) : 𝓞 K) ∣ gaussOf K (c - 1) e := intCast_dvd_gaussOf_iff.2 ⟨hc2, he2⟩
      obtain ⟨q, hq⟩ := hdvd
      rw [hq, Int.cast_natCast]
      exact v'.asIdeal.mul_mem_right _ hm'

end CMPoints
