import HeckeCM.GaussTwo

/-!
# Arithmetic for the twisted character

For `K = ℚ(i)`:

* `nrm z`: the norm `a² + b²` of `z = a + b i ∈ 𝓞 K`, multiplicative;
* `natCast_dvd_nrm_sub`: if `m ∣ z − w` then `m ∣ nrm z − nrm w`;
* `tau d z = (nrm z / d)`, a Jacobi symbol: multiplicative, depends only on
  `z` modulo `d`, equals 1 on units;
* `natCast_dvd_of_forall_mem`: for `d` odd and squarefree, an element lying in
  all the places containing `d` is divisible by `d`;
* `not_dvd_nrm_of_forall_notMem`: if `z` lies in no place above `p`,
  then `p ∤ nrm z`.
-/

open NumberField IsDedekindDomain Ideal

namespace CMPoints

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

/-! ## The norm -/

variable (K) in
/-- The norm `a² + b²` of `a + b i`. -/
noncomputable def nrm (z : 𝓞 K) : ℤ := ((gaussEquiv K).symm z).norm

lemma nrm_gaussOf (a b : ℤ) : nrm K (gaussOf K a b) = a ^ 2 + b ^ 2 := by
  have h : (gaussEquiv K).symm (gaussOf K a b) = ⟨a, b⟩ := by
    rw [RingEquiv.symm_apply_eq]
    exact (gaussHom_mk K a b).symm
  rw [nrm, h, Zsqrtd.norm_def]
  ring

lemma nrm_mul (z w : 𝓞 K) : nrm K (z * w) = nrm K z * nrm K w := by
  rw [nrm, map_mul, Zsqrtd.norm_mul]
  rfl

lemma nrm_one : nrm K (1 : 𝓞 K) = 1 := by
  rw [nrm, map_one, Zsqrtd.norm_one]

lemma nrm_nonneg (z : 𝓞 K) : 0 ≤ nrm K z := by
  obtain ⟨a, b, rfl⟩ := exists_coords z
  change 0 ≤ nrm K (gaussOf K a b)
  rw [nrm_gaussOf]
  positivity

lemma nrm_unit (u : (𝓞 K)ˣ) : nrm K (u : 𝓞 K) = 1 := by
  obtain ⟨a, b, hab⟩ := exists_coords (u : 𝓞 K)
  have h := (isUnit_coords_iff a b).1 (hab ▸ u.isUnit)
  rw [hab]
  change nrm K (gaussOf K a b) = 1
  rw [nrm_gaussOf, h]

/-- `nrm z = z · z̄`. -/
lemma nrm_eq_mul_conj (z : 𝓞 K) : ((nrm K z : ℤ) : 𝓞 K) = z * gaussConj K z := by
  obtain ⟨a, b, rfl⟩ := exists_coords z
  rw [gaussConj_coords, coords_mul_conj]
  change ((nrm K (gaussOf K a b) : ℤ) : 𝓞 K) = _
  rw [nrm_gaussOf]

/-- If `m ∣ z − w` in `𝓞 K` then `m ∣ nrm z − nrm w` in `ℤ`. -/
theorem intCast_dvd_nrm_sub {m : ℤ} {z w : 𝓞 K} (h : (m : 𝓞 K) ∣ z - w) :
    m ∣ nrm K z - nrm K w := by
  obtain ⟨a, b, rfl⟩ := exists_coords z
  obtain ⟨c, d, rfl⟩ := exists_coords w
  obtain ⟨q, hq⟩ := h
  obtain ⟨e, f, rfl⟩ := exists_coords q
  have hc := coords_unique (K := K) (a := a - c) (b := b - d) (c := m * e) (d := m * f) (by
    push_cast
    linear_combination hq)
  change m ∣ nrm K (gaussOf K a b) - nrm K (gaussOf K c d)
  rw [nrm_gaussOf, nrm_gaussOf]
  exact ⟨e * (a + c) + f * (b + d), by
    have h1 : a = c + m * e := by linarith [hc.1]
    have h2 : b = d + m * f := by linarith [hc.2]
    rw [h1, h2]
    ring⟩

/-- `m ∣ a + b i` in `𝓞 K` if and only if `m` divides both coordinates. -/
lemma intCast_dvd_gaussOf_iff {m a b : ℤ} : (m : 𝓞 K) ∣ gaussOf K a b ↔ m ∣ a ∧ m ∣ b := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨e, f, rfl⟩ := exists_coords q
    have hc := coords_unique (K := K) (a := a) (b := b) (c := m * e) (d := m * f) (by
      unfold gaussOf at hq
      push_cast
      linear_combination hq)
    exact ⟨⟨e, hc.1⟩, ⟨f, hc.2⟩⟩
  · rintro ⟨⟨e, rfl⟩, ⟨f, rfl⟩⟩
    exact ⟨gaussOf K e f, by unfold gaussOf; push_cast; ring⟩

/-! ## The Jacobi symbol of the norm -/

variable (K) in
/-- `tau d z = (nrm z / d)`. -/
noncomputable def tau (d : ℕ) (z : 𝓞 K) : ℤ := jacobiSym (nrm K z) d

lemma tau_mul (d : ℕ) (z w : 𝓞 K) : tau K d (z * w) = tau K d z * tau K d w := by
  rw [tau, nrm_mul, jacobiSym.mul_left]
  rfl

lemma tau_one (d : ℕ) : tau K d (1 : 𝓞 K) = 1 := by
  rw [tau, nrm_one, jacobiSym.one_left]

lemma tau_unit (d : ℕ) (u : (𝓞 K)ˣ) : tau K d (u : 𝓞 K) = 1 := by
  rw [tau, nrm_unit, jacobiSym.one_left]

/-- `tau d` depends only on the class modulo `d`. -/
theorem tau_congr {d : ℕ} {z w : 𝓞 K} (h : ((d : ℤ) : 𝓞 K) ∣ z - w) : tau K d z = tau K d w := by
  have hd := intCast_dvd_nrm_sub h
  have hm : nrm K z % (d : ℤ) = nrm K w % (d : ℤ) :=
    (Int.modEq_iff_dvd.2 ((dvd_sub_comm).1 hd) : nrm K z ≡ nrm K w [ZMOD d])
  rw [tau, tau, jacobiSym.mod_left (nrm K z), jacobiSym.mod_left (nrm K w), hm]

/-! ## Elements lying in all the places above `d` -/

/-- An odd prime `p` divides `z` if `z` lies in all the places above `p`. -/
theorem natCast_dvd_of_forall_mem_prime {p : ℕ} (hp : p.Prime) (hodd : p % 2 = 1) {z : 𝓞 K}
    (h : ∀ v : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ v.asIdeal → z ∈ v.asIdeal) :
    ((p : ℕ) : 𝓞 K) ∣ z := by
  haveI := Fact.mk hp
  rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h1 | h3
  · obtain ⟨v, w, a, b, hvw, hmem, -, -, -, -, hn, hv, hw⟩ := exists_primary_split (K := K) p h1
    have hzv := h v ((hmem v).2 (Or.inl rfl))
    have hzw := h w ((hmem w).2 (Or.inr rfl))
    rw [hv, Ideal.mem_span_singleton] at hzv
    rw [hw, Ideal.mem_span_singleton] at hzw
    obtain ⟨t, rfl⟩ := hzv
    have hprime : Prime (gaussOf K a (-b)) := by
      have hne : gaussOf K a (-b) ≠ 0 := by
        intro h0
        have := w.ne_bot
        rw [hw, h0, Ideal.span_singleton_eq_bot.2 rfl] at this
        exact this rfl
      exact (Ideal.span_singleton_prime hne).1 (hw ▸ w.isPrime)
    have hndvd : ¬ gaussOf K a (-b) ∣ gaussOf K a b := by
      intro hd
      apply hvw
      have hle : v.asIdeal ≤ w.asIdeal := by
        rw [hv, hw, Ideal.span_singleton_le_span_singleton]
        exact hd
      exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hle)
    obtain ⟨t', rfl⟩ := (hprime.dvd_or_dvd hzw).resolve_left hndvd
    have hpp : gaussOf K a b * gaussOf K a (-b) = ((p : ℕ) : 𝓞 K) := by
      have : ((p : ℕ) : 𝓞 K) = (((a ^ 2 + b ^ 2 : ℤ)) : 𝓞 K) := by
        rw [hn]
        norm_cast
      rw [this]
      unfold gaussOf
      push_cast
      linear_combination (-(b : 𝓞 K) ^ 2) * gaussI_sq K
    exact ⟨t', by rw [← hpp]; ring⟩
  · obtain ⟨v, hmem, -, -, hv⟩ := exists_primary_inert (K := K) p h3
    have hzv := h v ((hmem v).2 rfl)
    rw [hv, Ideal.mem_span_singleton] at hzv
    obtain ⟨t, rfl⟩ := hzv
    exact ⟨-t, by unfold gaussOf; push_cast; ring⟩

/-- **For `d` odd and squarefree**, an element lying in all the places
containing `d` is divisible by `d`. -/
theorem natCast_dvd_of_forall_mem {d : ℕ} (hodd : d % 2 = 1) (hsq : Squarefree d) {z : 𝓞 K}
    (h : ∀ v : HeightOneSpectrum (𝓞 K), ((d : ℕ) : 𝓞 K) ∈ v.asIdeal → z ∈ v.asIdeal) :
    ((d : ℤ) : 𝓞 K) ∣ z := by
  obtain ⟨a, b, rfl⟩ := exists_coords z
  change ((d : ℤ) : 𝓞 K) ∣ gaussOf K a b
  have hpf : ∀ p ∈ d.primeFactors, (p : ℤ) ∣ a ∧ (p : ℤ) ∣ b := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpd := Nat.dvd_of_mem_primeFactors hp
    have hpodd : p % 2 = 1 := by
      rcases hpp.eq_two_or_odd with h2 | h2
      · subst h2
        omega
      · exact h2
    have := natCast_dvd_of_forall_mem_prime (K := K) hpp hpodd (z := gaussOf K a b) (fun v hv => by
      refine h v ?_
      obtain ⟨m, rfl⟩ := hpd
      rw [Nat.cast_mul]
      exact v.asIdeal.mul_mem_right _ hv)
    rw [← Int.cast_natCast] at this
    exact intCast_dvd_gaussOf_iff.1 this
  have key : ∀ m : ℤ, (∀ p ∈ d.primeFactors, (p : ℤ) ∣ m) → (d : ℤ) ∣ m := by
    intro m hm
    rw [Int.natCast_dvd]
    rw [← Nat.prod_primeFactors_of_squarefree hsq]
    refine Finset.prod_primes_dvd _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime)
      fun p hp => ?_
    exact Int.natCast_dvd.1 (hm p hp)
  exact intCast_dvd_gaussOf_iff.2 ⟨key a fun p hp => (hpf p hp).1, key b fun p hp => (hpf p hp).2⟩

/-- If `z` lies in no place above `p`, then `p ∤ nrm z`. -/
theorem not_dvd_nrm_of_forall_notMem {p : ℕ} (hp : p.Prime) {z : 𝓞 K}
    (h : ∀ v : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ v.asIdeal → z ∉ v.asIdeal) :
    ¬ (p : ℤ) ∣ nrm K z := by
  intro hd
  -- a place above `p`
  have hp0 : ((p : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hnu : ¬ IsUnit ((p : ℕ) : 𝓞 K) := by
    intro hu
    have := (isUnit_coords_iff (K := K) (p : ℤ) 0).1 (by simpa using hu)
    have h2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
    nlinarith
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (span {((p : ℕ) : 𝓞 K)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hMbot : M ≠ ⊥ := by
    rintro rfl
    exact hp0 (Ideal.span_singleton_eq_bot.1 (le_bot_iff.1 hle))
  set v : HeightOneSpectrum (𝓞 K) := ⟨M, hM.isPrime, hMbot⟩ with hv
  have hpv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal := hle (Ideal.mem_span_singleton_self _)
  have hmem : z * gaussConj K z ∈ v.asIdeal := by
    rw [← nrm_eq_mul_conj]
    obtain ⟨m, hm⟩ := hd
    rw [hm]
    push_cast
    exact v.asIdeal.mul_mem_right _ hpv
  rcases v.isPrime.mem_or_mem hmem with h1 | h1
  · exact h v hpv h1
  · -- `z̄ ∈ v`, so `z` lies in the conjugate place, which still contains `p`
    set M' : Ideal (𝓞 K) := M.comap (gaussConj K : 𝓞 K →+* 𝓞 K) with hM'
    have hM'prime : M'.IsPrime := Ideal.comap_isPrime _ M
    have hpM' : ((p : ℕ) : 𝓞 K) ∈ M' := by
      rw [hM', Ideal.mem_comap]
      have : (gaussConj K : 𝓞 K →+* 𝓞 K) ((p : ℕ) : 𝓞 K) = ((p : ℕ) : 𝓞 K) := map_natCast _ _
      rw [this]
      exact hpv
    have hM'bot : M' ≠ ⊥ := by
      intro h0
      rw [h0] at hpM'
      exact hp0 hpM'
    exact h ⟨M', hM'prime, hM'bot⟩ hpM' (Ideal.mem_comap.2 h1)

end CMPoints
