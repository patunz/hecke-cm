import Mathlib

/-!
# Two tools for the rank of `y² = x³ − 25x`

Mathlib only.

* `even_padicValRat_two_sq_sub`: for rational `s`, `t` and `σ = ±1`, the 5-adic
  valuation of `2s² − σt²` is even (the forms `2s² ∓ t²` do not represent `0`
  modulo `5`, because `±2` are not squares modulo `5`);
* `exists_generator_of_card_quotient_lt`: a finitely generated abelian group
  whose torsion is killed by `2`, with four distinct elements killed by `2`,
  an element of infinite order and fewer than `16` classes modulo `2G`, is
  `ℤ P ⊕ G[2]` for some `P`.
-/

set_option autoImplicit false

namespace BSD

/-! ## The forms `2s² ∓ t²` at the prime `5` -/

lemma zmod_five_form {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (a b : ZMod 5)
    (h : 2 * a ^ 2 - (σ : ZMod 5) * b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  rcases hσ with rfl | rfl
  · revert a b
    decide
  · revert a b
    decide

/-- Integer version, by descent. -/
lemma even_padicValInt_two_sq_sub {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    ∀ n : ℕ, ∀ X Y : ℤ, X.natAbs + Y.natAbs ≤ n → Even (padicValInt 5 (2 * X ^ 2 - σ * Y ^ 2)) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro n
  induction n with
  | zero =>
    intro X Y h
    have hX : X = 0 := by omega
    have hY : Y = 0 := by omega
    subst hX hY
    simp
  | succ n ih =>
    intro X Y h
    by_cases h5 : (5 : ℤ) ∣ 2 * X ^ 2 - σ * Y ^ 2
    · have hz : (2 * (X : ZMod 5) ^ 2 - (σ : ZMod 5) * (Y : ZMod 5) ^ 2 = 0) := by
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * X ^ 2 - σ * Y ^ 2) 5).2 h5
        push_cast at this
        exact this
      obtain ⟨hX, hY⟩ := zmod_five_form hσ _ _ hz
      obtain ⟨X', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd X 5).1 hX
      obtain ⟨Y', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd Y 5).1 hY
      have hexp : ∀ c : ℤ, 2 * (c * X') ^ 2 - σ * (c * Y') ^ 2 =
          c * (c * (2 * X' ^ 2 - σ * Y' ^ 2)) := fun c => by ring
      rw [hexp]
      by_cases h0 : 2 * X' ^ 2 - σ * Y' ^ 2 = 0
      · rw [h0]
        simp
      · have hsmall : X'.natAbs + Y'.natAbs ≤ n := by
          have h1 : (5 * X').natAbs = 5 * X'.natAbs := by simp [Int.natAbs_mul]
          have h2 : (5 * Y').natAbs = 5 * Y'.natAbs := by simp [Int.natAbs_mul]
          have hne : X'.natAbs + Y'.natAbs ≠ 0 := by
            intro hzero
            have hx : X' = 0 := by omega
            have hy : Y' = 0 := by omega
            apply h0
            rw [hx, hy]
            ring
          omega
        have hev := ih X' Y' hsmall
        have h5ne : ((5 : ℕ) : ℤ) ≠ 0 := by norm_num
        rw [padicValInt.mul h5ne (mul_ne_zero h5ne h0), padicValInt.mul h5ne h0,
          padicValInt.self (by norm_num)]
        obtain ⟨k, hk⟩ := hev
        exact ⟨k + 1, by omega⟩
    · rw [padicValInt.eq_zero_of_not_dvd h5]
      exact ⟨0, rfl⟩

/-- **The 5-adic valuation of `2s² − σt²` is even**, for rational `s`, `t` and `σ = ±1`. -/
theorem even_padicValRat_two_sq_sub {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (s t : ℚ) :
    Even (padicValRat 5 (2 * s ^ 2 - (σ : ℚ) * t ^ 2)) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set X : ℤ := s.num * t.den with hX
  set Y : ℤ := t.num * s.den with hY
  set D : ℤ := s.den * t.den with hD
  have hD0 : (D : ℚ) ≠ 0 := by
    rw [hD]
    exact_mod_cast mul_ne_zero s.den_ne_zero t.den_ne_zero
  have hsd : (s.den : ℚ) ≠ 0 := by exact_mod_cast s.den_ne_zero
  have htd : (t.den : ℚ) ≠ 0 := by exact_mod_cast t.den_ne_zero
  have hs : s * s.den = s.num := Rat.mul_den_eq_num s
  have ht : t * t.den = t.num := Rat.mul_den_eq_num t
  have hexp : 2 * s ^ 2 - (σ : ℚ) * t ^ 2 =
      ((2 * X ^ 2 - σ * Y ^ 2 : ℤ) : ℚ) / (D : ℚ) ^ 2 := by
    rw [hX, hY, hD]
    push_cast
    rw [eq_div_iff (pow_ne_zero 2 (mul_ne_zero hsd htd))]
    linear_combination (2 * (t.den : ℚ) ^ 2 * (s * s.den + s.num)) * hs -
      ((σ : ℚ) * (s.den : ℚ) ^ 2 * (t * t.den + t.num)) * ht
  rw [hexp]
  by_cases h0 : (2 * X ^ 2 - σ * Y ^ 2 : ℤ) = 0
  · rw [h0]
    simp
  have hN0 : ((2 * X ^ 2 - σ * Y ^ 2 : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.2 h0
  rw [padicValRat.div hN0 (pow_ne_zero 2 hD0), padicValRat.of_int, padicValRat.pow]
  obtain ⟨k, hk⟩ := even_padicValInt_two_sq_sub hσ _ X Y le_rfl
  refine ⟨(k : ℤ) - padicValRat 5 (D : ℚ), ?_⟩
  rw [hk]
  push_cast
  ring

/-! ## From the index of `2G` to a generator -/

/-- **Rank one from the descent index.** -/
theorem exists_generator_of_card_quotient_lt {G : Type*} [AddCommGroup G] [AddGroup.FG G]
    (htors : ∀ g : G, IsOfFinAddOrder g → 2 • g = 0)
    (t : Fin 4 → G) (ht : Function.Injective t) (ht2 : ∀ i, 2 • t i = 0)
    [Finite (G ⧸ (nsmulAddMonoidHom (α := G) 2).range)]
    (hcard : Nat.card (G ⧸ (nsmulAddMonoidHom (α := G) 2).range) < 16)
    (P₀ : G) (hP₀ : ¬ IsOfFinAddOrder P₀) :
    ∃ P : G, ¬ IsOfFinAddOrder P ∧ ∀ Q : G, ∃ m : ℤ, ∃ T : G, 2 • T = 0 ∧ Q = m • P + T := by
  classical
  haveI : Module.Finite ℤ G := Module.Finite.iff_addGroup_fg.2 inferInstance
  set Tor : Submodule ℤ G := Submodule.torsion ℤ G with hTor
  have hmem : ∀ g : G, g ∈ Tor ↔ IsOfFinAddOrder g := by
    intro g
    rw [hTor, Submodule.mem_torsion_iff]
    constructor
    · rintro ⟨a, ha⟩
      have ha0 : (a : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero a
      refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨(a : ℤ).natAbs, Int.natAbs_pos.2 ha0, ?_⟩
      have h1 : ((a : ℤ).natAbs : ℤ) • g = 0 := by
        rcases Int.natAbs_eq (a : ℤ) with h | h
        · rw [← h]
          exact ha
        · have : ((a : ℤ).natAbs : ℤ) = -(a : ℤ) := by omega
          rw [this, neg_smul]
          exact neg_eq_zero.2 ha
      exact_mod_cast h1
    · intro hg
      obtain ⟨k, hk, hkg⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 hg
      refine ⟨⟨(k : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hk.ne')⟩, ?_⟩
      show (k : ℤ) • g = 0
      exact_mod_cast hkg
  set π : G →ₗ[ℤ] G ⧸ Tor := Tor.mkQ with hπ
  have hπ0 : ∀ g : G, π g = 0 ↔ IsOfFinAddOrder g := by
    intro g
    rw [hπ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hmem]
  let b := Module.finBasis ℤ (G ⧸ Tor)
  set r := Module.finrank ℤ (G ⧸ Tor) with hr
  -- `r ≥ 1`
  have hr1 : 1 ≤ r := by
    by_contra hlt
    have hr0 : Module.finrank ℤ (G ⧸ Tor) = 0 := by omega
    have hsub : Subsingleton (G ⧸ Tor) := Module.finrank_zero_iff.1 hr0
    exact hP₀ ((hπ0 P₀).1 (Subsingleton.elim _ _))
  have hH : ∀ g : G, g ∈ (nsmulAddMonoidHom (α := G) 2).range ↔ ∃ h : G, 2 • h = g := by
    intro g
    rfl
  -- `r ≤ 1`
  have hr2 : r ≤ 1 := by
    by_contra hgt
    have h2 : 2 ≤ r := by omega
    let i0 : Fin r := ⟨0, by omega⟩
    let i1 : Fin r := ⟨1, by omega⟩
    have hi01 : i0 ≠ i1 := by
      intro h
      have := congrArg Fin.val h
      simp [i0, i1] at this
    obtain ⟨g0, hg0⟩ := Submodule.mkQ_surjective Tor (b i0)
    obtain ⟨g1, hg1⟩ := Submodule.mkQ_surjective Tor (b i1)
    let F : Fin 4 × Fin 2 × Fin 2 → G ⧸ (nsmulAddMonoidHom (α := G) 2).range := fun x =>
      QuotientAddGroup.mk (t x.1 + ((x.2.1 : ℕ) : ℤ) • g0 + ((x.2.2 : ℕ) : ℤ) • g1)
    have hF : Function.Injective F := by
      rintro ⟨i, e0, e1⟩ ⟨i', e0', e1'⟩ hxy
      have hsub := QuotientAddGroup.eq_iff_sub_mem.1 hxy
      obtain ⟨h, hh⟩ := (hH _).1 hsub
      have hti : ∀ j, π (t j) = 0 := fun j =>
        (hπ0 _).2 (isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨2, by norm_num, ht2 j⟩)
      dsimp only at hh
      have hg0' : π g0 = b i0 := hg0
      have hg1' : π g1 = b i1 := hg1
      have hπeq : (((e0 : ℕ) : ℤ) - ((e0' : ℕ) : ℤ)) • b i0 +
          (((e1 : ℕ) : ℤ) - ((e1' : ℕ) : ℤ)) • b i1 = (2 : ℤ) • π h := by
        have h2h : (2 : ℤ) • h = 2 • h := by rw [two_zsmul, two_nsmul]
        have e1 : (2 : ℤ) • π h = π (2 • h) := by rw [← h2h, map_zsmul]
        rw [e1, hh]
        simp only [map_sub, map_add, map_zsmul, hti, hg0', hg1', zero_add, sub_smul]
        abel
      have hrepr := congrArg b.repr hπeq
      simp only [map_add, map_zsmul, b.repr_self] at hrepr
      have hc0 := DFunLike.congr_fun hrepr i0
      have hc1 := DFunLike.congr_fun hrepr i1
      simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne hi01, Finsupp.single_eq_of_ne hi01.symm, smul_eq_mul, mul_one,
        mul_zero, add_zero, zero_add] at hc0 hc1
      have he0 : e0 = e0' := by
        have := e0.isLt
        have := e0'.isLt
        apply Fin.ext
        omega
      have he1 : e1 = e1' := by
        have := e1.isLt
        have := e1'.isLt
        apply Fin.ext
        omega
      subst he0 he1
      have hdiff : 2 • h = t i - t i' := by
        rw [hh]
        abel
      have h4 : 2 • (2 • h) = 0 := by
        rw [hdiff, nsmul_sub, ht2, ht2, sub_zero]
      have hfin : IsOfFinAddOrder h :=
        isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨4, by norm_num, by
          rw [show 4 = 2 * 2 by norm_num, mul_nsmul]
          exact h4⟩
      have h2 : 2 • h = 0 := htors h hfin
      have hteq : t i = t i' := by
        rw [h2] at hdiff
        exact (sub_eq_zero.1 hdiff.symm)
      rw [ht hteq]
    have hle := Nat.card_le_card_of_injective F hF
    have hdom : Nat.card (Fin 4 × Fin 2 × Fin 2) = 16 := by
      simp [Nat.card_eq_fintype_card]
    omega
  have hreq : r = 1 := by omega
  let i0 : Fin r := ⟨0, by omega⟩
  have huniq : ∀ j : Fin r, j = i0 := fun j => Fin.ext (by
    have := j.isLt
    simp only [i0]
    omega)
  obtain ⟨P, hP⟩ := Submodule.mkQ_surjective Tor (b i0)
  refine ⟨P, ?_, fun Q => ?_⟩
  · intro hfin
    have h0 : b i0 = 0 := by
      rw [← hP]
      exact (hπ0 P).2 hfin
    exact b.ne_zero i0 h0
  · set m : ℤ := b.repr (π Q) i0 with hm
    have hzero : π (Q - m • P) = 0 := by
      apply b.repr.injective
      ext j
      rw [huniq j]
      have hPπ : π P = b i0 := hP
      simp only [map_sub, map_zsmul, hPπ, b.repr_self, Finsupp.sub_apply, Finsupp.smul_apply,
        Finsupp.single_eq_same, smul_eq_mul, mul_one, map_zero, Finsupp.zero_apply]
      rw [hm]
      ring
    have hT := htors _ ((hπ0 _).1 hzero)
    exact ⟨m, Q - m • P, hT, by abel⟩

end BSD
