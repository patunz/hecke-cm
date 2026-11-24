import HeckeCM.Descent.WeakMordellWeil
import HeckeCM.Descent.LocalFive
import HeckeCM.InfiniteOrder

/-!
# The Mordell–Weil group of `y² = x³ − 25x` has rank one

Mathlib only. Let `E : y² = (x + 5) x (x − 5)` over `ℚ`.

* `descentClass_eq_of_codeFive_eq`: for points with `y ≠ 0`, the 2-descent
  invariant is determined by three bits (the sign of `x` and the parities of
  `v₂(x + 5)`, `v₅(x + 5)`);
* `card_quotient_five_le`: hence `E(ℚ) / 2E(ℚ)` has at most 8 elements;
* `exists_generator_five`: `E(ℚ) = ℤ P ⊕ E(ℚ)[2]` for a point `P` of infinite
  order, i.e. the rank is exactly one;
* `exists_generator_curve_five`: the same for the curve written as
  `⟨0, 0, 0, −5², 0⟩`.

The generator is not exhibited: the statement is an existence statement.
-/

set_option autoImplicit false

open WeierstrassCurve Affine Affine.Point

namespace BSD

/-! ## Parities in `ZMod 2` -/

lemma zmod_two_cast_eq_zero {n : ℤ} (h : Even n) : ((n : ℤ) : ZMod 2) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd n 2).2 (even_iff_two_dvd.1 h)

lemma zmod_two_cast_eq {n m : ℤ} (h : Even n ↔ Even m) : ((n : ℤ) : ZMod 2) = (m : ZMod 2) := by
  have he : Even (n - m) := Int.even_sub.2 h
  have := zmod_two_cast_eq_zero he
  push_cast at this
  exact sub_eq_zero.1 this

lemma even_iff_of_zmod_two_cast_eq {n m : ℤ} (h : ((n : ℤ) : ZMod 2) = (m : ZMod 2)) :
    Even n ↔ Even m := by
  have h0 : (((n - m : ℤ)) : ZMod 2) = 0 := by
    push_cast
    exact sub_eq_zero.2 h
  have he : Even (n - m) := even_iff_two_dvd.2 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).1 h0)
  exact Int.even_sub.1 he

/-! ## The bad primes -/

lemma mem_badPrimes_five {p : ℕ} (hp : p ∈ badPrimes (-5) 0 5) : p.Prime ∧ (p = 2 ∨ p = 5) := by
  have e1 : ((-5 : ℚ) - 0).num.natAbs * ((-5 : ℚ) - 0).den = 5 := by
    rw [show ((-5 : ℚ) - 0) = ((-5 : ℤ) : ℚ) by norm_num, Rat.num_intCast, Rat.den_intCast]
    rfl
  have e2 : ((-5 : ℚ) - 5).num.natAbs * ((-5 : ℚ) - 5).den = 10 := by
    rw [show ((-5 : ℚ) - 5) = ((-10 : ℤ) : ℚ) by norm_num, Rat.num_intCast, Rat.den_intCast]
    rfl
  have e3 : ((0 : ℚ) - 5).num.natAbs * ((0 : ℚ) - 5).den = 5 := by
    rw [show ((0 : ℚ) - 5) = ((-5 : ℤ) : ℚ) by norm_num, Rat.num_intCast, Rat.den_intCast]
    rfl
  simp only [badPrimes, ratPrimes, Finset.mem_union, e1, e2, e3, Nat.mem_primeFactors] at hp
  have h5 : ∀ {q : ℕ}, q.Prime → q ∣ 5 → q = 5 := fun hq hd =>
    (Nat.prime_dvd_prime_iff_eq hq Nat.prime_five).1 hd
  have h2 : ∀ {q : ℕ}, q.Prime → q ∣ 2 → q = 2 := fun hq hd =>
    (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 hd
  rcases hp with (⟨hp, hd, -⟩ | ⟨hp, hd, -⟩) | ⟨hp, hd, -⟩
  · exact ⟨hp, Or.inr (h5 hp hd)⟩
  · refine ⟨hp, ?_⟩
    rcases (Nat.Prime.dvd_mul hp).1 (show p ∣ 2 * 5 from hd) with h | h
    · exact Or.inl (h2 hp h)
    · exact Or.inr (h5 hp h)
  · exact ⟨hp, Or.inr (h5 hp hd)⟩

/-! ## The three bits -/

/-- The sign of `x` and the parities of `v₂(x + 5)`, `v₅(x + 5)`. -/
noncomputable def codeFive (P : (ratCurve (-5) 0 5).toAffine.Point) : Bool × ZMod 2 × ZMod 2 :=
  (decide (0 < pointX P - 0), ((padicValRat 2 (pointX P - (-5)) : ℤ) : ZMod 2),
    ((padicValRat 5 (pointX P - (-5)) : ℤ) : ZMod 2))

/-- The profile of a point with `y ≠ 0`. -/
lemma profile_five {x y : ℚ} (hE : y ^ 2 = (x - (-5)) * (x - 0) * (x - 5)) (hy : y ≠ 0) :
    0 < x - (-5) ∧ ((0 < x - 5) ↔ (0 < x - 0)) ∧
      ((padicValRat 2 (x - 0) : ℤ) : ZMod 2) = 0 ∧
      ((padicValRat 5 (x - 0) : ℤ) : ZMod 2) = ((padicValRat 2 (x - (-5)) : ℤ) : ZMod 2) ∧
      ∀ p : ℕ, p.Prime → ((padicValRat p (x - 5) : ℤ) : ZMod 2) =
        ((padicValRat p (x - (-5)) : ℤ) : ZMod 2) + ((padicValRat p (x - 0) : ℤ) : ZMod 2) := by
  obtain ⟨ha, hsign⟩ := pos_and_sign hE hy
  obtain ⟨ha0, hb0, hc0⟩ := ne_zero_of_point hE hy
  refine ⟨ha, hsign.symm, ?_, ?_, ?_⟩
  · exact zmod_two_cast_eq_zero (even_padicValRat_b hE hy Nat.prime_two (by norm_num))
  · exact zmod_two_cast_eq (parity_relation hE hy).symm
  · intro p hp
    haveI := Fact.mk hp
    have hv := congrArg (padicValRat p) hE
    rw [padicValRat.pow, padicValRat.mul (mul_ne_zero ha0 hb0) hc0, padicValRat.mul ha0 hb0] at hv
    have hev : Even (padicValRat p (x - (-5)) + padicValRat p (x - 0) + padicValRat p (x - 5)) :=
      ⟨padicValRat p y, by rw [← hv]; push_cast; ring⟩
    have h0 := zmod_two_cast_eq_zero hev
    push_cast at h0
    have hneg : ((padicValRat p (x - 5) : ℤ) : ZMod 2) =
        -(((padicValRat p (x - (-5)) : ℤ) : ZMod 2) + ((padicValRat p (x - 0) : ℤ) : ZMod 2)) := by
      linear_combination h0
    rw [hneg, ZMod.neg_eq_self_mod_two]

lemma sqClass_eq {S : Finset ℕ} {a b : ℚ} (hs : 0 < a ↔ 0 < b)
    (hv : ∀ p ∈ S, ((padicValRat p a : ℤ) : ZMod 2) = ((padicValRat p b : ℤ) : ZMod 2)) :
    sqClass S a = sqClass S b := by
  simp only [sqClass, Prod.mk.injEq]
  exact ⟨decide_eq_decide.2 hs, funext fun p => hv p.1 p.2⟩

/-- **Three bits determine the descent invariant.** -/
theorem descentClass_eq_of_codeFive_eq {P Q : (ratCurve (-5) 0 5).toAffine.Point}
    (hP : pointY P ≠ 0) (hQ : pointY Q ≠ 0) (h : codeFive P = codeFive Q) :
    descentClass (-5) 0 5 P = descentClass (-5) 0 5 Q := by
  rcases P with _ | ⟨x1, y1, h1⟩
  · exact absurd rfl hP
  rcases Q with _ | ⟨x2, y2, h2⟩
  · exact absurd rfl hQ
  change y1 ≠ 0 at hP
  change y2 ≠ 0 at hQ
  have hE1 := (twoTorsionCurve_equation ..).1 h1.1
  have hE2 := (twoTorsionCurve_equation ..).1 h2.1
  obtain ⟨a1, s1, b12, b15, c1⟩ := profile_five hE1 hP
  obtain ⟨a2, s2, b22, b25, c2⟩ := profile_five hE2 hQ
  have h' : (decide (0 < x1 - 0), ((padicValRat 2 (x1 - (-5)) : ℤ) : ZMod 2),
      ((padicValRat 5 (x1 - (-5)) : ℤ) : ZMod 2)) =
      (decide (0 < x2 - 0), ((padicValRat 2 (x2 - (-5)) : ℤ) : ZMod 2),
        ((padicValRat 5 (x2 - (-5)) : ℤ) : ZMod 2)) := h
  simp only [Prod.mk.injEq] at h'
  obtain ⟨hσ', hε, hδ⟩ := h'
  have hσ : 0 < x1 - 0 ↔ 0 < x2 - 0 := decide_eq_decide.1 hσ'
  -- the parities at the bad primes
  have hA : ∀ p ∈ badPrimes (-5) 0 5, ((padicValRat p (x1 - (-5)) : ℤ) : ZMod 2) =
      ((padicValRat p (x2 - (-5)) : ℤ) : ZMod 2) := by
    intro p hp
    rcases (mem_badPrimes_five hp).2 with rfl | rfl
    · exact hε
    · exact hδ
  have hB : ∀ p ∈ badPrimes (-5) 0 5, ((padicValRat p (x1 - 0) : ℤ) : ZMod 2) =
      ((padicValRat p (x2 - 0) : ℤ) : ZMod 2) := by
    intro p hp
    rcases (mem_badPrimes_five hp).2 with rfl | rfl
    · rw [b12, b22]
    · rw [b15, b25, hε]
  have hC : ∀ p ∈ badPrimes (-5) 0 5, ((padicValRat p (x1 - 5) : ℤ) : ZMod 2) =
      ((padicValRat p (x2 - 5) : ℤ) : ZMod 2) := by
    intro p hp
    rw [c1 p (mem_badPrimes_five hp).1, c2 p (mem_badPrimes_five hp).1, hA p hp, hB p hp]
  show (sqClass (badPrimes (-5) 0 5) (x1 - (-5)), sqClass (badPrimes (-5) 0 5) (x1 - 0),
      sqClass (badPrimes (-5) 0 5) (x1 - 5)) =
    (sqClass (badPrimes (-5) 0 5) (x2 - (-5)), sqClass (badPrimes (-5) 0 5) (x2 - 0),
      sqClass (badPrimes (-5) 0 5) (x2 - 5))
  rw [sqClass_eq (iff_of_true a1 a2) hA, sqClass_eq hσ hB,
    sqClass_eq (s1.trans (hσ.trans s2.symm)) hC]

/-! ## The index of `2E(ℚ)` -/

/-- A point with `y = 0` is killed by `2`. -/
lemma two_nsmul_eq_zero_of_pointY_eq_zero {P : (ratCurve (-5) 0 5).toAffine.Point}
    (h : pointY P = 0) : 2 • P = 0 := by
  rcases P with _ | ⟨x, y, hxy⟩
  · exact nsmul_zero 2
  · change y = 0 at h
    rw [two_nsmul]
    refine Point.add_self_of_Y_eq ?_
    rw [twoTorsionCurve_negY, h, _root_.neg_zero]

/-- The curve, written with its coefficients. -/
lemma ratCurve_five_eq :
    ratCurve (-5) 0 5 = (⟨0, 0, 0, -((5 : ℕ) : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ) := by
  simp only [ratCurve, twoTorsionCurve]
  norm_num

lemma exists_not_isOfFinAddOrder_ratCurve_five :
    ∃ P : (ratCurve (-5) 0 5).toAffine.Point, ¬ IsOfFinAddOrder P := by
  rw [ratCurve_five_eq]
  exact CMPoints.exists_not_isOfFinAddOrder_five

lemma two_nsmul_eq_zero_of_isOfFinAddOrder_five :
    ∀ P : (ratCurve (-5) 0 5).toAffine.Point, IsOfFinAddOrder P → 2 • P = 0 := by
  rw [ratCurve_five_eq]
  exact fun P hP => (CMPoints.isOfFinAddOrder_iff_two_nsmul_eq_zero (d := 5) (by norm_num) P).1 hP

instance finite_quotient_five : Finite ((ratCurve (-5) 0 5).toAffine.Point ⧸
    (nsmulAddMonoidHom (α := (ratCurve (-5) 0 5).toAffine.Point) 2).range) := by
  haveI := finiteIndex_two_nsmul (e₁ := -5) (e₂ := 0) (e₃ := 5) (by norm_num) (by norm_num)
    (by norm_num)
  exact AddSubgroup.finite_quotient_of_finiteIndex

/-- **`E(ℚ) / 2E(ℚ)` has at most 8 elements.** -/
theorem card_quotient_five_le :
    Nat.card ((ratCurve (-5) 0 5).toAffine.Point ⧸
      (nsmulAddMonoidHom (α := (ratCurve (-5) 0 5).toAffine.Point) 2).range) ≤ 8 := by
  classical
  set H := (nsmulAddMonoidHom (α := (ratCurve (-5) 0 5).toAffine.Point) 2).range with hH
  obtain ⟨P₀, hP₀⟩ := exists_not_isOfFinAddOrder_ratCurve_five
  let B := {P : (ratCurve (-5) 0 5).toAffine.Point // pointY P ≠ 0}
  let g : B → (ratCurve (-5) 0 5).toAffine.Point ⧸ H := fun P => (P.1 : _ ⧸ H)
  let f : B → Bool × ZMod 2 × ZMod 2 := fun P => codeFive P.1
  have hfac : g.FactorsThrough f := by
    intro P Q hPQ
    exact QuotientAddGroup.eq_iff_sub_mem.2
      (sub_mem_range_of_descentClass_eq (by norm_num) (by norm_num) (by norm_num) P.2 Q.2
        (descentClass_eq_of_codeFive_eq P.2 Q.2 hPQ))
  have hsurj : Function.Surjective (Function.extend f g fun _ => 0) := by
    intro q
    obtain ⟨Q, rfl⟩ := QuotientAddGroup.mk_surjective q
    by_cases hQ : pointY Q = 0
    · have h2Q := two_nsmul_eq_zero_of_pointY_eq_zero hQ
      have hR : pointY (Q + 2 • P₀) ≠ 0 := by
        intro h0
        have h2R := two_nsmul_eq_zero_of_pointY_eq_zero h0
        rw [nsmul_add, h2Q, zero_add, ← mul_nsmul] at h2R
        exact hP₀ (isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨2 * 2, by norm_num, h2R⟩)
      refine ⟨f ⟨Q + 2 • P₀, hR⟩, ?_⟩
      rw [hfac.extend_apply _ ⟨Q + 2 • P₀, hR⟩]
      refine QuotientAddGroup.eq_iff_sub_mem.2 ?_
      rw [add_sub_cancel_left]
      exact ⟨P₀, rfl⟩
    · exact ⟨f ⟨Q, hQ⟩, hfac.extend_apply _ ⟨Q, hQ⟩⟩
  have hle := Nat.card_le_card_of_surjective _ hsurj
  have hcode : Nat.card (Bool × ZMod 2 × ZMod 2) = 8 := by
    simp [Nat.card_eq_fintype_card]
  omega

/-! ## The generator -/

lemma nonsingular_two_torsion_five {x : ℚ} (h : x = 0 ∨ x = 5 ∨ x = -5) :
    (ratCurve (-5) 0 5).toAffine.Nonsingular x 0 := by
  rw [Affine.nonsingular_iff, twoTorsionCurve_equation]
  simp only [ratCurve, twoTorsionCurve]
  rcases h with rfl | rfl | rfl <;> norm_num

/-- The four points killed by `2`. -/
noncomputable def twoTorsionFive : Fin 4 → (ratCurve (-5) 0 5).toAffine.Point :=
  ![0, Point.some 0 0 (nonsingular_two_torsion_five (Or.inl rfl)),
    Point.some 5 0 (nonsingular_two_torsion_five (Or.inr (Or.inl rfl))),
    Point.some (-5) 0 (nonsingular_two_torsion_five (Or.inr (Or.inr rfl)))]

lemma twoTorsionFive_injective : Function.Injective twoTorsionFive := by
  have hcomp : pointToOption ∘ twoTorsionFive =
      ![none, some ((0 : ℚ), (0 : ℚ)), some (5, 0), some (-5, 0)] := by
    funext i
    fin_cases i <;> rfl
  have hinj : Function.Injective (pointToOption ∘ twoTorsionFive) := by
    rw [hcomp]
    decide
  exact Function.Injective.of_comp hinj

lemma two_nsmul_twoTorsionFive (i : Fin 4) : 2 • twoTorsionFive i = 0 := by
  refine two_nsmul_eq_zero_of_pointY_eq_zero ?_
  fin_cases i <;> rfl

/-- **`E(ℚ) = ℤ P ⊕ E(ℚ)[2]`** for `E : y² = (x + 5) x (x − 5)`. -/
theorem exists_generator_five :
    ∃ P : (ratCurve (-5) 0 5).toAffine.Point, ¬ IsOfFinAddOrder P ∧
      ∀ Q : (ratCurve (-5) 0 5).toAffine.Point, ∃ m : ℤ, ∃ T : (ratCurve (-5) 0 5).toAffine.Point,
        2 • T = 0 ∧ Q = m • P + T := by
  haveI : AddGroup.FG (ratCurve (-5) 0 5).toAffine.Point := fg_congruent_five
  obtain ⟨P₀, hP₀⟩ := exists_not_isOfFinAddOrder_ratCurve_five
  exact exists_generator_of_card_quotient_lt two_nsmul_eq_zero_of_isOfFinAddOrder_five
    twoTorsionFive twoTorsionFive_injective two_nsmul_twoTorsionFive
    (lt_of_le_of_lt card_quotient_five_le (by norm_num)) P₀ hP₀

/-- **The Mordell–Weil group of `y² = x³ − 25x` is `ℤ P ⊕ (2-torsion)`.** -/
theorem exists_generator_curve_five :
    ∃ P : (⟨0, 0, 0, -((5 : ℕ) : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ).toAffine.Point,
      ¬ IsOfFinAddOrder P ∧
      ∀ Q : (⟨0, 0, 0, -((5 : ℕ) : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ).toAffine.Point,
        ∃ m : ℤ, ∃ T : (⟨0, 0, 0, -((5 : ℕ) : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ).toAffine.Point,
          2 • T = 0 ∧ Q = m • P + T := by
  rw [← ratCurve_five_eq]
  exact exists_generator_five

end BSD
