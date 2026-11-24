import Mathlib
import HeckeCM.Descent.TwoDescent
import HeckeCM.Descent.SquareClass
import HeckeCM.Descent.NaiveHeight

/-!
# Mordell–Weil for `y² = (x - e₁)(x - e₂)(x - e₃)` over `ℚ`

For distinct rational `e₁`, `e₂`, `e₃`:

* `finiteIndex_two_nsmul`: `E(ℚ)/2E(ℚ)` is finite (weak Mordell–Weil);
* `fg_twoTorsionCurve`: `E(ℚ)` is finitely generated (Mordell–Weil).

The descent: to a point with `y ≠ 0` one associates the class modulo squares of
`x - eᵢ`, which is determined by the sign and the parity of the valuations at the
primes occurring in the differences `eᵢ - eⱼ`. Two points with the same class
differ by twice a point.
-/

open WeierstrassCurve Affine Affine.Point

namespace BSD

section Coordinate

variable {K : Type*} [Field K] {W : WeierstrassCurve K}

/-- The `x`-coordinate of a point (`0` for the point at infinity). -/
def pointX : W.toAffine.Point → K
  | .zero => 0
  | .some x _ _ => x

/-- The `y`-coordinate of a point (`0` for the point at infinity). -/
def pointY : W.toAffine.Point → K
  | .zero => 0
  | .some _ y _ => y

/-- A point viewed as a pair of coordinates, or nothing for the point at infinity. -/
def pointToOption : W.toAffine.Point → Option (K × K)
  | .zero => none
  | .some x y _ => some (x, y)

lemma pointToOption_injective : Function.Injective (pointToOption (W := W)) := by
  rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hPQ
  · rfl
  · cases hPQ
  · cases hPQ
  · simp only [pointToOption, Option.some.injEq, Prod.mk.injEq] at hPQ
    obtain ⟨rfl, rfl⟩ := hPQ
    rfl

end Coordinate

section Classe

/-- The class modulo squares of a rational, seen through the sign and the
parity of the valuations at the primes of `S`. -/
def sqClass (S : Finset ℕ) (a : ℚ) : Bool × (S → ZMod 2) :=
  (decide (0 < a), fun p => ((padicValRat p a : ℤ) : ZMod 2))

/-- Two rationals with the same class, and even valuations outside `S`, have a
square product. -/
lemma isSquare_mul_of_sqClass_eq {S : Finset ℕ} {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : sqClass S a = sqClass S b)
    (hout : ∀ p : ℕ, p.Prime → p ∉ S → Even (padicValRat p a) ∧ Even (padicValRat p b)) :
    IsSquare (a * b) := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [sqClass] at h1 h2
  refine isSquare_mul_of_same_class ha hb (decide_eq_decide.1 h1) fun p hp => ?_
  by_cases hpS : p ∈ S
  · have := congrFun h2 ⟨p, hpS⟩
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at this
    obtain ⟨k, hk⟩ := this
    refine ⟨padicValRat p a + k, ?_⟩
    push_cast at hk
    omega
  · obtain ⟨ea, eb⟩ := hout p hp hpS
    exact ea.add eb

end Classe

section Discesa

variable (e₁ e₂ e₃ : ℚ)

/-- The curve `y² = (x - e₁)(x - e₂)(x - e₃)` over `ℚ`. -/
abbrev ratCurve : WeierstrassCurve ℚ := twoTorsionCurve e₁ e₂ e₃

/-- The primes occurring in the numerator or the denominator of a rational. -/
def ratPrimes (d : ℚ) : Finset ℕ := (d.num.natAbs * d.den).primeFactors

lemma padicValRat_eq_zero_of_notMem_ratPrimes {d : ℚ} (hd : d ≠ 0) {p : ℕ} (hp : p.Prime)
    (h : p ∉ ratPrimes d) : padicValRat p d = 0 := by
  have hn0 : d.num.natAbs * d.den ≠ 0 :=
    mul_ne_zero (Int.natAbs_ne_zero.2 (Rat.num_ne_zero.2 hd)) d.den_nz
  have hnd : ¬ p ∣ d.num.natAbs * d.den := fun hdvd =>
    h (Nat.mem_primeFactors.2 ⟨hp, hdvd, hn0⟩)
  have h1 : padicValInt p d.num = 0 :=
    padicValNat.eq_zero_of_not_dvd fun h' => hnd (h'.mul_right _)
  have h2 : padicValNat p d.den = 0 :=
    padicValNat.eq_zero_of_not_dvd fun h' => hnd (h'.mul_left _)
  rw [padicValRat_def, h1, h2]
  simp

/-- The primes occurring in the differences of the roots. -/
def badPrimes : Finset ℕ := ratPrimes (e₁ - e₂) ∪ ratPrimes (e₁ - e₃) ∪ ratPrimes (e₂ - e₃)

/-- The descent invariant of a point. -/
def descentClass (P : (ratCurve e₁ e₂ e₃).toAffine.Point) :
    (Bool × (badPrimes e₁ e₂ e₃ → ZMod 2)) × (Bool × (badPrimes e₁ e₂ e₃ → ZMod 2)) ×
      (Bool × (badPrimes e₁ e₂ e₃ → ZMod 2)) :=
  (sqClass _ (pointX P - e₁), sqClass _ (pointX P - e₂), sqClass _ (pointX P - e₃))

variable {e₁ e₂ e₃}

/-- Two points with `y ≠ 0` and the same invariant differ by twice a point. -/
theorem sub_mem_range_of_descentClass_eq (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃)
    {P Q : (ratCurve e₁ e₂ e₃).toAffine.Point} (hP : pointY P ≠ 0) (hQ : pointY Q ≠ 0)
    (h : descentClass e₁ e₂ e₃ P = descentClass e₁ e₂ e₃ Q) :
    P - Q ∈ (nsmulAddMonoidHom (α := (ratCurve e₁ e₂ e₃).toAffine.Point) 2).range := by
  rcases P with _ | ⟨x1, y1, h1⟩
  · exact absurd rfl hP
  rcases Q with _ | ⟨x2, y2, h2⟩
  · exact absurd rfl hQ
  change y1 ≠ 0 at hP
  change y2 ≠ 0 at hQ
  have hE1 := (twoTorsionCurve_equation ..).1 h1.1
  have hE2 := (twoTorsionCurve_equation ..).1 h2.1
  by_cases hx : x1 = x2
  · subst hx
    rcases Affine.Y_eq_of_X_eq h1.1 h2.1 rfl with hy | hy
    · subst hy
      rw [sub_self]
      exact zero_mem _
    · refine ⟨some x1 y1 h1, ?_⟩
      have hneg : some x1 y2 h2 = -some x1 y1 h1 := by
        rw [neg_some]
        congr 1
        rw [hy, Affine.negY_negY]
      rw [hneg, sub_neg_eq_add]
      exact two_nsmul _
  · -- equal classes give square products
    have hp1 : (x1 - e₁) * (x1 - e₂) * (x1 - e₃) ≠ 0 := by rw [← hE1]; exact pow_ne_zero 2 hP
    have hp2 : (x2 - e₁) * (x2 - e₂) * (x2 - e₃) ≠ 0 := by rw [← hE2]; exact pow_ne_zero 2 hQ
    have a11 : x1 - e₁ ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hp1)
    have a12 : x1 - e₂ ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hp1)
    have a13 : x1 - e₃ ≠ 0 := right_ne_zero_of_mul hp1
    have a21 : x2 - e₁ ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hp2)
    have a22 : x2 - e₂ ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hp2)
    have a23 : x2 - e₃ ≠ 0 := right_ne_zero_of_mul hp2
    have v12 : ∀ {p : ℕ}, p.Prime → p ∉ badPrimes e₁ e₂ e₃ → padicValRat p (e₁ - e₂) = 0 :=
      fun hp hpS => padicValRat_eq_zero_of_notMem_ratPrimes (sub_ne_zero.2 h12) hp
        fun hm => hpS (by simp [badPrimes, hm])
    have v13 : ∀ {p : ℕ}, p.Prime → p ∉ badPrimes e₁ e₂ e₃ → padicValRat p (e₁ - e₃) = 0 :=
      fun hp hpS => padicValRat_eq_zero_of_notMem_ratPrimes (sub_ne_zero.2 h13) hp
        fun hm => hpS (by simp [badPrimes, hm])
    have v23 : ∀ {p : ℕ}, p.Prime → p ∉ badPrimes e₁ e₂ e₃ → padicValRat p (e₂ - e₃) = 0 :=
      fun hp hpS => padicValRat_eq_zero_of_notMem_ratPrimes (sub_ne_zero.2 h23) hp
        fun hm => hpS (by simp [badPrimes, hm])
    have v21 : ∀ {p : ℕ}, p.Prime → p ∉ badPrimes e₁ e₂ e₃ → padicValRat p (e₂ - e₁) = 0 :=
      fun hp hpS => by rw [← neg_sub, padicValRat.neg]; exact v12 hp hpS
    have v31 : ∀ {p : ℕ}, p.Prime → p ∉ badPrimes e₁ e₂ e₃ → padicValRat p (e₃ - e₁) = 0 :=
      fun hp hpS => by rw [← neg_sub, padicValRat.neg]; exact v13 hp hpS
    have v32 : ∀ {p : ℕ}, p.Prime → p ∉ badPrimes e₁ e₂ e₃ → padicValRat p (e₃ - e₂) = 0 :=
      fun hp hpS => by rw [← neg_sub, padicValRat.neg]; exact v23 hp hpS
    have c1 := congrArg Prod.fst h
    have c2 := congrArg (fun t => t.2.1) h
    have c3 := congrArg (fun t => t.2.2) h
    simp only [descentClass, pointX] at c1 c2 c3
    have s1 : IsSquare ((x1 - e₁) * (x2 - e₁)) :=
      isSquare_mul_of_sqClass_eq a11 a21 c1 fun p hp hpS =>
        ⟨even_padicValRat_sub_root hE1 hP hp h12 h13 (v12 hp hpS) (v13 hp hpS),
          even_padicValRat_sub_root hE2 hQ hp h12 h13 (v12 hp hpS) (v13 hp hpS)⟩
    have s2 : IsSquare ((x1 - e₂) * (x2 - e₂)) :=
      isSquare_mul_of_sqClass_eq a12 a22 c2 fun p hp hpS =>
        ⟨even_padicValRat_sub_root (e₁ := e₂) (e₂ := e₁) (e₃ := e₃) (by rw [hE1]; ring) hP hp
            h12.symm h23 (v21 hp hpS) (v23 hp hpS),
          even_padicValRat_sub_root (e₁ := e₂) (e₂ := e₁) (e₃ := e₃) (by rw [hE2]; ring) hQ hp
            h12.symm h23 (v21 hp hpS) (v23 hp hpS)⟩
    have s3 : IsSquare ((x1 - e₃) * (x2 - e₃)) :=
      isSquare_mul_of_sqClass_eq a13 a23 c3 fun p hp hpS =>
        ⟨even_padicValRat_sub_root (e₁ := e₃) (e₂ := e₁) (e₃ := e₂) (by rw [hE1]; ring) hP hp
            h13.symm h23.symm (v31 hp hpS) (v32 hp hpS),
          even_padicValRat_sub_root (e₁ := e₃) (e₂ := e₁) (e₃ := e₂) (by rw [hE2]; ring) hQ hp
            h13.symm h23.symm (v31 hp hpS) (v32 hp hpS)⟩
    -- the chord
    obtain ⟨x3, y3, h3, hsub, t1, t2, t3⟩ := exists_sub_eq_some_and_isSquare h1 h2 hx
    obtain ⟨α₁, hα₁⟩ := isSquare_of_mul_left (mul_ne_zero a11 a21) s1 t1
    obtain ⟨α₂, hα₂⟩ := isSquare_of_mul_left (mul_ne_zero a12 a22) s2 t2
    obtain ⟨α₃, hα₃⟩ := isSquare_of_mul_left (mul_ne_zero a13 a23) s3 t3
    obtain ⟨R, hR⟩ := exists_two_nsmul_eq_or_eq_neg (two_ne_zero) h12 h13 h23 h3
      (by rw [sq, ← hα₁]) (by rw [sq, ← hα₂]) (by rw [sq, ← hα₃])
    rw [hsub]
    rcases hR with hR | hR
    · exact ⟨R, hR⟩
    · refine ⟨-R, ?_⟩
      change 2 • (-R) = _
      rw [smul_neg, hR, neg_neg]

/-- The points with `y = 0`, including the point at infinity, are finite in number. -/
lemma finite_pointY_eq_zero :
    {P : (ratCurve e₁ e₂ e₃).toAffine.Point | pointY P = 0}.Finite := by
  let T : Set (Option (ℚ × ℚ)) :=
    {none, Option.some (e₁, (0 : ℚ)), Option.some (e₂, (0 : ℚ)), Option.some (e₃, (0 : ℚ))}
  have hT : T.Finite := Set.toFinite _
  refine (hT.preimage pointToOption_injective.injOn).subset ?_
  rintro (_ | ⟨x, y, h⟩) hP
  · exact Or.inl rfl
  · change y = 0 at hP
    subst hP
    have hE := (twoTorsionCurve_equation ..).1 h.1
    have h0 : (x - e₁) * (x - e₂) * (x - e₃) = 0 := by rw [← hE]; ring
    rcases mul_eq_zero.1 h0 with h0 | h0
    · rcases mul_eq_zero.1 h0 with h0 | h0
      · have : x = e₁ := sub_eq_zero.1 h0
        subst this
        exact Or.inr (Or.inl rfl)
      · have : x = e₂ := sub_eq_zero.1 h0
        subst this
        exact Or.inr (Or.inr (Or.inl rfl))
    · have : x = e₃ := sub_eq_zero.1 h0
      subst this
      exact Or.inr (Or.inr (Or.inr rfl))

/-- **Weak Mordell–Weil** for `y² = (x - e₁)(x - e₂)(x - e₃)` su `ℚ`. -/
theorem finiteIndex_two_nsmul (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃) :
    (nsmulAddMonoidHom (α := (ratCurve e₁ e₂ e₃).toAffine.Point) 2).range.FiniteIndex := by
  classical
  set H := (nsmulAddMonoidHom (α := (ratCurve e₁ e₂ e₃).toAffine.Point) 2).range with hH
  have hfin : Finite ((ratCurve e₁ e₂ e₃).toAffine.Point ⧸ H) := by
    rw [← Set.finite_univ_iff]
    let B := {P : (ratCurve e₁ e₂ e₃).toAffine.Point // pointY P ≠ 0}
    let g : B → (ratCurve e₁ e₂ e₃).toAffine.Point ⧸ H := fun P => (P.1 : _ ⧸ H)
    let f : B → _ := fun P => descentClass e₁ e₂ e₃ P.1
    have hfac : g.FactorsThrough f := by
      intro P Q hPQ
      exact QuotientAddGroup.eq_iff_sub_mem.2
        (sub_mem_range_of_descentClass_eq h12 h13 h23 P.2 Q.2 hPQ)
    have hfin1 : (Set.range (Function.extend f g fun _ => 0)).Finite := Set.finite_range _
    have hfin2 : ((fun P : (ratCurve e₁ e₂ e₃).toAffine.Point => (P : _ ⧸ H)) ''
        {P | pointY P = 0}).Finite := finite_pointY_eq_zero.image _
    refine (hfin1.union hfin2).subset ?_
    intro q _
    obtain ⟨P, rfl⟩ := QuotientAddGroup.mk_surjective q
    by_cases hP : pointY P = 0
    · exact Or.inr ⟨P, hP, rfl⟩
    · exact Or.inl ⟨f ⟨P, hP⟩, hfac.extend_apply _ ⟨P, hP⟩⟩
  exact AddSubgroup.finiteIndex_of_finite_quotient

lemma ratCurve_isElliptic (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃) :
    (ratCurve e₁ e₂ e₃).IsElliptic := by
  rw [isElliptic_iff, isUnit_iff_ne_zero]
  have hΔ : (ratCurve e₁ e₂ e₃).Δ = 16 * ((e₁ - e₂) * (e₁ - e₃) * (e₂ - e₃)) ^ 2 := by
    simp only [ratCurve, twoTorsionCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  rw [hΔ]
  have q12 : e₁ - e₂ ≠ 0 := sub_ne_zero.2 h12
  have q13 : e₁ - e₃ ≠ 0 := sub_ne_zero.2 h13
  have q23 : e₂ - e₃ ≠ 0 := sub_ne_zero.2 h23
  positivity

/-- **Mordell–Weil** for `y² = (x - e₁)(x - e₂)(x - e₃)` over `ℚ`, with distinct
rational roots: the group of rational points is finitely generated. -/
theorem fg_twoTorsionCurve (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃) :
    AddGroup.FG (ratCurve e₁ e₂ e₃).toAffine.Point := by
  have := ratCurve_isElliptic h12 h13 h23
  exact fg_of_finiteIndex _ (finiteIndex_two_nsmul h12 h13 h23)

end Discesa

/-- The congruent number curve `y² = x³ - x` has a finitely generated group of
rational points. -/
theorem fg_congruent_one : AddGroup.FG (ratCurve (-1) 0 1).toAffine.Point :=
  fg_twoTorsionCurve (by norm_num) (by norm_num) (by norm_num)

/-- The curve `y² = x³ - 25x`, attached to the congruent number 5, has a finitely
generated group of rational points. -/
theorem fg_congruent_five : AddGroup.FG (ratCurve (-5) 0 5).toAffine.Point :=
  fg_twoTorsionCurve (by norm_num) (by norm_num) (by norm_num)

/-- An example with non-integer roots: `y² = (x - 1/2)(x - 1/3)(x + 2/5)`. -/
theorem fg_rational_roots : AddGroup.FG (ratCurve (1 / 2) (1 / 3) (-2 / 5)).toAffine.Point :=
  fg_twoTorsionCurve (by norm_num) (by norm_num) (by norm_num)

end BSD
