import Mathlib

/-!
# Torsion and points of infinite order on `y² = x³ − d²x`

Let `d` be a natural number not divisible by `4` (for instance squarefree) and
`C_d : y² = x³ − d²x` over `ℚ`.

* `add_self_eq_some`: for a rational point `P = (x, y)` with `y ≠ 0`, the
  `x`-coordinate of `2P` is `(x² + d²)² / (4x(x² − d²))`.
* `padicValRat_two_mul_neg`: that number has negative 2-adic valuation.
* `padicValRat_add_self`: if `v₂(x) < 0` then `v₂(x(2P)) = v₂(x) − 2`.

So for `y ≠ 0` the points `2P, 4P, 8P, …` have pairwise distinct
`x`-coordinates, and `P` has infinite order:

* `not_isOfFinAddOrder_of_ne_zero`: a point with `y ≠ 0` has infinite order;
* `isOfFinAddOrder_iff_two_nsmul_eq_zero`: the torsion of `C_d(ℚ)` is its
  2-torsion;
* `exists_not_isOfFinAddOrder_iff_isCongruent`: `C_d(ℚ)` has a point of
  infinite order if and only if `d` is a congruent number, i.e. the area of a
  right triangle with rational sides.

Nothing here uses reduction modulo primes: only the duplication formula and
parity.
-/

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace CMPoints

/-- The curve `y² = x³ − d²x` in affine coordinates. -/
abbrev congCurve (d : ℕ) : Affine ℚ := (⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ).toAffine

lemma congCurve_equation_iff (d : ℕ) (x y : ℚ) :
    (congCurve d).Equation x y ↔ y ^ 2 = x * (x ^ 2 - (d : ℚ) ^ 2) := by
  rw [Affine.equation_iff]
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h

/-- A point of the curve with `y ≠ 0` is nonsingular. -/
lemma nonsingular_of_equation_of_ne {d : ℕ} {x y : ℚ}
    (heq : y ^ 2 = x * (x ^ 2 - (d : ℚ) ^ 2)) (hy : y ≠ 0) : (congCurve d).Nonsingular x y := by
  rw [Affine.nonsingular_iff]
  refine ⟨(congCurve_equation_iff d x y).2 heq, Or.inr ?_⟩
  intro h0
  exact hy (by linear_combination h0 / 2)

/-! ## The duplication formula -/

/-- **Duplication.** For `y ≠ 0`, the point `2P` is affine with
`x(2P) = (x² + d²)² / (4x(x² − d²))`. -/
theorem add_self_eq_some {d : ℕ} {x y : ℚ} (h : (congCurve d).Nonsingular x y) (hy : y ≠ 0) :
    x ≠ 0 ∧ x ^ 2 - (d : ℚ) ^ 2 ≠ 0 ∧
      ∃ (y' : ℚ) (h' : (congCurve d).Nonsingular
          ((x ^ 2 + (d : ℚ) ^ 2) ^ 2 / (4 * x * (x ^ 2 - (d : ℚ) ^ 2))) y'),
        (Point.some x y h + Point.some x y h : (congCurve d).Point) = Point.some _ y' h' := by
  have heq : y ^ 2 = x * (x ^ 2 - (d : ℚ) ^ 2) := (congCurve_equation_iff d x y).1 h.left
  have hprod : x * (x ^ 2 - (d : ℚ) ^ 2) ≠ 0 := by
    rw [← heq]
    exact pow_ne_zero 2 hy
  have hx0 : x ≠ 0 := left_ne_zero_of_mul hprod
  have hB : x ^ 2 - (d : ℚ) ^ 2 ≠ 0 := right_ne_zero_of_mul hprod
  have hneg : y ≠ (congCurve d).negY x y := by
    simp only [negY]
    intro hyy
    exact hy (by linear_combination hyy / 2)
  have hslope : (congCurve d).slope x x y y = (3 * x ^ 2 - (d : ℚ) ^ 2) / (2 * y) := by
    rw [slope_of_Y_ne rfl hneg]
    simp only [negY]
    congr 1 <;> ring
  have hX : (congCurve d).addX x x ((congCurve d).slope x x y y) =
      (x ^ 2 + (d : ℚ) ^ 2) ^ 2 / (4 * x * (x ^ 2 - (d : ℚ) ^ 2)) := by
    have h4 : (2 * y) ^ 2 = 4 * x * (x ^ 2 - (d : ℚ) ^ 2) := by linear_combination 4 * heq
    rw [hslope]
    simp only [addX]
    rw [div_pow, h4]
    field_simp
    ring
  refine ⟨hx0, hB, ?_⟩
  have key := Point.add_self_of_Y_ne (h₁ := h) hneg
  rw [key]
  generalize_proofs hns
  revert hns
  rw [hX]
  intro hns
  exact ⟨_, hns, rfl⟩

/-! ## 2-adic valuations -/

lemma padicValRat_natCast_sq_nonneg (d : ℕ) : 0 ≤ padicValRat 2 ((d : ℚ) ^ 2) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · rw [padicValRat.pow, padicValRat.of_nat]
    positivity

/-- The valuations of `x² ± d²` when `v₂(x) < 0`. -/
lemma padicValRat_sq_add {d : ℕ} (hd : d ≠ 0) {x : ℚ} (hv : padicValRat 2 x < 0) (s : ℚ)
    (hs : s = 1 ∨ s = -1) :
    x ^ 2 + s * (d : ℚ) ^ 2 ≠ 0 ∧
      padicValRat 2 (x ^ 2 + s * (d : ℚ) ^ 2) = 2 * padicValRat 2 x := by
  have hx0 : x ≠ 0 := fun h => by simp [h] at hv
  have hd0 : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hd
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have hsv : padicValRat 2 (s * (d : ℚ) ^ 2) = padicValRat 2 ((d : ℚ) ^ 2) := by
    rcases hs with rfl | rfl
    · rw [one_mul]
    · rw [neg_one_mul, padicValRat.neg]
  have hx2 : padicValRat 2 (x ^ 2) = 2 * padicValRat 2 x := by
    rw [padicValRat.pow]
    norm_num
  have hlt : padicValRat 2 (x ^ 2) < padicValRat 2 (s * (d : ℚ) ^ 2) := by
    rw [hsv, hx2]
    have := padicValRat_natCast_sq_nonneg d
    omega
  have hne : x ^ 2 + s * (d : ℚ) ^ 2 ≠ 0 := by
    intro h
    have h1 : x ^ 2 = -(s * (d : ℚ) ^ 2) := by linear_combination h
    rw [h1, padicValRat.neg] at hlt
    exact lt_irrefl _ hlt
  refine ⟨hne, ?_⟩
  rw [padicValRat.add_eq_of_lt hne (pow_ne_zero 2 hx0) (mul_ne_zero hs0 (pow_ne_zero 2 hd0)) hlt,
    hx2]

/-- If `v₂(x) < 0`, the `x`-coordinate of `2P` has valuation `v₂(x) − 2`. -/
theorem padicValRat_add_self {d : ℕ} (hd : d ≠ 0) {x : ℚ} (hv : padicValRat 2 x < 0) :
    padicValRat 2 ((x ^ 2 + (d : ℚ) ^ 2) ^ 2 / (4 * x * (x ^ 2 - (d : ℚ) ^ 2))) =
      padicValRat 2 x - 2 := by
  have hx0 : x ≠ 0 := fun h0 => by simp [h0] at hv
  obtain ⟨hA, hAv⟩ := padicValRat_sq_add hd hv 1 (Or.inl rfl)
  obtain ⟨hB, hBv⟩ := padicValRat_sq_add hd hv (-1) (Or.inr rfl)
  rw [one_mul] at hA hAv
  rw [neg_one_mul, ← sub_eq_add_neg] at hB hBv
  rw [padicValRat.div (pow_ne_zero 2 hA) (mul_ne_zero (mul_ne_zero (by norm_num) hx0) hB),
    padicValRat.pow, padicValRat.mul (mul_ne_zero (by norm_num) hx0) hB,
    padicValRat.mul (by norm_num) hx0, hAv, hBv]
  have h4v : padicValRat 2 (4 : ℚ) = 2 := by
    rw [show (4 : ℚ) = 2 ^ 2 by norm_num, padicValRat.pow]
    have : padicValRat 2 (2 : ℚ) = 1 := by exact_mod_cast padicValRat.self (p := 2) (by norm_num)
    rw [this]
    norm_num
  rw [h4v]
  push_cast
  ring

/-! ## Parity -/

lemma sq_of_odd {a : ℤ} (h : a % 2 = 1) : ∃ t : ℤ, a ^ 2 = 8 * t + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k + 1 := ⟨a / 2, by omega⟩
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · obtain ⟨l, rfl⟩ : ∃ l, k = 2 * l := ⟨k / 2, by omega⟩
    exact ⟨2 * l ^ 2 + l, by ring⟩
  · obtain ⟨l, rfl⟩ : ∃ l, k = 2 * l + 1 := ⟨k / 2, by omega⟩
    exact ⟨2 * l ^ 2 + 3 * l + 1, by ring⟩

lemma sq_of_even {a : ℤ} (h : a % 2 = 0) : ∃ t : ℤ, a ^ 2 = 4 * t := by
  obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k := ⟨a / 2, by omega⟩
  exact ⟨k ^ 2, by ring⟩

lemma not_two_dvd {N r : ℤ} (h : N = 2 * r + 1) : ¬ (2 : ℤ) ^ 1 ∣ N := by
  subst h
  rw [show (2 : ℤ) ^ 1 = 2 by norm_num]
  omega

lemma not_eight_dvd {N r : ℤ} (h : N = 4 * (2 * r + 1)) : ¬ (2 : ℤ) ^ 3 ∣ N := by
  subst h
  rw [show (2 : ℤ) ^ 3 = 8 by norm_num]
  omega

lemma not_thirtyTwo_dvd {N r : ℤ} (h : N = 16 * (2 * r + 1)) : ¬ (2 : ℤ) ^ 5 ∣ N := by
  subst h
  rw [show (2 : ℤ) ^ 5 = 32 by norm_num]
  omega

lemma not_oneTwentyEight_dvd {N r : ℤ} (h : N = 64 * (2 * r + 1)) : ¬ (2 : ℤ) ^ 7 ∣ N := by
  subst h
  rw [show (2 : ℤ) ^ 7 = 128 by norm_num]
  omega

/-- **The parity argument.** If `4 ∤ d` and `m`, `n` are not both even, some
power of `2` divides `4mn(m² − d²n²)` but not `(m² + d²n²)²`. -/
theorem exists_two_pow_dvd {d m n : ℤ} (hd : ¬ (4 : ℤ) ∣ d) (hmn : ¬ ((2 : ℤ) ∣ m ∧ (2 : ℤ) ∣ n)) :
    ∃ j : ℕ, (2 : ℤ) ^ j ∣ 4 * m * n * (m ^ 2 - d ^ 2 * n ^ 2) ∧
      ¬ (2 : ℤ) ^ j ∣ (m ^ 2 + d ^ 2 * n ^ 2) ^ 2 := by
  rcases (by omega : d % 2 = 1 ∨ d % 4 = 2) with hd1 | hd2
  · obtain ⟨u, hu⟩ := sq_of_odd hd1
    rcases Int.emod_two_eq_zero_or_one m with hm | hm <;>
      rcases Int.emod_two_eq_zero_or_one n with hn | hn
    · exact absurd ⟨Int.dvd_of_emod_eq_zero hm, Int.dvd_of_emod_eq_zero hn⟩ hmn
    · -- `m` even, `n` odd
      obtain ⟨t, ht⟩ := sq_of_even hm
      obtain ⟨w, hw⟩ := sq_of_odd hn
      refine ⟨1, ⟨2 * m * n * (m ^ 2 - d ^ 2 * n ^ 2), by ring⟩,
        not_two_dvd (r := 2 * (2 * t + 4 * (8 * u * w + u + w)) ^ 2 +
          2 * (2 * t + 4 * (8 * u * w + u + w))) ?_⟩
      have hS : m ^ 2 + d ^ 2 * n ^ 2 = 2 * (2 * t + 4 * (8 * u * w + u + w)) + 1 := by
        linear_combination ht + n ^ 2 * hu + (8 * u + 1) * hw
      rw [hS]
      ring
    · -- `m` odd, `n` even
      obtain ⟨a, ha⟩ := sq_of_odd hm
      obtain ⟨t, ht⟩ := sq_of_even hn
      refine ⟨1, ⟨2 * m * n * (m ^ 2 - d ^ 2 * n ^ 2), by ring⟩,
        not_two_dvd (r := 2 * (4 * a + 2 * d ^ 2 * t) ^ 2 + 2 * (4 * a + 2 * d ^ 2 * t)) ?_⟩
      have hS : m ^ 2 + d ^ 2 * n ^ 2 = 2 * (4 * a + 2 * d ^ 2 * t) + 1 := by
        linear_combination ha + d ^ 2 * ht
      rw [hS]
      ring
    · -- `m` odd, `n` odd
      obtain ⟨a, ha⟩ := sq_of_odd hm
      obtain ⟨w, hw⟩ := sq_of_odd hn
      have hT : m ^ 2 - d ^ 2 * n ^ 2 = 8 * (a - (8 * u * w + u + w)) := by
        linear_combination ha - n ^ 2 * hu - (8 * u + 1) * hw
      have hS : m ^ 2 + d ^ 2 * n ^ 2 = 8 * (a + (8 * u * w + u + w)) + 2 := by
        linear_combination ha + n ^ 2 * hu + (8 * u + 1) * hw
      refine ⟨3, ⟨4 * m * n * (a - (8 * u * w + u + w)), by rw [hT]; ring⟩,
        not_eight_dvd (r := 8 * (a + (8 * u * w + u + w)) ^ 2 +
          4 * (a + (8 * u * w + u + w))) ?_⟩
      rw [hS]
      ring
  · obtain ⟨e, rfl⟩ : ∃ e, d = 2 * e := ⟨d / 2, by omega⟩
    have he : e % 2 = 1 := by omega
    obtain ⟨u, hu⟩ := sq_of_odd he
    rcases Int.emod_two_eq_zero_or_one m with hm | hm
    · have hn : n % 2 = 1 := by
        rcases Int.emod_two_eq_zero_or_one n with hn | hn
        · exact absurd ⟨Int.dvd_of_emod_eq_zero hm, Int.dvd_of_emod_eq_zero hn⟩ hmn
        · exact hn
      obtain ⟨w, hw⟩ := sq_of_odd hn
      obtain ⟨m', rfl⟩ : ∃ m', m = 2 * m' := ⟨m / 2, by omega⟩
      have hD : 4 * (2 * m') * n * ((2 * m') ^ 2 - (2 * e) ^ 2 * n ^ 2) =
          32 * (m' * n * (m' ^ 2 - e ^ 2 * n ^ 2)) := by ring
      rcases Int.emod_two_eq_zero_or_one m' with hm' | hm'
      · -- `m = 2m'` with `m'` even
        obtain ⟨t, ht⟩ := sq_of_even hm'
        have hS : (2 * m') ^ 2 + (2 * e) ^ 2 * n ^ 2 =
            4 * (2 * (2 * t + 4 * (8 * u * w + u + w)) + 1) := by
          linear_combination 4 * ht + 4 * n ^ 2 * hu + 4 * (8 * u + 1) * hw
        refine ⟨5, ⟨m' * n * (m' ^ 2 - e ^ 2 * n ^ 2), by rw [hD]; norm_num⟩,
          not_thirtyTwo_dvd (r := 2 * (2 * t + 4 * (8 * u * w + u + w)) ^ 2 +
            2 * (2 * t + 4 * (8 * u * w + u + w))) ?_⟩
        rw [hS]
        ring
      · -- `m = 2m'` with `m'` odd
        obtain ⟨a, ha⟩ := sq_of_odd hm'
        have hT : m' ^ 2 - e ^ 2 * n ^ 2 = 8 * (a - (8 * u * w + u + w)) := by
          linear_combination ha - n ^ 2 * hu - (8 * u + 1) * hw
        have hS : (2 * m') ^ 2 + (2 * e) ^ 2 * n ^ 2 =
            8 * (4 * (a + (8 * u * w + u + w)) + 1) := by
          linear_combination 4 * ha + 4 * n ^ 2 * hu + 4 * (8 * u + 1) * hw
        refine ⟨7, ⟨2 * (m' * n * (a - (8 * u * w + u + w))), by rw [hD, hT]; norm_num; ring⟩,
          not_oneTwentyEight_dvd (r := 8 * (a + (8 * u * w + u + w)) ^ 2 +
            4 * (a + (8 * u * w + u + w))) ?_⟩
        rw [hS]
        ring
    · -- `m` odd
      obtain ⟨a, ha⟩ := sq_of_odd hm
      refine ⟨1, ⟨2 * m * n * (m ^ 2 - (2 * e) ^ 2 * n ^ 2), by ring⟩,
        not_two_dvd (r := 2 * (4 * a + 2 * e ^ 2 * n ^ 2) ^ 2 + 2 * (4 * a + 2 * e ^ 2 * n ^ 2)) ?_⟩
      have hS : m ^ 2 + (2 * e) ^ 2 * n ^ 2 = 2 * (4 * a + 2 * e ^ 2 * n ^ 2) + 1 := by
        linear_combination ha
      rw [hS]
      ring

/-- A quotient of integers `N / D` has negative 2-adic valuation as soon as
some power of `2` divides `D` but not `N`. -/
lemma padicValRat_div_neg {N D : ℤ} (hN : N ≠ 0) (hD : D ≠ 0) {j : ℕ} (h1 : (2 : ℤ) ^ j ∣ D)
    (h2 : ¬ (2 : ℤ) ^ j ∣ N) : padicValRat 2 ((N : ℚ) / D) < 0 := by
  have hN' : (N : ℚ) ≠ 0 := Int.cast_ne_zero.2 hN
  have hD' : (D : ℚ) ≠ 0 := Int.cast_ne_zero.2 hD
  have e1 : j ≤ padicValInt 2 D := by
    have := (padicValInt_dvd_iff (p := 2) j D).1 (by exact_mod_cast h1)
    exact this.resolve_left hD
  have e2 : padicValInt 2 N < j := by
    by_contra hle
    exact h2 (by exact_mod_cast (padicValInt_dvd_iff (p := 2) j N).2 (Or.inr (not_lt.1 hle)))
  rw [padicValRat.div hN' hD', padicValRat.of_int, padicValRat.of_int]
  omega

/-- **For `4 ∤ d` and `y ≠ 0`, the `x`-coordinate of `2P` has negative 2-adic
valuation.** -/
theorem padicValRat_two_mul_neg {d : ℕ} (hd4 : ¬ 4 ∣ d) {x : ℚ} (hx0 : x ≠ 0)
    (hB : x ^ 2 - (d : ℚ) ^ 2 ≠ 0) :
    padicValRat 2 ((x ^ 2 + (d : ℚ) ^ 2) ^ 2 / (4 * x * (x ^ 2 - (d : ℚ) ^ 2))) < 0 := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hd4 (dvd_zero 4)
  have hdQ : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hd0
  set m : ℤ := x.num with hm
  set n : ℤ := (x.den : ℤ) with hn
  have hn0 : n ≠ 0 := by
    rw [hn]
    exact_mod_cast x.den_ne_zero
  have hnQ : (n : ℚ) ≠ 0 := Int.cast_ne_zero.2 hn0
  have hx : x = (m : ℚ) / n := by
    rw [hm, hn]
    exact_mod_cast (Rat.num_div_den x).symm
  have hm0 : m ≠ 0 := by
    intro h
    rw [hx, h] at hx0
    simp at hx0
  have hmn : ¬ ((2 : ℤ) ∣ m ∧ (2 : ℤ) ∣ n) := by
    rintro ⟨h1, h2⟩
    have h1' : 2 ∣ x.num.natAbs := by
      have := Int.natAbs_dvd_natAbs.2 h1
      simpa using this
    have h2' : 2 ∣ x.den := by
      rw [hn] at h2
      exact_mod_cast h2
    have := Nat.dvd_gcd h1' h2'
    rw [x.reduced.gcd_eq_one] at this
    omega
  have hdZ : ¬ (4 : ℤ) ∣ (d : ℤ) := by
    intro h
    exact hd4 (by exact_mod_cast h)
  obtain ⟨j, hj1, hj2⟩ := exists_two_pow_dvd hdZ hmn
  have hT0 : m ^ 2 - (d : ℤ) ^ 2 * n ^ 2 ≠ 0 := by
    intro h
    apply hB
    have hq : ((m : ℚ)) ^ 2 - (d : ℚ) ^ 2 * (n : ℚ) ^ 2 = 0 := by exact_mod_cast h
    rw [hx]
    field_simp
    linear_combination hq
  have hS0 : m ^ 2 + (d : ℤ) ^ 2 * n ^ 2 ≠ 0 := by
    have h1 : 0 < m ^ 2 := by positivity
    have h2 : 0 ≤ (d : ℤ) ^ 2 * n ^ 2 := by positivity
    omega
  have hval := padicValRat_div_neg (N := (m ^ 2 + (d : ℤ) ^ 2 * n ^ 2) ^ 2)
    (D := 4 * m * n * (m ^ 2 - (d : ℤ) ^ 2 * n ^ 2)) (pow_ne_zero 2 hS0)
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hm0) hn0) hT0) hj1 hj2
  have hTq : ((m : ℚ)) ^ 2 - (d : ℚ) ^ 2 * (n : ℚ) ^ 2 ≠ 0 := by exact_mod_cast hT0
  have hrew : (x ^ 2 + (d : ℚ) ^ 2) ^ 2 / (4 * x * (x ^ 2 - (d : ℚ) ^ 2)) =
      (((m ^ 2 + (d : ℤ) ^ 2 * n ^ 2) ^ 2 : ℤ) : ℚ) /
        ((4 * m * n * (m ^ 2 - (d : ℤ) ^ 2 * n ^ 2) : ℤ) : ℚ) := by
    have hB' : ((m : ℚ) / n) ^ 2 - (d : ℚ) ^ 2 ≠ 0 := by rwa [hx] at hB
    have hm0Q : (m : ℚ) ≠ 0 := Int.cast_ne_zero.2 hm0
    rw [hx]
    push_cast
    field_simp
  rw [hrew]
  exact hval

/-! ## Infinite order -/

/-- The multiples `2ᵏ P` of a point with `v₂(x) < 0` are affine points with
valuation `v₂(x) − 2k`. -/
theorem exists_two_pow_nsmul_eq_some {d : ℕ} (hd : d ≠ 0) {x y : ℚ}
    (h : (congCurve d).Nonsingular x y) (hv : padicValRat 2 x < 0) (k : ℕ) :
    ∃ (x' y' : ℚ) (h' : (congCurve d).Nonsingular x' y'),
      (2 ^ k • Point.some x y h : (congCurve d).Point) = Point.some x' y' h' ∧
        padicValRat 2 x' = padicValRat 2 x - 2 * k := by
  induction k with
  | zero => exact ⟨x, y, h, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨x₁, y₁, h₁, heq, hval⟩ := ih
    have hv₁ : padicValRat 2 x₁ < 0 := by
      rw [hval]
      have : (0 : ℤ) ≤ 2 * (k : ℤ) := by positivity
      omega
    have hy₁ : y₁ ≠ 0 := by
      intro hy
      have hx₁ : x₁ ≠ 0 := fun h0 => by simp [h0] at hv₁
      obtain ⟨hB, -⟩ := padicValRat_sq_add hd hv₁ (-1) (Or.inr rfl)
      rw [neg_one_mul, ← sub_eq_add_neg] at hB
      have he := (congCurve_equation_iff d x₁ y₁).1 h₁.left
      rw [hy] at he
      exact mul_ne_zero hx₁ hB (by linear_combination -he)
    obtain ⟨-, -, y₂, h₂, heq₂⟩ := add_self_eq_some h₁ hy₁
    refine ⟨_, y₂, h₂, ?_, ?_⟩
    · rw [pow_succ, mul_nsmul, two_nsmul, heq, heq₂]
    · rw [padicValRat_add_self hd hv₁, hval]
      push_cast
      ring

/-- A point with `v₂(x) < 0` has infinite order. -/
theorem not_isOfFinAddOrder_of_padicValRat_neg {d : ℕ} (hd : d ≠ 0) {x y : ℚ}
    (h : (congCurve d).Nonsingular x y) (hv : padicValRat 2 x < 0) :
    ¬ IsOfFinAddOrder (Point.some x y h : (congCurve d).Point) := by
  intro hfin
  have : Finite (AddSubgroup.zmultiples (Point.some x y h : (congCurve d).Point)) :=
    finite_zmultiples.2 hfin
  let f : ℕ → AddSubgroup.zmultiples (Point.some x y h : (congCurve d).Point) := fun k =>
    ⟨2 ^ k • Point.some x y h, AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples _) _⟩
  have hinj : Function.Injective f := by
    intro k l hkl
    have hkl' : (2 ^ k • Point.some x y h : (congCurve d).Point) = 2 ^ l • Point.some x y h :=
      congrArg Subtype.val hkl
    obtain ⟨x₁, y₁, h₁, e₁, v₁⟩ := exists_two_pow_nsmul_eq_some hd h hv k
    obtain ⟨x₂, y₂, h₂, e₂, v₂⟩ := exists_two_pow_nsmul_eq_some hd h hv l
    rw [e₁, e₂] at hkl'
    have hx : x₁ = x₂ := by
      injection hkl'
    rw [hx, v₂] at v₁
    omega
  exact not_injective_infinite_finite f hinj

/-- **A rational point with `y ≠ 0` has infinite order** (for `4 ∤ d`). -/
theorem not_isOfFinAddOrder_of_ne_zero {d : ℕ} (hd4 : ¬ 4 ∣ d) {x y : ℚ}
    (h : (congCurve d).Nonsingular x y) (hy : y ≠ 0) :
    ¬ IsOfFinAddOrder (Point.some x y h : (congCurve d).Point) := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hd4 (dvd_zero 4)
  obtain ⟨hx0, hB, y', h', heq⟩ := add_self_eq_some h hy
  intro hfin
  have h2 : IsOfFinAddOrder (2 • Point.some x y h : (congCurve d).Point) := hfin.nsmul
  rw [two_nsmul, heq] at h2
  exact not_isOfFinAddOrder_of_padicValRat_neg hd0 h' (padicValRat_two_mul_neg hd4 hx0 hB) h2

/-- **The torsion of `C_d(ℚ)` is its 2-torsion** (for `4 ∤ d`). -/
theorem isOfFinAddOrder_iff_two_nsmul_eq_zero {d : ℕ} (hd4 : ¬ 4 ∣ d) (P : (congCurve d).Point) :
    IsOfFinAddOrder P ↔ 2 • P = 0 := by
  constructor
  · intro hfin
    rcases P with _ | ⟨x, y, h⟩
    · exact nsmul_zero 2
    · by_cases hy : y = 0
      · rw [two_nsmul]
        exact Point.add_self_of_Y_eq (by simp only [negY]; rw [hy]; ring)
      · exact absurd hfin (not_isOfFinAddOrder_of_ne_zero hd4 h hy)
  · intro h2
    exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨2, by norm_num, h2⟩

/-! ## Congruent numbers -/

/-- `d` is a congruent number: the area of a right triangle with rational sides. -/
def IsCongruent (d : ℕ) : Prop :=
  ∃ a b c : ℚ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ a * b / 2 = d

/-- A rational right triangle of area `d` gives a rational point with `y ≠ 0`. -/
theorem exists_point_of_isCongruent {d : ℕ} (h : IsCongruent d) :
    ∃ x y : ℚ, y ^ 2 = x * (x ^ 2 - (d : ℚ) ^ 2) ∧ y ≠ 0 := by
  obtain ⟨a, b, c, ha, hb, hc, h1, h2⟩ := h
  have hca : 0 < c - a := by
    have : a ^ 2 < c ^ 2 := by nlinarith
    have := lt_of_pow_lt_pow_left₀ 2 hc.le this
    linarith
  have hca0 : c - a ≠ 0 := hca.ne'
  have hD : (d : ℚ) = a * b / 2 := h2.symm
  have hD0 : (d : ℚ) ≠ 0 := by
    rw [hD]
    positivity
  have hk : b ^ 2 - (c - a) ^ 2 = 2 * a * (c - a) := by linear_combination h1
  obtain ⟨t, ht⟩ : ∃ t : ℚ, (c - a) * t = 1 := ⟨(c - a)⁻¹, mul_inv_cancel₀ hca0⟩
  have ht0 : t ≠ 0 := right_ne_zero_of_mul (ht ▸ one_ne_zero)
  have hx2 : ((d : ℚ) * b * t) ^ 2 - (d : ℚ) ^ 2 = 2 * a * (d : ℚ) ^ 2 * t := by
    linear_combination (d : ℚ) ^ 2 * t ^ 2 * hk +
      ((d : ℚ) ^ 2 * ((c - a) * t + 1) + 2 * a * (d : ℚ) ^ 2 * t) * ht
  refine ⟨(d : ℚ) * b * t, 2 * (d : ℚ) ^ 2 * t, ?_,
    mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 2 hD0)) ht0⟩
  linear_combination (-((d : ℚ) * b * t)) * hx2 + 4 * (d : ℚ) ^ 3 * t ^ 2 * hD

/-- A rational point with `y ≠ 0` gives a rational right triangle of area `d`. -/
theorem isCongruent_of_point {d : ℕ} (hd : d ≠ 0) {x y : ℚ}
    (heq : y ^ 2 = x * (x ^ 2 - (d : ℚ) ^ 2)) (hy : y ≠ 0) : IsCongruent d := by
  have hd0 : (0 : ℚ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hprod : x * (x ^ 2 - (d : ℚ) ^ 2) ≠ 0 := by
    rw [← heq]
    exact pow_ne_zero 2 hy
  have hx0 : x ≠ 0 := left_ne_zero_of_mul hprod
  have hB : x ^ 2 - (d : ℚ) ^ 2 ≠ 0 := right_ne_zero_of_mul hprod
  have hA : x ^ 2 + (d : ℚ) ^ 2 ≠ 0 := by positivity
  refine ⟨|(x ^ 2 - (d : ℚ) ^ 2) / y|, |2 * (d : ℚ) * x / y|, |(x ^ 2 + (d : ℚ) ^ 2) / y|,
    abs_pos.2 (div_ne_zero hB hy),
    abs_pos.2 (div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hd0.ne') hx0) hy),
    abs_pos.2 (div_ne_zero hA hy), ?_, ?_⟩
  · rw [sq_abs, sq_abs, sq_abs]
    field_simp
    ring
  · rw [← abs_mul]
    have hmul : (x ^ 2 - (d : ℚ) ^ 2) / y * (2 * (d : ℚ) * x / y) = 2 * (d : ℚ) := by
      rw [div_mul_div_comm, div_eq_iff (mul_ne_zero hy hy)]
      linear_combination (-2 * (d : ℚ)) * heq
    rw [hmul, abs_of_pos (by positivity)]
    ring

/-- **`C_d(ℚ)` has a point of infinite order if and only if `d` is a congruent
number** (for `4 ∤ d`). -/
theorem exists_not_isOfFinAddOrder_iff_isCongruent {d : ℕ} (hd4 : ¬ 4 ∣ d) :
    (∃ P : (congCurve d).Point, ¬ IsOfFinAddOrder P) ↔ IsCongruent d := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hd4 (dvd_zero 4)
  constructor
  · rintro ⟨P, hP⟩
    rcases P with _ | ⟨x, y, h⟩
    · exact absurd (isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨1, one_pos, nsmul_zero 1⟩) hP
    · have hy : y ≠ 0 := by
        intro hy
        apply hP
        rw [isOfFinAddOrder_iff_two_nsmul_eq_zero hd4, two_nsmul]
        exact Point.add_self_of_Y_eq (by simp only [negY]; rw [hy]; ring)
      exact isCongruent_of_point hd0 ((congCurve_equation_iff d x y).1 h.left) hy
  · intro hc
    obtain ⟨x, y, heq, hy⟩ := exists_point_of_isCongruent hc
    exact ⟨_, not_isOfFinAddOrder_of_ne_zero hd4 (nonsingular_of_equation_of_ne heq hy) hy⟩

/-! ## Three examples -/

/-- `(−4, 6)` on `y² = x³ − 25x` has infinite order. -/
theorem exists_not_isOfFinAddOrder_five : ∃ P : (congCurve 5).Point, ¬ IsOfFinAddOrder P :=
  ⟨_, not_isOfFinAddOrder_of_ne_zero (by decide)
    (nonsingular_of_equation_of_ne (x := -4) (y := 6) (by norm_num) (by norm_num)) (by norm_num)⟩

/-- `(−3, 9)` on `y² = x³ − 36x` has infinite order. -/
theorem exists_not_isOfFinAddOrder_six : ∃ P : (congCurve 6).Point, ¬ IsOfFinAddOrder P :=
  ⟨_, not_isOfFinAddOrder_of_ne_zero (by decide)
    (nonsingular_of_equation_of_ne (x := -3) (y := 9) (by norm_num) (by norm_num)) (by norm_num)⟩

/-- `(25, 120)` on `y² = x³ − 49x` has infinite order. -/
theorem exists_not_isOfFinAddOrder_seven : ∃ P : (congCurve 7).Point, ¬ IsOfFinAddOrder P :=
  ⟨_, not_isOfFinAddOrder_of_ne_zero (by decide)
    (nonsingular_of_equation_of_ne (x := 25) (y := 120) (by norm_num) (by norm_num))
    (by norm_num)⟩

end CMPoints
