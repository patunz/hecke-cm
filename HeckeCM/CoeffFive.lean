import HeckeCM.GenCoeffBounds
import HeckeCM.DerivativeValue

/-!
# The coefficients of `y² = x³ − 25x` up to `n = 48`

Mathlib only. `gFive` is the sequence of CM type with bad primes `2`, `5` and
`a_p = (5/p) · cmPrime p`; it is the coefficient sequence of the L-series of
`y² = x³ − 25x` (that identification needs the rest of the library).

* `gFive_table`: for `n < 49`, `gFive n = fiveTable n`: the nonzero values are
  `a₁ = 1`, `a₉ = −3`, `a₁₃ = −6`, `a₁₇ = −2`, `a₂₉ = −10`, `a₃₇ = 2`, `a₄₁ = 10`;
* `two_pi_div_sqrt_bounds`: `0.22214 ≤ 2π / √800 ≤ 0.22215`.
-/

set_option autoImplicit false

noncomputable section

open Real

namespace CMPoints

/-- The sequence of CM type attached to `y² = x³ − 25x`. -/
def gFive : ℕ → ℤ :=
  gCoeff (fun p : ℕ => (p : ℤ) ∣ 2 * ((5 : ℕ) : ℤ)) (fun p => jacobiSym ((5 : ℕ) : ℤ) p * cmPrime p)

lemma gFive_even (n : ℕ) (h : 2 ∣ n) : gFive n = 0 :=
  gCoeff_eq_zero_of_bad Nat.prime_two (by norm_num) h

lemma gFive_five (n : ℕ) (h : 5 ∣ n) : gFive n = 0 :=
  gCoeff_eq_zero_of_bad Nat.prime_five (by norm_num) h

lemma gFive_one : gFive 1 = 1 := gCoeff_one

/-- At a good prime. -/
lemma gFive_prime {p : ℕ} (hp : p.Prime) (hB : ¬ ((p : ℤ) ∣ 2 * ((5 : ℕ) : ℤ))) :
    gFive p = jacobiSym ((5 : ℕ) : ℤ) p * cmPrime p :=
  gCoeff_prime hp hB

lemma gFive_inert {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 3)
    (hB : ¬ ((p : ℤ) ∣ 2 * ((5 : ℕ) : ℤ))) : gFive p = 0 := by
  rw [gFive_prime hp hB, cmPrime, if_neg (by omega), mul_zero]

lemma gFive_three : gFive 3 = 0 := gFive_inert Nat.prime_three (by norm_num) (by norm_num)

lemma gFive_three_mul (m : ℕ) (h : Nat.Coprime 3 m) : gFive (3 * m) = 0 := by
  rw [gFive, gCoeff_mul_of_coprime h]
  have : gCoeff (fun p : ℕ => (p : ℤ) ∣ 2 * ((5 : ℕ) : ℤ))
      (fun p => jacobiSym ((5 : ℕ) : ℤ) p * cmPrime p) 3 = 0 := gFive_three
  rw [this, zero_mul]

lemma gFive_three_pow (k : ℕ) (hk : k ≠ 0) : gFive (3 ^ k) = cmPow 3 0 k := by
  have h := gCoeff_prime_pow (B := fun p : ℕ => (p : ℤ) ∣ 2 * ((5 : ℕ) : ℤ))
    (a := fun p => jacobiSym ((5 : ℕ) : ℤ) p * cmPrime p) Nat.prime_three hk
  rw [if_neg (by norm_num)] at h
  have h0 : jacobiSym ((5 : ℕ) : ℤ) 3 * cmPrime 3 = 0 := by
    rw [cmPrime, if_neg (by norm_num), mul_zero]
  rw [gFive, h, h0]

lemma gFive_nine : gFive 9 = -3 := by
  rw [show (9 : ℕ) = 3 ^ 2 from rfl, gFive_three_pow 2 (by norm_num)]
  rfl

lemma gFive_twentySeven : gFive 27 = 0 := by
  rw [show (27 : ℕ) = 3 ^ 3 from rfl, gFive_three_pow 3 (by norm_num)]
  rfl

/-- At a prime `p ≡ 1 (mod 4)` written as `a² + b²` with `(a, b)` primary. -/
lemma gFive_split {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 1)
    (hB : ¬ ((p : ℤ) ∣ 2 * ((5 : ℕ) : ℤ))) {a b : ℤ} (h : a ^ 2 + b ^ 2 = p)
    (hab : IsPrimaryPair a b) : gFive p = jacobiSym ((5 : ℕ) : ℤ) p * (2 * a) := by
  rw [gFive_prime hp hB, cmPrime, if_pos h4, cmA_eq hp h hab]

lemma jacobi_five_thirteen : jacobiSym ((5 : ℕ) : ℤ) 13 = -1 := by norm_num
lemma jacobi_five_seventeen : jacobiSym ((5 : ℕ) : ℤ) 17 = -1 := by norm_num
lemma jacobi_five_twentyNine : jacobiSym ((5 : ℕ) : ℤ) 29 = 1 := by norm_num
lemma jacobi_five_thirtySeven : jacobiSym ((5 : ℕ) : ℤ) 37 = -1 := by norm_num
lemma jacobi_five_fortyOne : jacobiSym ((5 : ℕ) : ℤ) 41 = 1 := by norm_num

lemma gFive_thirteen : gFive 13 = -6 := by
  rw [gFive_split (p := 13) (by norm_num) (by norm_num) (by norm_num) (a := 3) (b := 2)
    (by norm_num) (by decide), jacobi_five_thirteen]
  norm_num

lemma gFive_seventeen : gFive 17 = -2 := by
  rw [gFive_split (p := 17) (by norm_num) (by norm_num) (by norm_num) (a := 1) (b := 4)
    (by norm_num) (by decide), jacobi_five_seventeen]
  norm_num

lemma gFive_twentyNine : gFive 29 = -10 := by
  rw [gFive_split (p := 29) (by norm_num) (by norm_num) (by norm_num) (a := -5) (b := 2)
    (by norm_num) (by decide), jacobi_five_twentyNine]
  norm_num

lemma gFive_thirtySeven : gFive 37 = 2 := by
  rw [gFive_split (p := 37) (by norm_num) (by norm_num) (by norm_num) (a := -1) (b := 6)
    (by norm_num) (by decide), jacobi_five_thirtySeven]
  norm_num

lemma gFive_fortyOne : gFive 41 = 10 := by
  rw [gFive_split (p := 41) (by norm_num) (by norm_num) (by norm_num) (a := 5) (b := 4)
    (by norm_num) (by decide), jacobi_five_fortyOne]
  norm_num

/-- **The coefficients of `y² = x³ − 25x` for `n < 49`.** -/
theorem gFive_table (n : ℕ) (hn : n < 49) : ((gFive n : ℤ) : ℝ) = fiveTable n := by
  interval_cases n
  all_goals first
    | ((rw [gFive_even] <;> norm_num [fiveTable]); done)
    | ((rw [gFive_five] <;> norm_num [fiveTable]); done)
    | ((rw [gFive_one]; norm_num [fiveTable]); done)
    | ((rw [gFive_nine]; norm_num [fiveTable]); done)
    | ((rw [gFive_thirteen]; norm_num [fiveTable]); done)
    | ((rw [gFive_seventeen]; norm_num [fiveTable]); done)
    | ((rw [gFive_twentySeven]; norm_num [fiveTable]); done)
    | ((rw [gFive_twentyNine]; norm_num [fiveTable]); done)
    | ((rw [gFive_thirtySeven]; norm_num [fiveTable]); done)
    | ((rw [gFive_fortyOne]; norm_num [fiveTable]); done)
    | ((rw [gFive_inert] <;> norm_num [fiveTable]); done)
    | ((rw [show (21 : ℕ) = 3 * 7 from rfl, gFive_three_mul] <;> norm_num [fiveTable]); done)
    | ((rw [show (33 : ℕ) = 3 * 11 from rfl, gFive_three_mul] <;> norm_num [fiveTable]); done)
    | ((rw [show (39 : ℕ) = 3 * 13 from rfl, gFive_three_mul] <;> norm_num [fiveTable]); done)

/-- `0.22214 ≤ 2π / √800 ≤ 0.22215`. -/
lemma two_pi_div_sqrt_bounds :
    (0.22214 : ℝ) ≤ 2 * π * (Real.sqrt 800)⁻¹ ∧ 2 * π * (Real.sqrt 800)⁻¹ ≤ 0.22215 := by
  have hs1 : Real.sqrt 800 ≤ 28.28428 :=
    (Real.sqrt_le_sqrt (by norm_num : (800 : ℝ) ≤ 28.28428 ^ 2)).trans_eq
      (Real.sqrt_sq (by norm_num))
  have hs2 : (28.28427 : ℝ) ≤ Real.sqrt 800 :=
    (Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 28.28427)).symm.le.trans
      (Real.sqrt_le_sqrt (by norm_num : (28.28427 : ℝ) ^ 2 ≤ 800))
  have hpos : (0 : ℝ) < Real.sqrt 800 := by linarith
  have hπ1 := Real.pi_gt_d6
  have hπ2 := Real.pi_lt_d6
  rw [← div_eq_mul_inv]
  constructor
  · rw [le_div_iff₀ hpos]
    nlinarith
  · rw [div_le_iff₀ hpos]
    nlinarith

end CMPoints
