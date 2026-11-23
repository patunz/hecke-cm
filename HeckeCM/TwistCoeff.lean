import HeckeCM.GenEuler
import HeckeCM.CurveGlobalD

/-!
# The twisted sequence as a sequence of CM type

`cmCoeffTw d` is `gCoeff B a` with `B p = (p ∣ 2d)` and `a p = (d/p) · cmPrime p`,
and these data satisfy the hypotheses of `GenEuler.lean`.
-/

namespace CMPoints

lemma cmCoeffTw_eq_gCoeff (d : ℤ) :
    cmCoeffTw d = gCoeff (fun p : ℕ => (p : ℤ) ∣ 2 * d) (fun p => jacobiSym d p * cmPrime p) :=
  rfl

lemma twCoeff_sq_le (d : ℤ) (p : ℕ) (hp : p.Prime) :
    (jacobiSym d p * cmPrime p) ^ 2 ≤ 4 * p := by
  have h := cmPrime_sq_le hp
  rcases jacobiSym.trichotomy d p with h0 | h1 | h1
  · rw [h0, zero_mul]
    positivity
  · rw [h1, one_mul]
    exact h
  · rw [h1]
    linarith [h, show ((-1 : ℤ) * cmPrime p) ^ 2 = cmPrime p ^ 2 by ring]

lemma twCoeff_eq_zero (d : ℤ) (p : ℕ) (h : p % 4 = 3) : jacobiSym d p * cmPrime p = 0 := by
  rw [cmPrime, if_neg (by omega), mul_zero]

end CMPoints
