import HeckeCM.Bridge
import HeckeCM.InfiniteOrder

/-!
# Vanishing at `s = 1` and rational points, side by side

For `d ≡ 5, 6, 7 (mod 8)` squarefree, `vanishing_and_rank` puts together what is
proved about the two sides of the Birch and Swinnerton-Dyer conjecture for
`C_d : y² = x³ − d²x`:

* analytic side: every entire continuation of Mathlib's L-series of `C_d`
  vanishes at `s = 1`;
* algebraic side: `C_d(ℚ)` has a point of infinite order if and only if `d` is
  a congruent number.

That every such `d` is congruent is not proved here: it is an open problem,
known to follow from the conjecture. For `d = 5, 6, 7` an explicit point gives
`PositiveRanks d`.

Neither the equality of the two ranks nor their value is proved.
-/

set_option autoImplicit false

namespace CMPoints

lemma not_four_dvd_of_squarefree {d : ℕ} (hsq : Squarefree d) : ¬ 4 ∣ d := by
  intro h
  have h2 : IsUnit (2 : ℕ) := hsq 2 (by rw [show (2 : ℕ) * 2 = 4 from rfl]; exact h)
  rw [Nat.isUnit_iff] at h2
  omega

/-- **Both sides, for `d ≡ 5, 6, 7 (mod 8)` squarefree.** The L-series vanishes
at `s = 1`, and the curve has a rational point of infinite order exactly when
`d` is a congruent number. -/
theorem vanishing_and_rank {d : ℕ} (hsq : Squarefree d)
    (h8 : d % 8 = 5 ∨ d % 8 = 6 ∨ d % 8 = 7) :
    (∀ F : ℂ → ℂ,
        IsEntireContinuation (⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ) F → F 1 = 0) ∧
      ((∃ P : (congCurve d).Point, ¬ IsOfFinAddOrder P) ↔ IsCongruent d) :=
  ⟨rootNumberVanishing d h8 hsq,
    exists_not_isOfFinAddOrder_iff_isCongruent (not_four_dvd_of_squarefree hsq)⟩

/-- A point of infinite order, and vanishing of the L-series at `s = 1`. -/
def PositiveRanks (d : ℕ) : Prop :=
  (∃ P : (congCurve d).Point, ¬ IsOfFinAddOrder P) ∧
    ∀ F : ℂ → ℂ, IsEntireContinuation (⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ) F →
      F 1 = 0

/-- For `d ≡ 5, 6, 7 (mod 8)` squarefree, `PositiveRanks d` holds as soon as
`d` is a congruent number. -/
theorem positiveRanks_of_isCongruent {d : ℕ} (hsq : Squarefree d)
    (h8 : d % 8 = 5 ∨ d % 8 = 6 ∨ d % 8 = 7) (hc : IsCongruent d) : PositiveRanks d :=
  ⟨(vanishing_and_rank hsq h8).2.2 hc, (vanishing_and_rank hsq h8).1⟩

lemma squarefree_six : Squarefree (6 : ℕ) := by
  rw [show (6 : ℕ) = 2 * 3 from rfl]
  exact Nat.squarefree_mul_iff.2 ⟨by decide, Nat.prime_two.squarefree, Nat.prime_three.squarefree⟩

theorem positiveRanks_five : PositiveRanks 5 :=
  ⟨exists_not_isOfFinAddOrder_five,
    rootNumberVanishing 5 (by decide) Nat.prime_five.squarefree⟩

theorem positiveRanks_six : PositiveRanks 6 :=
  ⟨exists_not_isOfFinAddOrder_six, rootNumberVanishing 6 (by decide) squarefree_six⟩

theorem positiveRanks_seven : PositiveRanks 7 :=
  ⟨exists_not_isOfFinAddOrder_seven,
    rootNumberVanishing 7 (by decide) (Nat.prime_seven.squarefree)⟩

end CMPoints
