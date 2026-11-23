import Mathlib
import HeckeCM.Analysis
import HeckeCM.Sequence

/-!
# Estimates on the local coefficients of `cmCoeff`

Everything uses Mathlib only:

* every prime `p ≡ 1 (mod 4)` has a primary representation
  (`exists_isPrimaryPair`), hence `cmPrime p ^ 2 ≤ 4 p` (`cmPrime_sq_le`);
* the power series of `cmPow p a` is the inverse of `1 - a T + p T²`
  (`mk_cmPow_mul`);
* `‖cmPow p a k‖ ≤ (k + 1) √p ^ k` when `a ^ 2 ≤ 4 p` (`norm_cmPow_le`).
-/

open LSeriesConv

namespace CMPoints

/-! ## Existence of the primary representation -/

/-- Every prime `p ≡ 1 (mod 4)` is `a² + b²` with `(a, b)` primary. -/
theorem exists_isPrimaryPair {p : ℕ} (hp : p.Prime) (h : p % 4 = 1) :
    ∃ a b : ℤ, a ^ 2 + b ^ 2 = p ∧ IsPrimaryPair a b := by
  have := Fact.mk hp
  obtain ⟨x, y, hxy⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  -- one of the two is odd and the other even
  have h4 : (x ^ 2 + y ^ 2) % 4 = 1 := by rw [hxy, h]
  have hpar : (x % 2 = 1 ∧ y % 2 = 0) ∨ (x % 2 = 0 ∧ y % 2 = 1) := by
    rw [Nat.add_mod, Nat.pow_mod, Nat.pow_mod y] at h4
    rcases (by omega : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3) with h1 | h1 | h1 | h1 <;>
    rcases (by omega : y % 4 = 0 ∨ y % 4 = 1 ∨ y % 4 = 2 ∨ y % 4 = 3) with h2 | h2 | h2 | h2 <;>
    rw [h1, h2] at h4 <;> first | (exfalso; revert h4; decide) | omega
  -- with `u` odd and `w` even, choose the sign of `u`
  have key : ∀ u w : ℕ, u ^ 2 + w ^ 2 = p → u % 2 = 1 → w % 2 = 0 →
      ∃ a b : ℤ, a ^ 2 + b ^ 2 = p ∧ IsPrimaryPair a b := by
    intro u w huw hu hw
    have hcast : (u : ℤ) ^ 2 + (w : ℤ) ^ 2 = p := by exact_mod_cast huw
    by_cases hprim : IsPrimaryPair (u : ℤ) (w : ℤ)
    · exact ⟨u, w, hcast, hprim⟩
    · refine ⟨-(u : ℤ), w, by rw [neg_sq]; exact hcast, ?_⟩
      unfold IsPrimaryPair at hprim ⊢
      omega
  rcases hpar with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact key x y hxy hx hy
  · exact key y x (by rw [add_comm]; exact hxy) hy hx

/-- **The Hasse bound for the sequence**: `cmPrime p ^ 2 ≤ 4 p`. -/
theorem cmPrime_sq_le {p : ℕ} (hp : p.Prime) : cmPrime p ^ 2 ≤ 4 * p := by
  unfold cmPrime
  split_ifs with h
  · obtain ⟨a, b, hab, hprim⟩ := exists_isPrimaryPair hp h
    rw [cmA_eq hp hab hprim]
    nlinarith [sq_nonneg b]
  · positivity

/-! ## Estimate on the prime powers -/

/-- The power series of the `cmPow` is the inverse of `1 - a T + p T²`. -/
lemma mk_cmPow_mul (p : ℕ) (a : ℤ) :
    (PowerSeries.mk (cmPow p a)) *
      (1 - PowerSeries.C a * PowerSeries.X + PowerSeries.C (p : ℤ) * PowerSeries.X ^ 2) = 1 := by
  have e : (PowerSeries.mk (cmPow p a)) *
      (1 - PowerSeries.C a * PowerSeries.X + PowerSeries.C (p : ℤ) * PowerSeries.X ^ 2) =
      PowerSeries.mk (cmPow p a) - PowerSeries.C a * (PowerSeries.X * PowerSeries.mk (cmPow p a)) +
        PowerSeries.C (p : ℤ) * (PowerSeries.X * (PowerSeries.X * PowerSeries.mk (cmPow p a))) := by
    ring
  rw [e]
  ext n
  rcases n with _ | _ | n
  · simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_X_mul,
      PowerSeries.coeff_mk, PowerSeries.coeff_one, cmPow]
    simp
  · simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_mk, PowerSeries.coeff_one, cmPow]
    simp
  · simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_mk, PowerSeries.coeff_one]
    rw [if_neg (by omega)]
    simp only [cmPow]
    ring

theorem norm_cmPow_le {p : ℕ} {a : ℤ} (h : a ^ 2 ≤ 4 * p) (k : ℕ) :
    ‖((cmPow p a k : ℤ) : ℂ)‖ ≤ (k + 1) * √(p : ℝ) ^ k := by
  obtain ⟨α, β, hα, hβ, hs, hprod⟩ := exists_roots h
  have := norm_coeff_le (f := PowerSeries.mk (cmPow p a)) hα hβ (by
    have hP : (1 - PowerSeries.C α * PowerSeries.X) * (1 - PowerSeries.C β * PowerSeries.X) =
        (1 - PowerSeries.C a * PowerSeries.X + PowerSeries.C (p : ℤ) * PowerSeries.X ^ 2 :
          PowerSeries ℤ).map (Int.castRingHom ℂ) := by
      simp only [map_add, map_sub, map_mul, map_pow, map_one, PowerSeries.map_C, PowerSeries.map_X]
      simp only [eq_intCast, Int.cast_natCast]
      rw [← hs, ← hprod, map_add, map_mul]
      ring
    rw [hP, ← map_mul, mk_cmPow_mul, map_one]) k
  simpa using this

end CMPoints
