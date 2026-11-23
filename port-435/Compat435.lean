import Mathlib

/-!
Compatibilità per il porting a Lean 4.35 / Mathlib v4.35.0.

In Mathlib `WithZeroMulInt.toNNReal_neg_apply` ora enuncia il risultato con
`WithZero.log`; qui c'è l'enunciato precedente, usato dal codice portato.
-/

open NNReal WithZero

namespace WithZeroMulInt

theorem toNNReal_neg_apply_old {e : ℝ≥0} (he : e ≠ 0) {x : ℤᵐ⁰} (hx : x ≠ 0) :
    toNNReal he x = e ^ (WithZero.unzero hx).toAdd := by
  rw [toNNReal_neg_apply he hx, WithZero.toAdd_unzero_eq_log hx]

end WithZeroMulInt
