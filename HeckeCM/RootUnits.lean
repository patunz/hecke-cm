import HeckeCM.RootCond

/-!
# The four units and the data of the Gauss sum at 2

* `unitPow k = i^k` for `k : Fin 4`, with explicit coordinates; every unit of
  `𝓞 K` is one of these, and they are distinct;
* `z₂ = (1 + i)/8` in the completion at 2, of valuation `exp 5`;
* `psi_z₂_mul_unit`: `ψ(z₂ · i^k) = exp(−2πi · (a_k − b_k)/4)`.
-/

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open NumberField.AdelicLevel AutomorphicForm NumberField.TateGlobal
open NumberField.StandardAddChar LanglandsTunnell.TateLocal
open scoped Classical

namespace CMPoints

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

local notation "𝔸" => AdeleRing (𝓞 K) K
local notation "K₂" => HeightOneSpectrum.adicCompletion K (placeTwo K)

/-! ## The four units -/

/-- Real part of `i^k`. -/
def uA : Fin 4 → ℤ := ![1, 0, -1, 0]

/-- Imaginary part of `i^k`. -/
def uB : Fin 4 → ℤ := ![0, 1, 0, -1]

variable (K) in
/-- The unit `i^k`. -/
def unitPow (k : Fin 4) : (𝓞 K)ˣ := gaussIUnit K ^ (k : ℕ)

lemma gaussIUnit_val : ((gaussIUnit K : (𝓞 K)ˣ) : 𝓞 K) = gaussI K := IsUnit.unit_spec _

lemma unitPow_val (k : Fin 4) : ((unitPow K k : (𝓞 K)ˣ) : 𝓞 K) = gaussOf K (uA k) (uB k) := by
  have hI := gaussI_sq K
  unfold unitPow gaussOf
  rw [Units.val_pow_eq_pow_val, gaussIUnit_val]
  fin_cases k
  · simp [uA, uB]
  · simp [uA, uB]
  · simp [uA, uB]
    exact hI
  · simp [uA, uB]
    linear_combination gaussI K * hI

lemma exists_unitPow (u : (𝓞 K)ˣ) : ∃ k : Fin 4, u = unitPow K k := by
  obtain ⟨e, f, hef⟩ := exists_coords (u : 𝓞 K)
  have h1 : e ^ 2 + f ^ 2 = 1 := (isUnit_coords_iff e f).1 (hef ▸ u.isUnit)
  have b1 : e ≤ 1 := by nlinarith [sq_nonneg f]
  have b2 : -1 ≤ e := by nlinarith [sq_nonneg f]
  have b3 : f ≤ 1 := by nlinarith [sq_nonneg e]
  have b4 : -1 ≤ f := by nlinarith [sq_nonneg e]
  have key : ∃ k : Fin 4, e = uA k ∧ f = uB k := by
    clear hef
    interval_cases e <;> interval_cases f <;> first
      | (exfalso; omega)
      | exact ⟨0, by decide⟩
      | exact ⟨1, by decide⟩
      | exact ⟨2, by decide⟩
      | exact ⟨3, by decide⟩
  obtain ⟨k, rfl, rfl⟩ := key
  exact ⟨k, Units.ext (by rw [hef, unitPow_val])⟩

lemma unitPow_injective : Function.Injective (unitPow K) := by
  intro k l h
  have h' := congrArg (fun u : (𝓞 K)ˣ => (u : 𝓞 K)) h
  simp only [unitPow_val] at h'
  obtain ⟨hA, hB⟩ := coords_unique (K := K) h'
  revert hA hB
  fin_cases k <;> fin_cases l <;> simp [uA, uB]

/-! ## The element `z₂ = (1 + i)/8` -/

variable (K) in
/-- `(1 + i)/8` in `K`. -/
def zK : K := algebraMap (𝓞 K) K (gaussOf K 1 1) / 2 ^ 3

variable (K) in
/-- `(1 + i)/8` in the completion at 2. -/
def z₂ : K₂ := algebraMap K K₂ (zK K)

lemma gaussOf_one_one : gaussOf K 1 1 = 1 + gaussI K := by simp [gaussOf]

lemma valued_z₂ : Valued.v (z₂ K) = exp (5 : ℤ) := by
  unfold z₂ zK
  rw [valued_half, gaussOf_one_one, valued_toCompl_one_add_gaussI, ← exp_add]
  norm_num

lemma z₂_ne_zero : z₂ K ≠ 0 := fun h => by
  have := valued_z₂ (K := K)
  rw [h, map_zero] at this
  exact exp_ne_zero this.symm

/-- `z₂ · i^k = ((a_k − b_k) + (a_k + b_k) i)/8`. -/
lemma z₂_mul_unitPow (k : Fin 4) :
    z₂ K * toCompl K (placeTwo K) (unitPow K k) =
      algebraMap K K₂ (algebraMap (𝓞 K) K (gaussOf K (uA k - uB k) (uA k + uB k)) / 2 ^ 3) := by
  have e : gaussOf K (uA k - uB k) (uA k + uB k) = gaussOf K 1 1 * (unitPow K k : 𝓞 K) := by
    rw [unitPow_val]
    unfold gaussOf
    push_cast
    linear_combination (-(uB k : 𝓞 K)) * gaussI_sq K
  unfold z₂ zK toCompl
  rw [e, map_mul, RingHom.comp_apply, ← map_mul]
  congr 1
  ring

/-- **The additive character at `z₂ · i^k`.** -/
theorem psi_z₂_mul_unit (k : Fin 4) :
    psiLocal K (placeTwo K) (z₂ K * toCompl K (placeTwo K) (unitPow K k)) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((((uA k - uB k : ℤ)) : ℂ) / 4)) := by
  rw [z₂_mul_unitPow, psi_half]
  congr 1
  push_cast
  ring

end CMPoints
