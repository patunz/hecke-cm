import Mathlib
import HeckeCM.Euler
import Theorems.Thm_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one

/-!
# The rational prime under a place

For a number field `K`, this file defines the rational prime lying under a finite
place `v` of `K` (`charOf`, `under`), and proves that `under K v = p` is
equivalent to `p ∈ v` (`under_eq_iff`, `liesOver_of_mem`) and that each fibre
of `under` is finite (`finite_fibre`).

The lemmas `charOf`, `under`, `under_eq_iff`, `liesOver_of_mem`, `finite_fibre`
are taken, with minimal changes, from
`P2M/Sol/S_ArtinL_Abelian_hasProd_primes_inv_eval_prod_placesOver.lean` of the
Fermat repository `anthropics/fermats-last-theorem` (Copyright 2026 Anthropic,
PBC, Apache 2.0 licence), where they are private.
-/

open IsDedekindDomain NumberField

namespace CMPoints

variable (K : Type) [Field K] [NumberField K]

/-! ## The rational prime under a place (from `fermats-last-theorem`) -/

noncomputable def charOf (v : HeightOneSpectrum (𝓞 K)) : ℕ := ringChar (𝓞 K ⧸ v.asIdeal)

theorem charOf_prime (v : HeightOneSpectrum (𝓞 K)) : (charOf K v).Prime := by
  haveI := v.isMaximal
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  letI := Ideal.Quotient.field v.asIdeal
  exact CharP.char_is_prime (𝓞 K ⧸ v.asIdeal) _

theorem natCast_mem_iff (v : HeightOneSpectrum (𝓞 K)) (p : ℕ) (hp : p.Prime) :
    ((p : ℕ) : 𝓞 K) ∈ v.asIdeal ↔ charOf K v = p := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast,
    CharP.cast_eq_zero_iff (𝓞 K ⧸ v.asIdeal) (charOf K v)]
  constructor
  · intro h
    exact (Nat.prime_dvd_prime_iff_eq (charOf_prime K v) hp).1 h
  · rintro rfl
    exact dvd_rfl

noncomputable def under (v : HeightOneSpectrum (𝓞 K)) : Nat.Primes :=
  ⟨charOf K v, charOf_prime K v⟩

theorem under_eq_iff (v : HeightOneSpectrum (𝓞 K)) (p : Nat.Primes) :
    under K v = p ↔ ((p : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  rw [natCast_mem_iff K v p p.2, under]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem liesOver_of_mem (v : HeightOneSpectrum (𝓞 K)) (p : ℕ) (hp : p.Prime)
    (hv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) : v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  haveI := v.isMaximal
  haveI := v.isPrime
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero) |>.2
      (Nat.prime_iff_prime_int.1 hp)) (by simpa using hp.ne_zero)
  haveI : (v.asIdeal.under ℤ).IsPrime := Ideal.IsPrime.under ℤ v.asIdeal
  refine ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
  rw [Ideal.span_le, Set.singleton_subset_iff]
  change algebraMap ℤ (𝓞 K) (p : ℤ) ∈ v.asIdeal
  rwa [map_natCast]

theorem finite_fibre (p : Nat.Primes) : Finite {v : HeightOneSpectrum (𝓞 K) // under K v = p} := by
  haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal (Ideal.span_singleton_prime (by exact_mod_cast p.2.ne_zero) |>.2
      (Nat.prime_iff_prime_int.1 p.2)) (by simpa using p.2.ne_zero)
  have hinj : Set.InjOn (fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal)
      ((fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal) ⁻¹'
        ((Ideal.span {((p : ℕ) : ℤ)}).primesOver (𝓞 K))) :=
    fun _ _ _ _ h => HeightOneSpectrum.ext h
  have hfin : {w : HeightOneSpectrum (𝓞 K) | under K w = p}.Finite :=
    ((IsDedekindDomain.primesOver_finite (Ideal.span {((p : ℕ) : ℤ)}) (𝓞 K)).preimage hinj).subset
      fun w hw => by
        have hw' : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal := (under_eq_iff K w p).1 hw
        exact ⟨w.isPrime, liesOver_of_mem K w p p.2 hw'⟩
  exact hfin.to_subtype

end CMPoints
