import HeckeCM.GaussTwo
import HeckeCM.Normalizer
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_AdelicTraceFin

/-!
# The local additive character at a global element

`psiLocal_algebraMap_of_integral_away`: let `y ∈ K` be integral at every place
other than `v`. Then the standard additive character at `v` equals

`ψ_v(y) = exp(−2πi · Tr_{K/ℚ}(y))`.

One writes the principal finite adèle of `y` as the sum of the adèle concentrated
at `v` and an integral adèle; the adelic trace of the latter is integral, so the
character takes the value 1 on it, and on the principal one it equals
`exp(−2πi · Tr y)`.

For `K = ℚ(i)`: `trace_gaussOf`, the trace of `a + b i` is `2a`.
-/

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField.StandardAddChar NumberField.AdelicTrace

namespace CMPoints

variable (K : Type) [Field K] [NumberField K]

open scoped Classical in
/-- **The local additive character at a global element integral away from `v`.** -/
theorem psiLocal_algebraMap_of_integral_away (v : HeightOneSpectrum (𝓞 K)) (y : K)
    (hy : ∀ w : HeightOneSpectrum (𝓞 K), w ≠ v → w.valuation K y ≤ 1) :
    psiLocal K v (algebraMap K (v.adicCompletion K) y) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (((Algebra.trace ℚ K y : ℚ)) : ℂ)) := by
  -- the integral part of the principal adèle of `y`
  let r : Π w : HeightOneSpectrum (𝓞 K), w.adicCompletionIntegers K := fun w =>
    if h : w = v then 0 else
      ⟨algebraMap K (w.adicCompletion K) y, (mem_adicCompletionIntegers (𝓞 K) K w).2 (by
        rw [valued_algebraMap]
        exact hy w h)⟩
  set S : FiniteAdeleRing (𝓞 K) K :=
    RestrictedProduct.structureMap (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
      (fun w => (w.adicCompletionIntegers K : Set (w.adicCompletion K))) Filter.cofinite r with hS
  have hdec : algebraMap K (FiniteAdeleRing (𝓞 K) K) y =
      finAdeleSingleAt K v (algebraMap K (v.adicCompletion K) y) + S := by
    refine RestrictedProduct.ext _ _ fun w => ?_
    show (algebraMap K (FiniteAdeleRing (𝓞 K) K) y) w =
      finAdeleSingleAt K v (algebraMap K (v.adicCompletion K) y) w + (r w : w.adicCompletion K)
    by_cases h : w = v
    · subst h
      rw [finAdeleSingleAt_apply_self]
      simp only [r, dif_pos]
      rw [ZeroMemClass.coe_zero, add_zero]
      rfl
    · rw [finAdeleSingleAt_apply_of_ne K v _ h, zero_add]
      simp only [r, dif_neg h]
      rfl
  have h1 := traceFinHom_algebraMap K y
  rw [hdec, map_add, hS, traceFinHom_structureMap] at h1
  have hint : psiFin (RestrictedProduct.structureMap
      (fun w : HeightOneSpectrum (𝓞 ℚ) => w.adicCompletion ℚ)
      (fun w => (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ))) Filter.cofinite
      (traceInt K r)) = 1 :=
    psiFin_eq_one_of_forall_mem _ fun w => (traceInt K r w).2
  have hpsi : psiLocal K v (algebraMap K (v.adicCompletion K) y) =
      psiFin (traceFinHom K (finAdeleSingleAt K v (algebraMap K (v.adicCompletion K) y))) := by
    rw [psiLocal_apply]
    show psiQ ((adelicTraceData K).adelicTrace (0, _)) = _
    rw [AdelicTraceData.adelicTrace_apply, psiQ_apply, map_zero, AddChar.map_zero_eq_one, one_mul]
    rfl
  rw [hpsi, ← psiFin_algebraMap, ← h1, AddChar.map_add_eq_mul, hint, mul_one]

variable {K} [IsCyclotomicExtension {4} ℚ K]

/-- The trace of `i` over `ℚ` is 0. -/
lemma trace_gaussI : Algebra.trace ℚ K (algebraMap (𝓞 K) K (gaussI K)) = 0 := by
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K
  have hgen : (IsPrimitiveRoot.powerBasis ℚ hζ).gen = algebraMap (𝓞 K) K (gaussI K) := by
    rw [IsPrimitiveRoot.powerBasis_gen]
    rfl
  rw [← hgen, PowerBasis.trace_gen_eq_nextCoeff_minpoly, IsPrimitiveRoot.powerBasis_gen,
    ← Polynomial.cyclotomic_eq_minpoly_rat hζ (by norm_num)]
  have h4 : Polynomial.cyclotomic 4 ℚ = Polynomial.X ^ 2 + 1 := by
    have : (4 : ℕ) = 2 ^ (1 + 1) := by norm_num
    rw [this, Polynomial.cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
    simp [Finset.sum_range_succ, add_comm]
  rw [h4]
  have : (Polynomial.X ^ 2 + 1 : Polynomial ℚ).nextCoeff = 0 := by
    rw [Polynomial.nextCoeff_of_natDegree_pos (by
      rw [show (Polynomial.X ^ 2 + 1 : Polynomial ℚ) = Polynomial.X ^ 2 + Polynomial.C 1 by simp,
        Polynomial.natDegree_X_pow_add_C]
      norm_num)]
    rw [show (Polynomial.X ^ 2 + 1 : Polynomial ℚ) = Polynomial.X ^ 2 + Polynomial.C 1 by simp,
      Polynomial.natDegree_X_pow_add_C]
    simp [Polynomial.coeff_X_pow, Polynomial.coeff_one]
  rw [this, neg_zero]

/-- **The trace of `a + b i` is `2a`.** -/
theorem trace_gaussOf (a b : ℤ) :
    Algebra.trace ℚ K (algebraMap (𝓞 K) K (gaussOf K a b)) = 2 * a := by
  have h2 : Module.finrank ℚ K = 2 := by
    rw [IsCyclotomicExtension.finrank (n := 4) K (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
    decide
  unfold gaussOf
  rw [map_add, map_mul, map_intCast, map_intCast, map_add]
  have e1 : Algebra.trace ℚ K ((a : ℤ) : K) = 2 * a := by
    have : ((a : ℤ) : K) = algebraMap ℚ K (a : ℚ) := by simp
    rw [this, Algebra.trace_algebraMap, h2]
    simp
  have e2 : Algebra.trace ℚ K (((b : ℤ) : K) * algebraMap (𝓞 K) K (gaussI K)) = 0 := by
    have : ((b : ℤ) : K) * algebraMap (𝓞 K) K (gaussI K) =
        (b : ℚ) • algebraMap (𝓞 K) K (gaussI K) := by
      rw [Algebra.smul_def]
      simp
    rw [this, map_smul, trace_gaussI, smul_zero]
  rw [e1, e2, add_zero]

end CMPoints
