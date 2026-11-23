import Mathlib

/-!
# The ring of integers of `ℚ(i)` as the Gaussian integers

Let `K` satisfy `IsCyclotomicExtension {4} ℚ K`. Once a primitive fourth root of
unity `gaussI K : 𝓞 K` is fixed, the homomorphism `ℤ[i] → 𝓞 K` sending `i` to it is
an isomorphism (`gaussEquiv`). It follows that:

* `𝓞 K` is a principal ideal ring (`isPrincipalIdealRing_gauss`);
* every element can be written uniquely as `a + b i` (`exists_coords`,
  `coords_unique`);
* the conjugation `gaussConj` and the norm: `absNorm (span {a + b i}) = a² + b²`
  (`absNorm_span_coords`);
* `a + b i` is a unit if and only if `a² + b² = 1` (`isUnit_coords_iff`).
-/

open NumberField

namespace CMPoints

variable (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

/-- The chosen primitive fourth root of unity in `𝓞 K`. -/
noncomputable def gaussI : 𝓞 K := (IsCyclotomicExtension.zeta_spec 4 ℚ K).toInteger

lemma gaussI_sq : gaussI K ^ 2 = -1 := by
  have h := (IsCyclotomicExtension.zeta_spec 4 ℚ K).toInteger_isPrimitiveRoot
  have h2 : IsPrimitiveRoot (gaussI K ^ 2) 2 :=
    IsPrimitiveRoot.pow (by norm_num) h (by norm_num : 4 = 2 * 2)
  exact h2.eq_neg_one_of_two_right

/-- The homomorphism `ℤ[i] → 𝓞 K`. -/
noncomputable def gaussHom : GaussianInt →+* 𝓞 K :=
  Zsqrtd.lift ⟨gaussI K, by rw [← sq, gaussI_sq]; norm_num⟩

lemma gaussHom_apply (z : GaussianInt) :
    gaussHom K z = (z.re : 𝓞 K) + (z.im : 𝓞 K) * gaussI K := by
  simp [gaussHom, Zsqrtd.lift]

lemma gaussHom_mk (a b : ℤ) : gaussHom K ⟨a, b⟩ = (a : 𝓞 K) + (b : 𝓞 K) * gaussI K :=
  gaussHom_apply K ⟨a, b⟩

lemma gaussHom_injective : Function.Injective (gaussHom K) :=
  Zsqrtd.lift_injective _ fun n h => by nlinarith [sq_nonneg n]

lemma gaussHom_surjective : Function.Surjective (gaussHom K) := by
  intro x
  have hx : x ∈ Algebra.adjoin ℤ {gaussI K} := by
    have := IsCyclotomicExtension.Rat.adjoin_singleton_eq_top
      (IsCyclotomicExtension.zeta_spec 4 ℚ K)
    unfold gaussI
    rw [this]
    exact Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    exact ⟨⟨0, 1⟩, by rw [gaussHom_mk, hy]; simp⟩
  | algebraMap r => exact ⟨(r : GaussianInt), by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨u, rfl⟩ := hy
    obtain ⟨v, rfl⟩ := hz
    exact ⟨u + v, map_add _ _ _⟩
  | mul y z _ _ hy hz =>
    obtain ⟨u, rfl⟩ := hy
    obtain ⟨v, rfl⟩ := hz
    exact ⟨u * v, map_mul _ _ _⟩

/-- `ℤ[i] ≃ 𝓞 K`. -/
noncomputable def gaussEquiv : GaussianInt ≃+* 𝓞 K :=
  RingEquiv.ofBijective (gaussHom K) ⟨gaussHom_injective K, gaussHom_surjective K⟩

/-- **`𝓞 K` is a principal ideal ring.** -/
theorem isPrincipalIdealRing_gauss : IsPrincipalIdealRing (𝓞 K) :=
  IsPrincipalIdealRing.of_surjective (gaussHom K) (gaussHom_surjective K)

variable {K}

theorem exists_coords (x : 𝓞 K) : ∃ a b : ℤ, x = (a : 𝓞 K) + (b : 𝓞 K) * gaussI K := by
  obtain ⟨z, rfl⟩ := gaussHom_surjective K x
  exact ⟨z.re, z.im, gaussHom_apply K z⟩

theorem coords_unique {a b c d : ℤ}
    (h : (a : 𝓞 K) + (b : 𝓞 K) * gaussI K = (c : 𝓞 K) + (d : 𝓞 K) * gaussI K) :
    a = c ∧ b = d := by
  rw [← gaussHom_mk, ← gaussHom_mk] at h
  have := gaussHom_injective K h
  exact ⟨congrArg Zsqrtd.re this, congrArg Zsqrtd.im this⟩

variable (K) in
/-- The conjugation `a + b i ↦ a − b i`. -/
noncomputable def gaussConj : 𝓞 K ≃+* 𝓞 K :=
  ((gaussEquiv K).symm.trans (starRingAut (R := GaussianInt))).trans (gaussEquiv K)

lemma gaussConj_coords (a b : ℤ) :
    gaussConj K ((a : 𝓞 K) + (b : 𝓞 K) * gaussI K) = (a : 𝓞 K) - (b : 𝓞 K) * gaussI K := by
  have h1 : (gaussEquiv K).symm ((a : 𝓞 K) + (b : 𝓞 K) * gaussI K) = ⟨a, b⟩ := by
    rw [RingEquiv.symm_apply_eq]
    exact (gaussHom_mk K a b).symm
  have h2 : gaussEquiv K (star (⟨a, b⟩ : GaussianInt)) = (a : 𝓞 K) - (b : 𝓞 K) * gaussI K := by
    change gaussHom K (star (⟨a, b⟩ : GaussianInt)) = _
    rw [gaussHom_apply]
    simp [sub_eq_add_neg]
  simp only [gaussConj, RingEquiv.trans_apply, h1]
  exact h2

lemma coords_mul_conj (a b : ℤ) :
    ((a : 𝓞 K) + (b : 𝓞 K) * gaussI K) * ((a : 𝓞 K) - (b : 𝓞 K) * gaussI K) =
      ((a ^ 2 + b ^ 2 : ℤ) : 𝓞 K) := by
  push_cast
  linear_combination (-(b : 𝓞 K) ^ 2) * gaussI_sq K

lemma finrank_int_gauss : Module.finrank ℤ (𝓞 K) = 2 := by
  rw [RingOfIntegers.rank,
    IsCyclotomicExtension.finrank (n := 4) K (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
  decide

lemma absNorm_span_intCast (n : ℤ) : Ideal.absNorm (Ideal.span {(n : 𝓞 K)}) = n.natAbs ^ 2 := by
  rw [Ideal.absNorm_span_singleton, ← eq_intCast (algebraMap ℤ (𝓞 K)) n, Algebra.norm_algebraMap,
    finrank_int_gauss, Int.natAbs_pow]

lemma absNorm_map_gaussConj (I : Ideal (𝓞 K)) :
    Ideal.absNorm (I.map (gaussConj K)) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I (I.map (gaussConj K)) (gaussConj K) rfl).toEquiv).symm

/-- **The norm of `a + b i` is `a² + b²`.** -/
theorem absNorm_span_coords (a b : ℤ) :
    Ideal.absNorm (Ideal.span {(a : 𝓞 K) + (b : 𝓞 K) * gaussI K}) = (a ^ 2 + b ^ 2).natAbs := by
  have hmul : Ideal.span {(a : 𝓞 K) + (b : 𝓞 K) * gaussI K} *
      (Ideal.span {(a : 𝓞 K) + (b : 𝓞 K) * gaussI K}).map (gaussConj K) =
      Ideal.span {((a ^ 2 + b ^ 2 : ℤ) : 𝓞 K)} := by
    rw [Ideal.map_span, Set.image_singleton, gaussConj_coords, Ideal.span_singleton_mul_span_singleton,
      coords_mul_conj]
  have h := congrArg Ideal.absNorm hmul
  rw [map_mul, absNorm_map_gaussConj, absNorm_span_intCast, ← sq] at h
  exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) h

/-- `a + b i` is a unit if and only if `a² + b² = 1`. -/
theorem isUnit_coords_iff (a b : ℤ) :
    IsUnit ((a : 𝓞 K) + (b : 𝓞 K) * gaussI K) ↔ a ^ 2 + b ^ 2 = 1 := by
  rw [← Ideal.span_singleton_eq_top, ← Ideal.absNorm_eq_one_iff, absNorm_span_coords]
  have : 0 ≤ a ^ 2 + b ^ 2 := by positivity
  omega

end CMPoints
