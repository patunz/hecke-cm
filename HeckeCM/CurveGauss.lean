import HeckeCM.JacobiQuartic
import HeckeCM.CurvePointCount
import HeckeCM.GaussTwo

/-!
# The Frobenius trace of `y² = x³ − x` for `p ≡ 1 (mod 4)`

`exists_primary_frobeniusTrace_zmod`: over `ZMod p` the trace is `2a`, with
`a² + b² = p` and `(a, b)` primary.

Outline: take a character `χ` of order 4 of `(ZMod p)ˣ` with values in
`𝓞 K = ℤ[i]` and its Jacobi sum `J = c + d i`. Then `J · J̄ = p`
(Mathlib), the trace is `−χ(−1)(J + J̄)` (`CurvePointCount`), and `−χ(−1) J` is
primary by the congruence modulo `(1 + i)³` (`JacobiQuartic`).

Unlike the Lean 4.37 version (`cm-pointcount`), the quartic residue symbol is
not needed: any character of order 4 will do.
-/

open NumberField Ideal

namespace CMPoints

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

lemma isPrimitiveRoot_gaussI : IsPrimitiveRoot (gaussI K) 4 :=
  (IsCyclotomicExtension.zeta_spec 4 ℚ K).toInteger_isPrimitiveRoot

/-- Conjugation sends a fourth root of unity to its cube. -/
lemma gaussConj_eq_pow_three {x : 𝓞 K} (hx : x ^ 4 = 1) : gaussConj K x = x ^ 3 := by
  obtain ⟨e, f, rfl⟩ := exists_coords x
  have hu : IsUnit ((e : 𝓞 K) + (f : 𝓞 K) * gaussI K) := IsUnit.of_pow_eq_one hx (by norm_num)
  have h1 := (isUnit_coords_iff e f).1 hu
  have hmul : ((e : 𝓞 K) + (f : 𝓞 K) * gaussI K) *
      gaussConj K ((e : 𝓞 K) + (f : 𝓞 K) * gaussI K) = 1 := by
    rw [gaussConj_coords, coords_mul_conj, h1, Int.cast_one]
  apply mul_left_cancel₀ hu.ne_zero
  rw [hmul, ← pow_succ', hx]

/-- `a + b i ≡ 1 (mod 2 + 2i)` says that `(a, b)` is primary. -/
lemma isPrimaryPair_of_dvd {a b : ℤ} (h : gaussOf K 2 2 ∣ gaussOf K a b - 1) :
    IsPrimaryPair a b := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨m, n, rfl⟩ := exists_coords q
  have hc := coords_unique (K := K) (a := a - 1) (b := b) (c := 2 * m - 2 * n)
    (d := 2 * m + 2 * n) (by
      have h1 : ((a - 1 : ℤ) : 𝓞 K) + (b : 𝓞 K) * gaussI K = gaussOf K a b - 1 := by
        unfold gaussOf
        push_cast
        ring
      rw [h1, hq]
      unfold gaussOf
      push_cast
      linear_combination (2 * (n : 𝓞 K)) * gaussI_sq K)
  unfold IsPrimaryPair
  omega

lemma two_add_two_dvd_of_one_add_pow_three_dvd {y : 𝓞 K} (h : (1 + gaussI K) ^ 3 ∣ y) :
    gaussOf K 2 2 ∣ y := by
  have hs : span {gaussOf K 2 2} = span {(1 + gaussI K) ^ 3} := by
    rw [span_two_add_two, placeTwo_asIdeal, Ideal.span_singleton_pow]
  rw [← Ideal.mem_span_singleton, hs, Ideal.mem_span_singleton]
  exact h

lemma ringHomComp_ne_one {F R R' : Type*} [CommMonoid F] [CommRing R] [CommRing R']
    {ψ : MulChar F R} {f : R →+* R'} (hf : Function.Injective f) (h : ψ ≠ 1) :
    ψ.ringHomComp f ≠ 1 := by
  intro h1
  apply h
  ext a
  apply hf
  have := congrArg (fun φ : MulChar F R' => φ a) h1
  simp only [MulChar.ringHomComp_apply, MulChar.one_apply_coe] at this
  rw [this, MulChar.one_apply_coe, map_one]

/-- **`p ≡ 1 (mod 4)`**: the Frobenius trace of `y² = x³ − x` over `ZMod p`
is `2a`, with `a² + b² = p` and `(a, b)` primary. -/
theorem exists_primary_frobeniusTrace_zmod (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {4} ℚ K] {p : ℕ} [hp : Fact p.Prime] (h : p % 4 = 1) :
    ∃ a b : ℤ, a ^ 2 + b ^ 2 = p ∧ IsPrimaryPair a b ∧
      (CurveX3SubX.curve (ZMod p)).frobeniusTrace = 2 * a := by
  classical
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hdvd : 4 ∣ Fintype.card (ZMod p) - 1 := by rw [hcard]; omega
  obtain ⟨χ, hχ⟩ := MulChar.exists_mulChar_orderOf (ZMod p) hdvd (isPrimitiveRoot_gaussI (K := K))
  have h4 : χ ^ 4 = 1 := hχ ▸ pow_orderOf_eq_one χ
  have hεε : χ (-1) * χ (-1) = 1 := mulChar_apply_neg_one_mul_self χ
  have hcong := one_add_pow_three_dvd_apply_neg_one_mul_jacobiSum_add_one h4 hdvd
    (isPrimitiveRoot_gaussI (K := K))
  -- the inverse character is the conjugate
  have hinv : χ⁻¹ = χ.ringHomComp (gaussConj K : 𝓞 K →+* 𝓞 K) := by
    refine MulChar.ext fun u => ?_
    rw [MulChar.ringHomComp_apply]
    change _ = gaussConj K (χ u)
    rw [gaussConj_eq_pow_three (by rw [← MulChar.pow_apply_coe, h4, MulChar.one_apply_coe]),
      inv_eq_of_mul_eq_one_right (b := χ ^ 3) (by rw [← pow_succ', h4]), MulChar.pow_apply_coe]
  have hJ' : jacobiSum χ⁻¹ χ⁻¹ = gaussConj K (jacobiSum χ χ) := by
    rw [hinv, jacobiSum_ringHomComp]
    rfl
  obtain ⟨c, d, hcd⟩ := exists_coords (jacobiSum χ χ)
  -- the norm: `J · J̄ = p`, passing through `K`
  have hχ1 : χ ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hχ; norm_num at hχ
  have hχ2 : χ * χ ≠ 1 := fun h2 => by
    have := orderOf_dvd_of_pow_eq_one (show χ ^ 2 = 1 by rw [sq]; exact h2)
    rw [hχ] at this
    exact absurd this (by decide)
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := RingOfIntegers.coe_injective
  have hnorm : jacobiSum χ χ * jacobiSum χ⁻¹ χ⁻¹ = (p : 𝓞 K) := by
    have hchar : ringChar K ≠ ringChar (ZMod p) := by
      rw [ringChar.eq_zero, ZMod.ringChar_zmod_n]
      exact hp.out.ne_zero.symm
    have hmul : (χ.ringHomComp (algebraMap (𝓞 K) K)) * (χ.ringHomComp (algebraMap (𝓞 K) K)) =
        (χ * χ).ringHomComp (algebraMap (𝓞 K) K) := by
      ext u
      simp [MulChar.ringHomComp_apply]
    have hinvK : (χ.ringHomComp (algebraMap (𝓞 K) K))⁻¹ =
        (χ⁻¹).ringHomComp (algebraMap (𝓞 K) K) := MulChar.ringHomComp_inv _ _
    have key := jacobiSum_mul_jacobiSum_inv hchar (ringHomComp_ne_one hinj hχ1)
      (ringHomComp_ne_one hinj hχ1) (by rw [hmul]; exact ringHomComp_ne_one hinj hχ2)
    rw [hinvK, jacobiSum_ringHomComp, jacobiSum_ringHomComp, hcard] at key
    apply hinj
    rw [map_mul, map_natCast]
    exact key
  have hn : c ^ 2 + d ^ 2 = p := by
    rw [hJ', hcd, gaussConj_coords, coords_mul_conj] at hnorm
    exact_mod_cast hnorm
  have htr := frobeniusTrace_curve_eq_jacobiSum (F := ZMod p) hχ
  rw [hJ', hcd, gaussConj_coords] at htr
  rw [hcd] at hcong
  rcases mul_self_eq_one_iff.1 hεε with h1 | h1
  · refine ⟨-c, -d, by rw [neg_sq, neg_sq]; exact hn, ?_, ?_⟩
    · apply isPrimaryPair_of_dvd (K := K)
      have : gaussOf K (-c) (-d) - 1 =
          -(χ (-1) * ((c : 𝓞 K) + (d : 𝓞 K) * gaussI K) + 1) := by
        rw [h1]
        unfold gaussOf
        push_cast
        ring
      rw [this, dvd_neg]
      exact two_add_two_dvd_of_one_add_pow_three_dvd hcong
    · apply Int.cast_injective (α := 𝓞 K)
      rw [htr, h1]
      push_cast
      ring
  · refine ⟨c, d, hn, ?_, ?_⟩
    · apply isPrimaryPair_of_dvd (K := K)
      have : gaussOf K c d - 1 =
          -(χ (-1) * ((c : 𝓞 K) + (d : 𝓞 K) * gaussI K) + 1) := by
        rw [h1]
        unfold gaussOf
        ring
      rw [this, dvd_neg]
      exact two_add_two_dvd_of_one_add_pow_three_dvd hcong
    · apply Int.cast_injective (α := 𝓞 K)
      rw [htr, h1]
      push_cast
      ring

end CMPoints
