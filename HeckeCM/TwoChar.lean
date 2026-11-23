import Definitions.Def_DedekindDomain_AdicValuation_InlineSpecific
import HeckeCM.Normalizer
import HeckeCM.GaussTwo

/-!
# The unit attached to a 2-adic unit of `ℚ(i)`

Let `v₂ = placeTwo K` be the place above 2. Every `t` of the completion with
valuation 1 is congruent modulo `(1 + i)³` to exactly one unit of `𝓞 K`
(`exists_unit_valued_sub_le`, `unit_eq_of_valued_sub_le`): we call it
`root2 t`. The map is multiplicative (`root2_mul`), equals `u` on the global
units (`root2_toCompl_unit`) and `1` on primary elements
(`root2_toCompl_primary`).

It is the character of conductor `(1 + i)³`, written without passing through the
quotient ring: existence comes from the density of `𝓞 K` in the integers of the
completion, multiplicativity from uniqueness.
-/

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

namespace CMPoints

variable (K : Type) [Field K] [NumberField K]

/-- The embedding of `𝓞 K` into the completion at `v`. -/
def toCompl (v : HeightOneSpectrum (𝓞 K)) : 𝓞 K →+* v.adicCompletion K :=
  (algebraMap K (v.adicCompletion K)).comp (algebraMap (𝓞 K) K)

variable {K}

theorem valued_toCompl (v : HeightOneSpectrum (𝓞 K)) (z : 𝓞 K) :
    Valued.v (toCompl K v z) = v.intValuation z := by
  unfold toCompl
  rw [RingHom.comp_apply, valued_algebraMap, valuation_of_algebraMap]

theorem valued_toCompl_unit (v : HeightOneSpectrum (𝓞 K)) (u : (𝓞 K)ˣ) :
    Valued.v (toCompl K v u) = 1 := by
  rw [valued_toCompl, intValuation_eq_one_iff]
  intro h
  exact v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h u.isUnit)

variable [IsCyclotomicExtension {4} ℚ K]

theorem valued_toCompl_two_le_iff (z : 𝓞 K) :
    Valued.v (toCompl K (placeTwo K) z) ≤ exp (-3 : ℤ) ↔ gaussOf K 2 2 ∣ z := by
  rw [valued_toCompl, show (-3 : ℤ) = -((3 : ℕ) : ℤ) by norm_num, intValuation_le_pow_iff_mem,
    ← span_two_add_two, Ideal.mem_span_singleton]

theorem valued_toCompl_two_lt_one_iff (z : 𝓞 K) :
    Valued.v (toCompl K (placeTwo K) z) < 1 ↔ (1 + gaussI K) ∣ z := by
  rw [valued_toCompl, intValuation_lt_one_iff_mem, placeTwo_asIdeal, Ideal.mem_span_singleton]

lemma exp_neg_three_lt_one : (exp (-3 : ℤ) : ℤᵐ⁰) < 1 := by
  rw [← exp_zero, exp_lt_exp]
  norm_num

/-- **Existence**: every 2-adic unit is close to a unit of `𝓞 K`. -/
theorem exists_unit_valued_sub_le (t : (placeTwo K).adicCompletion K) (ht : Valued.v t = 1) :
    ∃ u : (𝓞 K)ˣ, Valued.v (t - toCompl K (placeTwo K) u) ≤ exp (-3 : ℤ) := by
  have hmem : t ∈ (placeTwo K).adicCompletionIntegers K :=
    (mem_adicCompletionIntegers (𝓞 K) K _).2 ht.le
  obtain ⟨a, ha⟩ := exists_adicValued_sub_lt_of_adicCompletionInteger K (placeTwo K) ⟨t, hmem⟩
    (Units.mk0 (exp (-3 : ℤ)) exp_ne_zero)
  have ha' : Valued.v (toCompl K (placeTwo K) a - t) < exp (-3 : ℤ) := ha
  have hlt1 : Valued.v (toCompl K (placeTwo K) a - t) < 1 := lt_trans ha' exp_neg_three_lt_one
  have hva : Valued.v (toCompl K (placeTwo K) a) = 1 := by
    have := Valuation.map_add_eq_of_lt_left (v := Valued.v) (x := t)
      (y := toCompl K (placeTwo K) a - t) (by rw [ht]; exact hlt1)
    rwa [add_sub_cancel, ht] at this
  have hndvd : ¬ (1 + gaussI K) ∣ a := fun h => by
    have := (valued_toCompl_two_lt_one_iff a).2 h
    rw [hva] at this
    exact lt_irrefl _ this
  obtain ⟨u, hu⟩ := exists_unit_dvd_sub a hndvd
  refine ⟨u, ?_⟩
  have h1 : Valued.v (toCompl K (placeTwo K) (a - u)) ≤ exp (-3 : ℤ) :=
    (valued_toCompl_two_le_iff _).2 hu
  have h2 : t - toCompl K (placeTwo K) u =
      (t - toCompl K (placeTwo K) a) + toCompl K (placeTwo K) (a - u) := by
    rw [map_sub]
    ring
  rw [h2]
  refine Valuation.map_add_le _ ?_ h1
  rw [Valuation.map_sub_swap]
  exact ha'.le

/-- **Uniqueness.** -/
theorem unit_eq_of_valued_sub_le {t : (placeTwo K).adicCompletion K} {u u' : (𝓞 K)ˣ}
    (h : Valued.v (t - toCompl K (placeTwo K) u) ≤ exp (-3 : ℤ))
    (h' : Valued.v (t - toCompl K (placeTwo K) u') ≤ exp (-3 : ℤ)) : u = u' := by
  refine unit_eq_of_dvd_sub u u' ((valued_toCompl_two_le_iff _).1 ?_)
  rw [map_sub, show toCompl K (placeTwo K) u - toCompl K (placeTwo K) u' =
    (t - toCompl K (placeTwo K) u') - (t - toCompl K (placeTwo K) u) by ring]
  exact Valuation.map_sub_le _ h' h

theorem valued_eq_one_of_sub_le {t : (placeTwo K).adicCompletion K} {u : (𝓞 K)ˣ}
    (h : Valued.v (t - toCompl K (placeTwo K) u) ≤ exp (-3 : ℤ)) : Valued.v t = 1 := by
  have := Valuation.map_add_eq_of_lt_left (v := Valued.v) (x := toCompl K (placeTwo K) u)
    (y := t - toCompl K (placeTwo K) u)
    (by rw [valued_toCompl_unit]; exact lt_of_le_of_lt h exp_neg_three_lt_one)
  rwa [add_sub_cancel, valued_toCompl_unit] at this

variable (K) in
open Classical in
/-- The unit congruent to `t` modulo `(1 + i)³`; `1` if `t` is not a
unit. -/
def root2 (t : (placeTwo K).adicCompletion K) : (𝓞 K)ˣ :=
  if h : Valued.v t = 1 then Classical.choose (exists_unit_valued_sub_le t h) else 1

theorem root2_spec {t : (placeTwo K).adicCompletion K} (h : Valued.v t = 1) :
    Valued.v (t - toCompl K (placeTwo K) (root2 K t)) ≤ exp (-3 : ℤ) := by
  unfold root2
  rw [dif_pos h]
  exact Classical.choose_spec (exists_unit_valued_sub_le t h)

theorem root2_eq {t : (placeTwo K).adicCompletion K} {u : (𝓞 K)ˣ}
    (h : Valued.v (t - toCompl K (placeTwo K) u) ≤ exp (-3 : ℤ)) : root2 K t = u :=
  unit_eq_of_valued_sub_le (root2_spec (valued_eq_one_of_sub_le h)) h

theorem root2_mul {t s : (placeTwo K).adicCompletion K} (ht : Valued.v t = 1)
    (hs : Valued.v s = 1) : root2 K (t * s) = root2 K t * root2 K s := by
  refine root2_eq ?_
  have h : t * s - toCompl K (placeTwo K) ((root2 K t * root2 K s : (𝓞 K)ˣ) : 𝓞 K) =
      t * (s - toCompl K (placeTwo K) (root2 K s)) +
        toCompl K (placeTwo K) (root2 K s) * (t - toCompl K (placeTwo K) (root2 K t)) := by
    rw [Units.val_mul, map_mul]
    ring
  rw [h]
  refine Valuation.map_add_le _ ?_ ?_
  · rw [map_mul, ht, one_mul]
    exact root2_spec hs
  · rw [map_mul, valued_toCompl_unit, one_mul]
    exact root2_spec ht

theorem root2_toCompl_unit (u : (𝓞 K)ˣ) : root2 K (toCompl K (placeTwo K) u) = u :=
  root2_eq (by rw [sub_self, map_zero]; exact zero_le)

theorem root2_one : root2 K 1 = 1 := by
  have := root2_toCompl_unit (K := K) 1
  rwa [Units.val_one, map_one] at this

theorem root2_of_sub_one_le {t : (placeTwo K).adicCompletion K}
    (h : Valued.v (t - 1) ≤ exp (-3 : ℤ)) : root2 K t = 1 :=
  root2_eq (by rwa [Units.val_one, map_one])

theorem root2_toCompl_primary {c d : ℤ} (h : IsPrimaryPair c d) :
    root2 K (toCompl K (placeTwo K) (gaussOf K c d)) = 1 :=
  root2_of_sub_one_le (by
    rw [← map_one (toCompl K (placeTwo K)), ← map_sub]
    exact (valued_toCompl_two_le_iff _).2 (two_add_two_dvd_of_isPrimaryPair h))

end CMPoints
