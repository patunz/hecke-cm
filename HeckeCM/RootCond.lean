import HeckeCM.RootPsi
import HeckeCM.FunctionalEqChar
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Theorems.Thm_LanglandsTunnell_TateLocal_psiLocal_eq_one_of_mem_integers

/-!
# At the place above 2: level of the additive character and conductor of `cmChar`

Let `v₂` be the place of `K = ℚ(i)` above 2.

* `psi_half`: `ψ_{v₂}((a + b i) / 2^k) = exp(−2πi · 2a / 2^k)`;
* `addCharLevel_psiLocal_placeTwo`: the level of the standard additive character
  at `v₂` is 2;
* `cmChar_locIdele_two_unit`: on a local unit `t` at `v₂`, `cmChar` equals
  `σ(root2 t)`;
* `hasConductorExponentAt_cmChar_two`: the local component of `cmChar` at `v₂`
  has conductor exponent 3.
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

/-! ## Valuations at the place above 2 -/

lemma one_add_gaussI_ne_zero : (1 + gaussI K : 𝓞 K) ≠ 0 := by
  intro h
  exact span_one_add_gaussI_ne_bot (K := K) (by rw [h, Ideal.span_singleton_eq_bot.2 rfl])

lemma valued_toCompl_one_add_gaussI :
    Valued.v (toCompl K (placeTwo K) (1 + gaussI K)) = exp (-1 : ℤ) := by
  rw [valued_toCompl]
  exact intValuation_singleton (placeTwo K) one_add_gaussI_ne_zero placeTwo_asIdeal

lemma two_eq : (2 : 𝓞 K) = -gaussI K * (1 + gaussI K) ^ 2 := by
  linear_combination (gaussI K + 2) * gaussI_sq K

lemma valued_toCompl_two : Valued.v (toCompl K (placeTwo K) (2 : 𝓞 K)) = exp (-2 : ℤ) := by
  rw [two_eq, map_mul, map_pow, map_mul, map_pow, map_neg, Valuation.map_neg,
    valued_toCompl_one_add_gaussI, sq, ← exp_add]
  have : Valued.v (toCompl K (placeTwo K) (gaussI K)) = 1 := valued_toCompl_unit _ (gaussIUnit K)
  rw [this, one_mul]
  norm_num

lemma valued_two : Valued.v (2 : K₂) = exp (-2 : ℤ) := by
  have : (2 : K₂) = toCompl K (placeTwo K) (2 : 𝓞 K) := (map_ofNat _ 2).symm
  rw [this, valued_toCompl_two]

lemma exp_neg_two_pow (k : ℕ) : (exp (-2 : ℤ) : ℤᵐ⁰) ^ k = exp (-(2 * (k : ℤ))) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, ← exp_add]
    congr 1
    push_cast
    ring

/-- The `v₂`-valuation of `z / 2^k`. -/
lemma valued_half (z : 𝓞 K) (k : ℕ) :
    Valued.v (algebraMap K K₂ (algebraMap (𝓞 K) K z / 2 ^ k)) =
      Valued.v (toCompl K (placeTwo K) z) * exp (2 * (k : ℤ)) := by
  rw [map_div₀, map_pow, map_ofNat, map_div₀, map_pow, valued_two, exp_neg_two_pow,
    div_eq_mul_inv, ← exp_neg, neg_neg]
  rfl

/-- `z / 2^k` is integral at every place other than `v₂`. -/
lemma valuation_half_le (z : 𝓞 K) (k : ℕ) {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ placeTwo K) :
    w.valuation K (algebraMap (𝓞 K) K z / 2 ^ k) ≤ 1 := by
  have h2 : w.valuation K (2 : K) = 1 := by
    have : (2 : K) = algebraMap (𝓞 K) K 2 := (map_ofNat _ 2).symm
    rw [this, valuation_of_algebraMap, intValuation_eq_one_iff]
    exact fun h => hw (eq_placeTwo_of_two_mem h)
  rw [map_div₀, map_pow, h2, one_pow, div_one]
  exact valuation_le_one w z

lemma trace_half (a b : ℤ) (k : ℕ) :
    Algebra.trace ℚ K (algebraMap (𝓞 K) K (gaussOf K a b) / 2 ^ k) = 2 * a / 2 ^ k := by
  have : algebraMap (𝓞 K) K (gaussOf K a b) / 2 ^ k =
      ((1 / 2 ^ k : ℚ)) • algebraMap (𝓞 K) K (gaussOf K a b) := by
    rw [Algebra.smul_def]
    simp
    ring
  rw [this, map_smul, trace_gaussOf, smul_eq_mul]
  ring

/-- **The additive character at `v₂` on `(a + b i) / 2^k`.** -/
theorem psi_half (a b : ℤ) (k : ℕ) :
    psiLocal K (placeTwo K) (algebraMap K K₂ (algebraMap (𝓞 K) K (gaussOf K a b) / 2 ^ k)) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (((2 * a / 2 ^ k : ℚ)) : ℂ)) := by
  rw [psiLocal_algebraMap_of_integral_away K (placeTwo K) _
    (fun w hw => valuation_half_le _ k hw), trace_half]

/-! ## The level is 2 -/

lemma psiLocal_two_eq_one_of_valued_le {x : K₂} (hx : Valued.v x ≤ exp (2 : ℤ)) :
    psiLocal K (placeTwo K) x = 1 := by
  have h2ne : (2 : K₂) ≠ 0 := fun h => by
    have := valued_two (K := K)
    rw [h, map_zero] at this
    exact exp_ne_zero this.symm
  have hmem : x * 2 ∈ (placeTwo K).adicCompletionIntegers K := by
    rw [mem_adicCompletionIntegers, map_mul, valued_two]
    calc Valued.v x * exp (-2 : ℤ) ≤ exp (2 : ℤ) * exp (-2 : ℤ) := mul_le_mul_left hx _
      _ = 1 := by rw [← exp_add]; norm_num
  obtain ⟨a, ha⟩ := exists_adicValued_sub_lt_of_adicCompletionInteger K (placeTwo K)
    ⟨x * 2, hmem⟩ (Units.mk0 (exp (-2 : ℤ)) exp_ne_zero)
  have ha' : Valued.v (toCompl K (placeTwo K) a - x * 2) < exp (-2 : ℤ) := ha
  have hx' : x = (x * 2 - toCompl K (placeTwo K) a) / 2 + toCompl K (placeTwo K) a / 2 := by
    field_simp
    ring
  rw [hx', AddChar.map_add_eq_mul]
  have h1 : psiLocal K (placeTwo K) ((x * 2 - toCompl K (placeTwo K) a) / 2) = 1 := by
    refine psiLocal_eq_one_of_mem_integers K (placeTwo K) _ ?_
    rw [mem_adicCompletionIntegers, map_div₀, valued_two, Valuation.map_sub_swap]
    rw [div_le_iff₀ (by simp), one_mul]
    exact ha'.le
  obtain ⟨c, d, rfl⟩ := exists_coords a
  have h2 : psiLocal K (placeTwo K) (toCompl K (placeTwo K) (gaussOf K c d) / 2) = 1 := by
    have e : toCompl K (placeTwo K) (gaussOf K c d) / 2 =
        algebraMap K K₂ (algebraMap (𝓞 K) K (gaussOf K c d) / 2 ^ 1) := by
      rw [pow_one, map_div₀, map_ofNat]
      rfl
    rw [e, psi_half, Complex.exp_eq_one_iff]
    exact ⟨-c, by push_cast; ring⟩
  rw [h1, h2, mul_one]

lemma exists_psiLocal_two_ne_one :
    ∃ x : K₂, Valued.v x ≤ exp (3 : ℤ) ∧ psiLocal K (placeTwo K) x ≠ 1 := by
  refine ⟨algebraMap K K₂ (algebraMap (𝓞 K) K (gaussOf K 1 1) / 2 ^ 2), ?_, ?_⟩
  · have e : gaussOf K 1 1 = 1 + gaussI K := by simp [gaussOf]
    rw [valued_half, e, valued_toCompl_one_add_gaussI, ← exp_add]
    norm_num
  · rw [psi_half]
    have : (-(2 * Real.pi * Complex.I) * (((2 * (1 : ℤ) / 2 ^ 2 : ℚ)) : ℂ)) =
        -(Real.pi * Complex.I) := by
      push_cast
      ring
    rw [this, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num

/-- **The level of the standard additive character at the place above 2 is 2.** -/
theorem addCharLevel_psiLocal_placeTwo : addCharLevel (psiLocal K (placeTwo K)) = 2 := by
  rw [addCharLevel_def]
  refine IsGreatest.csSup_eq ⟨fun x hx => psiLocal_two_eq_one_of_valued_le hx, fun n hn => ?_⟩
  by_contra hlt
  obtain ⟨x, hx, hne⟩ := exists_psiLocal_two_ne_one (K := K)
  exact hne (hn x (hx.trans (exp_le_exp.2 (by omega))))

/-! ## The local character of `cmChar` at `v₂` -/

/-- On a local unit at `v₂`, `cmChar` equals `σ(root2 t)`. -/
theorem cmChar_locIdele_two_unit (t : (K₂)ˣ) (ht : Valued.v (t : K₂) = 1) :
    cmChar K (locIdele K (placeTwo K) t) = sigmaU K (root2 K t) := by
  have hρ := ρ_localUnit_unit (placeTwo K) t ht
  have h2 : unit2 K (locIdele K (placeTwo K) t) = t := by
    unfold unit2
    rw [hρ, map_one, inv_one, mul_one, Units.coe_map, finIncl_apply_snd, localUnit_apply_self]
  have hθ : thetaHom K (locIdele K (placeTwo K) t) = 1 :=
    Units.ext (by
      rw [thetaHom_val, hρ, map_one, inv_one, mul_one, Units.coe_map]
      exact archHom_finIncl K _)
  rw [cmChar_apply, hθ, rootHom_apply, h2, map_one, inv_one, one_mul]

/-- **The conductor exponent of `cmChar` at `v₂` is 3.** -/
theorem hasConductorExponentAt_cmChar_two :
    HasConductorExponentAt K (placeTwo K) (localChar (cmChar K) (placeTwo K)) 3 := by
  constructor
  · intro u hu
    obtain ⟨h1, h3⟩ := hu
    have h3' : Valued.v ((u : K₂) - 1) ≤ exp (-3 : ℤ) := by
      rcases h3 with h | h
      · exact absurd h (by norm_num)
      · exact_mod_cast h
    show cmChar K (locIdele K (placeTwo K) u) = 1
    rw [cmChar_locIdele_two_unit u h1, root2_of_sub_one_le h3', map_one]
  · intro m hm
    have hneg1 : Valued.v (((-1 : (K₂)ˣ)) : K₂) = 1 := by
      rw [Units.val_neg, Units.val_one, Valuation.map_neg, map_one]
    refine ⟨-1, ⟨hneg1, Or.inr ?_⟩, ?_⟩
    · have e : (((-1 : (K₂)ˣ)) : K₂) - 1 = -2 := by
        rw [Units.val_neg, Units.val_one]
        ring
      rw [e, Valuation.map_neg, valued_two, exp_le_exp]
      omega
    · show cmChar K (locIdele K (placeTwo K) (-1)) ≠ 1
      rw [cmChar_locIdele_two_unit _ hneg1]
      have hr : root2 K (((-1 : (K₂)ˣ)) : K₂) = -1 := by
        have := root2_toCompl_unit (K := K) (-1)
        rwa [Units.val_neg, Units.val_one, map_neg, map_one, ← Units.val_one, ← Units.val_neg]
          at this
      rw [hr]
      intro h
      have := congrArg Units.val h
      rw [sigmaU_val, Units.val_neg, Units.val_one, map_neg, map_one, map_neg, map_one,
        Units.val_one] at this
      norm_num at this

end CMPoints
