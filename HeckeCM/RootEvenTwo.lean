import HeckeCM.GaussLocalN

/-!
# The local root number at the place above 2, for `d = 2e`

For `e` odd and squarefree, the character `cmCharEv = cmChar · twC · tw8C`
has conductor exponent 4 at the place above 2. The local units are the disjoint
union of the eight classes `i^k · (3 + 2i)^j` modulo 4; the Gauss sum
equals `−4i` and

`stdRootNumberAt_cmCharEv_two`: the local root number is `−i`.
-/

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero MeasureTheory
open NumberField.AdelicLevel AutomorphicForm NumberField.TateGlobal
open NumberField.StandardAddChar LanglandsTunnell.TateLocal
open scoped Classical

namespace CMPoints

/-! ## Powers of `−i` -/

lemma exp_quarter_int (a : ℤ) :
    Complex.exp (-(2 * Real.pi * Complex.I) * ((a : ℂ) / 4)) = (-Complex.I) ^ a := by
  rw [show -(2 * (Real.pi : ℂ) * Complex.I) * ((a : ℂ) / 4) =
    (a : ℂ) * (-(2 * (Real.pi : ℂ) * Complex.I) * ((1 : ℂ) / 4)) by ring, Complex.exp_int_mul,
    exp_quarter]

lemma negI_pow_two : (-Complex.I) ^ (2 : ℕ) = -1 := by rw [neg_sq, Complex.I_sq]

lemma negI_pow_three : (-Complex.I) ^ (3 : ℕ) = Complex.I := by
  rw [pow_succ, negI_pow_two]
  ring

lemma negI_zpow_three : (-Complex.I) ^ (3 : ℤ) = Complex.I := by
  rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, negI_pow_three]

lemma negI_zpow_two : (-Complex.I) ^ (2 : ℤ) = -1 := by
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, negI_pow_two]

lemma negI_zpow_neg_one : (-Complex.I) ^ (-1 : ℤ) = Complex.I := by
  rw [zpow_neg_one, inv_neg, Complex.inv_I, neg_neg]

lemma negI_zpow_neg_two : (-Complex.I) ^ (-2 : ℤ) = -1 := by
  rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast, negI_pow_two]
  norm_num

lemma negI_zpow_neg_three : (-Complex.I) ^ (-3 : ℤ) = -Complex.I := by
  rw [show (-3 : ℤ) = -((3 : ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast, negI_pow_three,
    Complex.inv_I]

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

local notation "𝔸" => AdeleRing (𝓞 K) K
local notation "K₂" => HeightOneSpectrum.adicCompletion K (placeTwo K)

attribute [local instance] localBorel borelSpace_localBorel

/-! ## Arithmetic modulo 4 -/

lemma four_eq : (4 : 𝓞 K) = -(1 + gaussI K) ^ 4 := by
  linear_combination (gaussI K ^ 2 + 4 * gaussI K + 5) * gaussI_sq K

lemma valued_toCompl_two_le_four_iff (z : 𝓞 K) :
    Valued.v (toCompl K (placeTwo K) z) ≤ exp (-((4 : ℕ) : ℤ)) ↔ (4 : 𝓞 K) ∣ z := by
  have hs : Ideal.span {(4 : 𝓞 K)} = (placeTwo K).asIdeal ^ 4 := by
    rw [placeTwo_asIdeal, Ideal.span_singleton_pow, four_eq, Ideal.span_singleton_neg]
  rw [valued_toCompl, intValuation_le_pow_iff_mem, ← hs, Ideal.mem_span_singleton]

/-- `(2 + 2i)(x + yi)` is a multiple of 4 if `x + y` is even. -/
lemma four_dvd_two_add_two_mul {x y : ℤ} (h : (x + y) % 2 = 0) :
    (4 : 𝓞 K) ∣ gaussOf K 2 2 * gaussOf K x y := by
  obtain ⟨m, hm⟩ : ∃ m, x = 2 * m - y := ⟨(x + y) / 2, by omega⟩
  refine ⟨gaussOf K (m - y) m, ?_⟩
  rw [hm]
  unfold gaussOf
  push_cast
  linear_combination (2 * (y : 𝓞 K)) * gaussI_sq K

lemma four_dvd_of_two_add_two : (gaussOf K 2 2 : 𝓞 K) ∣ 4 :=
  ⟨gaussOf K 1 (-1), by
    unfold gaussOf
    push_cast
    linear_combination (2 : 𝓞 K) * gaussI_sq K⟩

lemma not_four_dvd_two_add_two : ¬ (4 : 𝓞 K) ∣ gaussOf K 2 2 := by
  intro h
  have h' : (((4 : ℤ)) : 𝓞 K) ∣ gaussOf K 2 2 := by simpa using h
  have := (intCast_dvd_gaussOf_iff (K := K)).1 h'
  omega

variable (K) in
/-- `g = 3 + 2i`. -/
def gEl : 𝓞 K := gaussOf K 3 2

lemma gEl_eq : gEl K = 1 + gaussOf K 2 2 := by
  unfold gEl gaussOf
  push_cast
  ring

lemma uA_add_uB (k : Fin 4) : (uA k + uB k) % 2 = 1 := by
  fin_cases k <;> decide

variable (K) in
/-- The representatives `i^k · g^j` of the units modulo 4. -/
def rep8 (i : Fin 4 × Fin 2) : 𝓞 K := (unitPow K i.1 : 𝓞 K) * gEl K ^ (i.2 : ℕ)

lemma rep8_zero (k : Fin 4) : rep8 K (k, 0) = (unitPow K k : 𝓞 K) := by simp [rep8]

lemma rep8_one (k : Fin 4) : rep8 K (k, 1) = (unitPow K k : 𝓞 K) * gEl K := by simp [rep8]

lemma rep8_sub (i : Fin 4 × Fin 2) :
    gaussOf K 2 2 ∣ rep8 K i - (unitPow K i.1 : 𝓞 K) := by
  obtain ⟨k, j⟩ := i
  fin_cases j
  · exact ⟨0, by
      show rep8 K (k, 0) - (unitPow K k : 𝓞 K) = _
      rw [rep8_zero]
      ring⟩
  · exact ⟨(unitPow K k : 𝓞 K), by
      show rep8 K (k, 1) - (unitPow K k : 𝓞 K) = _
      rw [rep8_one, gEl_eq]
      ring⟩

lemma one_add_gaussI_dvd_two_add_two : (1 + gaussI K) ∣ gaussOf K 2 2 :=
  ⟨2, by
    unfold gaussOf
    push_cast
    ring⟩

lemma rep8_notMem (i : Fin 4 × Fin 2) : rep8 K i ∉ (placeTwo K).asIdeal := by
  intro h
  rw [placeTwo_asIdeal, Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := (one_add_gaussI_dvd_two_add_two (K := K)).trans (rep8_sub i)
  have hu : (1 + gaussI K) ∣ (unitPow K i.1 : 𝓞 K) := by
    have : (unitPow K i.1 : 𝓞 K) = rep8 K i - (1 + gaussI K) * c := by rw [← hc]; ring
    rw [this]
    exact dvd_sub h (dvd_mul_right _ _)
  have htop : (placeTwo K).asIdeal = ⊤ := by
    rw [placeTwo_asIdeal]
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_span_singleton.2 hu) (unitPow K i.1).isUnit
  exact (placeTwo K).isPrime.ne_top htop

lemma rep8_cover (α : 𝓞 K) (hα : α ∉ (placeTwo K).asIdeal) :
    ∃ i, Valued.v (toCompl K (placeTwo K) (α - rep8 K i)) ≤ exp (-((4 : ℕ) : ℤ)) := by
  have hnd : ¬ (1 + gaussI K) ∣ α := fun h => hα (by
    rw [placeTwo_asIdeal, Ideal.mem_span_singleton]
    exact h)
  obtain ⟨u, γ, hγ⟩ := exists_unit_dvd_sub α hnd
  obtain ⟨k, rfl⟩ := exists_unitPow u
  obtain ⟨c, d, rfl⟩ := exists_coords γ
  rcases (by omega : (c + d) % 2 = 0 ∨ (c + d) % 2 = 1) with h | h
  · refine ⟨(k, 0), (valued_toCompl_two_le_four_iff _).2 ?_⟩
    have e : α - rep8 K (k, 0) = gaussOf K 2 2 * gaussOf K c d := by
      rw [rep8_zero]
      exact hγ
    rw [e]
    exact four_dvd_two_add_two_mul h
  · refine ⟨(k, 1), (valued_toCompl_two_le_four_iff _).2 ?_⟩
    have e : α - rep8 K (k, 1) =
        gaussOf K 2 2 * gaussOf K (c - uA k) (d - uB k) := by
      have h1 : α = (unitPow K k : 𝓞 K) + gaussOf K 2 2 * gaussOf K c d := by
        linear_combination hγ
      have h2 : gaussOf K (c - uA k) (d - uB k) = gaussOf K c d - (unitPow K k : 𝓞 K) := by
        rw [unitPow_val]
        unfold gaussOf
        push_cast
        ring
      rw [h1, h2, rep8_one, gEl_eq]
      ring
    rw [e]
    have := uA_add_uB k
    exact four_dvd_two_add_two_mul (by omega)

lemma rep8_inj (i j : Fin 4 × Fin 2)
    (h : Valued.v (toCompl K (placeTwo K) (rep8 K i - rep8 K j)) ≤ exp (-((4 : ℕ) : ℤ))) :
    i = j := by
  have h4 := (valued_toCompl_two_le_four_iff _).1 h
  have h22 : gaussOf K 2 2 ∣ rep8 K i - rep8 K j := (four_dvd_of_two_add_two (K := K)).trans h4
  have hk : i.1 = j.1 := by
    refine unitPow_injective (unit_eq_of_dvd_sub (K := K) (unitPow K i.1) (unitPow K j.1) ?_)
    have : (unitPow K i.1 : 𝓞 K) - (unitPow K j.1 : 𝓞 K) =
        (rep8 K i - rep8 K j) - (rep8 K i - (unitPow K i.1 : 𝓞 K)) +
          (rep8 K j - (unitPow K j.1 : 𝓞 K)) := by ring
    rw [this]
    exact dvd_add (dvd_sub h22 (rep8_sub i)) (rep8_sub j)
  obtain ⟨k, a⟩ := i
  obtain ⟨k', b⟩ := j
  obtain rfl : k = k' := hk
  refine Prod.ext rfl ?_
  by_contra hne
  have key : (4 : 𝓞 K) ∣ (unitPow K k : 𝓞 K) * gaussOf K 2 2 := by
    fin_cases a <;> fin_cases b
    · exact absurd rfl hne
    · have e : (unitPow K k : 𝓞 K) * gaussOf K 2 2 = -(rep8 K (k, 0) - rep8 K (k, 1)) := by
        rw [rep8_zero, rep8_one, gEl_eq]
        ring
      rw [e]
      exact (dvd_neg).2 h4
    · have e : (unitPow K k : 𝓞 K) * gaussOf K 2 2 = rep8 K (k, 1) - rep8 K (k, 0) := by
        rw [rep8_zero, rep8_one, gEl_eq]
        ring
      rw [e]
      exact h4
    · exact absurd rfl hne
  obtain ⟨c, hc⟩ := key
  apply not_four_dvd_two_add_two (K := K)
  refine ⟨((unitPow K k)⁻¹ : (𝓞 K)ˣ) * c, ?_⟩
  have : gaussOf K 2 2 = ((unitPow K k)⁻¹ : (𝓞 K)ˣ) * ((unitPow K k : 𝓞 K) * gaussOf K 2 2) := by
    rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [this, hc]
  ring

end CMPoints
