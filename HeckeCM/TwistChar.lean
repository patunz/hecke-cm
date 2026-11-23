import HeckeCM.Final
import HeckeCM.TwistArith

/-!
# The quadratic character twisting `cmChar`

For `d` odd and squarefree and an idèle `x` of `K = ℚ(i)`:

* `unitAt v x = x_v / ρ x`, a unit of the completion at every place;
* `IsClose d x α`: `α ∈ 𝓞 K` approximates `unitAt v x` at all the places
  containing `d`;
* `tw x = (nrm α / d)` for such an `α` (independent of the choice);
* `twC : 𝔸ˣ →* ℂˣ`, with values `±1`, trivial on principal idèles.

This is the character of `K(√d)/K`, written without quotient rings: `(nrm α / d)`
depends only on `α` modulo `d`, and two approximants differ by a
multiple of `d` because `d` is squarefree.
-/

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open NumberField.AdelicLevel AutomorphicForm
open scoped Classical

namespace CMPoints

variable (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

local notation "𝔸" => AdeleRing (𝓞 K) K

/-! ## The local unit of an idèle -/

/-- The component at `v` divided by the normalizer. -/
def unitAt (v : HeightOneSpectrum (𝓞 K)) (x : (𝔸)ˣ) : v.adicCompletion K :=
  (x : 𝔸).2 v * (algebraMap K (v.adicCompletion K) (ρ K x))⁻¹

theorem valued_unitAt (v : HeightOneSpectrum (𝓞 K)) (x : (𝔸)ˣ) :
    Valued.v (unitAt K v x) = 1 := by
  unfold unitAt
  rw [map_mul, map_inv₀, valued_algebraMap, valuation_ρ,
    mul_inv_cancel₀ (valued_snd_ne_zero x _)]

theorem unitAt_mul (v : HeightOneSpectrum (𝓞 K)) (x y : (𝔸)ˣ) :
    unitAt K v (x * y) = unitAt K v x * unitAt K v y := by
  unfold unitAt
  rw [show (((x * y : (𝔸)ˣ)) : 𝔸).2 v = (x : 𝔸).2 v * (y : 𝔸).2 v from rfl, ρ_mul, map_mul,
    mul_inv]
  ring

theorem unitAt_one (v : HeightOneSpectrum (𝓞 K)) : unitAt K v (1 : (𝔸)ˣ) = 1 := by
  unfold unitAt
  rw [ρ_one, map_one, inv_one, mul_one]
  rfl

variable {K}

lemma valued_toCompl_le_one (v : HeightOneSpectrum (𝓞 K)) (z : 𝓞 K) :
    Valued.v (toCompl K v z) ≤ 1 := by
  rw [valued_toCompl]
  exact v.intValuation_le_one z

/-! ## Approximation at the places above `d` -/

/-- `α` approximates the local unit of `x` at all the places containing `d`. -/
def IsClose (d : ℕ) (x : (𝔸)ˣ) (α : 𝓞 K) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 K), ((d : ℕ) : 𝓞 K) ∈ v.asIdeal →
    Valued.v (unitAt K v x - toCompl K v α) < 1

lemma finite_setOf_natCast_mem {d : ℕ} (hd : d ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | ((d : ℕ) : 𝓞 K) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((d : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hd
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  rw [Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem exists_isClose {d : ℕ} (hd : d ≠ 0) (x : (𝔸)ˣ) : ∃ α : 𝓞 K, IsClose d x α := by
  obtain ⟨a, ha⟩ := exists_forall_adicValued_sub_lt (K := K)
    (finite_setOf_natCast_mem (K := K) hd).toFinset
    (fun _ => (1 : (WithZero (Multiplicative ℤ))ˣ)) (fun v : HeightOneSpectrum (𝓞 K) => v)
    (fun _ _ h => h)
    (fun v => ⟨unitAt K v x, (mem_adicCompletionIntegers (𝓞 K) K v).2 (valued_unitAt K v x).le⟩)
  refine ⟨a, fun v hv => ?_⟩
  have h1 := ha v ((Set.Finite.mem_toFinset _).2 hv)
  rw [Valuation.map_sub_swap]
  exact h1

variable {d : ℕ}

lemma IsClose.valued_eq_one {x : (𝔸)ˣ} {α : 𝓞 K} (h : IsClose d x α) {v : HeightOneSpectrum (𝓞 K)}
    (hv : ((d : ℕ) : 𝓞 K) ∈ v.asIdeal) : Valued.v (toCompl K v α) = 1 := by
  have := Valuation.map_add_eq_of_lt_left (v := Valued.v) (x := unitAt K v x)
    (y := toCompl K v α - unitAt K v x) (by
      rw [valued_unitAt, Valuation.map_sub_swap]
      exact h v hv)
  rwa [add_sub_cancel, valued_unitAt] at this

lemma IsClose.notMem {x : (𝔸)ˣ} {α : 𝓞 K} (h : IsClose d x α) {v : HeightOneSpectrum (𝓞 K)}
    (hv : ((d : ℕ) : 𝓞 K) ∈ v.asIdeal) : α ∉ v.asIdeal := by
  have := h.valued_eq_one hv
  rwa [valued_toCompl, intValuation_eq_one_iff] at this

lemma IsClose.mul {x y : (𝔸)ˣ} {α β : 𝓞 K} (h : IsClose d x α) (h' : IsClose d y β) : IsClose d (x * y) (α * β) := by
  intro v hv
  have e : unitAt K v (x * y) - toCompl K v (α * β) =
      unitAt K v x * (unitAt K v y - toCompl K v β) +
        toCompl K v β * (unitAt K v x - toCompl K v α) := by
    rw [unitAt_mul, map_mul]
    ring
  rw [e]
  refine Valuation.map_add_lt _ ?_ ?_
  · rw [map_mul, valued_unitAt, one_mul]
    exact h' v hv
  · rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (valued_toCompl_le_one v β)) (h v hv)

lemma isClose_one : IsClose d (1 : (𝔸)ˣ) (1 : 𝓞 K) := by
  intro v _
  rw [unitAt_one, map_one, sub_self, map_zero]
  exact zero_lt_one

section Squarefree

variable (hodd : d % 2 = 1) (hsq : Squarefree d)
include hodd hsq

/-- Two approximants differ by a multiple of `d`. -/
lemma IsClose.dvd_sub {x : (𝔸)ˣ} {α β : 𝓞 K} (h : IsClose d x α) (h' : IsClose d x β) : ((d : ℤ) : 𝓞 K) ∣ α - β := by
  refine natCast_dvd_of_forall_mem hodd hsq fun v hv => ?_
  have : Valued.v (toCompl K v (α - β)) < 1 := by
    rw [map_sub, show toCompl K v α - toCompl K v β =
      (unitAt K v x - toCompl K v β) + -(unitAt K v x - toCompl K v α) by ring]
    refine Valuation.map_add_lt _ (h' v hv) ?_
    rw [Valuation.map_neg]
    exact h v hv
  rwa [valued_toCompl, intValuation_lt_one_iff_mem] at this

end Squarefree

/-- The norm of an approximant is coprime to `d`. -/
lemma IsClose.gcd_nrm {x : (𝔸)ˣ} {α : 𝓞 K} (h : IsClose d x α) : Int.gcd (nrm K α) d = 1 := by
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have h1 : (p : ℤ) ∣ nrm K α := (Int.natCast_dvd_natCast.2 hpd).trans (Int.gcd_dvd_left _ _)
  have h2 : p ∣ d :=
    Int.natCast_dvd_natCast.1 ((Int.natCast_dvd_natCast.2 hpd).trans (Int.gcd_dvd_right _ _))
  refine not_dvd_nrm_of_forall_notMem hp (fun v hv => h.notMem ?_) h1
  obtain ⟨m, rfl⟩ := h2
  rw [Nat.cast_mul]
  exact v.asIdeal.mul_mem_right _ hv

/-! ## The character -/

variable (K) in
/-- `(nrm α / d)` for an approximant `α` of the local unit of `x`. -/
def tw (d : ℕ) (hd : d ≠ 0) (x : (𝔸)ˣ) : ℤ := tau K d (Classical.choose (exists_isClose hd x))

section Squarefree

variable (hodd : d % 2 = 1) (hsq : Squarefree d) (hd : d ≠ 0)
include hodd hsq

theorem tw_eq {x : (𝔸)ˣ} {α : 𝓞 K} (h : IsClose d x α) : tw K d hd x = tau K d α :=
  tau_congr ((Classical.choose_spec (exists_isClose hd x)).dvd_sub hodd hsq h)

theorem tw_mul (x y : (𝔸)ˣ) : tw K d hd (x * y) = tw K d hd x * tw K d hd y := by
  have hx := Classical.choose_spec (exists_isClose (K := K) hd x)
  have hy := Classical.choose_spec (exists_isClose (K := K) hd y)
  rw [tw_eq hodd hsq hd (hx.mul hy), tau_mul, ← tw_eq hodd hsq hd hx, ← tw_eq hodd hsq hd hy]

theorem tw_one : tw K d hd (1 : (𝔸)ˣ) = 1 := by
  rw [tw_eq hodd hsq hd (isClose_one (K := K) (d := d)), tau_one]

omit hodd hsq in
theorem tw_eq_one_or (x : (𝔸)ˣ) : tw K d hd x = 1 ∨ tw K d hd x = -1 :=
  jacobiSym.eq_one_or_neg_one (Classical.choose_spec (exists_isClose hd x)).gcd_nrm

omit hodd hsq in
theorem tw_mul_self (x : (𝔸)ˣ) : tw K d hd x * tw K d hd x = 1 := by
  rcases tw_eq_one_or hd x with h | h <;> rw [h] <;> norm_num

variable (K) in
/-- The `ℤˣ`-valued character. -/
def twUnit : (𝔸)ˣ →* ℤˣ where
  toFun x := Units.mkOfMulEqOne (tw K d hd x) (tw K d hd x) (tw_mul_self hd x)
  map_one' := Units.ext (tw_one hodd hsq hd)
  map_mul' x y := Units.ext (tw_mul hodd hsq hd x y)

variable (K) in
/-- **The twisting quadratic character**, with values in `ℂˣ`. -/
def twC : (𝔸)ˣ →* ℂˣ :=
  (Units.map ((Int.castRingHom ℂ : ℤ →+* ℂ) : ℤ →* ℂ)).comp (twUnit K hodd hsq hd)

theorem twC_val (x : (𝔸)ˣ) : ((twC K hodd hsq hd x : ℂˣ) : ℂ) = ((tw K d hd x : ℤ) : ℂ) := rfl

theorem norm_twC (x : (𝔸)ˣ) : ‖((twC K hodd hsq hd x : ℂˣ) : ℂ)‖ = 1 := by
  rw [twC_val]
  rcases tw_eq_one_or hd x with h | h <;> rw [h] <;> simp

theorem twC_eq_one_of_isClose_one {x : (𝔸)ˣ} (h : IsClose d x (1 : 𝓞 K)) : twC K hodd hsq hd x = 1 :=
  Units.ext (by rw [twC_val, tw_eq hodd hsq hd h, tau_one, Int.cast_one, Units.val_one])

/-- **`twC` is trivial on principal idèles.** -/
theorem twC_principal (a : Kˣ) :
    twC K hodd hsq hd (Units.map (algebraMap K 𝔸 : K →* 𝔸) a) = 1 := by
  obtain ⟨u, hu⟩ := exists_unit_mul_ρ_principal a
  have hclose : IsClose d (Units.map (algebraMap K 𝔸 : K →* 𝔸) a) (u : 𝓞 K) := by
    intro v _
    have hρ0 : ρ K (Units.map (algebraMap K 𝔸 : K →* 𝔸) a) ≠ 0 := ρ_ne_zero _
    have h2 : unitAt K v (Units.map (algebraMap K 𝔸 : K →* 𝔸) a) = toCompl K v u := by
      unfold unitAt toCompl
      rw [Units.coe_map, MonoidHom.coe_coe, algebraMap_adeleRing_snd]
      conv_lhs => rw [hu]
      rw [map_mul, RingHom.comp_apply, mul_inv_cancel_right₀ ((map_ne_zero _).2 hρ0)]
    rw [h2, sub_self, map_zero]
    exact zero_lt_one
  refine Units.ext ?_
  rw [twC_val, tw_eq hodd hsq hd hclose, tau_unit, Int.cast_one, Units.val_one]

end Squarefree

end CMPoints
