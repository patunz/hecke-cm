import Definitions.Def_AutomorphicForm_AdelicLsXi
import HeckeCM.TwoChar

/-!
# The Hecke character of `ℚ(i)` attached to `y² = x³ − x`

For an idèle `x` of `K = ℚ(i)`, with `ρ x ∈ Kˣ` the normalizer:

* `rootHom x` is the root of unity congruent to `x₂ / ρ x` modulo `(1 + i)³`;
* `thetaHom x = x_∞ / σ(ρ x) ∈ ℂˣ`, with `σ` the chosen complex embedding;
* `cmChar x = (θ / |θ|)⁻¹ · σ(rootHom x)`.

Results: `cmChar` is a homomorphism `𝔸ˣ → ℂˣ`, trivial on `Kˣ`
(`isIdeleClassChar_cmChar`) and of modulus 1 (`isUnitaryChar_cmChar`).
-/

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open NumberField.AdelicLevel AutomorphicForm

namespace CMPoints

variable (K : Type) [Field K] [NumberField K]

local notation "𝔸" => AdeleRing (𝓞 K) K

/-! ## The archimedean part -/

/-- The chosen archimedean place. -/
def archPlace : InfinitePlace K := Classical.arbitrary _

/-- The chosen complex embedding. -/
def sigma : K →+* ℂ := (archPlace K).embedding

/-- The archimedean coordinate of an adèle, in `ℂ`. -/
def archHom : 𝔸 →+* ℂ :=
  (InfinitePlace.Completion.extensionEmbedding (archPlace K)).comp
    ((archEval K (archPlace K)).comp (adeleArch (𝓞 K) K))

theorem archHom_algebraMap (q : K) : archHom K (algebraMap K 𝔸 q) = sigma K q := by
  show InfinitePlace.Completion.extensionEmbedding (archPlace K)
    ((algebraMap K 𝔸 q).1 (archPlace K)) = _
  rw [AdeleRing.algebraMap_fst_apply, InfinitePlace.Completion.extensionEmbedding_coe]
  rfl

theorem archHom_finIncl (y : FiniteAdeleRing (𝓞 K) K) : archHom K (finIncl (𝓞 K) K y) = 1 := by
  show InfinitePlace.Completion.extensionEmbedding (archPlace K)
    ((finIncl (𝓞 K) K y).1 (archPlace K)) = 1
  rw [finIncl_apply_fst]
  exact map_one _

/-- `z ↦ z / |z|` su `ℂˣ`. -/
def unitDir : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ))
    (div_ne_zero z.ne_zero (by exact_mod_cast (norm_ne_zero_iff.2 z.ne_zero)))
  map_one' := Units.ext (by simp)
  map_mul' z w := Units.ext (by
    simp only [Units.val_mul, Units.val_mk0, norm_mul, Complex.ofReal_mul]
    rw [mul_div_mul_comm])

theorem unitDir_val (z : ℂˣ) : ((unitDir z : ℂˣ) : ℂ) = (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) := rfl

theorem norm_unitDir (z : ℂˣ) : ‖((unitDir z : ℂˣ) : ℂ)‖ = 1 := by
  rw [unitDir_val, norm_div, Complex.norm_real, norm_norm,
    div_self (norm_ne_zero_iff.2 z.ne_zero)]

theorem unitDir_of_norm_one {z : ℂˣ} (h : ‖(z : ℂ)‖ = 1) : unitDir z = z :=
  Units.ext (by rw [unitDir_val, h, Complex.ofReal_one, div_one])

variable [IsCyclotomicExtension {4} ℚ K]

/-! ## The units of `𝓞 K` have order dividing 4 -/

variable {K} in
theorem unit_pow_four (u : (𝓞 K)ˣ) : u ^ 4 = 1 := by
  obtain ⟨e, f, hef⟩ := exists_coords (u : 𝓞 K)
  have h1 : e ^ 2 + f ^ 2 = 1 := (isUnit_coords_iff e f).1 (hef ▸ u.isUnit)
  have h0 : e * f = 0 := by
    have b1 : e ≤ 1 := by nlinarith [sq_nonneg f]
    have b2 : -1 ≤ e := by nlinarith [sq_nonneg f]
    have b3 : f ≤ 1 := by nlinarith [sq_nonneg e]
    have b4 : -1 ≤ f := by nlinarith [sq_nonneg e]
    clear hef
    interval_cases e <;> interval_cases f <;> omega
  have h1' : (e : 𝓞 K) ^ 2 + (f : 𝓞 K) ^ 2 = 1 := by exact_mod_cast h1
  have h0' : (e : 𝓞 K) * (f : 𝓞 K) = 0 := by exact_mod_cast h0
  have hI := gaussI_sq K
  have hsq : ((e : 𝓞 K) + (f : 𝓞 K) * gaussI K) ^ 2 = (e : 𝓞 K) ^ 2 - (f : 𝓞 K) ^ 2 := by
    linear_combination ((f : 𝓞 K) ^ 2) * hI + 2 * gaussI K * h0'
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, hef, Units.val_one]
  calc ((e : 𝓞 K) + (f : 𝓞 K) * gaussI K) ^ 4
      = (((e : 𝓞 K) + (f : 𝓞 K) * gaussI K) ^ 2) ^ 2 := by ring
    _ = 1 := by
      rw [hsq]
      linear_combination ((e : 𝓞 K) ^ 2 + (f : 𝓞 K) ^ 2 + 1) * h1' - 4 * (e : 𝓞 K) * (f : 𝓞 K) * h0'

/-- `σ` on the units of `𝓞 K`. -/
def sigmaU : (𝓞 K)ˣ →* ℂˣ :=
  Units.map (((sigma K).comp (algebraMap (𝓞 K) K) : 𝓞 K →+* ℂ) : 𝓞 K →* ℂ)

theorem sigmaU_val (u : (𝓞 K)ˣ) :
    ((sigmaU K u : ℂˣ) : ℂ) = sigma K (algebraMap (𝓞 K) K u) := rfl

theorem norm_sigmaU (u : (𝓞 K)ˣ) : ‖((sigmaU K u : ℂˣ) : ℂ)‖ = 1 := by
  have h4 : ((sigmaU K u : ℂˣ) : ℂ) ^ 4 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, unit_pow_four, map_one, Units.val_one]
  have hn : ‖((sigmaU K u : ℂˣ) : ℂ)‖ ^ 4 = 1 := by rw [← norm_pow, h4, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 hn

/-! ## The two components of the character -/

/-- The normalizer as a homomorphism into `Kˣ`. -/
def ρU : (𝔸)ˣ →* Kˣ where
  toFun x := Units.mk0 (ρ K x) (ρ_ne_zero x)
  map_one' := Units.ext ρ_one
  map_mul' x y := Units.ext (ρ_mul x y)

/-- The component at 2 divided by the normalizer: a 2-adic unit. -/
def unit2 (x : (𝔸)ˣ) : (placeTwo K).adicCompletion K :=
  (x : 𝔸).2 (placeTwo K) * (algebraMap K ((placeTwo K).adicCompletion K) (ρ K x))⁻¹

theorem valued_unit2 (x : (𝔸)ˣ) : Valued.v (unit2 K x) = 1 := by
  unfold unit2
  rw [map_mul, map_inv₀, valued_algebraMap, valuation_ρ,
    mul_inv_cancel₀ (valued_snd_ne_zero x _)]

theorem unit2_mul (x y : (𝔸)ˣ) : unit2 K (x * y) = unit2 K x * unit2 K y := by
  unfold unit2
  rw [show (((x * y : (𝔸)ˣ)) : 𝔸).2 (placeTwo K) =
      (x : 𝔸).2 (placeTwo K) * (y : 𝔸).2 (placeTwo K) from rfl, ρ_mul, map_mul, mul_inv]
  ring

theorem unit2_one : unit2 K (1 : (𝔸)ˣ) = 1 := by
  unfold unit2
  rw [ρ_one, map_one, inv_one, mul_one]
  rfl

/-- The root of unity of an idèle. -/
def rootHom : (𝔸)ˣ →* (𝓞 K)ˣ where
  toFun x := root2 K (unit2 K x)
  map_one' := by rw [unit2_one, root2_one]
  map_mul' x y := by rw [unit2_mul, root2_mul (valued_unit2 K x) (valued_unit2 K y)]

theorem rootHom_apply (x : (𝔸)ˣ) : rootHom K x = root2 K (unit2 K x) := rfl

/-- The archimedean component divided by the normalizer. -/
def thetaHom : (𝔸)ˣ →* ℂˣ where
  toFun x := Units.mk0 (archHom K (x : 𝔸) * (sigma K (ρ K x))⁻¹)
    (mul_ne_zero ((x.map (archHom K : 𝔸 →* ℂ)).ne_zero)
      (inv_ne_zero ((map_ne_zero _).2 (ρ_ne_zero x))))
  map_one' := Units.ext (by
    rw [Units.val_mk0, Units.val_one, map_one, ρ_one, map_one, inv_one, mul_one, Units.val_one])
  map_mul' x y := Units.ext (by
    simp only [Units.val_mul, Units.val_mk0, map_mul, ρ_mul, mul_inv]
    ring)

theorem thetaHom_val (x : (𝔸)ˣ) :
    ((thetaHom K x : ℂˣ) : ℂ) = archHom K (x : 𝔸) * (sigma K (ρ K x))⁻¹ := rfl

/-- **The Hecke character.** -/
def cmChar : (𝔸)ˣ →* ℂˣ :=
  (unitDir.comp (thetaHom K))⁻¹ * (sigmaU K).comp (rootHom K)

theorem cmChar_apply (x : (𝔸)ˣ) :
    cmChar K x = (unitDir (thetaHom K x))⁻¹ * sigmaU K (rootHom K x) := rfl

/-- **`cmChar` has modulus 1.** -/
theorem isUnitaryChar_cmChar : IsUnitaryChar (𝓞 K) K (cmChar K) := by
  intro x
  rw [cmChar_apply, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv, norm_unitDir,
    norm_sigmaU, inv_one, one_mul]

/-- **`cmChar` is trivial on principal idèles.** -/
theorem isIdeleClassChar_cmChar : IsIdeleClassChar (𝓞 K) K (cmChar K) := by
  intro α
  obtain ⟨u, hu⟩ := exists_unit_mul_ρ_principal α
  set x : (𝔸)ˣ := Units.map (algebraMap K 𝔸 : K →* 𝔸) α with hx
  have hρ0 : ρ K x ≠ 0 := ρ_ne_zero x
  have hroot : rootHom K x = u := by
    rw [rootHom_apply]
    have h2 : unit2 K x = toCompl K (placeTwo K) u := by
      unfold unit2 toCompl
      rw [hx, Units.coe_map, MonoidHom.coe_coe, algebraMap_adeleRing_snd, ← hx, hu, map_mul,
        RingHom.comp_apply, mul_inv_cancel_right₀ ((map_ne_zero _).2 hρ0)]
    rw [h2, root2_toCompl_unit]
  have htheta : thetaHom K x = sigmaU K u := by
    refine Units.ext ?_
    rw [thetaHom_val, sigmaU_val, hx, Units.coe_map, MonoidHom.coe_coe, archHom_algebraMap, ← hx,
      hu, map_mul, mul_inv_cancel_right₀ ((map_ne_zero _).2 hρ0)]
  rw [cmChar_apply, hroot, htheta, unitDir_of_norm_one (norm_sigmaU K u), inv_mul_cancel]

end CMPoints
