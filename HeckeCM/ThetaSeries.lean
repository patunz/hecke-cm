import Mathlib

/-!
# The theta series of a Dirichlet series, and its Mellin transform

Mathlib only. For a sequence `a : ℕ → ℂ` with `a 0 = 0` and
`∑ ‖a n‖ / n ^ c < ∞` for some `c > 0`, put

`θ(y) = ∑ a n · exp(−2π n y)`  for `y > 0`.

* `norm_Gamma_le`, `norm_Gamma_mul_abs_im_pow_le`: `‖Γ(s)‖ ≤ Γ(Re s)` and
  `‖Γ(s)‖ · |Im s|ᵐ ≤ Γ(Re s + m)` for `Re s > 0`: decay of `Γ` on vertical
  lines, from the functional equation alone;
* `hasSum_thetaSeries`, `norm_thetaSeries_le`, `norm_thetaSeries_le_exp`:
  convergence, `θ(y) = O(y^{−c})` and `θ(y) = O(e^{−πy})` for `y ≥ 1`;
* `continuousOn_thetaSeries`: `θ` is continuous on `(0, ∞)`;
* `mellin_thetaSeries`: for `Re s ≥ c`,
  `∫₀^∞ θ(y) y^{s−1} dy = (2π)^{−s} Γ(s) · ∑ a n / n^s`;
* `mellinConvergent_thetaSeries`: the Mellin integral converges for `Re s > c`.
-/

set_option autoImplicit false

noncomputable section

open Real Complex MeasureTheory Set Filter Asymptotics
open scoped Topology Nat

namespace CMPoints

/-! ## Decay of `Γ` on vertical lines -/

/-- `‖Γ(s)‖ ≤ Γ(Re s)` for `Re s > 0`. -/
theorem norm_Gamma_le {s : ℂ} (hs : 0 < s.re) : ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Real.Gamma_eq_integral hs, Complex.GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 < x := hx
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re, Complex.one_re]

/-- `‖Γ(s)‖ · |Im s|ᵐ ≤ Γ(Re s + m)` for `Re s > 0`. -/
theorem norm_Gamma_mul_abs_im_pow_le (m : ℕ) : ∀ {s : ℂ}, 0 < s.re →
    ‖Complex.Gamma s‖ * |s.im| ^ m ≤ Real.Gamma (s.re + m) := by
  induction m with
  | zero =>
    intro s hs
    simpa using norm_Gamma_le hs
  | succ m ih =>
    intro s hs
    have hs0 : s ≠ 0 := fun h => by simp [h] at hs
    have h1 : (0 : ℝ) < (s + 1).re := by simp; linarith
    have key := ih h1
    rw [Complex.Gamma_add_one s hs0, norm_mul] at key
    have him : (s + 1).im = s.im := by simp
    have hre : (s + 1).re + (m : ℝ) = s.re + ((m + 1 : ℕ) : ℝ) := by
      simp
      ring
    rw [him, hre] at key
    refine le_trans ?_ key
    have hle : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
    calc ‖Complex.Gamma s‖ * |s.im| ^ (m + 1)
        = |s.im| * (‖Complex.Gamma s‖ * |s.im| ^ m) := by ring
      _ ≤ ‖s‖ * (‖Complex.Gamma s‖ * |s.im| ^ m) :=
          mul_le_mul_of_nonneg_right hle (by positivity)
      _ = ‖s‖ * ‖Complex.Gamma s‖ * |s.im| ^ m := by ring

/-! ## An elementary bound -/

/-- `u^c · e^{−u} ≤ ⌈c⌉!` for `u ≥ 0`, `c ≥ 0`. -/
lemma rpow_mul_exp_neg_le {c : ℝ} (hc : 0 ≤ c) {u : ℝ} (hu : 0 ≤ u) :
    u ^ c * Real.exp (-u) ≤ (⌈c⌉₊ ! : ℝ) := by
  have hk1 : (1 : ℝ) ≤ (⌈c⌉₊ ! : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
  rcases le_total u 1 with h1 | h1
  · have e1 : u ^ c ≤ 1 := Real.rpow_le_one hu h1 hc
    have e2 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    calc u ^ c * Real.exp (-u) ≤ 1 * 1 := mul_le_mul e1 e2 (Real.exp_pos _).le zero_le_one
      _ ≤ _ := by simpa using hk1
  · have e1 : u ^ c ≤ u ^ (⌈c⌉₊ : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil c)
    rw [Real.rpow_natCast] at e1
    have e2 := Real.pow_div_factorial_le_exp u hu ⌈c⌉₊
    have hfac : (0 : ℝ) < (⌈c⌉₊ ! : ℝ) := by positivity
    rw [div_le_iff₀ hfac] at e2
    have e3 : u ^ ⌈c⌉₊ * Real.exp (-u) ≤ (⌈c⌉₊ ! : ℝ) := by
      calc u ^ ⌈c⌉₊ * Real.exp (-u) ≤ Real.exp u * (⌈c⌉₊ ! : ℝ) * Real.exp (-u) :=
            mul_le_mul_of_nonneg_right e2 (Real.exp_pos _).le
        _ = (⌈c⌉₊ ! : ℝ) * (Real.exp u * Real.exp (-u)) := by ring
        _ = (⌈c⌉₊ ! : ℝ) := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    exact (mul_le_mul_of_nonneg_right e1 (Real.exp_pos _).le).trans e3

/-! ## The theta series -/

/-- `θ(y) = ∑ a n · exp(−2π n y)`. -/
def thetaSeries (a : ℕ → ℂ) (y : ℝ) : ℂ :=
  ∑' n : ℕ, a n * (Real.exp (-(2 * π * n) * y) : ℂ)

section

variable {a : ℕ → ℂ} {c : ℝ}

/-- The constant in the bounds: `(∑ ‖a n‖ / n^c) · ⌈c⌉!`. -/
def thetaConst (a : ℕ → ℂ) (c : ℝ) : ℝ := (∑' n : ℕ, ‖a n‖ / (n : ℝ) ^ c) * (⌈c⌉₊ ! : ℝ)

lemma thetaConst_nonneg (a : ℕ → ℂ) (c : ℝ) : 0 ≤ thetaConst a c :=
  mul_nonneg (tsum_nonneg fun n => by positivity) (by positivity)

/-- Termwise bound: `‖a n‖ e^{−b n y} ≤ (‖a n‖ / n^c) · ⌈c⌉! · (b y)^{−c}`. -/
lemma norm_mul_exp_le (ha0 : a 0 = 0) (hc : 0 < c) {b : ℝ} (hb : 0 < b) {y : ℝ} (hy : 0 < y)
    (n : ℕ) :
    ‖a n‖ * Real.exp (-(b * n) * y) ≤ ‖a n‖ / (n : ℝ) ^ c * ((⌈c⌉₊ ! : ℝ) * (b * y) ^ (-c)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ha0]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hby : 0 < b * y := mul_pos hb hy
  have hnc : (0 : ℝ) < (n : ℝ) ^ c := Real.rpow_pos_of_pos hn0 c
  have hbyc : (0 : ℝ) < (b * y) ^ c := Real.rpow_pos_of_pos hby c
  have hu := rpow_mul_exp_neg_le hc.le (u := b * y * n) (by positivity)
  rw [Real.mul_rpow hby.le hn0.le] at hu
  have hexp : Real.exp (-(b * n) * y) = Real.exp (-(b * y * n)) := by
    congr 1
    ring
  rw [hexp, Real.rpow_neg hby.le, div_mul_eq_mul_div, le_div_iff₀ hnc]
  have h2 : (n : ℝ) ^ c * Real.exp (-(b * y * n)) ≤ (⌈c⌉₊ ! : ℝ) * ((b * y) ^ c)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hbyc]
    calc (n : ℝ) ^ c * Real.exp (-(b * y * n)) * (b * y) ^ c
        = (b * y) ^ c * (n : ℝ) ^ c * Real.exp (-(b * y * n)) := by ring
      _ ≤ _ := hu
  calc ‖a n‖ * Real.exp (-(b * y * n)) * (n : ℝ) ^ c
      = ‖a n‖ * ((n : ℝ) ^ c * Real.exp (-(b * y * n))) := by ring
    _ ≤ ‖a n‖ * ((⌈c⌉₊ ! : ℝ) * ((b * y) ^ c)⁻¹) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)

/-- Summability of the norms, with the bound `C · (b y)^{−c}`. -/
lemma summable_norm_mul_exp (ha0 : a 0 = 0) (hc : 0 < c)
    (hsum : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ c) {b : ℝ} (hb : 0 < b) {y : ℝ} (hy : 0 < y) :
    Summable (fun n : ℕ => ‖a n‖ * Real.exp (-(b * n) * y)) ∧
      ∑' n : ℕ, ‖a n‖ * Real.exp (-(b * n) * y) ≤ thetaConst a c * (b * y) ^ (-c) := by
  have hg : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ c * ((⌈c⌉₊ ! : ℝ) * (b * y) ^ (-c)) :=
    hsum.mul_right _
  have hle := norm_mul_exp_le (a := a) ha0 hc hb hy
  have hs : Summable fun n : ℕ => ‖a n‖ * Real.exp (-(b * n) * y) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hle hg
  refine ⟨hs, ?_⟩
  calc ∑' n : ℕ, ‖a n‖ * Real.exp (-(b * n) * y)
      ≤ ∑' n : ℕ, ‖a n‖ / (n : ℝ) ^ c * ((⌈c⌉₊ ! : ℝ) * (b * y) ^ (-c)) := hs.tsum_le_tsum hle hg
    _ = thetaConst a c * (b * y) ^ (-c) := by
        rw [tsum_mul_right, thetaConst]
        ring

lemma norm_term (n : ℕ) (y : ℝ) :
    ‖a n * (Real.exp (-(2 * π * n) * y) : ℂ)‖ = ‖a n‖ * Real.exp (-(2 * π * n) * y) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- The theta series converges for `y > 0`. -/
theorem hasSum_thetaSeries (ha0 : a 0 = 0) (hc : 0 < c)
    (hsum : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ c) {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => a n * (Real.exp (-(2 * π * n) * y) : ℂ)) (thetaSeries a y) := by
  have h := (summable_norm_mul_exp ha0 hc hsum (b := 2 * π) (by positivity) hy).1
  exact (Summable.of_norm (by simpa only [norm_term] using h)).hasSum

/-- `‖θ(y)‖ ≤ C · (2π y)^{−c}` for `y > 0`. -/
theorem norm_thetaSeries_le (ha0 : a 0 = 0) (hc : 0 < c)
    (hsum : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ c) {y : ℝ} (hy : 0 < y) :
    ‖thetaSeries a y‖ ≤ thetaConst a c * (2 * π * y) ^ (-c) := by
  obtain ⟨h1, h2⟩ := summable_norm_mul_exp ha0 hc hsum (b := 2 * π) (by positivity) hy
  refine le_trans ?_ h2
  rw [thetaSeries]
  refine (norm_tsum_le_tsum_norm (by simpa only [norm_term] using h1)).trans_eq ?_
  simp only [norm_term]

/-- `‖θ(y)‖ ≤ C · π^{−c} · e^{−π y}` for `y ≥ 1`. -/
theorem norm_thetaSeries_le_exp (ha0 : a 0 = 0) (hc : 0 < c)
    (hsum : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ c) {y : ℝ} (hy : 1 ≤ y) :
    ‖thetaSeries a y‖ ≤ thetaConst a c * π ^ (-c) * Real.exp (-π * y) := by
  have hy0 : 0 < y := by linarith
  obtain ⟨h1, -⟩ := summable_norm_mul_exp ha0 hc hsum (b := 2 * π) (by positivity) hy0
  obtain ⟨h3, h4⟩ := summable_norm_mul_exp ha0 hc hsum (b := π) Real.pi_pos hy0
  have hterm : ∀ n : ℕ, ‖a n‖ * Real.exp (-(2 * π * n) * y) ≤
      Real.exp (-π * y) * (‖a n‖ * Real.exp (-(π * n) * y)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ha0]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hexp : Real.exp (-(2 * π * n) * y) ≤ Real.exp (-π * y) * Real.exp (-(π * n) * y) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have : 0 ≤ π * y * ((n : ℝ) - 1) := by
        have := Real.pi_pos
        have h0 : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
        positivity
      nlinarith
    calc ‖a n‖ * Real.exp (-(2 * π * n) * y)
        ≤ ‖a n‖ * (Real.exp (-π * y) * Real.exp (-(π * n) * y)) :=
          mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
      _ = _ := by ring
  have hpy : (π * y) ^ (-c) ≤ π ^ (-c) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_neg Real.pi_pos.le]
    refine inv_anti₀ (Real.rpow_pos_of_pos Real.pi_pos c) ?_
    refine Real.rpow_le_rpow Real.pi_pos.le ?_ hc.le
    nlinarith [Real.pi_pos]
  rw [thetaSeries]
  calc ‖∑' n : ℕ, a n * (Real.exp (-(2 * π * n) * y) : ℂ)‖
      ≤ ∑' n : ℕ, ‖a n‖ * Real.exp (-(2 * π * n) * y) := by
        refine (norm_tsum_le_tsum_norm (by simpa only [norm_term] using h1)).trans_eq ?_
        simp only [norm_term]
    _ ≤ ∑' n : ℕ, Real.exp (-π * y) * (‖a n‖ * Real.exp (-(π * n) * y)) :=
        h1.tsum_le_tsum hterm (h3.mul_left _)
    _ = Real.exp (-π * y) * ∑' n : ℕ, ‖a n‖ * Real.exp (-(π * n) * y) := tsum_mul_left
    _ ≤ Real.exp (-π * y) * (thetaConst a c * (π * y) ^ (-c)) :=
        mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
    _ ≤ Real.exp (-π * y) * (thetaConst a c * π ^ (-c)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpy (thetaConst_nonneg a c))
          (Real.exp_pos _).le
    _ = _ := by ring

/-- `θ` is continuous on `(0, ∞)`. -/
theorem continuousOn_thetaSeries (ha0 : a 0 = 0) (hc : 0 < c)
    (hsum : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ c) : ContinuousOn (thetaSeries a) (Ioi 0) := by
  intro x hx
  have hx0 : 0 < x := hx
  have hδ : 0 < x / 2 := by positivity
  have hu := (summable_norm_mul_exp ha0 hc hsum (b := 2 * π) (by positivity) hδ).1
  have hcont : ContinuousOn (thetaSeries a) (Ioi (x / 2)) := by
    refine continuousOn_tsum (fun n => ?_) hu fun n y hy => ?_
    · exact (Continuous.continuousOn (by fun_prop))
    · rw [norm_term]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
      have hy' : x / 2 < y := hy
      have : 0 ≤ 2 * π * (n : ℝ) := by positivity
      nlinarith
  exact (hcont.continuousAt (Ioi_mem_nhds (by linarith))).continuousWithinAt

/-! ## The Mellin transform -/

/-- **Mellin transform of the theta series**: for `Re s ≥ c`,
`∫₀^∞ θ(y) y^{s−1} dy = (2π)^{−s} Γ(s) · L(a, s)`. -/
theorem mellin_thetaSeries (ha0 : a 0 = 0) (hc : 0 < c)
    (hsum : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ c) {s : ℂ} (hs : c ≤ s.re) :
    mellin (thetaSeries a) s = (2 * π : ℂ) ^ (-s) * Complex.Gamma s * LSeries a s := by
  have hs0 : 0 < s.re := hc.trans_le hs
  have h2π : (0 : ℝ) < 2 * π := by positivity
  have hsummable : Summable fun n : ℕ => ‖a n‖ / (2 * π * (n : ℝ)) ^ s.re := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (hsum.mul_left ((2 * π) ^ (-s.re)))
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ha0]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [Real.mul_rpow h2π.le hn0.le, Real.rpow_neg h2π.le]
    have hp : (0 : ℝ) < (2 * π) ^ s.re := Real.rpow_pos_of_pos h2π _
    have hq : (0 : ℝ) < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos hn0 _
    have h1 : ‖a n‖ / (n : ℝ) ^ s.re ≤ ‖a n‖ / (n : ℝ) ^ c :=
      div_le_div_of_nonneg_left (norm_nonneg _) (Real.rpow_pos_of_pos hn0 c)
        (Real.rpow_le_rpow_of_exponent_le hn1 hs)
    calc ‖a n‖ / ((2 * π) ^ s.re * (n : ℝ) ^ s.re)
        = ((2 * π) ^ s.re)⁻¹ * (‖a n‖ / (n : ℝ) ^ s.re) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hp.le)
  have key := hasSum_mellin (a := a) (p := fun n : ℕ => 2 * π * (n : ℝ)) (F := thetaSeries a)
    (s := s) (fun n => by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact Or.inl ha0
      · exact Or.inr (by positivity)) hs0
    (fun t ht => by
      have := hasSum_thetaSeries ha0 hc hsum (y := t) ht
      simpa using this) hsummable
  rw [← key.tsum_eq, LSeries, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ha0]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [LSeries.term_of_ne_zero hn.ne']
  have hcp : ((2 * π * (n : ℝ) : ℝ) : ℂ) ^ s = (2 * π : ℂ) ^ s * (n : ℂ) ^ s := by
    have := Complex.mul_cpow_ofReal_nonneg h2π.le (Nat.cast_nonneg n) s
    push_cast at this ⊢
    exact this
  rw [hcp, Complex.cpow_neg]
  field_simp

/-- The Mellin integral of the theta series converges for `Re s > c`. -/
theorem mellinConvergent_thetaSeries (ha0 : a 0 = 0) (hc : 0 < c)
    (hsum : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ c) {s : ℂ} (hs : c < s.re) :
    MellinConvergent (thetaSeries a) s := by
  refine mellinConvergent_of_isBigO_rpow_exp (a := π) (b := c) Real.pi_pos
    ((continuousOn_thetaSeries ha0 hc hsum).locallyIntegrableOn measurableSet_Ioi) ?_ ?_ hs
  · refine IsBigO.of_bound (thetaConst a c * π ^ (-c)) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact norm_thetaSeries_le_exp ha0 hc hsum hy
  · refine IsBigO.of_bound (thetaConst a c * (2 * π) ^ (-c)) ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : 0 < y := hy
    rw [Real.norm_of_nonneg (Real.rpow_pos_of_pos hy0 _).le]
    refine (norm_thetaSeries_le ha0 hc hsum hy0).trans_eq ?_
    rw [Real.mul_rpow (by positivity) hy0.le]
    ring

end

end CMPoints
