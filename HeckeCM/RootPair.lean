import HeckeCM.RootSplit

/-!
# The two places above a split prime

With `p = a² + b²`, `v = (a + bi)`, `w = (a − bi)` and `d = p·m`:

* `stdRootNumberAt_twC_split_eq`: the local root numbers of `twC` at `v` and
  at `w` coincide;
* `stdRootNumberAt_twC_split_sq`: their square is 1;
* `stdRootNumberAt_cmCharTw_split`: the product of the local root numbers of
  `cmCharTw` at `v` and at `w` is 1.
-/

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero MeasureTheory
open NumberField.AdelicLevel AutomorphicForm NumberField.TateGlobal
open NumberField.StandardAddChar LanglandsTunnell.TateLocal
open scoped Classical

namespace CMPoints

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

local notation "𝔸" => AdeleRing (𝓞 K) K

variable {p : ℕ} [hp : Fact p.Prime] {a b : ℤ} (hp1 : p % 4 = 1) (hab : IsPrimaryPair a b)
  (hn : a ^ 2 + b ^ 2 = p) {v : HeightOneSpectrum (𝓞 K)}
  (hv : v.asIdeal = Ideal.span {gaussOf K a b})
  {m : ℕ} (hodd : (p * m) % 2 = 1) (hsq : Squarefree (p * m)) (hd : p * m ≠ 0)
include hp1 hab hn hv hodd hsq

omit hp hp1 hab hn hv in
lemma twC_inv_eq (u : HeightOneSpectrum (𝓞 K)) :
    (localChar (twC K hodd hsq hd) u)⁻¹ = localChar (twC K hodd hsq hd) u := by
  refine MonoidHom.ext fun t => ?_
  rw [MonoidHom.inv_apply, inv_eq_iff_eq_inv, eq_inv_iff_mul_eq_one]
  refine Units.ext ?_
  show ((twC K hodd hsq hd (locIdele K u t) : ℂˣ) : ℂ) * ((twC K hodd hsq hd (locIdele K u t) :
    ℂˣ) : ℂ) = 1
  rw [twC_val, ← Int.cast_mul, tw_mul_self hd, Int.cast_one]

/-- **The square of the local root number of `twC` at a split place is 1.** -/
theorem stdRootNumberAt_twC_split_sq :
    stdRootNumberAt K v (localChar (twC K hodd hsq hd) v) ^ 2 = 1 := by
  have hpv := natCast_mem_split hn hv
  have hdv : (((p * m : ℕ)) : 𝓞 K) ∈ v.asIdeal := by
    rw [Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ hpv
  have h := stdRootNumberAt_mul_stdRootNumberAt_inv_eq_apply_neg_one K v
    (localChar (twC K hodd hsq hd) v) 1 le_rfl (hasConductorExponentAt_twC hodd hsq hd hdv)
    (norm_twC hodd hsq hd _)
  rw [twC_inv_eq hodd hsq hd v] at h
  have hρ : toCompl K v (((-1 : ℤ)) : 𝓞 K) ≠ 0 := by
    rw [Int.cast_neg, Int.cast_one, map_neg, map_one]
    exact neg_ne_zero.2 one_ne_zero
  have hN : ¬ (p : ℤ) ∣ (-1 : ℤ) := by
    intro hdvd
    have h1 := Int.le_of_dvd (by norm_num) ((dvd_neg).1 hdvd)
    have h2 := hp.out.two_le
    omega
  have hval := twC_locIdele_int hp1 hab hn hv hodd hsq hd (-1) hρ hN
  have hu : Units.mk0 (toCompl K v (((-1 : ℤ)) : 𝓞 K)) hρ = -1 :=
    Units.ext (by simp)
  rw [hu] at hval
  have hleg : legendreSym p (-1) = 1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym, jacobiSym.at_neg_one (Nat.odd_iff.2 (by omega)),
      ZMod.χ₄_nat_one_mod_four hp1]
  have hneg : ((localChar (twC K hodd hsq hd) v (-1) : ℂˣ) : ℂ) = 1 := by
    have : ((localChar (twC K hodd hsq hd) v (-1) : ℂˣ) : ℂ) =
        ((twC K hodd hsq hd (locIdele K v (-1)) : ℂˣ) : ℂ) := rfl
    rw [this, hval, hleg, Int.cast_one]
  rw [sq, h, hneg]

omit hv in
/-- **The local root numbers of `twC` at the two places above `p` coincide.** -/
theorem stdRootNumberAt_twC_split_eq (hab' : IsPrimaryPair a (-b))
    {w : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal = Ideal.span {gaussOf K a b})
    (hw : w.asIdeal = Ideal.span {gaussOf K a (-b)})
    (hNv : Ideal.absNorm v.asIdeal = p) (hNw : Ideal.absNorm w.asIdeal = p) :
    stdRootNumberAt K v (localChar (twC K hodd hsq hd) v) =
      stdRootNumberAt K w (localChar (twC K hodd hsq hd) w) := by
  have hn' : a ^ 2 + (-b) ^ 2 = (p : ℤ) := by rw [neg_sq]; exact hn
  have hpm : p.Coprime m := Nat.coprime_of_squarefree_mul hsq
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hd
  obtain ⟨E, F, hE1, hE2, hF1, hF2⟩ := exists_EF hp1 hn hab hpm hm0
  have Gv := gauss_sum_split hp1 hab hn hv hodd hsq hd hNv
  have Gw := gauss_sum_split hp1 hab' hn' hw hodd hsq hd hNw
  have cv := charExt_twC_gen_inv_split hp1 hab hn hv hodd hsq hd hE1 hE2 hF1 hF2
  have cw := charExt_twC_gen_inv_split hp1 hab' hn' hw hodd hsq hd hE1 hE2 hF1 hF2
  have htau : tau K (p * m) (gaussOf K ((E + F) * a) ((F - E) * -b)) =
      tau K (p * m) (gaussOf K ((E + F) * a) ((F - E) * b)) := by
    rw [tau, tau, nrm_gaussOf, nrm_gaussOf]
    congr 1
    ring
  rw [htau, ← cv] at cw
  rw [cw] at Gw
  have hz : (toCompl K v (gen K v))⁻¹ ≠ 0 := inv_ne_zero (toCompl_gen_ne_zero' v)
  have hc0 : charExt (localChar (twC K hodd hsq hd) v) (toCompl K v (gen K v))⁻¹ ≠ 0 := by
    rw [charExt_of_ne_zero _ hz]
    exact Units.ne_zero _
  exact mul_left_cancel₀ hc0 (Gv.symm.trans Gw)

omit hv in
/-- **The product of the local root numbers of `cmCharTw` at the two places above
a split prime is 1.** -/
theorem stdRootNumberAt_cmCharTw_split (hab' : IsPrimaryPair a (-b))
    {w : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal = Ideal.span {gaussOf K a b})
    (hw : w.asIdeal = Ideal.span {gaussOf K a (-b)})
    (hNv : Ideal.absNorm v.asIdeal = p) (hNw : Ideal.absNorm w.asIdeal = p) :
    stdRootNumberAt K v (localChar (cmCharTw K hodd hsq hd) v) *
      stdRootNumberAt K w (localChar (cmCharTw K hodd hsq hd) w) = 1 := by
  have hn' : a ^ 2 + (-b) ^ 2 = (p : ℤ) := by rw [neg_sq]; exact hn
  have hpv := natCast_mem_split hn hv
  have hpw := natCast_mem_split hn' hw
  have hdv : (((p * m : ℕ)) : 𝓞 K) ∈ v.asIdeal := by
    rw [Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ hpv
  have hdw : (((p * m : ℕ)) : 𝓞 K) ∈ w.asIdeal := by
    rw [Nat.cast_mul]
    exact w.asIdeal.mul_mem_right _ hpw
  have h2v : (2 : 𝓞 K) ∉ v.asIdeal := two_not_mem v (by omega) hpv
  have h2w : (2 : 𝓞 K) ∉ w.asIdeal := two_not_mem w (by omega) hpw
  have hj := sigJ_sq (K := K)
  have hs0 : ((Real.sqrt p : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero, Real.sqrt_eq_zero (Nat.cast_nonneg p)]
    exact Nat.cast_ne_zero.2 hp.out.ne_zero
  have hss : ((Real.sqrt p : ℝ) : ℂ) ^ 2 = p := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg p), Complex.ofReal_natCast]
  have hnC : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = p := by exact_mod_cast congrArg (Int.cast : ℤ → ℂ) hn
  have hnv : ‖(a : ℂ) + (b : ℂ) * sigJ K‖ = Real.sqrt p := by
    rw [norm_add_mul_of_sq hj, hn, Int.cast_natCast]
  have hnw : ‖(a : ℂ) + ((-b : ℤ) : ℂ) * sigJ K‖ = Real.sqrt p := by
    rw [norm_add_mul_of_sq hj, hn', Int.cast_natCast]
  have hprod : sigma K (genK K v) / ((‖sigma K (genK K v)‖ : ℝ) : ℂ) *
      (sigma K (genK K w) / ((‖sigma K (genK K w)‖ : ℝ) : ℂ)) = 1 := by
    unfold genK
    rw [gen_eq_of_primary h2v hab hv, gen_eq_of_primary h2w hab' hw, sigma_gaussOf,
      sigma_gaussOf, hnv, hnw, div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero hs0 hs0)]
    push_cast
    linear_combination hnC - hss - (b : ℂ) ^ 2 * hj
  have heq := stdRootNumberAt_twC_split_eq hp1 hab hn hodd hsq hd hab' hv hw hNv hNw
  have hsq1 := stdRootNumberAt_twC_split_sq hp1 hab hn hv hodd hsq hd
  rw [stdRootNumberAt_cmCharTw_of_mem hodd hsq hd hdv,
    stdRootNumberAt_cmCharTw_of_mem hodd hsq hd hdw, ← heq]
  linear_combination
    (stdRootNumberAt K v (localChar (twC K hodd hsq hd) v)) ^ 2 * hprod + hsq1

end CMPoints
