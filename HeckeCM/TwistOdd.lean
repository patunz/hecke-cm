import HeckeCM.TwistFinal
import HeckeCM.CurveSquare

/-!
# The L-series of `y² = x³ − d²x` has an entire continuation, for every odd `d`

Every odd `d` is `d' m²` with `d'` odd and squarefree. The two curves have
the same L-series (`LFunction_curveD_mul_sq`) and for `d'` the continuation is
`entire_lseries_curveD`.
-/

/-- **The Mathlib L-series of `y² = x³ − d²x` over `ℚ` has an entire
continuation**, for every odd natural `d`. -/
theorem CMPoints.entire_lseries_curveD_of_odd {d : ℕ} (hodd : d % 2 = 1) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      ∀ s : ℂ, 3 / 2 < s.re →
        F s = (⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ).LSeries s := by
  obtain ⟨d', m, hmd, hsq⟩ := Nat.sq_mul_squarefree d
  have hd'odd : d' % 2 = 1 := by
    by_contra h
    have h0 : d' % 2 = 0 := by omega
    have : d % 2 = 0 := by
      rw [← hmd, Nat.mul_mod, h0]
      simp
    omega
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hmd
    omega
  obtain ⟨F, hF, h⟩ := CMPoints.entire_lseries_curveD hd'odd hsq
  refine ⟨F, hF, fun s hs => ?_⟩
  rw [h s hs]
  have e1 : (⟨0, 0, 0, -(d : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ) =
      CMPoints.curveD ℚ ((((d' : ℤ) * (m : ℤ) ^ 2 : ℤ)) : ℚ) := by
    have hq : (d : ℚ) = ((((d' : ℤ) * (m : ℤ) ^ 2 : ℤ)) : ℚ) := by
      rw [← hmd]
      push_cast
      ring
    rw [hq]
    rfl
  have e2 : (⟨0, 0, 0, -(d' : ℚ) ^ 2, 0⟩ : WeierstrassCurve ℚ) =
      CMPoints.curveD ℚ (((d' : ℤ) : ℤ) : ℚ) := by
    rw [Int.cast_natCast]
    rfl
  rw [e1, e2, WeierstrassCurve.LSeries, WeierstrassCurve.LSeries,
    CMPoints.LFunction_curveD_mul_sq (by exact_mod_cast Nat.odd_iff.2 hd'odd)
      (Int.squarefree_natCast.2 hsq) (by exact_mod_cast hm0)]
