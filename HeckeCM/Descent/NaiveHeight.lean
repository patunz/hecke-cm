import Mathlib
import HeckeCM.Descent.AddSubMap

/-!
# The naive height and the approximate parallelogram law

For an elliptic curve `W` over a field `K` with a theory of heights:

* `naiveHeight`: the logarithmic height of the `x`-coordinate of a point;
* `abs_naiveHeight_add_sub_le`: there is `C` with
  `|h(P+Q) + h(P-Q) - 2(h(P) + h(Q))| ≤ C` for all `P`, `Q`;
* `northcott_naiveHeight`: the points of bounded height are finite in number;
* `fg_of_finiteIndex`: if `E(K)/2E(K)` is finite, `E(K)` is finitely generated;
* `finite_torsion`: the torsion of `E(K)` is finite, with no hypothesis.

Mathlib has the key lemma on the sum-difference map and the abstract descent
theorem; the rest was marked TODO.
-/

open WeierstrassCurve MvPolynomial Height
open Affine Affine.Point

namespace BSD

variable {K : Type*} [Field K] [DecidableEq K] [AdmissibleAbsValues K]
  (W : WeierstrassCurve K) [W.IsElliptic]

/-- The naive height of a point: the logarithmic height of its `x`-coordinate. -/
noncomputable def naiveHeight (P : W.toAffine.Point) : ℝ := logHeight P.xRep

lemma naiveHeight_nonneg (P : W.toAffine.Point) : 0 ≤ naiveHeight W P := logHeight_nonneg _

lemma naiveHeight_some {x y : K} (h : W.toAffine.Nonsingular x y) :
    naiveHeight W (some x y h) = logHeight₁ x := by
  rw [naiveHeight, xRep_some, logHeight₁_eq_logHeight]

section Simmetrico

/-- The three linear forms giving `sym2x` from the vector of products. -/
noncomputable def symForms : Fin 3 → MvPolynomial (Fin 2 × Fin 2) K :=
  ![X (0, 0), X (0, 1) + X (1, 0), X (1, 1)]

/-- The coefficients recovering the squares of the products from the forms `symForms`. -/
noncomputable def symCoeff : (Fin 2 × Fin 2) × Fin 3 → MvPolynomial (Fin 2 × Fin 2) K :=
  fun a => match a with
    | ((0, 0), 0) => X (0, 0)
    | ((0, 1), 0) => -X (1, 1)
    | ((0, 1), 1) => X (0, 1)
    | ((1, 0), 0) => -X (1, 1)
    | ((1, 0), 1) => X (1, 0)
    | ((1, 1), 2) => X (1, 1)
    | _ => 0

lemma isHomogeneous_symForms (j : Fin 3) : (symForms (K := K) j).IsHomogeneous 1 := by
  fin_cases j
  · exact isHomogeneous_X _ _
  · exact (isHomogeneous_X _ _).add (isHomogeneous_X _ _)
  · exact isHomogeneous_X _ _

lemma isHomogeneous_symCoeff (a : (Fin 2 × Fin 2) × Fin 3) :
    (symCoeff (K := K) a).IsHomogeneous 1 := by
  obtain ⟨⟨i, j⟩, k⟩ := a
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    first
      | exact isHomogeneous_X _ _
      | exact (isHomogeneous_X _ _).neg
      | exact isHomogeneous_zero _ _ _

/-- The vector of products `p i * q j`. -/
def prodVec (p q : Fin 2 → K) : Fin 2 × Fin 2 → K := fun a => p a.1 * q a.2

lemma symForms_eval (P Q : W.toAffine.Point) :
    (fun j => (symForms j).eval (prodVec P.xRep Q.xRep)) = P.sym2x Q := by
  ext j
  fin_cases j <;> simp [symForms, prodVec, sym2x]

lemma symCoeff_condition (p q : Fin 2 → K) (k : Fin 2 × Fin 2) :
    ∑ j, (symCoeff (k, j)).eval (prodVec p q) * (symForms j).eval (prodVec p q) =
      (prodVec p q k) ^ (1 + 1) := by
  obtain ⟨i, j⟩ := k
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_three, symCoeff, symForms, prodVec] <;> ring

/-- The height of `sym2x P Q` is `h(P) + h(Q)` up to a constant. -/
theorem abs_logHeight_sym2x_sub_le :
    ∃ C, ∀ P Q : W.toAffine.Point,
      |logHeight (P.sym2x Q) - (naiveHeight W P + naiveHeight W Q)| ≤ C := by
  obtain ⟨C₁, h₁⟩ := logHeight_eval_le' (K := K) (N := 1) isHomogeneous_symForms
  obtain ⟨C₂, h₂⟩ := logHeight_eval_ge' (K := K) (M := 1) (N := 1) isHomogeneous_symCoeff
  refine ⟨max C₁ (-C₂), fun P Q => ?_⟩
  have hz : logHeight (prodVec P.xRep Q.xRep) = naiveHeight W P + naiveHeight W Q :=
    logHeight_fun_mul_eq (xRep_ne_zero P) (xRep_ne_zero Q)
  have hle := h₁ (prodVec P.xRep Q.xRep)
  have hge := h₂ symForms (x := prodVec P.xRep Q.xRep) (symCoeff_condition _ _)
  rw [symForms_eval, hz] at hle hge
  rw [abs_sub_le_iff]
  constructor
  · have := le_max_left C₁ (-C₂); push_cast at hle; linarith
  · have := le_max_right C₁ (-C₂); push_cast at hge; linarith

end Simmetrico

/-- **Approximate parallelogram law** for the naive height. -/
theorem abs_naiveHeight_add_sub_le :
    ∃ C, ∀ P Q : W.toAffine.Point,
      |naiveHeight W (P + Q) + naiveHeight W (P - Q) -
        2 * (naiveHeight W P + naiveHeight W Q)| ≤ C := by
  obtain ⟨C₁, h₁⟩ := abs_logHeight_sym2x_sub_le W
  obtain ⟨C₂, h₂⟩ := abs_logHeight_addSubMap_sub_two_mul_logHeight_le W
  refine ⟨3 * C₁ + C₂, fun P Q => ?_⟩
  obtain ⟨c, hc, hF⟩ := addSubSpec W P Q
  have e : logHeight (fun i => (W.addSubMap i).eval (P.sym2x Q)) =
      logHeight ((P + Q).sym2x (P - Q)) := by
    rw [hF, logHeight_smul_eq_logHeight _ hc]
  have a1 := abs_sub_le_iff.1 (h₁ P Q)
  have a2 := abs_sub_le_iff.1 (h₁ (P + Q) (P - Q))
  have a3 := abs_sub_le_iff.1 (h₂ (P.sym2x Q))
  rw [e] at a3
  rw [abs_sub_le_iff]
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]

section Finitezza

variable [Northcott (logHeight₁ (K := K))]

/-- The points of bounded naive height are finite in number. -/
instance northcott_naiveHeight : Northcott (naiveHeight W) where
  finite_le B := by
    classical
    have hS : {x : K | logHeight₁ x ≤ B}.Finite := Northcott.finite_le B
    -- for each `x` there are at most two `y`
    have hy : ∀ x : K, {y : K | W.toAffine.Equation x y}.Finite := by
      intro x
      by_cases hne : ∃ y, W.toAffine.Equation x y
      · obtain ⟨y₁, hy₁⟩ := hne
        refine ((Set.finite_singleton (W.toAffine.negY x y₁)).insert y₁).subset ?_
        intro y hy
        rcases Affine.Y_eq_of_X_eq hy hy₁ rfl with h | h
        · exact Or.inl h
        · exact Or.inr h
      · have : {y : K | W.toAffine.Equation x y} = ∅ := by
          ext y; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          exact fun h => hne ⟨y, h⟩
        rw [this]; exact Set.finite_empty
    let g : W.toAffine.Point → Option (K × K) := fun P =>
      match P with
      | .zero => none
      | .some x y _ => some (x, y)
    have hg : Function.Injective g := by
      rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) hPQ
      · rfl
      · cases hPQ
      · cases hPQ
      · simp only [g, Option.some.injEq, Prod.mk.injEq] at hPQ
        obtain ⟨rfl, rfl⟩ := hPQ
        rfl
    let T : Set (Option (K × K)) :=
      insert none (Option.some '' (⋃ x ∈ {x : K | logHeight₁ x ≤ B},
        (fun y => (x, y)) '' {y : K | W.toAffine.Equation x y}))
    have hT : T.Finite :=
      ((hS.biUnion fun x _ => (hy x).image _).image _).insert _
    refine (hT.preimage hg.injOn).subset ?_
    rintro (_ | ⟨x, y, h⟩) hP
    · exact Set.mem_insert _ _
    · refine Set.mem_insert_of_mem _ ⟨(x, y), ?_, rfl⟩
      rw [Set.mem_ofPred_eq, naiveHeight_some] at hP
      exact Set.mem_biUnion hP ⟨y, h.1, rfl⟩

/-- **Mordell–Weil from weak Mordell–Weil.** If `2E(K)` has finite index
in `E(K)`, then `E(K)` is finitely generated. -/
theorem fg_of_finiteIndex
    (h : (nsmulAddMonoidHom (α := W.toAffine.Point) 2).range.FiniteIndex) :
    AddGroup.FG W.toAffine.Point := by
  obtain ⟨C, hC⟩ := abs_naiveHeight_add_sub_le W
  exact AddCommGroup.fg_of_descent' h (naiveHeight_nonneg W) hC

/-- **The torsion of `E(K)` is finite.** -/
theorem finite_torsion : Finite (AddCommGroup.torsion W.toAffine.Point) := by
  obtain ⟨C, hC⟩ := abs_naiveHeight_add_sub_le W
  exact AddCommGroup.finite_torsion_of_descent' hC

end Finitezza

end BSD
