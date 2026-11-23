import HeckeCM.Places
import HeckeCM.GenEuler

/-!
# From the product over the places of `ℚ(i)` to a CM-type sequence

`IsGenEulerDatum K B a c` describes the local values `c_v` of a Hecke character
whose Euler product is the Dirichlet series of `gCoeff B a`, and
`hasProd_places_of_isGenEulerDatum` groups the places by rational prime. The
sequence `cmCoeff` is the case `B = (· = 2)`, `a = cmPrime` (`cmCoeff_eq_gCoeff`).
-/

open IsDedekindDomain NumberField

namespace CMPoints

variable (K : Type) [Field K] [NumberField K]

/-- The local values of a Hecke character of `ℚ(i)` whose Euler product
is the Dirichlet series of `gCoeff B a`. -/
structure IsGenEulerDatum (B : ℕ → Prop) (a : ℕ → ℤ) (c : HeightOneSpectrum (𝓞 K) → ℂ) :
    Prop where
  /-- the values have modulus at most 1 -/
  norm_le : ∀ v, ‖c v‖ ≤ 1
  /-- above a bad prime the factor is trivial -/
  bad : ∀ p : ℕ, p.Prime → B p → ∀ v, ((p : ℕ) : 𝓞 K) ∈ v.asIdeal → c v = 0
  /-- a good prime `p ≡ 3 (mod 4)`: a single place, of norm `p²`, value `-1` -/
  inert : ∀ p : ℕ, p.Prime → ¬ B p → p % 4 = 3 →
    ∃ v, (∀ u, ((p : ℕ) : 𝓞 K) ∈ u.asIdeal ↔ u = v) ∧ Ideal.absNorm v.asIdeal = p ^ 2 ∧ c v = -1
  /-- a good prime `p ≡ 1 (mod 4)`: two places of norm `p`, with given sum and product -/
  split : ∀ p : ℕ, p.Prime → ¬ B p → p % 4 = 1 →
    ∃ v w, v ≠ w ∧ (∀ u, ((p : ℕ) : 𝓞 K) ∈ u.asIdeal ↔ u = v ∨ u = w) ∧
      Ideal.absNorm v.asIdeal = p ∧ Ideal.absNorm w.asIdeal = p ∧
      c v + c w = (a p : ℂ) * (p : ℂ) ^ (-(1 / 2 : ℂ)) ∧ c v * c w = 1

variable {K} {B : ℕ → Prop} [DecidablePred B] {a : ℕ → ℤ}

/-- The product over the places above `p` is the factor `gFactor B a p (s + 1/2)`. -/
theorem prod_fibre_eq_gFactor {c : HeightOneSpectrum (𝓞 K) → ℂ} (hc : IsGenEulerDatum K B a c)
    (hB2 : B 2) (ha3 : ∀ p : ℕ, p.Prime → p % 4 = 3 → a p = 0)
    (p : Nat.Primes) (s : ℂ) [Fintype {v : HeightOneSpectrum (𝓞 K) // under K v = p}] :
    ∏ v : {v : HeightOneSpectrum (𝓞 K) // under K v = p},
        (1 - c v.1 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ =
      gFactor B a p (s + 1 / 2) := by
  classical
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  set x : ℂ := ((p : ℕ) : ℂ) ^ (-s) with hx
  have hy : ((p : ℕ) : ℂ) ^ (-(s + 1 / 2)) = x * ((p : ℕ) : ℂ) ^ (-(1 / 2 : ℂ)) := by
    rw [hx, ← Complex.cpow_add _ _ hp0]
    congr 1
    ring
  have hhalf : (((p : ℕ) : ℂ) ^ (-(1 / 2 : ℂ))) ^ 2 * ((p : ℕ) : ℂ) = 1 := by
    rw [← Complex.cpow_nat_mul]
    have : ((2 : ℕ) : ℂ) * (-(1 / 2 : ℂ)) = -1 := by push_cast; ring
    rw [this, Complex.cpow_neg_one, inv_mul_cancel₀ hp0]
  by_cases hb : B p
  · -- above a bad prime every factor is 1
    rw [gFactor, if_pos hb]
    refine Finset.prod_eq_one fun v _ => ?_
    rw [hc.bad p p.2 hb v.1 ((under_eq_iff K v.1 p).1 v.2)]
    simp
  · have hne2 : (p : ℕ) ≠ 2 := fun h => hb (h ▸ hB2)
    have hodd : (p : ℕ) % 2 = 1 := (p.2.eq_two_or_odd).resolve_left hne2
    rw [gFactor, if_neg hb, hy]
    rcases (by omega : (p : ℕ) % 4 = 1 ∨ (p : ℕ) % 4 = 3) with h1 | h3
    · obtain ⟨v, w, hvw, hmem, hNv, hNw, hsum, hprod⟩ := hc.split p p.2 hb h1
      have hset : ∀ u : HeightOneSpectrum (𝓞 K), u ∈ ({v, w} : Finset _) ↔ under K u = p := by
        intro u
        rw [under_eq_iff, hmem, Finset.mem_insert, Finset.mem_singleton]
      rw [← Finset.prod_subtype ({v, w} : Finset (HeightOneSpectrum (𝓞 K))) hset
        (fun u => (1 - c u * ((Ideal.absNorm u.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹),
        Finset.prod_pair hvw, hNv, hNw, ← mul_inv]
      congr 1
      linear_combination (-x) * hsum + x ^ 2 * hprod - (((p : ℕ) : ℂ) ^ (-(1 / 2 : ℂ))) ^ 2 * 0
        - x ^ 2 * hhalf
    · obtain ⟨v, hmem, hNv, hcv⟩ := hc.inert p p.2 hb h3
      have hset : ∀ u : HeightOneSpectrum (𝓞 K), u ∈ ({v} : Finset _) ↔ under K u = p := by
        intro u
        rw [under_eq_iff, hmem, Finset.mem_singleton]
      have hcm : a p = 0 := ha3 p p.2 h3
      have hsq : ((((p : ℕ) ^ 2 : ℕ) : ℂ)) ^ (-s) = x ^ 2 := by
        rw [hx, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
      rw [← Finset.prod_subtype ({v} : Finset (HeightOneSpectrum (𝓞 K))) hset
        (fun u => (1 - c u * ((Ideal.absNorm u.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹),
        Finset.prod_singleton, hNv, hcv, hsq, hcm]
      congr 1
      push_cast
      linear_combination (-(x ^ 2)) * hhalf

/-- **From the product over the places to the Dirichlet series of the sequence.** -/
theorem hasProd_places_of_isGenEulerDatum {c : HeightOneSpectrum (𝓞 K) → ℂ}
    (hc : IsGenEulerDatum K B a c) (hB2 : B 2) (ha3 : ∀ p : ℕ, p.Prime → p % 4 = 3 → a p = 0)
    (ha : ∀ p : ℕ, p.Prime → a p ^ 2 ≤ 4 * p) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) =>
        (1 - c v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
      (LSeries (fun n => ((gCoeff B a n : ℤ) : ℂ)) (s + 1 / 2)) := by
  classical
  -- multipliability over the places, from the Fermat repository with `S = ∅`
  obtain ⟨hmult, -, -⟩ := NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
    K ∅ (fun v => c v.1) (fun v => hc.norm_le v.1)
  let e : {v : HeightOneSpectrum (𝓞 K) // v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 K)))} ≃
      HeightOneSpectrum (𝓞 K) :=
    Equiv.subtypeUnivEquiv (fun v => Finset.notMem_empty v)
  have hmult' : Multipliable (fun v : HeightOneSpectrum (𝓞 K) =>
      (1 - c v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) := by
    have := hmult s hs
    exact (e.multipliable_iff (f := fun v : HeightOneSpectrum (𝓞 K) =>
      (1 - c v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)).1 this
  have hprod := hmult'.hasProd
  -- grouping by rational prime
  have h2 := (Equiv.hasProd_iff (Equiv.sigmaFiberEquiv (under K))).2 hprod
  have h3 : HasProd (fun p : Nat.Primes => gFactor B a p (s + 1 / 2))
      (∏' v : HeightOneSpectrum (𝓞 K), (1 - c v * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) := by
    refine h2.sigma fun p => ?_
    haveI : Fintype {v : HeightOneSpectrum (𝓞 K) // under K v = p} :=
      @Fintype.ofFinite _ (finite_fibre K p)
    have := hasProd_fintype (fun v : {v : HeightOneSpectrum (𝓞 K) // under K v = p} =>
      (1 - c v.1 * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
    rw [prod_fibre_eq_gFactor hc hB2 ha3 p s] at this
    exact this
  have h4 := hasProd_gFactor (B := B) ha (s := s + 1 / 2) (by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
    linarith)
  rw [← h3.unique h4]
  exact hprod

end CMPoints
