import Mathlib

open MeasureTheory Matrix BigOperators

namespace MaynardTaoCert

def simplex (k : ℕ) : Set (Fin k → ℝ) :=
  { t | (∀ i, 0 ≤ t i) ∧ (∑ i, t i) ≤ 1 }

structure SplineAtom where
  knot : ℚ
  knot_pos : 0 < knot
  knot_le_one : knot ≤ 1
  radDeg : ℕ
  part : List ℕ

noncomputable def I_func (k : ℕ) (F : (Fin k → ℝ) → ℝ) : ℝ :=
  ∫ t in simplex k, (F t) ^ 2

noncomputable def marginal (k : ℕ) (F : (Fin (k + 1) → ℝ) → ℝ)
    (m : Fin (k + 1)) (t : Fin k → ℝ) : ℝ :=
  ∫ u in Set.Icc (0 : ℝ) (1 - ∑ i, t i), F (Fin.insertNth m u t)

noncomputable def J_coord (k : ℕ) (F : (Fin (k + 1) → ℝ) → ℝ)
    (m : Fin (k + 1)) : ℝ :=
  ∫ t in simplex k, (marginal k F m t) ^ 2

/-- The support condition is needed even when a = 0. -/
lemma radial_spline_marginal_reduction
    (r S' : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (hS : 0 ≤ S')
    (hSr : S' ≤ r) (a d : ℕ) :
    (∫ u in Set.Icc (0 : ℝ) (1 - S'),
      if u ≤ r - S' then (r - S' - u) ^ a * u ^ d else 0) =
    ((Nat.factorial a : ℝ) * (Nat.factorial d : ℝ) /
      (Nat.factorial (a + d + 1) : ℝ)) *
      (r - S') ^ (a + d + 1) := by
  sorry

/-- Target: transfer a finite rational quadratic-form certificate to the integrals. -/
theorem rayleigh_cert_lower_bound
    {k N : ℕ} (φ : Fin N → (Fin (k + 1) → ℝ) → ℝ)
    (A_Q B_Q : Matrix (Fin N) (Fin N) ℚ)
    (v : Fin N → ℚ) (τ : ℚ)
    (hFiber : ∀ i m t, t ∈ simplex k →
      IntegrableOn (fun u => φ i (Fin.insertNth m u t))
        (Set.Icc (0 : ℝ) (1 - ∑ r, t r)))
    (hB_integrable : ∀ i j,
      IntegrableOn (fun t => φ i t * φ j t) (simplex (k + 1)))
    (hA_integrable : ∀ i j m,
      IntegrableOn (fun t => marginal k (φ i) m t * marginal k (φ j) m t)
        (simplex k))
    (hB_exact : ∀ i j,
      (∫ t in simplex (k + 1), φ i t * φ j t) = (B_Q i j : ℝ))
    (hA_exact : ∀ i j,
      (∑ m : Fin (k + 1), ∫ t in simplex k,
        marginal k (φ i) m t * marginal k (φ j) m t) = (A_Q i j : ℝ))
    (hI_pos : 0 < dotProduct v (B_Q.mulVec v))
    (hCert : τ * dotProduct v (B_Q.mulVec v) < dotProduct v (A_Q.mulVec v)) :
    let F : (Fin (k + 1) → ℝ) → ℝ := fun t => ∑ i, (v i : ℝ) * φ i t
    0 < I_func (k + 1) F ∧
      (τ : ℝ) * I_func (k + 1) F < ∑ m : Fin (k + 1), J_coord k F m := by
  sorry

end MaynardTaoCert
