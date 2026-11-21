import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.ReducedHessian
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

namespace VariationalNotes.Ch05

open Matrix

variable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
  (Q : Matrix (Fin n) (Fin n) ℝ)

/-- The saddle point block matrix as an endomorphism of the product space. -/
def kktMap : ((Fin n → ℝ) × (Fin m → ℝ)) →ₗ[ℝ]
    ((Fin n → ℝ) × (Fin m → ℝ)) :=
  ((Q.mulVecLin.comp (LinearMap.fst ℝ _ _) +
    Aᵀ.mulVecLin.comp (LinearMap.snd ℝ _ _))).prod
    (A.mulVecLin.comp (LinearMap.fst ℝ _ _))

@[simp] theorem kktMap_apply (z : (Fin n → ℝ) × (Fin m → ℝ)) :
    kktMap A Q z = (Q *ᵥ z.1 + Aᵀ *ᵥ z.2, A *ᵥ z.1) := rfl

theorem kktMap_injective
    (hA : LinearIndependent ℝ (fun i => fun j => A i j))
    (hpos : ∀ u : Fin n → ℝ, A *ᵥ u = 0 → u ≠ 0 → 0 < u ⬝ᵥ (Q *ᵥ u)) :
    Function.Injective (kktMap A Q) := by
  have hAT : Function.Injective Aᵀ.mulVec :=
    Matrix.mulVec_injective_iff.mpr hA
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  have h1 : Q *ᵥ z.1 + Aᵀ *ᵥ z.2 = 0 := congrArg Prod.fst hz
  have h2 : A *ᵥ z.1 = 0 := congrArg Prod.snd hz
  have hdot : z.1 ⬝ᵥ (Q *ᵥ z.1) = 0 := by
    have h := congrArg (fun v => z.1 ⬝ᵥ v) h1
    rw [dotProduct_add, dotProduct_transpose_mulVec, h2] at h
    simpa using h
  have hu : z.1 = 0 := by
    by_contra hu
    have hp := hpos z.1 h2 hu
    rw [hdot] at hp
    exact lt_irrefl _ hp
  have hv : z.2 = 0 := hAT (by simpa [hu] using h1)
  exact Prod.ext hu hv

theorem quadraticObjective_add (hQ : Q.IsSymm) (c x u : Fin n → ℝ) :
    quadraticObjective Q c (x + u) = quadraticObjective Q c x +
      (Q *ᵥ x + c) ⬝ᵥ u + (u ⬝ᵥ (Q *ᵥ u)) / 2 := by
  have hcross : x ⬝ᵥ (Q *ᵥ u) = u ⬝ᵥ (Q *ᵥ x) := by
    simpa only [hQ.eq] using dotProduct_transpose_mulVec Q x u
  simp only [quadraticObjective, mulVec_add, dotProduct_add, add_dotProduct]
  rw [hcross, dotProduct_comm (Q *ᵥ x) u, dotProduct_comm c u]
  ring

/-- On the feasible affine space the KKT equations remove the entire linear
term from the quadratic expansion. -/
theorem objective_gap_of_kkt (hQ : Q.IsSymm)
    {b : Fin m → ℝ} {c : Fin n → ℝ}
    {z : (Fin n → ℝ) × (Fin m → ℝ)} (hz : IsKKTSolution A Q b c z)
    {y : Fin n → ℝ} (hy : A *ᵥ y = b) :
    quadraticObjective Q c y = quadraticObjective Q c z.1 +
      ((y - z.1) ⬝ᵥ (Q *ᵥ (y - z.1))) / 2 := by
  have hu : A *ᵥ (y - z.1) = 0 := by
    rw [mulVec_sub, hy, hz.2, sub_self]
  have hlinear : (Q *ᵥ z.1 + c) ⬝ᵥ (y - z.1) = 0 := by
    have h := congrArg (fun v => (y - z.1) ⬝ᵥ v) hz.1
    rw [dotProduct_add, dotProduct_transpose_mulVec, hu, dotProduct_zero,
      dotProduct_neg] at h
    rw [dotProduct_comm, dotProduct_add]
    linarith
  calc
    quadraticObjective Q c y = quadraticObjective Q c (z.1 + (y - z.1)) := by
      rw [add_sub_cancel]
    _ = _ := by rw [quadraticObjective_add Q hQ, hlinear]; ring

theorem kkt_uniqueGlobalMinimizer
    (hQ : Q.IsSymm)
    (hpos : ∀ u : Fin n → ℝ, A *ᵥ u = 0 → u ≠ 0 → 0 < u ⬝ᵥ (Q *ᵥ u))
    {b : Fin m → ℝ} {c : Fin n → ℝ}
    {z : (Fin n → ℝ) × (Fin m → ℝ)} (hz : IsKKTSolution A Q b c z) :
    IsUniqueGlobalMinimizer A Q b c z.1 := by
  have hstrict : ∀ y, A *ᵥ y = b → y ≠ z.1 →
      quadraticObjective Q c z.1 < quadraticObjective Q c y := by
    intro y hy hne
    have hu : A *ᵥ (y - z.1) = 0 := by rw [mulVec_sub, hy, hz.2, sub_self]
    have hp := hpos (y - z.1) hu (sub_ne_zero.mpr hne)
    rw [objective_gap_of_kkt A Q hQ hz hy]
    linarith
  refine ⟨hz.2, ?_, ?_⟩
  · intro y hy
    by_cases heq : y = z.1
    · subst y; exact le_refl _
    · exact (hstrict y hy heq).le
  · intro y hy hle
    by_contra hne
    exact (not_lt_of_ge hle) (hstrict y hy hne)

/-- Equality constraints with a positive reduced Hessian have one KKT pair,
whose primal component is the unique global minimizer. -/
theorem reducedHessian : Specs.VariationalNotes.Ch05.ReducedHessianStatement := by
  intro m n A Q hA hQ hpos b c
  have hinj := kktMap_injective A Q hA hpos
  obtain ⟨z, hz⟩ := LinearMap.surjective_of_injective hinj (-c, b)
  have hsol : IsKKTSolution A Q b c z :=
    ⟨congrArg Prod.fst hz, congrArg Prod.snd hz⟩
  refine ⟨⟨z, hsol, ?_⟩, ?_⟩
  · intro w hw
    apply hinj
    exact (Prod.ext hw.1 hw.2).trans hz.symm
  · intro w hw
    exact kkt_uniqueGlobalMinimizer A Q hQ hpos hw

end VariationalNotes.Ch05
