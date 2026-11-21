import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch05.LinearProgramAttainment
import MathGenome.Internal.VariationalMethods.VariationalNotes.Ch05.LinearProgramModels
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexGeometry.PolyhedraElimination
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Order.IsLUB

noncomputable section
open Set Matrix
universe u v
namespace VariationalNotes.Ch05.LinearProgramAttainment

open VariationalNotes.ConvexGeometry
open VariationalNotes.Ch05.LinearProgramModels

/-- The standard-form feasible region is polyhedral, including in dimension zero. -/
lemma primalFeasible_polyhedron {m : Type u} {n : Type v} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) (b : m → ℝ) :
    IsPolyhedron {x | primalFeasible A b x} := by
  classical
  let row : n → ((n → ℝ) →ᵃ[ℝ] ℝ) :=
    fun i => -(LinearMap.proj i).toAffineMap
  have hpos : IsPolyhedron {x : n → ℝ | ∀ i, 0 ≤ x i} := by
    refine ⟨Finset.univ.image row, ?_⟩
    ext x
    simp [row]
  have heq := polyhedron_affine_preimage
    (A.mulVecLin.toAffineMap - AffineMap.const ℝ (n → ℝ) b)
    {0} (polyhedron_zero (E := m → ℝ))
  convert polyhedron_inter heq hpos using 1
  ext x
  change (A *ᵥ x = b ∧ ∀ i, 0 ≤ x i) ↔
    (A *ᵥ x - b ∈ ({0} : Set (m → ℝ)) ∧ ∀ i, 0 ≤ x i)
  simp only [mem_singleton_iff, sub_eq_zero]

/-- A linear objective maps the feasible polyhedron to a closed subset of the real line. -/
lemma primalObjective_image_isClosed {m : Type u} {n : Type v}
    [Fintype m] [Fintype n] (A : Matrix m n ℝ) (b : m → ℝ) (c : n → ℝ) :
    IsClosed (primalObjective c '' {x | primalFeasible A b x}) := by
  exact polyhedron_affine_image_isClosed
    (dotProductBilin ℝ ℝ c).toAffineMap _ (primalFeasible_polyhedron A b)

/-- A real primal value is attained by a primal feasible point. -/
theorem primal_attainment : Specs.primal_attainment.{u,v} := by
  intro m n _ _ A b c p hfeas hp
  change primalValue A b c = (p : EReal) at hp
  let S : Set ℝ := primalObjective c '' {x | primalFeasible A b x}
  have hne : S.Nonempty := by
    obtain ⟨x, hx⟩ := hfeas
    exact ⟨_, ⟨x, hx, rfl⟩⟩
  have hglb : IsGLB S p := by
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      have hle := primalValue_le A b c x hx
      change primalValue A b c ≤ (primalObjective c x : EReal) at hle
      rw [hp] at hle
      exact EReal.coe_le_coe_iff.mp hle
    · intro r hr
      have hle : (r : EReal) ≤ primalValue A b c := by
        apply le_sInf
        rintro _ ⟨x, hx, rfl⟩
        exact EReal.coe_le_coe (hr ⟨x, hx, rfl⟩)
      rw [hp] at hle
      exact EReal.coe_le_coe_iff.mp hle
  obtain ⟨x, hx, hxp⟩ := hglb.mem_of_isClosed hne
    (primalObjective_image_isClosed A b c)
  have hxopt : PrimalOptimal A b c x :=
    ⟨hx, hp.trans (congrArg (fun r : ℝ => (r : EReal)) hxp).symm⟩
  exact ⟨x, hxopt, hxp⟩

end VariationalNotes.Ch05.LinearProgramAttainment
