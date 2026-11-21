import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.Conjugates
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-! Independent statements for paper.tex, §v02-05, Theorem
`thm:fenchel-moreau` and its proper-conjugate consequence. The dual is the
continuous dual for the given topology; suprema have full `EReal` values.
The primal `WithTop ℝ` values exclude minus infinity by construction. -/
noncomputable section
universe u
namespace VariationalNotes.ConvexAnalysis.Specs

/-- Equality also at points outside the effective domain. -/
def fenchel_moreau : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [T2Space X]
    [LocallyConvexSpace ℝ X],
  ∀ (f : X → WithTop ℝ), Proper f → IsConvex f → IsLowerSemicontinuous f →
    ∀ x, toEReal (f x) = biconjugate f x

/-- The supremum is over all continuous affine real minorants. -/
def affine_minorant_representation : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [T2Space X]
    [LocallyConvexSpace ℝ X],
  ∀ (f : X → WithTop ℝ), Proper f → IsConvex f → IsLowerSemicontinuous f →
    ∀ x, toEReal (f x) =
      ⨆ (y : X →L[ℝ] ℝ) (b : ℝ)
        (_ : ∀ z, ((y z + b : ℝ) : WithTop ℝ) ≤ f z), ((y x + b : ℝ) : EReal)

def exists_affine_minorant : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [T2Space X]
    [LocallyConvexSpace ℝ X],
  ∀ (f : X → WithTop ℝ), Proper f → IsConvex f → IsLowerSemicontinuous f →
    ∃ (y : X →L[ℝ] ℝ) (b : ℝ), ∀ z, ((y z + b : ℝ) : WithTop ℝ) ≤ f z

/-- Properness for the full extended-real conjugate: no minus-infinite value,
and a finite value somewhere. -/
def conjugate_proper : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [T2Space X]
    [LocallyConvexSpace ℝ X],
  ∀ (f : X → WithTop ℝ), Proper f → IsConvex f → IsLowerSemicontinuous f →
    (∀ y, conjugate f y ≠ ⊥) ∧ ∃ (y : X →L[ℝ] ℝ) (r : ℝ), conjugate f y = (r : EReal)

end VariationalNotes.ConvexAnalysis.Specs
