import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch04.SubdifferentialSum

/-! Independent statements of the affine-chain clause and the complete
sum-and-chain theorem, paper.tex, Theorem `thm:exact-subdiff`. -/
noncomputable section
open Set
universe u v
namespace VariationalNotes.Ch04.Specs
open VariationalNotes.ConvexAnalysis.Specs
open VariationalNotes.ConvexGeometry.Specs

def subdifferential_affine_chain_banach : Prop :=
  ∀ {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (A : X →L[ℝ] Y) (b : Y) (g : Y → WithTop ℝ),
    Proper g → IsConvex g →
    (∃ x₀ : X, A x₀ + b ∈ effectiveDomain g ∧ ContinuousAt g (A x₀ + b)) →
    ∀ x : X, A x + b ∈ effectiveDomain g →
      subdifferential (fun z => g (A z + b)) x =
        (fun y : Y →L[ℝ] ℝ => y.comp A) '' subdifferential g (A x + b)

def subdifferential_affine_chain_finite : Prop :=
  ∀ {X : Type u} {Y : Type v}
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [T2Space X] [FiniteDimensional ℝ X]
    [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [T2Space Y] [FiniteDimensional ℝ Y]
    (A : X →ₗ[ℝ] Y) (b : Y) (g : Y → WithTop ℝ),
    Proper g → IsConvex g →
    (range (fun z => A z + b) ∩ relativeInterior (effectiveDomain g)).Nonempty →
    ∀ x : X, A x + b ∈ effectiveDomain g →
      subdifferential (fun z => g (A z + b)) x =
        (fun y : Y →L[ℝ] ℝ => y.comp A.toContinuousLinearMap) ''
          subdifferential g (A x + b)

def exact_subdifferential_rules : Prop :=
  subdifferential_sum_banach.{u} ∧ subdifferential_sum_finite.{u} ∧
  subdifferential_affine_chain_banach.{u,v} ∧ subdifferential_affine_chain_finite.{u,v}

end VariationalNotes.Ch04.Specs
