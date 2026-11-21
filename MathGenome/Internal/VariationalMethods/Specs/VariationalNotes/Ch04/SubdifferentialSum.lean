import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch04.BanachFenchel
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch04.FiniteFenchel
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.Subgradients
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-! Independent statements for the sum clause of `thm:exact-subdiff`
(paper.tex §v04-04) and its normal-intersection consequence. The finite-dimensional
statement uses the given Hausdorff vector topology. Neither statement assumes
lower semicontinuity or existence of subgradients of either summand. -/
noncomputable section
open Set
open scoped Pointwise Topology
universe u
namespace VariationalNotes.Ch04.Specs
open VariationalNotes.ConvexAnalysis.Specs
open VariationalNotes.ConvexGeometry.Specs

def subdifferential_sum_banach : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (f g : X → WithTop ℝ),
    Proper f → IsConvex f → Proper g → IsConvex g →
    (∃ x₀ : X, x₀ ∈ effectiveDomain f ∧ x₀ ∈ effectiveDomain g ∧ ContinuousAt g x₀) →
    ∀ x ∈ effectiveDomain f, x ∈ effectiveDomain g →
      subdifferential (fun z => f z + g z) x = subdifferential f x + subdifferential g x

def subdifferential_sum_finite : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [T2Space X] [FiniteDimensional ℝ X]
    (f g : X → WithTop ℝ),
    Proper f → IsConvex f → Proper g → IsConvex g →
    (relativeInterior (effectiveDomain f) ∩ relativeInterior (effectiveDomain g)).Nonempty →
    ∀ x ∈ effectiveDomain f, x ∈ effectiveDomain g →
      subdifferential (fun z => f z + g z) x = subdifferential f x + subdifferential g x

def normalCone_inter_banach : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (C D : Set X), C.Nonempty → Convex ℝ C → D.Nonempty → Convex ℝ D →
    (∃ z ∈ C, D ∈ 𝓝 z) → ∀ x ∈ C ∩ D,
      normalCone (C ∩ D) x = normalCone C x + normalCone D x

def normalCone_inter_finite : Prop :=
  ∀ {X : Type u} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [T2Space X] [FiniteDimensional ℝ X]
    (C D : Set X), C.Nonempty → Convex ℝ C → D.Nonempty → Convex ℝ D →
    (relativeInterior C ∩ relativeInterior D).Nonempty → ∀ x ∈ C ∩ D,
      normalCone (C ∩ D) x = normalCone C x + normalCone D x

end VariationalNotes.Ch04.Specs
