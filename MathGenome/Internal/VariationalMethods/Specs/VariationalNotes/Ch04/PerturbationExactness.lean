import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch04.PerturbationAlgebra

/-! The pointwise exactness criterion and the complete perturbation-duality
 theorem (paper.tex, §v04-01, Theorem thm:perturbation-duality).
 The marginal and the continuous dual use the original topology of Y.
 Lower semicontinuity is required only at zero; no maximizer is asserted. -/
noncomputable section
universe u v
namespace VariationalNotes.Ch04.Specs
open VariationalNotes.ConvexAnalysis.Specs

def perturbation_exactness : Prop :=
  ∀ {X : Type u} {Y : Type v}
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [T2Space X] [LocallyConvexSpace ℝ X]
    [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [T2Space Y] [LocallyConvexSpace ℝ Y]
    (Φ : X × Y → WithTop ℝ), Proper Φ → IsConvex Φ →
    ExtendedProper (marginal Φ) → ∀ p : ℝ, marginal Φ 0 = (p : EReal) →
    (perturbationDualValue Φ = (p : EReal) ↔
      LowerSemicontinuousAt (marginal Φ) 0)

def perturbation_duality : Prop :=
  ∀ {X : Type u} {Y : Type v}
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [T2Space X] [LocallyConvexSpace ℝ X]
    [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [T2Space Y] [LocallyConvexSpace ℝ Y]
    (Φ : X × Y → WithTop ℝ), Proper Φ → IsConvex Φ →
    ExtendedProper (marginal Φ) → ∀ p : ℝ, marginal Φ 0 = (p : EReal) →
    ((∀ y : Y →L[ℝ] ℝ,
      marginalConjugate Φ y = conjugate Φ (y.comp (ContinuousLinearMap.snd ℝ X Y))) ∧
    perturbationDualValue Φ = extendedBiconjugate (marginal Φ) 0 ∧
    extendedBiconjugate (marginal Φ) 0 ≤ (p : EReal) ∧
    (∀ y : Y →L[ℝ] ℝ,
      ((perturbationDualObjective Φ y = (p : EReal) ∧
          perturbationDualValue Φ = (p : EReal)) ↔
        y ∈ subdifferential (marginalFunction Φ) 0) ∧
      (y ∈ subdifferential (marginalFunction Φ) 0 ↔
        ∀ u, ((p + y u : ℝ) : EReal) ≤ marginal Φ u))) ∧
    (perturbationDualValue Φ = (p : EReal) ↔
      LowerSemicontinuousAt (marginal Φ) 0)

end VariationalNotes.Ch04.Specs
