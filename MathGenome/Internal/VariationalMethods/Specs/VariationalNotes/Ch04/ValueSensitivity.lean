import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch04.PerturbationAlgebra
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Convex.Function

/-!
Independent specification of paper.tex, Proposition `prop:fenchel-sensitivity`
(2087–2110), with the conventions of `thm:perturbation-duality` (1698–1741).
A real representative `f` with `marginal Φ u = ↑(f u)` at every perturbation
expresses exactly the additional assumption that the proper marginal is finite
everywhere. `HasFDerivAt f D 0` specifies its Fréchet derivative; no differentiability
is inferred from equality of primal and dual values. The algebraic bound needs
only absence of minus infinity and a finite value at zero. The differentiable
conclusion needs no additional closedness or completeness hypothesis.
-/
noncomputable section
universe u v
namespace VariationalNotes.Ch04.Specs
open VariationalNotes.ConvexAnalysis.Specs

/-- A multiplier whose dual objective equals p supports the value globally. -/
def value_sensitivity_bound : Prop :=
  ∀ {X : Type u} {Y : Type v}
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]
    (Φ : X × Y → WithTop ℝ) (p : ℝ),
    (∀ u, marginal Φ u ≠ ⊥) → marginal Φ 0 = (p : EReal) →
    ∀ y : Y →L[ℝ] ℝ, perturbationDualObjective Φ y = (p : EReal) →
      ∀ u, ((p + y u : ℝ) : EReal) ≤ marginal Φ u

/-- The finite convex case, stated for an arbitrary real normed space. -/
def finite_convex_subdifferential : Prop :=
  ∀ {Y : Type v} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (f : Y → ℝ) (D : Y →L[ℝ] ℝ),
    ConvexOn ℝ Set.univ f → HasFDerivAt f D 0 →
    subdifferential (fun u => (f u : WithTop ℝ)) 0 = {D} ∧
      ∀ u, f 0 + D u ≤ f u

/-- The derivative is the global support and the unique multiplier attaining p.
The dual value equality records attainment as well as uniqueness. -/
def value_sensitivity_differentiable : Prop :=
  ∀ {X : Type u} {Y : Type v}
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Φ : X × Y → WithTop ℝ), IsConvex Φ →
    ∀ (f : Y → ℝ), (∀ u, marginal Φ u = (f u : EReal)) →
    ∀ D : Y →L[ℝ] ℝ, HasFDerivAt f D 0 →
      subdifferential (marginalFunction Φ) 0 = {D} ∧
      (∀ u, ((f 0 + D u : ℝ) : EReal) ≤ marginal Φ u) ∧
      perturbationDualObjective Φ D = (f 0 : EReal) ∧
      perturbationDualValue Φ = (f 0 : EReal) ∧
      (∀ y : Y →L[ℝ] ℝ,
        perturbationDualObjective Φ y = (f 0 : EReal) ↔ y = D)

end VariationalNotes.Ch04.Specs
