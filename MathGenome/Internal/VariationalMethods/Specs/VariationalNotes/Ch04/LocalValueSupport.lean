import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch04.PerturbationModels
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Independent statement of paper.tex, Lemma `lem:local-value-support`.
The supporting inequality is the definition of a continuous subgradient of
an EReal-valued function at the specified finite value. Local finiteness is
recorded explicitly, so the real representative in the Lipschitz estimate
has no dependence on the convention for `EReal.toReal` at infinity. -/
noncomputable section
open Set Topology
universe u v
namespace VariationalNotes.Ch04.Specs

def local_value_support : Prop :=
  ∀ {X : Type u} {Y : Type v} [AddCommGroup X] [Module ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Φ : X × Y → WithTop ℝ),
    ConvexAnalysis.Specs.Proper Φ → ConvexAnalysis.Specs.IsConvex Φ →
    ∀ (p r M : ℝ), marginal Φ 0 = (p : EReal) → 0 < r →
    (∀ u : Y, ‖u‖ < r → marginal Φ u ≤ (M : EReal)) →
    (∀ u, marginal Φ u ≠ ⊥) ∧
    (∃ U : Set Y, U ∈ 𝓝 (0 : Y) ∧ ∃ K : NNReal,
      (∀ u ∈ U, marginal Φ u = ((marginal Φ u).toReal : EReal)) ∧
      LipschitzOnWith K (fun u => (marginal Φ u).toReal) U) ∧
    (∃ y : Y →L[ℝ] ℝ, ∀ u, ((p + y u : ℝ) : EReal) ≤ marginal Φ u)

end VariationalNotes.Ch04.Specs
