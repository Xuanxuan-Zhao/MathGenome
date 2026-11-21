import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.ConfiningSchrodingerRealization
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Compactness and the full discrete inverse spectrum in
`fa2:p3:confining-potential`, over either manuscript scalar field. -/
noncomputable section
open MeasureTheory Set Filter
open scoped InnerProductSpace Topology

namespace ExpandedFA.Models.ConfiningCompactResolvent
open WeightedConfiningEnergySpace

/-- The potential tends to infinity at both ends of the real line. -/
def IsConfining (p : Potential) : Prop :=
  ∀ M : ℝ, ∃ R : ℝ, 0 < R ∧ ∀ x : ℝ, R ≤ |x| → M ≤ p.toContinuousMap x

/-- T solves the original variational problem on the actual weighted space. -/
def IsSolutionOperator {𝕜 : Type} [RCLike 𝕜] (p : Potential)
    (T : L2 𝕜 →L[𝕜] L2 𝕜) : Prop :=
  ∀ f : L2 𝕜, ∃ u : Space 𝕜 p, value u = T f ∧
    ∀ v : Space 𝕜 p, energyForm v u = ⟪value v, f⟫_𝕜

end ExpandedFA.Models.ConfiningCompactResolvent

namespace Specs.ExpandedFA.Models.ConfiningCompactResolvent
open _root_.ExpandedFA.Models.WeightedConfiningEnergySpace
open _root_.ExpandedFA.Models.ConfiningCompactResolvent

/-- Compactness of the actual inclusion V ↪ L². -/
def CompactInclusion : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (p : Potential), IsConfining p →
    IsCompactOperator (value (𝕜 := 𝕜) (p := p))

/-- Compactness holds for the already constructed variational solution. -/
def CompactSolutionOperator : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (p : Potential), IsConfining p →
    ∀ T : L2 𝕜 →L[𝕜] L2 𝕜, IsSolutionOperator p T → IsCompactOperator T

/-- A genuine countably infinite Hilbert basis, positive eigenvalues tending
to infinity, and the exact domain. The coefficient criterion describes exactly
those Hilbert expansions whose weighted square sum is finite. Graph membership
records both membership in D(A) and the equation Ae_n = λ_n e_n. -/
def DiscreteSpectrum : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (p : Potential), IsConfining p →
    ∀ T : L2 𝕜 →L[𝕜] L2 𝕜, IsSolutionOperator p T →
    ∀ A : L2 𝕜 →ₗ.[𝕜] L2 𝕜,
      (∀ u f : L2 𝕜, (u, f) ∈ A.graph ↔ T f = u) →
    ∃ (e : HilbertBasis ℕ 𝕜 (L2 𝕜)) (ev : ℕ → ℝ),
      (∀ n, 0 < ev n) ∧ Tendsto ev atTop atTop ∧
      (∀ n, (e n, (ev n : 𝕜) • e n) ∈ A.graph) ∧
      (∀ u : L2 𝕜, u ∈ A.domain ↔
        Summable (fun n => (ev n) ^ 2 * ‖⟪e n, u⟫_𝕜‖ ^ 2))

end Specs.ExpandedFA.Models.ConfiningCompactResolvent
