import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.WeightedConfiningEnergySpace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! The realization clause of `fa2:p3:confining-potential`. Compactness and
spectral discreteness are separate obligations. The second derivative below
acts on compactly supported smooth tests, and imposes no H² assumption. -/
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped InnerProductSpace ComplexConjugate

namespace ExpandedFA.Models.ConfiningSchrodingerRealization
open ExpandedFA.Models.WeightedConfiningEnergySpace
open ExpandedFA.Sobolev ExpandedFA.Distributions

/-- The distributional equality −u″ + pu = f. Multiplication by the merely
continuous potential is applied to the locally integrable function u, rather
than to an arbitrary distribution. Tests and distributions are scalar-linear. -/
def DistributionEquation {𝕜 : Type} [RCLike 𝕜] {p : Potential}
    (u : Space 𝕜 p) (f : L2 𝕜) : Prop :=
  ∀ φ : Tests 𝕜 (⊤ : Opens Line),
    -lpDistribution (value u) (testPartialCLM [0, 0] φ) +
      (∫ x, (p.toContinuousMap (x 0) : 𝕜) * φ x * value u x ∂lineMeasure) =
    lpDistribution f φ

end ExpandedFA.Models.ConfiningSchrodingerRealization

namespace Specs.ExpandedFA.Models.ConfiningSchrodingerRealization
open _root_.ExpandedFA.Models.WeightedConfiningEnergySpace
open _root_.ExpandedFA.Models.ConfiningSchrodingerRealization

/-- Both directions are required, including the extension from compact tests
to every weighted energy test. This assertion does not require exterior positivity. -/
def FormDistributionEquivalence : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (p : Potential) (u : Space 𝕜 p) (f : L2 𝕜),
    DistributionEquation u f ↔
      ∀ v : Space 𝕜 p, energyForm v u = ⟪value v, f⟫_𝕜

/-- T is an everywhere defined bounded operator on the actual L² space; A
includes its exact domain and action, and equality with its Hilbert adjoint.
The graph equivalence specifies the differential action as well as the domain. -/
def Realization : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (p : Potential), PositiveAtInfinity p →
  ∃ T : L2 𝕜 →L[𝕜] L2 𝕜,
    (∀ f : L2 𝕜, ∃ u : Space 𝕜 p, value u = T f ∧
      ∀ v : Space 𝕜 p, energyForm v u = ⟪value v, f⟫_𝕜) ∧
    IsSelfAdjoint T ∧ (∀ f, 0 ≤ RCLike.re ⟪f, T f⟫_𝕜) ∧
    Function.Injective T ∧ DenseRange T ∧
    ∃ A : L2 𝕜 →ₗ.[𝕜] L2 𝕜,
      (∀ u f : L2 𝕜, (u, f) ∈ A.graph ↔ T f = u) ∧
      Dense (A.domain : Set (L2 𝕜)) ∧ A.adjoint = A ∧
      (∀ u : A.domain, 0 ≤ RCLike.re ⟪(u : L2 𝕜), A u⟫_𝕜) ∧
      (∀ u f : L2 𝕜, (u, f) ∈ A.graph ↔
        ∃ v : Space 𝕜 p, value v = u ∧ DistributionEquation v f) ∧
      (∀ u : L2 𝕜, u ∈ A.domain ↔
        ∃ v : Space 𝕜 p, value v = u ∧ ∃ f : L2 𝕜, DistributionEquation v f)

end Specs.ExpandedFA.Models.ConfiningSchrodingerRealization
