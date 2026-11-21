import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.ApproximationPropertyOperatorForm
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.OrthonormalExpansion
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15PartialSums
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Independent statements for paper.tex:9531–9538 and 9560–9571.
Hilbert projections are indexed by all finite subsets, with no separability
assumption. Basis hypotheses are the raw unique-expansion predicates, and
include finite and empty bases. The bound is chosen before K and ε.
-/
noncomputable section
open Filter Topology
namespace ExpandedFA.Compactness.HilbertBasisApproximationPropertySpec
universe u v w

/-- The orthogonal projector onto the span of the selected basis vectors. -/
def finiteSubsetProjection {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {ι : Type w}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (e : ι → H) (F : Finset ι) : H →L[𝕜] H :=
  letI : FiniteDimensional 𝕜 (Submodule.span 𝕜 (e '' (F : Set ι))) :=
    FiniteDimensional.span_of_finite 𝕜 (F.finite_toSet.image e)
  (Submodule.span 𝕜 (e '' (F : Set ι))).starProjection

def FiniteSubsetProjectionProperties : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {ι : Type w}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (e : ι → H) (F : Finset ι),
    FiniteDimensional 𝕜 (LinearMap.range (finiteSubsetProjection (𝕜 := 𝕜) e F).toLinearMap) ∧
      ‖finiteSubsetProjection (𝕜 := 𝕜) e F‖ ≤ 1

def HilbertUniformOnCompact : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {H : Type v} {ι : Type w}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (e : ι → H),
    ExpandedFA.Hilbert.OrthonormalExpansion.Spec.IsMaximalOrthonormalValue 𝕜 H ι e →
    ∀ K : Set H, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ F : Finset ι in atTop,
        sSup ((fun x => ‖finiteSubsetProjection (𝕜 := 𝕜) e F x - x‖) '' K) < ε

def HilbertBAP : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H],
    ∀ K : Set H, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∃ P : H →L[𝕜] H,
        FiniteDimensional 𝕜 (LinearMap.range P.toLinearMap) ∧
        ‖P‖ ≤ 1 ∧ sSup ((fun x => ‖P x - x‖) '' K) < ε

def HilbertAP : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H],
    ApproximationPropertyDefinitionsSpec.HasApproximationPropertyValue 𝕜 H

def SchauderUniformOnCompact : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    {e : ℕ → X} (h : ExpandedFA.P1.C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) e),
    ∃ (P : ℕ → X →L[𝕜] X) (M : ℝ), 0 ≤ M ∧
      (∀ N x, P N x = ExpandedFA.P1.C15Basis.Spec.rawPartialSum h N x) ∧
      (∀ N, FiniteDimensional 𝕜 (LinearMap.range (P N).toLinearMap) ∧ ‖P N‖ ≤ M) ∧
      ∀ K : Set X, IsCompact K → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ N in atTop, sSup ((fun x => ‖P N x - x‖) '' K) < ε

def FiniteBasisUniformOnCompact : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    {d : ℕ} {e : Fin d → X}
    (h : ExpandedFA.P1.C15Basis.Spec.IsRawFiniteBasis (𝕜 := 𝕜) e),
    ∃ (P : ℕ → X →L[𝕜] X) (M : ℝ), 0 ≤ M ∧
      (∀ N x, P N x = ExpandedFA.P1.C15Basis.Spec.finitePartialSum h N x) ∧
      (∀ N, FiniteDimensional 𝕜 (LinearMap.range (P N).toLinearMap) ∧ ‖P N‖ ≤ M) ∧
      ∀ K : Set X, IsCompact K → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ N in atTop, sSup ((fun x => ‖P N x - x‖) '' K) < ε

def SchauderBAP : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    {e : ℕ → X}, ExpandedFA.P1.C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) e →
    ApproximationPropertyDefinitionsSpec.HasBoundedApproximationPropertyValue 𝕜 X

def FiniteBasisBAP : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    {d : ℕ} {e : Fin d → X},
    ExpandedFA.P1.C15Basis.Spec.IsRawFiniteBasis (𝕜 := 𝕜) e →
    ApproximationPropertyDefinitionsSpec.HasBoundedApproximationPropertyValue 𝕜 X

def SchauderAP : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    {e : ℕ → X}, ExpandedFA.P1.C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) e →
    ApproximationPropertyDefinitionsSpec.HasApproximationPropertyValue 𝕜 X

def FiniteBasisAP : Prop :=
  ∀ {𝕜 : Type u} [RCLike 𝕜] {X : Type v}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    {d : ℕ} {e : Fin d → X},
    ExpandedFA.P1.C15Basis.Spec.IsRawFiniteBasis (𝕜 := 𝕜) e →
    ApproximationPropertyDefinitionsSpec.HasApproximationPropertyValue 𝕜 X

/-- The characterization is supplied by the accepted prerequisite; this
module combines it with the Hilbert and basis clauses of the source theorem. -/
def OperatorForm : Prop := ApproximationPropertyOperatorFormSpec.Equivalence.{u, v}

end ExpandedFA.Compactness.HilbertBasisApproximationPropertySpec
