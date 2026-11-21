import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.BochnerIntegral
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.Topology.Algebra.Module.Basic

/-!
Independent specification of paper.tex:17078–17105, Pettis measurability and
weak integrals. Strong measurability retains the accepted a.e. convention.
Weak measurability uses actual measurable scalar evaluations, so completeness
of the measure is included in the criterion. The essential separable subspace
need not be closed; no separability of the ambient Banach space is assumed.
All duals are continuous linear duals over the original real/complex field.
The counterexample at 17096–17103 is allocated to `ops_weak_not_bochner`.
-/

noncomputable section
open Filter MeasureTheory TopologicalSpace
open scoped Topology
universe w u v

namespace ExpandedFA.FunctionSpaces.PettisMeasurabilitySpec

/-- Scalar Borel measurability of every continuous linear evaluation. -/
def WeaklyMeasurableType :=
  ∀ (𝕜 : Type w) [RCLike 𝕜] {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E], (X → E) → Prop

def WeaklyMeasurableValue : WeaklyMeasurableType.{w,u,v} :=
  fun 𝕜 _ _ _ _ _ _ f =>
    letI : MeasurableSpace 𝕜 := borel 𝕜
    ∀ ℓ : _ →L[𝕜] 𝕜, Measurable (fun x => ℓ (f x))

/-- A.e. containment in a separable linear subspace, including the zero space. -/
def EssentiallySeparablyValuedType :=
  ∀ (𝕜 : Type w) [RCLike 𝕜] {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    Measure X → (X → E) → Prop

def EssentiallySeparablyValuedValue : EssentiallySeparablyValuedType.{w,u,v} :=
  fun 𝕜 _ _ E _ _ _ μ f =>
    ∃ S : Submodule 𝕜 E, IsSeparable (S : Set E) ∧ ∀ᵐ x ∂μ, f x ∈ S

/-- The vector represents all scalar integrals, which must be integrable. -/
def IsWeakIntegralType :=
  ∀ (𝕜 : Type w) [RCLike 𝕜] {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    Measure X → (X → E) → E → Prop

def IsWeakIntegralValue : IsWeakIntegralType.{w,u,v} :=
  fun 𝕜 _ _ _ _ _ _ μ f I =>
    ∀ ℓ : _ →L[𝕜] 𝕜, Integrable (fun x => ℓ (f x)) μ ∧
      ℓ I = ∫ x, ℓ (f x) ∂μ

/-- Pettis's criterion on every complete positive measure space. -/
def PettisCriterion : Prop :=
  ∀ (𝕜 : Type w) [RCLike 𝕜] {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (μ : Measure X) [μ.IsComplete] (f : X → E),
    BochnerDefinitionsSpec.StrongMeasurableValue μ f ↔
      WeaklyMeasurableValue 𝕜 f ∧ EssentiallySeparablyValuedValue 𝕜 μ f

/-- The weak integral identity, including scalar integrability, for both fields. -/
def BochnerIsWeakIntegral : Prop :=
  ∀ (𝕜 : Type w) [RCLike 𝕜] {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (μ : Measure X) (f : X → E),
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    BochnerDefinitionsSpec.BochnerIntegrableValue μ f →
      IsWeakIntegralValue 𝕜 μ f (BochnerIntegralSpec.IntegralValue μ f)

end ExpandedFA.FunctionSpaces.PettisMeasurabilitySpec
