import Mathlib.Analysis.Convex.Extreme
import Mathlib.Algebra.BigOperators.Module
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C24LcsSeparation

/-!
Independent statements for `fa2:p2:extreme-set-tests`, paper.tex:8719–8730.
The algebraic assertions have no topology assumptions. All combinations use
real weights, also when the ambient vector space is complex. `IsExtreme ℝ K A`
includes `A ⊆ K` and the endpoint property; it imposes no convexity on `A`.
-/
namespace Specs.ExpandedFA.BanachGeometry.ExtremeSetTests

universe u v

/-- Deleting a point of a convex set tests whether it is extreme. -/
def deletionType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] (K : Set E) (a : E),
    Convex ℝ K → a ∈ K →
      (a ∈ K.extremePoints ℝ ↔ Convex ℝ (K \ {a}))

/-- A finite positive barycenter equal to an extreme point has constant entries.
The index set can be empty; the sum-one hypothesis then cannot hold. -/
def positiveBarycenterType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] {ι : Type v}
    (K : Set E) (a : E) (s : Finset ι) (w : ι → ℝ) (x : ι → E),
    Convex ℝ K → a ∈ K.extremePoints ℝ →
    (∀ i ∈ s, 0 < w i) → (∑ i ∈ s, w i) = 1 →
    (∀ i ∈ s, x i ∈ K) → (∑ i ∈ s, w i • x i) = a →
      ∀ i ∈ s, x i = a

/-- A nonempty closed extreme subset, without an assumption of convexity,
contains an extreme point of the original compact convex set. -/
def closedExtremeSubsetType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    [LocallyConvexSpace ℝ E] (K A : Set E),
    IsCompact K → Convex ℝ K → A.Nonempty → IsClosed A →
    IsExtreme ℝ K A → ∃ a ∈ A, a ∈ K.extremePoints ℝ

/-- The complex case uses the given topology and underlying real convexity. -/
def complexClosedExtremeSubsetType : Prop :=
  ∀ {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
    [LocallyConvexSpace ℝ E] (K A : Set E),
    IsCompact K → Convex ℝ K → A.Nonempty → IsClosed A →
    IsExtreme ℝ K A → ∃ a ∈ A, a ∈ K.extremePoints ℝ

end Specs.ExpandedFA.BanachGeometry.ExtremeSetTests
