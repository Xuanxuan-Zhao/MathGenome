import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Conventions
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
Independent statements for paper.tex 7749–7763 (pre-Hilbert Bessel and
Parseval). No ambient completeness, countability of the index type, or
nonemptiness of the orthonormal family is assumed. The remaining annihilator
and incomplete-space counterexample clauses are allocated to
PreHilbertTotalityBoundary.
-/

noncomputable section
open scoped InnerProductSpace
open Filter Topology

namespace ExpandedFA.Hilbert.PreHilbertBesselParseval
universe u v w

/-- The manuscript's partial sum, with the coefficient in the linear slot. -/
def fourierPartialSum (𝕜 : Type u) {E : Type v} {ι : Type w} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (e : ι → E) (x : E) (F : Finset ι) : E :=
  ∑ i ∈ F, ⟪e i, x⟫_𝕜 • e i

namespace Spec

def FiniteProjectionIdentity : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (e : ι → E), Orthonormal 𝕜 e → ∀ (x : E) (F : Finset ι),
    ‖x - fourierPartialSum 𝕜 e x F‖ ^ 2 =
      ‖x‖ ^ 2 - ∑ i ∈ F, ‖⟪e i, x⟫_𝕜‖ ^ 2

def FiniteBessel : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (e : ι → E), Orthonormal 𝕜 e → ∀ (x : E) (F : Finset ι),
    ∑ i ∈ F, ‖⟪e i, x⟫_𝕜‖ ^ 2 ≤ ‖x‖ ^ 2

def CoefficientSquaresSummable : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (e : ι → E), Orthonormal 𝕜 e → ∀ x : E,
    Summable (fun i => ‖⟪e i, x⟫_𝕜‖ ^ 2)

def Bessel : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (e : ι → E), Orthonormal 𝕜 e → ∀ x : E,
    ∑' i, ‖⟪e i, x⟫_𝕜‖ ^ 2 ≤ ‖x‖ ^ 2

def CountableCoefficientSupport : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (e : ι → E), Orthonormal 𝕜 e → ∀ x : E,
    Set.Countable {i | ⟪e i, x⟫_𝕜 ≠ 0}

/-- Convergence is explicitly the net over all finite subsets. -/
def ClosedSpanIffNetConvergence : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (e : ι → E), Orthonormal 𝕜 e → ∀ x : E,
    x ∈ (Submodule.span 𝕜 (Set.range e)).topologicalClosure ↔
      Tendsto (fourierPartialSum 𝕜 e x) atTop (𝓝 x)

def NetConvergenceIffParseval : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (e : ι → E), Orthonormal 𝕜 e → ∀ x : E,
    Tendsto (fourierPartialSum 𝕜 e x) atTop (𝓝 x) ↔
      ∑' i, ‖⟪e i, x⟫_𝕜‖ ^ 2 = ‖x‖ ^ 2

def ClosedSpanIffParseval : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (e : ι → E), Orthonormal 𝕜 e → ∀ x : E,
    x ∈ (Submodule.span 𝕜 (Set.range e)).topologicalClosure ↔
      ∑' i, ‖⟪e i, x⟫_𝕜‖ ^ 2 = ‖x‖ ^ 2

def TotalIffParseval : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (e : ι → E), Orthonormal 𝕜 e →
    ((Submodule.span 𝕜 (Set.range e)).topologicalClosure = ⊤ ↔
      ∀ x : E, ∑' i, ‖⟪e i, x⟫_𝕜‖ ^ 2 = ‖x‖ ^ 2)

end Spec
end ExpandedFA.Hilbert.PreHilbertBesselParseval
