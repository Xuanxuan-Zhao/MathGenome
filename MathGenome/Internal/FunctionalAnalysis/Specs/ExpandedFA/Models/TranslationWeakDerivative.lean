import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.TranslationFourierModel

/-! Exact spatial generator in `fa2:p3:translation-model` (paper.tex:16744ff).
The scalar tests and the spatial graph are exactly the shared definitions.
No assertion about the generator's domain is a hypothesis. -/
noncomputable section
open MeasureTheory Filter Topology

namespace ExpandedFA.Models.TranslationWeakDerivative.Spec
open FullTranslationModel ExpandedFA.Semigroups.Stone ExpandedFA.Unbounded
open ExpandedFA.Unbounded.SymmetryAndDeficienciesSpec
universe u

/-- The full two-sided norm quotient criterion, for every L² vector and every
proposed derivative. There is no conjugation in the compact-test definition. -/
def DifferenceQuotientCriterion : Prop :=
  ∀ (M : Type u) [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]
    (f w : L2 M),
    Tendsto (fun h : ℝ => (h : ℂ)⁻¹ • (translate h f - f))
      (𝓝[≠] (0 : ℝ)) (𝓝 w) ↔ HasWeakDerivative f w

/-- An actual self-adjoint partial operator, its PVM exponential, its entire
norm-derivative graph, and its entire unconjugated distributional graph. -/
def SpatialStone : Prop :=
  ∀ (M : Type u) [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M],
    ∃ (V : UnitaryGroup (L2 M)) (A : Operator ℂ (L2 M) (L2 M)),
      IsTranslationGroup V ∧ selfAdjointValue A ∧ SpectralExponential A V ∧
      DerivativeGraph V A ∧ ∀ f g, (f, g) ∈ A.graph ↔ SpatialGraph f g

/-- Uniqueness of a weak L² derivative, including nonseparable targets. -/
def WeakDerivativeUnique : Prop :=
  ∀ (M : Type u) [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M]
    (f w z : L2 M), HasWeakDerivative f w → HasWeakDerivative f z → w = z

/-- Closedness in the product L² norm topology. -/
def WeakDerivativeGraphClosed : Prop :=
  ∀ (M : Type u) [NormedAddCommGroup M] [InnerProductSpace ℂ M] [CompleteSpace M],
    IsClosed {p : L2 M × L2 M | HasWeakDerivative p.1 p.2}

end ExpandedFA.Models.TranslationWeakDerivative.Spec
