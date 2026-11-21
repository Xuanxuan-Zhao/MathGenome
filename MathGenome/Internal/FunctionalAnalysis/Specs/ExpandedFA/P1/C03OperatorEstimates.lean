import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C03OperatorNorm
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.FiniteDomainOperators

/-! Independent full statement of `fa2:p1:c03:operator-estimates`, paper.tex
618–639. The operator type and its
norm are the native ones fixed by C03OperatorNorm. Arbitrary subspaces carry
the inherited norm; no closedness or completeness is assumed.
The finite-coordinate clauses use the shared upstream definitions verbatim.
-/

namespace ExpandedFA.P1.C03OperatorEstimates.Spec

universe u v w z

/-- All manuscript norm axioms, including scalar homogeneity and definiteness,
for the actual operator norm on the canonical operator space. -/
def OperatorNormAxioms : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
    C01Norm.NormAxioms 𝕜 (norm : (E →L[𝕜] F) → ℝ)

def EvaluationBound : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (T : E →L[𝕜] F) (x : E),
    ‖T x‖ ≤ ‖T‖ * ‖x‖

def CompositionBound : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) (G : Type z) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]
    (S : F →L[𝕜] G) (T : E →L[𝕜] F),
    ‖S.comp T‖ ≤ ‖S‖ * ‖T‖

/-- Restriction to any linear subspace, with its inherited norm. -/
def DomainRestrictionBound : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (T : E →L[𝕜] F) (M : Submodule 𝕜 E),
    ‖T.domRestrict M‖ ≤ ‖T‖

/-- Restricting only the codomain to a subspace containing the image preserves
the norm, hence also cannot increase it. -/
def CodomainRestrictionNorm : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (T : E →L[𝕜] F) (N : Submodule 𝕜 F) (h : ∀ x, T x ∈ N),
    ‖T.codRestrict N h‖ = ‖T‖

/-- Simultaneous restriction in both variables whenever T maps M into N. -/
def RestrictionBound : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (T : E →L[𝕜] F) (M : Submodule 𝕜 E) (N : Submodule 𝕜 F)
    (h : ∀ x ∈ M, T x ∈ N),
    ‖T.restrict h‖ ≤ ‖T‖

/-- Every algebraic linear map from a finite-dimensional normed domain is bounded,
with no finite-dimension assumption on its target. -/
def FiniteDomainBoundedness : Prop := FiniteDomainOperators.Spec.Boundedness.{u, v, w}

/-- The usual matrix entries, multiplication, synthesis, and Euclidean transport. -/
def MatrixCoordinates : Prop := FiniteDomainOperators.Spec.MatrixCoordinates.{u, v, w}

/-- The arbitrary-norm formula agrees with the native operator norm. -/
def NativeNormFormula : Prop := FiniteDomainOperators.Spec.NativeNormFormula.{u, v, w}

/-- The displayed infimum is a genuine least nonnegative bound. -/
def NormForIsLeastBound : Prop := FiniteDomainOperators.Spec.NormForIsLeastBound.{u, v, w}

/-- Two domain and target norms give positive comparison constants uniform in T. -/
def NormChangeComparison : Prop := FiniteDomainOperators.Spec.NormChangeComparison.{u, v, w}

/-- Original and Euclidean matrix operator norms are uniformly equivalent. -/
def CoordinateNormComparison : Prop := FiniteDomainOperators.Spec.CoordinateNormComparison.{u, v, w}

/-- Changing both bases gives uniformly equivalent matrix operator norms. -/
def BasisChangeComparison : Prop := FiniteDomainOperators.Spec.BasisChangeComparison.{u, v, w}

end ExpandedFA.P1.C03OperatorEstimates.Spec
