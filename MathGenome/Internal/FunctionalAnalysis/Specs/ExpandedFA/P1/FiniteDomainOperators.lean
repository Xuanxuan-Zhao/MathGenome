import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01FiniteDimension
import Mathlib.Analysis.InnerProductSpace.PiL2
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C03OperatorNorm
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
Independent statements for the finite-domain and coordinate clauses of
`fa2:p1:c03:operator-estimates` (paper.tex 618–639), including the continuity
consequence at lines 216–218. Scalars are real or complex. There are no
completeness or positive-dimension assumptions. Norm and basis comparison
constants are uniform over all algebraic linear maps.

The three auxiliary definitions below fix the displayed operator norm for
arbitrary norm functions and transport a map to genuine Euclidean coordinates.
Their least-bound and native-norm identifications are separate proof obligations.
-/

noncomputable section
namespace ExpandedFA.P1.FiniteDomainOperators

/-- The manuscript's infimum formula, for two displayed norm functions.
For actual norms on finite-dimensional spaces the theorems below verify that
this is the ordinary operator norm; no boundedness certificate is assumed. -/
def operatorNormFor {𝕜 E F : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
    (p : E → ℝ) (q : F → ℝ) (T : E →ₗ[𝕜] F) : ℝ :=
  sInf {C : ℝ | 0 ≤ C ∧ ∀ x, q (T x) ≤ C * p x}

/-- The chosen basis coordinates, carrying the Euclidean norm. -/
def euclideanCoordinates {𝕜 E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] {n : ℕ} (b : Module.Basis (Fin n) 𝕜 E) :
    E ≃ₗ[𝕜] EuclideanSpace 𝕜 (Fin n) :=
  b.equivFun.trans (WithLp.linearEquiv 2 𝕜 (Fin n → 𝕜)).symm

/-- The original map in the two chosen Euclidean coordinate spaces. -/
def operatorInCoordinates {𝕜 E F : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
    {n m : ℕ} (b : Module.Basis (Fin n) 𝕜 E) (c : Module.Basis (Fin m) 𝕜 F)
    (T : E →ₗ[𝕜] F) : EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin m) :=
  (euclideanCoordinates b).arrowCongr (euclideanCoordinates c) T

namespace Spec

def Boundedness : Prop :=
  ∀ (𝕜 E F : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : E →ₗ[𝕜] F),
    Continuous T ∧ ∃ C > (0 : ℝ), ∀ x, ‖T x‖ ≤ C * ‖x‖

/-- Entries, action on coordinates, and action on arbitrary synthesized vectors
all use the usual matrix, with the target index as row and domain index as column. -/
def MatrixCoordinates : Prop :=
  ∀ (𝕜 E F : Type*) [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
    (n m : ℕ) (b : Module.Basis (Fin n) 𝕜 E) (c : Module.Basis (Fin m) 𝕜 F)
    (T : E →ₗ[𝕜] F),
    (∀ i j, LinearMap.toMatrix b c T i j = c.repr (T (b j)) i) ∧
    (∀ x, (LinearMap.toMatrix b c T).mulVec (b.repr x) = c.repr (T x)) ∧
    (∀ a, T (∑ j, a j • b j) =
      ∑ i, ((LinearMap.toMatrix b c T).mulVec a) i • c i) ∧
    (∀ a, operatorInCoordinates b c T a =
      WithLp.toLp 2 ((LinearMap.toMatrix b c T).mulVec (WithLp.ofLp a)))

/-- Agreement with the native operator norm for the given normed spaces. -/
def NativeNormFormula : Prop :=
  ∀ (𝕜 E F : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : E →ₗ[𝕜] F),
    operatorNormFor (norm : E → ℝ) (norm : F → ℝ) T = ‖T.toContinuousLinearMap‖

/-- The infimum really is a nonnegative least bound for any displayed pair of
norms; in particular its defining set is nonempty and its inequalities hold. -/
def NormForIsLeastBound : Prop :=
  ∀ (𝕜 E F : Type*) [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F]
    (p : E → ℝ) (q : F → ℝ), C01Norm.NormAxioms 𝕜 p → C01Norm.NormAxioms 𝕜 q →
    ∀ T : E →ₗ[𝕜] F,
      IsLeast {C : ℝ | 0 ≤ C ∧ ∀ x, q (T x) ≤ C * p x} (operatorNormFor p q T)

/-- Changing both norms gives fixed positive constants for all algebraic maps. -/
def NormChangeComparison : Prop :=
  ∀ (𝕜 E F : Type*) [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [FiniteDimensional 𝕜 F]
    (p₁ p₂ : E → ℝ) (q₁ q₂ : F → ℝ),
    C01Norm.NormAxioms 𝕜 p₁ → C01Norm.NormAxioms 𝕜 p₂ →
    C01Norm.NormAxioms 𝕜 q₁ → C01Norm.NormAxioms 𝕜 q₂ →
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ T : E →ₗ[𝕜] F,
      c * operatorNormFor p₁ q₁ T ≤ operatorNormFor p₂ q₂ T ∧
      operatorNormFor p₂ q₂ T ≤ C * operatorNormFor p₁ q₁ T

/-- For fixed bases the matrix operator norm and the original operator norm
are equivalent, uniformly over maps, using genuine Euclidean coordinate norms. -/
def CoordinateNormComparison : Prop :=
  ∀ (𝕜 E F : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (n m : ℕ) (b : Module.Basis (Fin n) 𝕜 E) (d : Module.Basis (Fin m) 𝕜 F),
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ T : E →ₗ[𝕜] F,
      letI := b.finiteDimensional_of_finite
      c * ‖T.toContinuousLinearMap‖ ≤ ‖(operatorInCoordinates b d T).toContinuousLinearMap‖ ∧
      ‖(operatorInCoordinates b d T).toContinuousLinearMap‖ ≤ C * ‖T.toContinuousLinearMap‖

/-- Changing either basis gives equivalent matrix operator norms. The spaces
need only be algebraic here, since their coordinate norms are explicitly fixed. -/
def BasisChangeComparison : Prop :=
  ∀ (𝕜 E F : Type*) [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
    (n₁ n₂ m₁ m₂ : ℕ)
    (b₁ : Module.Basis (Fin n₁) 𝕜 E) (b₂ : Module.Basis (Fin n₂) 𝕜 E)
    (d₁ : Module.Basis (Fin m₁) 𝕜 F) (d₂ : Module.Basis (Fin m₂) 𝕜 F),
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ T : E →ₗ[𝕜] F,
      c * ‖(operatorInCoordinates b₁ d₁ T).toContinuousLinearMap‖ ≤
        ‖(operatorInCoordinates b₂ d₂ T).toContinuousLinearMap‖ ∧
      ‖(operatorInCoordinates b₂ d₂ T).toContinuousLinearMap‖ ≤
        C * ‖(operatorInCoordinates b₁ d₁ T).toContinuousLinearMap‖

end Spec
end ExpandedFA.P1.FiniteDomainOperators
