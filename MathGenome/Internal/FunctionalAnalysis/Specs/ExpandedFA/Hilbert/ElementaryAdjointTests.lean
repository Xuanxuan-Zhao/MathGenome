import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
Independent statements for `paper.tex` 7878–7889 and its proof, the elementary
adjoint tests with the scalar qualification. Inner products are conjugate-first.
Real-valuedness in the complex criterion means zero imaginary part. There is no
normality or nonzero-space hypothesis. Product and norm-closure statements apply
to both scalar fields via `RCLike`. The real counterexample uses the native L²
norm on the actual Euclidean plane, not the sup norm on a product.
-/

noncomputable section
open scoped InnerProductSpace

namespace ExpandedFA.Hilbert.ElementaryAdjointTests.Spec
universe u v

/-- The complex-only criterion, including both implications. -/
def ComplexQuadraticCriterion : Prop :=
  ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H),
    T = Adjoint.Spec.AdjointValue ℂ H H T ↔ ∀ x : H, (⟪x, T x⟫_ℂ).im = 0

abbrev RotationType := EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)

/-- The matrix of J(s,t) = (-t,s) in the standard orthonormal coordinates. -/
def RotationValue : RotationType :=
  (Matrix.toEuclideanLin (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)).toContinuousLinearMap

/-- Zero (hence real) quadratic values do not imply self-adjointness over ℝ. -/
def RealRotationCounterexample : Prop :=
  (∀ x : EuclideanSpace ℝ (Fin 2),
    RotationValue x 0 = -x 1 ∧ RotationValue x 1 = x 0) ∧
  RotationValue ≠ 0 ∧
  (∀ x : EuclideanSpace ℝ (Fin 2), ⟪x, RotationValue x⟫_ℝ = 0) ∧
  Adjoint.Spec.AdjointValue ℝ _ _ RotationValue = -RotationValue ∧
  RotationValue ≠ Adjoint.Spec.AdjointValue ℝ _ _ RotationValue

/-- Composition of two self-adjoint operators is self-adjoint exactly when
those operators commute. Includes real and complex Hilbert spaces. -/
def ProductCriterion : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (S T : H →L[𝕜] H),
    S = Adjoint.Spec.AdjointValue 𝕜 H H S →
    T = Adjoint.Spec.AdjointValue 𝕜 H H T →
    (S.comp T = Adjoint.Spec.AdjointValue 𝕜 H H (S.comp T) ↔ S.comp T = T.comp S)

/-- Closedness is in the operator norm topology. No dimension or nontriviality
assumption is imposed on the underlying Hilbert space. -/
def SelfAdjointClosed : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H],
    IsClosed {T : H →L[𝕜] H | T = Adjoint.Spec.AdjointValue 𝕜 H H T}

end ExpandedFA.Hilbert.ElementaryAdjointTests.Spec
