import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Adjoint
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Lattice.Fold

/-! Independent statements for the finite part of `paper.tex` 13040–13077.
The finite supremum is taken in ℝ≥0, so its empty value is zero.
The star and multiplication on endomorphisms are the Hilbert adjoint and composition.
-/
noncomputable section
open scoped NNReal
namespace ExpandedFA.Geometry.CotlarSteinFinite.Spec
universe u v w

variable {𝕜 : Type u} {H : Type v} {ι : Type w} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] [Fintype ι]

/-- Maximum of the rows of square roots of adjoint-product norms. -/
def leftBound (T : ι → H →L[𝕜] H) : ℝ≥0 :=
  Finset.univ.sup fun i => ∑ j, NNReal.sqrt ‖(T i).adjoint.comp (T j)‖₊

/-- Maximum of the rows of square roots of product-adjoint norms. -/
def rightBound (T : ι → H →L[𝕜] H) : ℝ≥0 :=
  Finset.univ.sup fun i => ∑ j, NNReal.sqrt ‖(T i).comp (T j).adjoint‖₊

/-- Row-bound version, suitable for applying the result to finite subfamilies. -/
def RowEstimate : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] [Fintype ι]
    (T : ι → H →L[𝕜] H) (A B : ℝ),
    0 ≤ A → 0 ≤ B →
    (∀ i, ∑ j, Real.sqrt ‖(T i).adjoint.comp (T j)‖ ≤ A) →
    (∀ i, ∑ j, Real.sqrt ‖(T i).comp (T j).adjoint‖ ≤ B) →
    ‖∑ i, T i‖ ≤ Real.sqrt (A * B)

/-- The exact finite-supremum assertion, including an empty index type. -/
def FiniteEstimate : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) (ι : Type w) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H] [Fintype ι]
    (T : ι → H →L[𝕜] H),
    ‖∑ i, T i‖ ≤ Real.sqrt ((leftBound T : ℝ) * (rightBound T : ℝ))

end ExpandedFA.Geometry.CotlarSteinFinite.Spec
