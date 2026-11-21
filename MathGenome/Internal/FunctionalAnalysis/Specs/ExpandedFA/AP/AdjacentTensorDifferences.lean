import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.AP.EnfloCoordinates

/-! Summable adjacent differences, paper.tex:12836–12882.
All tensors are algebraic tensors of the canonical continuous real dual and X.
Natural index m denotes the source's index m+1. -/
noncomputable section
open scoped BigOperators TensorProduct
namespace ExpandedFA.AP.AdjacentTensorDifferences.Spec
open EnfloSpace.Spec
open AlgebraicRankOneTensorsSpec

/-- Uniform tensor on the incident lower level in one next-block row. -/
def lowerTensor (D : IncidenceData) (m : ℕ) (j : Row D (m + 1)) : Tensor ℝ (X D) :=
  (t D (m + 1) : ℝ)⁻¹ • ∑ e ∈ incident D m j,
    EnfloCoordinates.Spec.coordinate D ⟨m, e⟩ ⊗ₜ[ℝ] generatorX D m e

/-- Uniform tensor on the upper level belonging to the same row. -/
def upperTensor (D : IncidenceData) (m : ℕ) (j : Row D (m + 1)) : Tensor ℝ (X D) :=
  (t D (m + 1) : ℝ)⁻¹ • ∑ p : Fin (t D (m + 1)),
    EnfloCoordinates.Spec.coordinate D ⟨m + 1, (j, p)⟩ ⊗ₜ[ℝ]
      generatorX D (m + 1) (j, p)

/-- A row evaluation, a continuous functional on the actual closed span. -/
def rowEvaluation (D : IncidenceData) (m : ℕ) (j : Row D (m + 1))
    (a : Walsh.Cube (n D (m + 1))) : X D →L[ℝ] ℝ :=
  (ContinuousMap.evalCLM ℝ (j, a) : Summand D (m + 1) →L[ℝ] ℝ).comp
    ((lp.evalCLM ℝ (Summand D) 2 (m + 1)).comp (closedSpan D).subtypeL)

/-- Lift of the translated normalized Walsh difference, as an explicit finite
combination of the original generators. -/
def rowVector (D : IncidenceData) (m : ℕ) (j : Row D (m + 1))
    (a : Walsh.Cube (n D (m + 1))) : X D :=
  (t D (m + 1) : ℝ)⁻¹ •
    ((∑ e : ↥(incident D m j),
      Walsh.character (n D (m + 1)) (lowerLabels D m j e).val a • generatorX D m e.val) -
     ∑ p : Fin (t D (m + 1)),
      Walsh.character (n D (m + 1)) (upperLabels D (m + 1) p).val a •
        generatorX D (m + 1) (j, p))

/-- This equality is in the algebraic tensor product, before applying any
operator map. Translation averaging is the exact Walsh diagonal averaging. -/
def RowRepresentation : Prop := ∀ D m j,
  lowerTensor D m j - upperTensor D m j =
    (Fintype.card (Walsh.Cube (n D (m + 1))) : ℝ)⁻¹ •
      ∑ a, rowEvaluation D m j a ⊗ₜ[ℝ] rowVector D m j a

def RowVectorBound : Prop := ∀ D m j a,
  ‖rowVector D m j a‖ ≤ 4 / (n D (m + 1) : ℝ)

def RowBound : Prop := ∀ D m j,
  nu (lowerTensor D m j - upperTensor D m j) ≤ 4 / (n D (m + 1) : ℝ)

def BalanceBound : Prop := ∀ D m,
  nu (EnfloCoordinates.Spec.u D m -
    (k D (m + 1) : ℝ)⁻¹ • ∑ j, lowerTensor D m j) ≤
      1 / (n D (m + 1) : ℝ)

def AdjacentBound : Prop := ∀ D m,
  nu (EnfloCoordinates.Spec.u D (m + 1) - EnfloCoordinates.Spec.u D m) ≤
    5 / (n D (m + 1) : ℝ)
end ExpandedFA.AP.AdjacentTensorDifferences.Spec
