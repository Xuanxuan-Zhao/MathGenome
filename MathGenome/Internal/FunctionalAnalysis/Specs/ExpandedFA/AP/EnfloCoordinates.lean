import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.AP.EnfloSpace
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.AP.AlgebraicRankOneTensors

/-! Coordinate functionals and finite tensors for paper.tex:12818–12834.
The functionals are concrete Fourier coefficient maps restricted to the original
closed span. Thus no biorthogonality or sharp norm certificate is assumed. -/
noncomputable section
open scoped BigOperators TensorProduct
namespace ExpandedFA.AP.EnfloCoordinates.Spec
open EnfloSpace.Spec

/-- Uniform Fourier coefficient on one row of a block. -/
def rowFourier (D : IncidenceData) (m : ℕ) (r : Row D m)
    (S : Finset (Fin (2 * n D m))) : Summand D m →L[ℝ] ℝ :=
  (Fintype.card (Walsh.Cube (n D m)) : ℝ)⁻¹ •
    ∑ a : Walsh.Cube (n D m),
      Walsh.character (n D m) S a • (ContinuousMap.evalCLM ℝ (r, a) : Summand D m →L[ℝ] ℝ)

/-- Coefficient extraction on the whole ambient space, using the own row. -/
def ambientCoordinate (D : IncidenceData) (e : AllSymbols D) : Y D →L[ℝ] ℝ :=
  (rowFourier D e.1 e.2.1 (upperLabels D e.1 e.2.2).val).comp
    (lp.evalCLM ℝ (Summand D) 2 e.1)

/-- The continuous extension of the algebraic coefficient map to X. -/
def coordinate (D : IncidenceData) (e : AllSymbols D) : X D →L[ℝ] ℝ :=
  (ambientCoordinate D e).comp (closedSpan D).subtypeL

/-- The normalized finite algebraic tensor, with the source's normalization. -/
def u (D : IncidenceData) (m : ℕ) : AlgebraicRankOneTensorsSpec.Tensor ℝ (X D) :=
  ((k D m : ℝ) * t D m)⁻¹ • ∑ e : Symbol D m,
    coordinate D ⟨m, e⟩ ⊗ₜ[ℝ] generatorX D m e

def CoordinateType := ∀ D, AllSymbols D → X D →L[ℝ] ℝ
def CoordinateValue : CoordinateType := coordinate
def UType := ∀ D, ℕ → AlgebraicRankOneTensorsSpec.Tensor ℝ (X D)
def UValue : UType := u

def CoefficientEstimate : Prop := ∀ D (A : Finset (AllSymbols D))
    (c : AllSymbols D → ℝ) (e : AllSymbols D), e ∈ A →
  |c e| * ‖generatorX D e.1 e.2‖ ≤ ‖∑ d ∈ A, c d • generatorX D d.1 d.2‖

def Independence : Prop := ∀ D,
  LinearIndependent ℝ (fun e : AllSymbols D => generatorX D e.1 e.2)

def Biorthogonal : Prop := ∀ D (e d : AllSymbols D),
  coordinate D e (generatorX D d.1 d.2) = if e = d then 1 else 0

def Extension : Prop := ∀ D (A : Finset (AllSymbols D)) (c : AllSymbols D → ℝ)
    (e : AllSymbols D), e ∈ A →
  coordinate D e (∑ d ∈ A, c d • generatorX D d.1 d.2) = c e

def SharpNorm : Prop := ∀ D (e : AllSymbols D),
  ‖coordinate D e‖ * ‖generatorX D e.1 e.2‖ = 1

def TraceOne : Prop := ∀ D m, AlgebraicRankOneTensorsSpec.trace (u D m) = 1

def ProjectiveBound : Prop := ∀ D m, AlgebraicRankOneTensorsSpec.nu (u D m) ≤ 1
end ExpandedFA.AP.EnfloCoordinates.Spec
