import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyDisk
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Projection
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Topology.Covering.FundamentalGroupCircle
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Independent objects for paper.tex:10466–10526 and 10763–10792.
The scalar Hardy space and boundary synthesis are the canonical upstream objects.
All measures are normalized Haar measure. Matrix spaces use the Hilbert direct
sum of finitely many copies, including the zero-dimensional case. -/
noncomputable section
open MeasureTheory
open scoped Real ENNReal InnerProductSpace

namespace ExpandedFA.Toeplitz.Definitions.Spec

abbrev H2 := ExpandedFA.PartIV.HardyDiskSpec.H2
abbrev Circle := ExpandedFA.PartIV.HardyDiskSpec.Circle
abbrev BoundaryL2 := ExpandedFA.PartIV.HardyDiskSpec.BoundaryL2
abbrev BoundaryH2 := ExpandedFA.PartIV.HardyDiskSpec.nonnegativeFourier
abbrev boundary := ExpandedFA.PartIV.HardyDiskSpec.boundary
abbrev circleMeasure := AddCircle.haarAddCircle (T := 2 * π)
abbrev ScalarSymbol : Type := Lp ℂ ∞ circleMeasure
abbrev MatrixSymbol (d : ℕ) := Matrix (Fin d) (Fin d) ScalarSymbol
abbrev VectorH2 (d : ℕ) := PiLp 2 (fun _ : Fin d => H2)
abbrev VectorBoundaryL2 (d : ℕ) := PiLp 2 (fun _ : Fin d => BoundaryL2)
abbrev VectorBoundaryH2 (d : ℕ) := PiLp 2 (fun _ : Fin d => BoundaryH2)

/-- Every a.e. bounded measurable symbol gives its a.e. class. -/
def symbolOfFunction (φ : Circle → ℂ) (hφ : MemLp φ ∞ circleMeasure) : ScalarSymbol :=
  hφ.toLp φ

/-- Construction directly from essential boundedness and measurability. -/
def boundedSymbolOfFunction (φ : Circle → ℂ) (hφ : AEStronglyMeasurable φ circleMeasure)
    (C : ℝ) (hbound : ∀ᵐ t ∂circleMeasure, ‖φ t‖ ≤ C) : ScalarSymbol :=
  symbolOfFunction φ (memLp_top_of_bound hφ C hbound)

def continuousSymbol (φ : C(Circle, ℂ)) : ScalarSymbol :=
  ContinuousMap.toLp ∞ circleMeasure ℂ φ

def continuousMatrixSymbol {d : ℕ}
    (Φ : Matrix (Fin d) (Fin d) C(Circle, ℂ)) : MatrixSymbol d :=
  fun i j => continuousSymbol (Φ i j)

/-- Multiplication by an L∞ symbol on the genuine circle L² quotient. -/
def multiplication (φ : ScalarSymbol) : BoundaryL2 →L[ℂ] BoundaryL2 :=
  ((ContinuousLinearMap.mul ℂ ℂ).holderL circleMeasure ∞ 2 2) φ

def boundaryInclusion : H2 →L[ℂ] BoundaryL2 := boundary.toContinuousLinearMap
def boundaryAnalysis : BoundaryL2 →L[ℂ] H2 := boundaryInclusion.adjoint

/-- Isometric synthesis followed by its adjoint: orthogonal projection onto
exactly the range of the upstream boundary map. -/
def positiveProjection : BoundaryL2 →L[ℂ] BoundaryL2 :=
  boundaryInclusion.comp boundaryAnalysis

def negativeProjection : BoundaryL2 →L[ℂ] BoundaryL2 :=
  ContinuousLinearMap.id ℂ BoundaryL2 - positiveProjection

def toeplitz (φ : ScalarSymbol) : H2 →L[ℂ] H2 :=
  boundaryAnalysis.comp ((multiplication φ).comp boundaryInclusion)

/-- The negative Hardy space is embedded in L²; its range property is specified below. -/
def hankel (φ : ScalarSymbol) : H2 →L[ℂ] BoundaryL2 :=
  negativeProjection.comp ((multiplication φ).comp boundaryInclusion)

/-- A matrix of bounded operators acts on the finite Hilbert direct sums by
ordinary row-by-column multiplication. -/
def operatorMatrix {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (d : ℕ)
    (A : Fin d → Fin d → E →L[ℂ] F) :
    PiLp 2 (fun _ : Fin d => E) →L[ℂ] PiLp 2 (fun _ : Fin d => F) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin d => F)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => ∑ j : Fin d,
      (A i j).comp (PiLp.proj (p := 2) (fun _ : Fin d => E) j)))

def matrixMultiplication {d : ℕ} (Φ : MatrixSymbol d) :
    VectorBoundaryL2 d →L[ℂ] VectorBoundaryL2 d :=
  operatorMatrix d (fun i j => multiplication (Φ i j))

def matrixToeplitz {d : ℕ} (Φ : MatrixSymbol d) : VectorH2 d →L[ℂ] VectorH2 d :=
  operatorMatrix d (fun i j => toeplitz (Φ i j))

def matrixHankel {d : ℕ} (Φ : MatrixSymbol d) :
    VectorH2 d →L[ℂ] VectorBoundaryL2 d :=
  operatorMatrix d (fun i j => hankel (Φ i j))

/-- The coordinatewise extension of any bounded operator, preserving Hilbert norms. -/
def coordinateOperator {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (d : ℕ) (A : E →L[ℂ] F) :
    PiLp 2 (fun _ : Fin d => E) →L[ℂ] PiLp 2 (fun _ : Fin d => F) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin d => F)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => A.comp (PiLp.proj (p := 2) (fun _ : Fin d => E) i))

def matrixBoundary (d : ℕ) : VectorH2 d →L[ℂ] VectorBoundaryL2 d :=
  coordinateOperator d boundaryInclusion

def matrixPositiveProjection (d : ℕ) :
    VectorBoundaryL2 d →L[ℂ] VectorBoundaryL2 d := coordinateOperator d positiveProjection

def matrixNegativeProjection (d : ℕ) :
    VectorBoundaryL2 d →L[ℂ] VectorBoundaryL2 d := coordinateOperator d negativeProjection

/-- Nonvanishing continuous scalar loops, without differentiability assumptions. -/
def NonvanishingLoop := {φ : C(Circle, ℂ) // ∀ t, φ t ≠ 0}

/-- Radial retraction of a nonzero complex loop to the multiplicative unit circle. -/
def loopPhase (φ : NonvanishingLoop) : C(Circle, _root_.Circle) where
  toFun t := ⟨φ.val t / (‖φ.val t‖ : ℂ), by
    exact mem_sphere_zero_iff_norm.mpr (by
      rw [norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.mpr (φ.property t))])⟩
  continuous_toFun := Continuous.subtype_mk
    (φ.val.continuous.div (Complex.continuous_ofReal.comp φ.val.continuous.norm)
      (fun t => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (φ.property t)))) _

/-- The positively oriented traversal θ=2πt, expressed in the additive circle. -/
def angularTraversal : Path (0 : Circle) 0 := AddCircle.zsmulLoop (2 * π) 0 1

/-- The phase loop, moved to the additive circle by its actual homeomorphism. -/
def phasePath (φ : NonvanishingLoop) :
    Path (AddCircle.homeomorphCircle'.symm (loopPhase φ 0))
      (AddCircle.homeomorphCircle'.symm (loopPhase φ 0)) :=
  angularTraversal.map
    (AddCircle.homeomorphCircle'.symm.continuous.comp (loopPhase φ).continuous)

/-- Topological winding, defined for all continuous nonvanishing loops.
It is the integer degree of their phase, with positive orientation. -/
def winding (φ : NonvanishingLoop) : ℤ :=
  AddCircle.windingNumber (.of (.mk (phasePath φ)))

/-- The coordinate z=e^{iθ}; its winding is +1, so the Toeplitz index
convention of the source is minus winding (index of T_z equals -1). -/
def coordinateLoop : NonvanishingLoop :=
  ⟨fourier (T := 2 * π) 1, fun t => by
    rw [fourier_one]
    exact (AddCircle.toCircle t).coe_ne_zero⟩

-- Independent full proposition contracts.
def HardyIdentification : Prop :=
  LinearMap.range boundary.toLinearMap = BoundaryH2 ∧ IsClosed (BoundaryH2 : Set BoundaryL2)

def ProjectionCharacterization : Prop := ∀ g : BoundaryL2,
  positiveProjection g ∈ BoundaryH2 ∧
  negativeProjection g ∈ BoundaryH2.orthogonal ∧
  positiveProjection g + negativeProjection g = g

def NativeProjections : Prop := ∀ hclosed : IsClosed (BoundaryH2 : Set BoundaryL2),
  letI : CompleteSpace BoundaryH2 := hclosed.completeSpace_coe
  positiveProjection = BoundaryH2.starProjection ∧
    negativeProjection = BoundaryH2.orthogonal.starProjection

def MultiplicationValues : Prop := ∀ (φ : ScalarSymbol) (g : BoundaryL2),
  (multiplication φ g : Circle → ℂ) =ᵐ[circleMeasure] fun t => φ t * g t

def FunctionSymbolValues : Prop := ∀ (φ : Circle → ℂ) (hφ : MemLp φ ∞ circleMeasure),
  (symbolOfFunction φ hφ : Circle → ℂ) =ᵐ[circleMeasure] φ

def BoundedSymbolValues : Prop := ∀ (φ : Circle → ℂ)
    (hφ : AEStronglyMeasurable φ circleMeasure) (C : ℝ)
    (hbound : ∀ᵐ t ∂circleMeasure, ‖φ t‖ ≤ C),
  (boundedSymbolOfFunction φ hφ C hbound : Circle → ℂ) =ᵐ[circleMeasure] φ

def ContinuousSymbolValues : Prop := ∀ φ : C(Circle, ℂ),
  (continuousSymbol φ : Circle → ℂ) =ᵐ[circleMeasure] φ

def ScalarCompression : Prop := ∀ (φ : ScalarSymbol) (f : H2),
  boundary (toeplitz φ f) = positiveProjection (multiplication φ (boundary f)) ∧
  hankel φ f = negativeProjection (multiplication φ (boundary f)) ∧
  hankel φ f ∈ BoundaryH2.orthogonal

/-- Finite coordinate model: the scalar boundary unitary extends to an actual
unitary, with the stated coordinates, including d=0. -/
def MatrixBoundaryUnitary : Prop := ∀ d : ℕ,
  ∃ U : VectorH2 d ≃ₗᵢ[ℂ] VectorBoundaryH2 d,
    ∀ (f : VectorH2 d) (i : Fin d), (U f i).val = boundary (f i)

def MatrixMultiplicationValues : Prop := ∀ (d : ℕ) (Φ : MatrixSymbol d)
    (g : VectorBoundaryL2 d) (i : Fin d),
  (matrixMultiplication Φ g i : Circle → ℂ) =ᵐ[circleMeasure]
    fun t => ∑ j : Fin d, Φ i j t * g j t

def MatrixCompression : Prop := ∀ (d : ℕ) (Φ : MatrixSymbol d) (f : VectorH2 d),
  matrixBoundary d (matrixToeplitz Φ f) =
    matrixPositiveProjection d (matrixMultiplication Φ (matrixBoundary d f)) ∧
  matrixHankel Φ f =
    matrixNegativeProjection d (matrixMultiplication Φ (matrixBoundary d f)) ∧
  ∀ i : Fin d, matrixHankel Φ f i ∈ BoundaryH2.orthogonal

def WindingLift : Prop := ∀ (φ : NonvanishingLoop) (a : C(unitInterval, ℝ)),
  (∀ t, (a t : Circle) = phasePath φ t) →
    (winding φ : ℝ) = (a 1 - a 0) / (2 * π)

def WindingCoordinate : Prop := winding coordinateLoop = 1

def CoordinateToeplitz : Prop :=
  toeplitz (continuousSymbol (fourier (T := 2 * π) 1)) =
    ExpandedFA.PartIV.HardyDiskSpec.shift.toContinuousLinearMap

-- Independent type and exact-value contracts for the public definitions.
def H2Type := Type
def H2Value : H2Type := @H2

def CircleType := Type
def CircleValue : CircleType := @Circle

def BoundaryL2Type := Type
def BoundaryL2Value : BoundaryL2Type := @BoundaryL2

def BoundaryH2Type := Submodule ℂ BoundaryL2
def BoundaryH2Value : BoundaryH2Type := @BoundaryH2

def ScalarSymbolType := Type
def ScalarSymbolValue : ScalarSymbolType := @ScalarSymbol

def MatrixSymbolType := ℕ → Type
def MatrixSymbolValue : MatrixSymbolType := @MatrixSymbol

def VectorH2Type := ℕ → Type
def VectorH2Value : VectorH2Type := @VectorH2

def VectorBoundaryL2Type := ℕ → Type
def VectorBoundaryL2Value : VectorBoundaryL2Type := @VectorBoundaryL2

def VectorBoundaryH2Type := ℕ → Type
def VectorBoundaryH2Value : VectorBoundaryH2Type := @VectorBoundaryH2

def SymbolOfFunctionType := ∀ (φ : Circle → ℂ), MemLp φ ∞ circleMeasure → ScalarSymbol
def SymbolOfFunctionValue : SymbolOfFunctionType := @symbolOfFunction

def BoundedSymbolOfFunctionType := ∀ (φ : Circle → ℂ), AEStronglyMeasurable φ circleMeasure →
  ∀ C : ℝ, (∀ᵐ t ∂circleMeasure, ‖φ t‖ ≤ C) → ScalarSymbol
def BoundedSymbolOfFunctionValue : BoundedSymbolOfFunctionType := @boundedSymbolOfFunction

def ContinuousSymbolType := C(Circle, ℂ) → ScalarSymbol
def ContinuousSymbolValue : ContinuousSymbolType := @continuousSymbol

def ContinuousMatrixSymbolType := ∀ {d : ℕ}, Matrix (Fin d) (Fin d) C(Circle, ℂ) → MatrixSymbol d
def ContinuousMatrixSymbolValue : ContinuousMatrixSymbolType := @continuousMatrixSymbol

def MultiplicationType := ScalarSymbol → BoundaryL2 →L[ℂ] BoundaryL2
def MultiplicationValue : MultiplicationType := @multiplication

def BoundaryInclusionType := H2 →L[ℂ] BoundaryL2
def BoundaryInclusionValue : BoundaryInclusionType := @boundaryInclusion

def BoundaryAnalysisType := BoundaryL2 →L[ℂ] H2
def BoundaryAnalysisValue : BoundaryAnalysisType := @boundaryAnalysis

def PositiveProjectionType := BoundaryL2 →L[ℂ] BoundaryL2
def PositiveProjectionValue : PositiveProjectionType := @positiveProjection

def NegativeProjectionType := BoundaryL2 →L[ℂ] BoundaryL2
def NegativeProjectionValue : NegativeProjectionType := @negativeProjection

def ToeplitzType := ScalarSymbol → H2 →L[ℂ] H2
def ToeplitzValue : ToeplitzType := @toeplitz

def HankelType := ScalarSymbol → H2 →L[ℂ] BoundaryL2
def HankelValue : HankelType := @hankel

def MatrixMultiplicationType := ∀ {d : ℕ}, MatrixSymbol d → VectorBoundaryL2 d →L[ℂ] VectorBoundaryL2 d
def MatrixMultiplicationValue : MatrixMultiplicationType := @matrixMultiplication

def MatrixToeplitzType := ∀ {d : ℕ}, MatrixSymbol d → VectorH2 d →L[ℂ] VectorH2 d
def MatrixToeplitzValue : MatrixToeplitzType := @matrixToeplitz

def MatrixHankelType := ∀ {d : ℕ}, MatrixSymbol d → VectorH2 d →L[ℂ] VectorBoundaryL2 d
def MatrixHankelValue : MatrixHankelType := @matrixHankel

def MatrixBoundaryType := ∀ d : ℕ, VectorH2 d →L[ℂ] VectorBoundaryL2 d
def MatrixBoundaryValue : MatrixBoundaryType := @matrixBoundary

def MatrixPositiveProjectionType := ∀ d : ℕ, VectorBoundaryL2 d →L[ℂ] VectorBoundaryL2 d
def MatrixPositiveProjectionValue : MatrixPositiveProjectionType := @matrixPositiveProjection

def MatrixNegativeProjectionType := ∀ d : ℕ, VectorBoundaryL2 d →L[ℂ] VectorBoundaryL2 d
def MatrixNegativeProjectionValue : MatrixNegativeProjectionType := @matrixNegativeProjection

def NonvanishingLoopType := Type
def NonvanishingLoopValue : NonvanishingLoopType := @NonvanishingLoop

def WindingType := NonvanishingLoop → ℤ
def WindingValue : WindingType := @winding

def CoordinateLoopType := NonvanishingLoop
def CoordinateLoopValue : CoordinateLoopType := @coordinateLoop

end ExpandedFA.Toeplitz.Definitions.Spec
