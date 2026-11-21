import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.ProperSupportConvolution
import Mathlib.Algebra.MvPolynomial.Basic

/-! Independent formulation of paper.tex, fa2:p4:fundamental-solution.
The coefficient field is ℝ or ℂ. The parameter s denotes the common scale in
D_j = s ∂_j: s = 1 gives ordinary derivatives, and over ℂ the manuscript's
normalization is s = (2πi)⁻¹. Nonzero s and nonzero polynomial symbols are the
only restrictions; dimension zero and order zero are included. Distributions
are the actual continuous scalar-linear functionals on the LF test space. -/
noncomputable section
open Set TopologicalSpace
open scoped Distributions

namespace ExpandedFA.Fourier.MalgrangeEhrenpreis
open ExpandedFA.Distributions

abbrev GlobalTests (𝕜 : Type) [RCLike 𝕜] (d : ℕ) := Tests 𝕜 (⊤ : Opens (Domain d))
abbrev GlobalDistribution (𝕜 : Type) [RCLike 𝕜] (d : ℕ) :=
  ScalarDistribution 𝕜 (⊤ : Opens (Domain d))
abbrev Symbol (𝕜 : Type) (d : ℕ) [CommSemiring 𝕜] := MvPolynomial (Fin d) 𝕜

/-- The transpose symbol P(-s∂) acting on compactly supported tests. -/
def testOperator {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (s : 𝕜) (P : Symbol 𝕜 d) :
    GlobalTests 𝕜 d →ₗ[𝕜] GlobalTests 𝕜 d :=
  P.coeff.sum fun α c =>
    ((c * (-s) ^ (∑ i, α i)) •
      (testPartialCLM (𝕜 := 𝕜) (Ω := ⊤) (multiIndexWord α)).toLinearMap :
      GlobalTests 𝕜 d →ₗ[𝕜] GlobalTests 𝕜 d)

/-- The finite sum of the upstream ordinary distribution derivatives is an
actual distribution. Its transpose identity is a separate theorem below. -/
def operator {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (s : 𝕜) (P : Symbol 𝕜 d)
    (u : GlobalDistribution 𝕜 d) : GlobalDistribution 𝕜 d :=
  P.coeff.sum fun α c => (c * s ^ (∑ i, α i)) •
    Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue 𝕜 d ⊤ α u

/-- Evaluation at zero, with continuity inherited from bounded function evaluation. -/
def diracZero (𝕜 : Type) [RCLike 𝕜] (d : ℕ) : GlobalDistribution 𝕜 d :=
  (BoundedContinuousFunction.evalCLM 𝕜 (0 : Domain d)).comp
    (TestFunction.toBoundedContinuousFunctionCLM 𝕜)

end ExpandedFA.Fourier.MalgrangeEhrenpreis

namespace Specs.ExpandedFA.Fourier.MalgrangeEhrenpreis
open _root_.ExpandedFA.Distributions
open _root_.ExpandedFA.Fourier.MalgrangeEhrenpreis

/-- Explicit bridge from the upstream multi-index derivatives to the
transpose action. This fixes all coefficients and signs. -/
def OperatorFormula : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (s : 𝕜) (P : Symbol 𝕜 d) (u : GlobalDistribution 𝕜 d) (φ : GlobalTests 𝕜 d),
  operator s P u φ = u (testOperator s P φ)

/-- The full existence conclusion, including continuity (E is a continuous
linear map), both scalar fields, and the manuscript's normalized operators. -/
def FundamentalSolution : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (s : 𝕜), s ≠ 0 → ∀ (P : Symbol 𝕜 d), P ≠ 0 →
  ∃ E : GlobalDistribution 𝕜 d, operator s P E = diracZero 𝕜 d

/-- The separate convolution conclusion holds for every fundamental solution,
not merely a chosen one. The actual support-valid upstream convolution is used. -/
def CompactRhs : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (s : 𝕜) (P : Symbol 𝕜 d) (E v : GlobalDistribution 𝕜 d),
  IsCompact (distributionSupport v) → operator s P E = diracZero 𝕜 d →
  ∃ h : Convolvable E v,
    operator s P
      (Specs.ExpandedFA.Distributions.ProperSupportConvolution.convolutionOperationValue
        𝕜 d E v h) = v

def OrderZero : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (s c : 𝕜), c ≠ 0 →
  operator s (MvPolynomial.C c) (c⁻¹ • diracZero 𝕜 d) = diracZero 𝕜 d

/-- Every symbol in zero variables is a constant. No positive-dimensional
assumption is attached to the fundamental-solution theorem. -/
def ZeroDimension : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (s : 𝕜)
    (P : Symbol 𝕜 0), P ≠ 0 →
  ∃ E : GlobalDistribution 𝕜 0, operator s P E = diracZero 𝕜 0

/-- An explicit pairing form useful for constructing E without changing its
required topology. The equality is the full distribution equation. -/
def PairingCriterion : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (s : 𝕜) (P : Symbol 𝕜 d) (E : GlobalDistribution 𝕜 d),
  operator s P E = diracZero 𝕜 d ↔
    ∀ φ : GlobalTests 𝕜 d, E (testOperator s P φ) = φ 0

end Specs.ExpandedFA.Fourier.MalgrangeEhrenpreis
