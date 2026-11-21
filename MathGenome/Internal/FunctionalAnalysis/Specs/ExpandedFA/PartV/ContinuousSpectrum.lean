import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.FourierHilbertScale
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Multiplication.RealAndContinuousMultiplierSpectra
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! The real line is modeled as `EuclideanSpace ℝ (Fin 1)`, with its canonical
Lebesgue measure, so that the accepted Fourier and Sobolev interfaces apply.
The coordinate map `ξ ↦ ξ 0` is its canonical identification with ℝ.
Source: paper.tex, `fa2:p5:continuous-spectrum-example` (the whole example and proof).
-/
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexInnerProductSpace

namespace ExpandedFA.PartV.ContinuousSpectrum
open ExpandedFA.Fourier ExpandedFA.Sobolev.FourierScale

abbrev Line := Euclidean 1
abbrev Space := L2 1
abbrev H2 := Hs 1 2

/-- The exact real reciprocal symbol for the 2π Fourier convention. -/
def realSymbol (ξ : Line) : ℝ := (frequencyWeight ξ)⁻¹

def symbol (ξ : Line) : ℂ := realSymbol ξ

/-- Distributional I - ∂², independently of any Fourier construction. -/
def differential (T : Tempered ℂ 1) : Tempered ℂ 1 :=
  T - temperedPartial 0 (temperedPartial 0 T)

/-- The inclusion must realize the actual Sobolev distribution, have exactly
H² as its image in L², and the operator must be distributional I - ∂².
These clauses rule out an arbitrary abstract isomorphism between Hilbert spaces. -/
def DomainAndInverse (J : H2 →L[ℂ] Space) (A : H2 →L[ℂ] Space)
    (R : Space →L[ℂ] Space) : Prop :=
  Function.Injective J ∧
  (∀ u, realization u = Lp.toTemperedDistribution (J u)) ∧
  (∀ f : Space, (∃ u, J u = f) ↔ MemHs 2 (Lp.toTemperedDistribution f)) ∧
  (∀ u, Lp.toTemperedDistribution (A u) = differential (realization u)) ∧
  (∀ f, ∃ u : H2, J u = R f ∧ A u = f) ∧
  (∀ u, R (A u) = J u)

/-- Fourier multiplication specifies the inverse on every L² input. -/
def FourierFormula (R : Space →L[ℂ] Space) : Prop :=
  ∀ f : Space, (l2Fourier 1 (R f) : Line → ℂ) =ᵐ[volume]
    fun ξ => symbol ξ * l2Fourier 1 f ξ

/-- Explicit normalized disjoint indicator vectors in frequency space, whose
physical inverse Fourier transforms have separated images under R. -/
def SeparatedIndicators (R : Space →L[ℂ] Space) : Prop :=
  ∃ (E : ℕ → Set Line) (v : ℕ → Space),
    Pairwise (fun n k => Disjoint (E n) (E k)) ∧
    (∀ n, MeasurableSet (E n) ∧ 0 < volume (E n) ∧ volume (E n) < ∞) ∧
    (∀ n, ∃ c : ℝ, 0 < c ∧
      (v n : Line → ℂ) =ᵐ[volume] (E n).indicator (fun _ => (c : ℂ))) ∧
    (∀ n, ‖v n‖ = 1) ∧
    (∀ n k, n ≠ k → inner ℂ (v n) (v k) = 0) ∧
    (∀ n k, n ≠ k → (1 / 2 : ℝ) ≤
      ‖R ((l2Fourier 1).symm (v n)) - R ((l2Fourier 1).symm (v k))‖)

/-- Actual real-valued physical L², distinct from the Hermitian Fourier model. -/
abbrev RealSpace := Lp ℝ 2 (volume : Measure Line)
abbrev RealH2 := RealHs 1 2

def complexEmbedding : RealSpace →L[ℝ] Space := Complex.ofRealCLM.compLpL 2 volume
def physicalRealPart : Space →L[ℝ] RealSpace := Complex.reCLM.compLpL 2 volume
def physicalImagPart : Space →L[ℝ] RealSpace := Complex.imCLM.compLpL 2 volume

def realRegularL2 (f : RealSpace) : Tempered ℝ 1 :=
  restrictTempered (Lp.toTemperedDistribution (complexEmbedding f))

def RealDomainAndInverse (J A : RealH2 →L[ℝ] RealSpace)
    (R : RealSpace →L[ℝ] RealSpace) : Prop :=
  Function.Injective J ∧
  (∀ u, realRealization u = realRegularL2 (J u)) ∧
  (∀ f : RealSpace, (∃ u, J u = f) ↔ realMemHs 2 (realRegularL2 f)) ∧
  (∀ u, Lp.toTemperedDistribution (complexEmbedding (A u)) =
    differential (complexifyTempered (realRealization u))) ∧
  (∀ f, ∃ u : RealH2, J u = R f ∧ A u = f) ∧
  (∀ u, R (A u) = J u)

/-- Fourier formula for actual real-valued physical inputs. -/
def RealFourierFormula (R : RealSpace →L[ℝ] RealSpace) : Prop :=
  ∀ f : RealSpace, (l2Fourier 1 (complexEmbedding (R f)) : Line → ℂ) =ᵐ[volume]
    fun ξ => symbol ξ * l2Fourier 1 (complexEmbedding f) ξ

/-- The checked complex operator is the natural complexification of the real
physical operator: the embedding is pointwise ofReal, and every input splits
into its real and imaginary parts. Compatibility includes the exact H² domain. -/
def RealCompatibility (J A : H2 →L[ℂ] Space) (R : Space →L[ℂ] Space)
    (Jr Ar : RealH2 →L[ℝ] RealSpace) (Rr : RealSpace →L[ℝ] RealSpace) : Prop :=
  (∀ u : RealH2, complexEmbedding (Jr u) = J (realCoordinates 1 2 u)) ∧
  (∀ u : RealH2, complexEmbedding (Ar u) = A (realCoordinates 1 2 u)) ∧
  (∀ f, complexEmbedding (Rr f) = R (complexEmbedding f)) ∧
  (∀ f : Space, f = complexEmbedding (physicalRealPart f) +
    Complex.I • complexEmbedding (physicalImagPart f)) ∧
  (∀ f : Space, R f = complexEmbedding (Rr (physicalRealPart f)) +
    Complex.I • complexEmbedding (Rr (physicalImagPart f)))

end ExpandedFA.PartV.ContinuousSpectrum

namespace Specs.ExpandedFA.PartV.ContinuousSpectrum
open _root_.ExpandedFA.PartV.ContinuousSpectrum
open _root_.ExpandedFA.Multiplication

/-- The one-dimensional Euclidean model is the usual real line, with its
coordinate, metric, linear structure and Lebesgue measure preserved. -/
def RealLineModel : Prop :=
  ∃ e : Line ≃ₗᵢ[ℝ] ℝ, (∀ ξ, e ξ = ξ 0) ∧ MeasurePreserving e volume volume

/-- The complete example, including the unbounded domain and the explicit
noncompactness witnesses requested in the assigned obligation. -/
def Result : Prop :=
  RealLineModel ∧ ∃ (J : H2 →L[ℂ] Space) (A : H2 →L[ℂ] Space) (R : Space →L[ℂ] Space),
    DomainAndInverse J A R ∧ FourierFormula R ∧
    IsSelfAdjoint R ∧ ‖R‖ = 1 ∧
    spectrum ℂ R = Complex.ofReal '' Set.Icc (0 : ℝ) 1 ∧
    (∀ (z : ℂ) (f : Space), R f = z • f → f = 0) ∧
    ¬ IsCompactOperator R ∧ SeparatedIndicators R

/-- Both scalar cases; the complex spectrum in this assertion is the spectrum
of the natural complexification specified by RealCompatibility. -/
def RealResult : Prop :=
  ∃ (J A : H2 →L[ℂ] Space) (R : Space →L[ℂ] Space)
    (Jr Ar : RealH2 →L[ℝ] RealSpace) (Rr : RealSpace →L[ℝ] RealSpace),
    DomainAndInverse J A R ∧ FourierFormula R ∧
    RealDomainAndInverse Jr Ar Rr ∧ RealFourierFormula Rr ∧
    RealCompatibility J A R Jr Ar Rr ∧
    IsSelfAdjoint Rr ∧ ‖Rr‖ = 1 ∧
    spectrum ℂ R = Complex.ofReal '' Set.Icc (0 : ℝ) 1 ∧
    (∀ (z : ℝ) (f : RealSpace), Rr f = z • f → f = 0) ∧
    ¬ IsCompactOperator Rr

/-- The real regular distribution uses the original bilinear test integral. -/
def RealRegularFormula : Prop :=
  ∀ (f : RealSpace) (φ : _root_.ExpandedFA.Fourier.Schwartz ℝ 1),
    realRegularL2 f φ = ∫ x, φ x * f x

def EssentialRange : Prop :=
  multiplierEssentialRange (volume : Measure Line) symbol =
    Complex.ofReal '' Set.Icc (0 : ℝ) 1

def NullLevels : Prop :=
  ∀ z : ℂ, volume {ξ : Line | symbol ξ = z} = 0

def SymbolRange : Prop :=
  Set.range realSymbol = Set.Ioc (0 : ℝ) 1

end Specs.ExpandedFA.PartV.ContinuousSpectrum
