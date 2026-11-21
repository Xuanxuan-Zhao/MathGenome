import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyCayley
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyFactorization

/-! The exponential-factor clauses of `fa2:p4:hardy-halfplane`, paper.tex
18906–18910 and 18944–18963. Measures are positive Borel measures on the
geometric circle; their mass at 1 has no extra 2π factor. The reciprocal
Cayley weight is discussed by its logarithm, without asserting H² membership.
Coefficients are attached to nonzero analytic functions, through their actual
canonical inner–outer factorizations, rather than an arbitrary radial limsup. -/
noncomputable section
open MeasureTheory Set
namespace ExpandedFA.PartIV.HardyExponentialFactor
open HardyDiskSpec HardyLogModulus HardyFactorization HardyCayleySpec

/-- The bounded inverse of the unnormalized Cayley prefactor. -/
def cayleyInverseWeight : H2 := lp.single 2 0 1 - lp.single 2 1 1

def atomMass (μ : Measure _root_.Circle) : ℝ := μ.real {1}
def atomRemainder (μ : Measure _root_.Circle) : Measure _root_.Circle :=
  μ.restrict ({1}ᶜ)
def exponentialInner (a : ℝ) (z : ℂ) : ℂ := Complex.exp (Complex.I * (a : ℂ) * z)

/-- All the factorization data refer to the same actual disk function. -/
def HasSingularMeasure (f : H2) (μ : Measure _root_.Circle) : Prop :=
  ∃ i o : H2, ∃ c : ℂ, IsInner i ∧ IsOuter o ∧ SingularMeasure μ ∧ ‖c‖ = 1 ∧
    (∀ w ∈ disk, eval f w = eval i w * eval o w) ∧
    (∀ w ∈ disk, eval i w = BlaschkeProducts.canonicalProduct i w * singularFactor μ c w)

/-- Existence of a coefficient includes existence of a canonical factorization.
It never assigns an arbitrary coefficient to the zero analytic function. -/
def HasCoefficient (F : ℂ → ℂ) (a : ℝ) : Prop :=
  ∃ g : H2, EqOn (eval g) (transform F) disk ∧
    ∃ μ : Measure _root_.Circle, HasSingularMeasure g μ ∧ a = atomMass μ

namespace Spec

def AtomFactor : Prop := ∀ a : ℝ, 0 ≤ a → ∀ w ∈ disk,
  singularFactor (ENNReal.ofReal a • Measure.dirac (1 : _root_.Circle)) 1 w =
    exponentialInner a (cayley w)

def AtomRemoval : Prop := ∀ μ : Measure _root_.Circle, SingularMeasure μ →
  0 ≤ atomMass μ ∧ SingularMeasure (atomRemainder μ) ∧ atomRemainder μ {1} = 0 ∧
    μ = ENNReal.ofReal (atomMass μ) • Measure.dirac (1 : _root_.Circle) + atomRemainder μ ∧
    ∀ c : ℂ, ∀ w ∈ disk,
      singularFactor μ c w = exponentialInner (atomMass μ) (cayley w) *
        singularFactor (atomRemainder μ) c w

/-- Exact Poisson-log modulus and a bounded outer inverse. This expresses that
there is no additional singular harmonic term in the weight or its reciprocal. -/
def Prefactor : Prop :=
  (∀ w ∈ disk, eval cayleyInverseWeight w = 1 - w) ∧
  IsOuter cayleyInverseWeight ∧ Integrable (boundaryLog cayleyInverseWeight) circleMeasure ∧
  ∀ w ∈ disk,
    Real.log ‖(1 - w)⁻¹‖ = poissonLog (fun t => -boundaryLog cayleyInverseWeight t) w

/-- In the logarithmic representation of the reciprocal weight, any proposed
positive singular measure is zero (so in particular its atom at 1 is zero). -/
def PrefactorSingularMeasureZero : Prop := ∀ μ : Measure _root_.Circle,
  SingularMeasure μ → ∀ c d : ℂ, ‖c‖ = 1 → ‖d‖ = 1 →
  (∀ w ∈ disk, (1 - w)⁻¹ = singularFactor μ c w *
    exponentialFactor (fun t => -boundaryLog cayleyInverseWeight t) d w) → μ = 0

def DiskProduct : Prop := ∀ F G : ℂ → ℂ, ∀ w ∈ disk,
  transform (fun z => F z * G z) w =
    (1 - w) * transform F w * transform G w / normalization

/-- This is the product-outerness justification; membership of the product
in H² is a conclusion, given that the original product belongs to H². -/
def ProductOuter : Prop := ∀ f₁ f₂ f : H2, ∀ i₁ o₁ i₂ o₂ : H2,
  IsInner i₁ → IsOuter o₁ → IsInner i₂ → IsOuter o₂ →
  (∀ w ∈ disk, eval f₁ w = eval i₁ w * eval o₁ w) →
  (∀ w ∈ disk, eval f₂ w = eval i₂ w * eval o₂ w) →
  (∀ w ∈ disk, eval f w = (1 - w) * eval f₁ w * eval f₂ w / normalization) →
  ∃ o : H2, IsOuter o ∧ ∀ w ∈ disk,
    eval o w = (1 - w) * eval o₁ w * eval o₂ w / normalization

def CoefficientExistence : Prop := ∀ F : ℂ → ℂ,
  HardyHalfPlaneRepresentationSpec.IsH2 F →
  (∃ z ∈ HardyHalfPlaneRepresentationSpec.upperHalfPlane, F z ≠ 0) →
  ∃ a : ℝ, 0 ≤ a ∧ HasCoefficient F a

/-- Removing exactly the atom leaves a half-plane Hardy function with no atom
at infinity. The removed factor is the actual analytic exponential e^{iaz}. -/
def ExponentialExtraction : Prop := ∀ F : ℂ → ℂ, ∀ a : ℝ, HasCoefficient F a →
  0 ≤ a ∧ ∃ H : ℂ → ℂ, HardyHalfPlaneRepresentationSpec.IsH2 H ∧
    HasCoefficient H 0 ∧ EqOn F (fun z => exponentialInner a z * H z)
      HardyHalfPlaneRepresentationSpec.upperHalfPlane

def CoefficientUniqueness : Prop := ∀ F : ℂ → ℂ, ∀ a b : ℝ,
  HasCoefficient F a → HasCoefficient F b → a = b

def CoefficientAdditivity : Prop := ∀ F G : ℂ → ℂ,
  HardyHalfPlaneRepresentationSpec.IsH2 F → HardyHalfPlaneRepresentationSpec.IsH2 G →
  HardyHalfPlaneRepresentationSpec.IsH2 (fun z => F z * G z) →
  ∀ a b c : ℝ, HasCoefficient F a → HasCoefficient G b →
    HasCoefficient (fun z => F z * G z) c → c = a + b

end Spec
end ExpandedFA.PartIV.HardyExponentialFactor
