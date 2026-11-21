import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.RealComplexDifferential
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
Independent statements of paper.tex:2324–2329, d12:10-01.
The differential and matrix are the canonical real Fréchet derivative and
its matrix in the ordered basis (1,i). A rotation is exhibited explicitly
as exp(i arg c), equal to c/|c|, with norm one. Oriented angles are represented
by the principal argument of the ordered tangent ratio w/v; equality of
these representatives also gives equality modulo 2π. Local equivalence uses
the canonical BiholomorphicPair, including both open sets and inverse laws.
The counterexample uses the previously constructed factorial-series E.
-/

noncomputable section
namespace Specs.D12Complex.Ch10.Conformality
open _root_.D12Complex

def conformal_differential_type : Prop :=
  ∀ (f : ℂ → ℂ) (c a : ℂ), HasComplexDerivativeAt f c a → c ≠ 0 →
    HasFDerivAt f (c • (1 : ℂ →L[ℝ] ℂ)) a ∧
    (∀ h : ℂ, fderiv ℝ f a h = c * h) ∧
    realDifferentialMatrix f a = !![c.re, -c.im; c.im, c.re] ∧
    LinearMap.det (fderiv ℝ f a).toLinearMap = ‖c‖ ^ 2 ∧
    (realDifferentialMatrix f a).det = ‖c‖ ^ 2 ∧
    0 < (realDifferentialMatrix f a).det

/-- Positive scale, explicit unit rotation, decomposition and length scaling. -/
def multiplication_rotation_dilation_type : Prop :=
  ∀ c : ℂ, c ≠ 0 →
    0 < ‖c‖ ∧ ‖c / (‖c‖ : ℂ)‖ = 1 ∧
    c / (‖c‖ : ℂ) = Complex.exp ((Complex.arg c : ℂ) * Complex.I) ∧
    (∀ h : ℂ, c * h = (‖c‖ : ℂ) * ((c / (‖c‖ : ℂ)) * h)) ∧
    ∀ h : ℂ, ‖c * h‖ = ‖c‖ * ‖h‖

/-- The algebraic tangent ratio, and its oriented angle, are preserved. -/
def multiplication_oriented_angles_type : Prop :=
  ∀ (c v w : ℂ), c ≠ 0 → v ≠ 0 → w ≠ 0 →
    c * v ≠ 0 ∧ c * w ≠ 0 ∧
    (c * w) / (c * v) = w / v ∧
    Complex.arg ((c * w) / (c * v)) = Complex.arg (w / v)

/-- Apply the ratio statement to the actual differential of f. -/
def conformal_tangent_angles_type : Prop :=
  ∀ (f : ℂ → ℂ) (c a : ℂ), HasComplexDerivativeAt f c a → c ≠ 0 →
    ∀ (v w : ℂ), v ≠ 0 → w ≠ 0 →
      fderiv ℝ f a v ≠ 0 ∧ fderiv ℝ f a w ≠ 0 ∧
      fderiv ℝ f a w / fderiv ℝ f a v = w / v ∧
      Complex.arg (fderiv ℝ f a w / fderiv ℝ f a v) = Complex.arg (w / v)

def local_conformal_equivalence_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ) (a : ℂ),
    HolomorphicOn Ω f → a ∈ Ω → deriv f a ≠ 0 →
    _root_.D12Complex.ConformalAt f a ∧
    ∃ (U V : Set ℂ) (h : ℂ → ℂ), a ∈ U ∧ f a ∈ V ∧ U ⊆ Ω ∧
      BiholomorphicPair U V f h ∧ ConformalOn U f

/-- E has no critical points, but its nonzero period prevents injectivity. -/
def exponential_counterexample_type : Prop :=
  ConformalOn Set.univ E ∧
    Function.Periodic E ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) ∧
    (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 ∧
    (∀ z : ℂ, z + (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ z ∧
      E (z + (2 : ℂ) * (Real.pi : ℂ) * Complex.I) = E z) ∧
    ¬Function.Injective E

end Specs.D12Complex.Ch10.Conformality
