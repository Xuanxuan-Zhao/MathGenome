import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Moments.StieltjesExistence
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Moments.FriedrichsKreinResolventBounds

/-! Independent statements for fa2:p3:stieltjes-determinacy. Measures on ℝ
concentrated on [0,∞) are the extension-by-zero version of measures on that
half-line. All absolute moments, zero mass and nondense polynomial images are
included. Nonnegative extensions are in the original polynomial Hilbert space.
No essential-self-adjointness hypothesis or conclusion is substituted. -/
noncomputable section
namespace ExpandedFA.Moments.StieltjesDeterminacy
open MeasureTheory Unbounded PolynomialMomentHilbertSpaceSpec
open StieltjesExistence FriedrichsExtension ClosedNonnegativeForms
open KreinNonnegativeExtension FriedrichsKreinResolventBounds

/-- The closure of the canonical domain-carrying polynomial multiplication. -/
abbrev minimalClosure (m : ℕ → ℝ) (h : HankelNonnegative m) :=
  (multiplicationValue m h).closure

/-- Uniqueness among all finite positive representing measures. -/
def Determinate (m : ℕ → ℝ) : Prop := ∃! μ : Measure ℝ, Represents μ m

/-- The actual Friedrichs form closure and the unshifted Krein energy
construction for the closed canonical operator have the same associated
operator. Existential witnesses avoid choosing arbitrary realizations of the
completed form spaces; no equality certificate is assumed. -/
def ExtremalsEqual (m : ℕ → ℝ) (h : HankelNonnegative m) : Prop :=
  ∃ hs : SemiboundedSymmetric (minimalClosure m h) 0,
  ∃ F : FormClosure (operatorForm (minimalClosure m h) 0 hs),
  ∃ K : Construction (minimalClosure m h) hs,
    F.closedForm.Associated K.extension

/-- Real Stieltjes transform on its nonsingular negative-axis parameters. -/
def stieltjesTransform (μ : Measure ℝ) (a : ℝ) : ℝ :=
  ∫ t : ℝ, (t + a)⁻¹ ∂μ

namespace Spec

def Determinacy : Prop := ∀ (m : ℕ → ℝ) (h : HankelNonnegative m),
  HankelNonnegative (shiftedMoments m) →
    (Determinate m ↔ ∃! A, NonnegativeExtension m h A)

def ExtremalCriterion : Prop := ∀ (m : ℕ → ℝ) (h : HankelNonnegative m),
  HankelNonnegative (shiftedMoments m) →
    ((∃! A, NonnegativeExtension m h A) ↔ ExtremalsEqual m h)

/-- The criterion for every chosen realization of the actual extremal
constructions, with operator equality including the domains. -/
def ChosenExtremalCriterion : Prop :=
  ∀ (m : ℕ → ℝ) (h : HankelNonnegative m),
    HankelNonnegative (shiftedMoments m) →
    ∀ (hs : SemiboundedSymmetric (minimalClosure m h) 0)
      (F : FormClosure (operatorForm (minimalClosure m h) 0 hs))
      (K : Construction (minimalClosure m h) hs)
      (SF : Operator ℂ (MomentHilbertSpace m h) (MomentHilbertSpace m h)),
      F.closedForm.Associated SF → (Determinate m ↔ SF = K.extension)

def MeasureImpliesExtension : Prop := ∀ (m : ℕ → ℝ) (h : HankelNonnegative m),
  HankelNonnegative (shiftedMoments m) →
    Determinate m → ∃! A, NonnegativeExtension m h A

def ZeroMass : Prop := ∀ (m : ℕ → ℝ) (h : HankelNonnegative m),
  m 0 = 0 → Determinate m

/-- A transform statement for arbitrary finite positive measures, without
moment or density restrictions. -/
def TransformInjectivity : Prop :=
  ∀ (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν],
    μ (Set.Iio 0) = 0 → ν (Set.Iio 0) = 0 →
    (∀ a : ℝ, 0 < a → stieltjesTransform μ a = stieltjesTransform ν a) → μ = ν

/-- This includes arbitrary representing measures, whether or not polynomials
are dense in their full L² spaces. -/
def CompressedCoefficient : Prop :=
  ∀ (m : ℕ → ℝ) (h : HankelNonnegative m),
    HankelNonnegative (shiftedMoments m) → ExtremalsEqual m h →
    ∀ (μ ν : Measure ℝ), Represents μ m → Represents ν m →
    ∀ a : ℝ, 0 < a → stieltjesTransform μ a = stieltjesTransform ν a
end Spec
end ExpandedFA.Moments.StieltjesDeterminacy
