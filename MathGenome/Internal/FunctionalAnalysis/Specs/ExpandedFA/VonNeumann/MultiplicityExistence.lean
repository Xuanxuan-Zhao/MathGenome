import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.MultiplicityModel
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.NormalAlgebraControlMeasure

/-!
Existence in `fa2:p2:spectral-multiplicity`, paper.tex 12136–12165.
The measure lives on ℂ, with its Borel sigma algebra, and is carried by the
actual spectrum. Its null ideal is that of the spectral resolution. Thus it
really is a scalar control measure, rather than an arbitrary model measure.
The space of sections and coordinate operator are the shared native L² model.
No nonzero-space or positive-mass hypothesis is imposed.
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ExpandedFA.VonNeumann.MultiplicityExistence.Spec
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The finite measure on ℂ is carried by the compact spectrum. -/
def SpectrumSupported (N : H →L[ℂ] H) (μ : Measure ℂ) : Prop :=
  μ (spectrum ℂ N)ᶜ = 0

/-- Null sets of μ are exactly the zero spectral projections, on all Borel
sets of ℂ. The PVM itself is defined on the spectrum. -/
def ComplexControlMeasure (N : H →L[ℂ] H)
    (E : SpectralMeasure.ProjectionValuedMeasure (spectrum ℂ N) H)
    (μ : Measure ℂ) : Prop :=
  ∀ B : Set ℂ, MeasurableSet B → (E (Subtype.val ⁻¹' B) = 0 ↔ μ B = 0)

/-- A genuine surjective linear isometry, intertwining the original operator
with the already defined coordinate multiplication on the direct integral.
The multiplicity is measurable and strictly positive μ-almost everywhere. -/
def Model (N : H →L[ℂ] H) (μ : Measure ℂ) : Prop :=
  ∃ (m : MultiplicityModel.Spec.Multiplicity μ)
    (h : MultiplicityModel.Spec.BoundedCoordinate μ)
    (U : MultiplicityModel.Spec.DirectIntegral μ m ≃ₗᵢ[ℂ] H),
    ∀ f, U (MultiplicityModel.Spec.coordinateOperatorValue μ m h f) = N (U f)

/-- Full existence assertion. The resolution, finite control measure,
multiplicity and unitary all refer to the same original normal operator. -/
def Existence : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (N : H →L[ℂ] H), IsStarNormal N →
    ∃ (E : SpectralMeasure.ProjectionValuedMeasure (spectrum ℂ N) H)
      (μ : Measure ℂ),
      SpectralMeasure.NormalPVM.Spec.Resolves N E ∧ IsFiniteMeasure μ ∧
      SpectrumSupported N μ ∧ ComplexControlMeasure N E μ ∧ Model N μ

/-- The zero Hilbert space is represented using exactly the zero measure. -/
def ZeroModel : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Subsingleton H] (N : H →L[ℂ] H), Model N 0

/-- The control measure part, together with the coordinate bound needed to
form M_z. This is a preliminary result, not a substitute for `Existence`. -/
def FiniteComplexControlMeasure : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (N : H →L[ℂ] H), IsStarNormal N →
    ∃ (E : SpectralMeasure.ProjectionValuedMeasure (spectrum ℂ N) H)
      (μ : Measure ℂ),
      SpectralMeasure.NormalPVM.Spec.Resolves N E ∧ IsFiniteMeasure μ ∧
      SpectrumSupported N μ ∧ ComplexControlMeasure N E μ ∧
      MultiplicityModel.Spec.BoundedCoordinate μ

end ExpandedFA.VonNeumann.MultiplicityExistence.Spec
