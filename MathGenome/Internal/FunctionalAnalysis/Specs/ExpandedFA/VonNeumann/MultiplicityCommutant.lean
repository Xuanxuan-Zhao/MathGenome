import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.MultiplicityExistence
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.MultiplicityUniqueness

/-!
Separable spectral multiplicity and the commutant, paper.tex,
`fa2:p2:spectral-multiplicity`. We use exactly the upstream native direct
integral, its positive measurable multiplicity, and its canonical zero-extended
strongly measurable operator fields. No operator-norm measurability is imposed.
The classification concerns complex normal operators, with spectral parameter ℂ.
Finite measures of mass zero and zero Hilbert spaces are included.
-/
noncomputable section
open MeasureTheory
namespace ExpandedFA.VonNeumann.MultiplicityCommutant.Spec
universe u
open MultiplicityModel.Spec

/-- Commutation with the actual coordinate multiplication operator. -/
def CommutesCoordinate {μ : Measure ℂ} {m : Multiplicity μ}
    (h : BoundedCoordinate μ) (T : DirectIntegral μ m →L[ℂ] DirectIntegral μ m) : Prop :=
  T.comp (coordinateOperatorValue μ m h) = (coordinateOperatorValue μ m h).comp T

/-- Every decomposable field commutes with all bounded Borel scalar actions. -/
def FieldScalarCommutation : Prop :=
  ∀ {μ : Measure ℂ} {m : Multiplicity μ} (B : OperatorField μ m),
    MultiplicityUniqueness.Spec.IntertwinesScalars (fieldActionValue B)

/-- The easy inclusion in the coordinate commutant, without finiteness. -/
def FieldCoordinateCommutation : Prop :=
  ∀ {μ : Measure ℂ} {m : Multiplicity μ} (h : BoundedCoordinate μ)
    (B : OperatorField μ m), CommutesCoordinate h (fieldActionValue B)

/-- A field is determined modulo a.e. equality by its action on L² sections. -/
def FieldActionFaithful : Prop :=
  ∀ {μ : Measure ℂ} [IsFiniteMeasure μ] {m : Multiplicity μ}
    (B C : OperatorField μ m), fieldActionValue B = fieldActionValue C ↔ B.AEEq C

/-- General bounded scalar-module maps, not merely unitaries, decompose. -/
def ScalarDecomposition : Prop :=
  ∀ (μ : Measure ℂ) [IsFiniteMeasure μ] (m : Multiplicity μ)
    (T : DirectIntegral μ m →L[ℂ] DirectIntegral μ m),
    MultiplicityUniqueness.Spec.IntertwinesScalars T →
      ∃ B : OperatorField μ m, fieldActionValue B = T

/-- Fuglede and the scalar Borel calculus must be proved for arbitrary bounded T. -/
def CoordinateScalarCommutation : Prop :=
  ∀ (μ : Measure ℂ) [IsFiniteMeasure μ] (m : Multiplicity μ)
    (h : BoundedCoordinate μ) (T : DirectIntegral μ m →L[ℂ] DirectIntegral μ m),
    CommutesCoordinate h T → MultiplicityUniqueness.Spec.IntertwinesScalars T

/-- Exact norm, with the zero extensions having the same norms as the fibers. -/
def FieldNormIdentity : Prop :=
  ∀ (μ : Measure ℂ) [IsFiniteMeasure μ] (m : Multiplicity μ)
    (B : OperatorField μ m), ‖fieldActionValue B‖ = fieldNorm B

/-- Full coordinate-model commutant and its quantitative assertion. -/
def Commutant : Prop :=
  ∀ (μ : Measure ℂ) [IsFiniteMeasure μ] (m : Multiplicity μ)
    (h : BoundedCoordinate μ) (T : DirectIntegral μ m →L[ℂ] DirectIntegral μ m),
    CommutesCoordinate h T ↔
      ∃ B : OperatorField μ m, fieldActionValue B = T ∧ ‖T‖ = fieldNorm B

/-- No representative choices are left in the bijective commutant description. -/
def EssentialCommutant : Prop :=
  ∀ (μ : Measure ℂ) [IsFiniteMeasure μ] (m : Multiplicity μ)
    (h : BoundedCoordinate μ),
    Function.Injective (essentialFieldActionValue (μ := μ) (m := m)) ∧
    (∀ T, CommutesCoordinate h T ↔
      ∃ B : EssentialOperatorField μ m, essentialFieldActionValue B = T) ∧
    ∀ B : EssentialOperatorField μ m,
      ‖essentialFieldActionValue B‖ = essentialFieldNormValue B

/-- The commutant on the original Hilbert space, transported by the same
unitary which supplies its coordinate model. No extra normality or nonzero
hypothesis is imposed on the commuting operator. -/
def OriginalCommutant : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : H →L[ℂ] H) (μ : Measure ℂ) [IsFiniteMeasure μ]
    (m : Multiplicity μ) (h : BoundedCoordinate μ)
    (U : DirectIntegral μ m ≃ₗᵢ[ℂ] H),
    (∀ f, U (coordinateOperatorValue μ m h f) = N (U f)) →
    ∀ T : H →L[ℂ] H,
      T.comp N = N.comp T ↔
        ∃ B : OperatorField μ m,
          (∀ f, T (U f) = U (fieldActionValue B f)) ∧ ‖T‖ = fieldNorm B

/-- Complete source conclusion: existence supported on the spectrum,
classification by measure class and multiplicity, and the full commutant. -/
def SpectralMultiplicity : Prop :=
  MultiplicityExistence.Spec.Existence.{u} ∧ MultiplicityUniqueness.Spec.Classification ∧
    Commutant ∧ EssentialCommutant ∧ OriginalCommutant.{u}

end ExpandedFA.VonNeumann.MultiplicityCommutant.Spec
