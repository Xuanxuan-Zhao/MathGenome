import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.BochnerDefinitions

/-!
Independent interface for paper.tex:15084–15094 and the distributional time
spaces used in 15096–15155 and 15212–15229. All Hilbert spaces here are real.
No separability, finite dimension, compact embedding, or lower norm bound is
included in the embedding data. The dual always has its operator norm.
The trace/energy and evolution theorems are separate obligations.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal Topology ContDiff
universe u v w

namespace ExpandedFA.Evolution

/-- The data of V ↪ H. `embedding` is bounded for the original, separate norms. -/
structure HilbertTriple (V : Type u) (H : Type v)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] where
  embedding : V →L[ℝ] H
  injective : Function.Injective embedding
  denseRange : DenseRange embedding

namespace HilbertTripleSpec

section Triple
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Canonical Riesz/adjoint construction; its pairing is specified below. -/
def pivotValue (j : HilbertTriple V H) : H →L[ℝ] StrongDual ℝ V :=
  (InnerProductSpace.toDual ℝ V).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.adjoint j.embedding)

def intoDualValue (j : HilbertTriple V H) : V →L[ℝ] StrongDual ℝ V :=
  (pivotValue j).comp j.embedding

def MakeExpected := (J : V →L[ℝ] H) → Function.Injective J →
  DenseRange J → HilbertTriple V H

def makeValue : MakeExpected (V := V) (H := H) := fun J hi hd => ⟨J, hi, hd⟩

def PivotExpected := HilbertTriple V H → H →L[ℝ] StrongDual ℝ V

def IntoDualExpected := HilbertTriple V H → V →L[ℝ] StrongDual ℝ V

def PairingExpected : Prop := ∀ (j : HilbertTriple V H) (h : H) (v : V),
  pivotValue j h v = inner ℝ h (j.embedding v)

def PivotInjectiveExpected : Prop := ∀ j : HilbertTriple V H,
  Function.Injective (pivotValue j)

def PivotDenseExpected : Prop := ∀ j : HilbertTriple V H,
  DenseRange (pivotValue j)

def IntoDualInjectionExpected : Prop := ∀ j : HilbertTriple V H,
  Function.Injective (intoDualValue j) ∧ DenseRange (intoDualValue j)

def CompatibilityExpected : Prop := ∀ (j : HilbertTriple V H) (u v : V),
  intoDualValue j u v = inner ℝ (j.embedding u) (j.embedding v)

/-- Distinct V, H, and V' norms: neither injection is asserted isometric. -/
def NormBoundsExpected : Prop := ∀ (j : HilbertTriple V H) (v : V) (h : H)
    (f : StrongDual ℝ V),
  ‖j.embedding v‖ ≤ ‖j.embedding‖ * ‖v‖ ∧
  ‖pivotValue j h‖ ≤ ‖j.embedding‖ * ‖h‖ ∧
  ‖f v‖ ≤ ‖f‖ * ‖v‖

end Triple

/-- Lebesgue time measure on the open interval. Endpoints have no mass. -/
def timeMeasureValue (T : ℝ) : Measure ℝ := volume.restrict (Set.Ioo 0 T)

def TimeMeasureExpected := ℝ → Measure ℝ

def TimeLpExpected := ∀ (E : Type w) [NormedAddCommGroup E]
  (p : ℝ≥0∞) [Fact (1 ≤ p)], ℝ → Type w

/-- Strongly measurable Bochner classes; no separability hypothesis on E. -/
abbrev timeLpValue : TimeLpExpected := fun E _ p _ T =>
  FunctionSpaces.BochnerDefinitionsSpec.BochnerLpValue E p (timeMeasureValue T)

def TestExpected := ℝ → (ℝ → ℝ) → Prop

def testValue : TestExpected := fun T φ =>
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Set.Ioo 0 T

def DerivativeExpected := ∀ {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E],
  ℝ → (ℝ → E) → (ℝ → E) → Prop

/-- Vector-valued distributional derivative: the sign and derivative belong to
exactly the scalar time test. Local integrability prevents interpreting
totalized integrals of nonintegrable functions as distributions. -/
def derivativeValue : DerivativeExpected := fun T u g =>
  LocallyIntegrableOn u (Set.Ioo 0 T) ∧ LocallyIntegrableOn g (Set.Ioo 0 T) ∧
  ∀ φ : ℝ → ℝ, testValue T φ →
    (∫ t, deriv φ t • u t ∂timeMeasureValue T) =
      -(∫ t, φ t • g t ∂timeMeasureValue T)

def TimeLpStrongExpected : Prop := ∀ {E : Type w} [NormedAddCommGroup E]
  (p : ℝ≥0∞) [Fact (1 ≤ p)] (T : ℝ) (u : timeLpValue E p T),
  FunctionSpaces.BochnerDefinitionsSpec.StrongMeasurableValue (timeMeasureValue T) u

/-- Graph presentation of W^{1,p}(0,T;E). Both components are a.e. quotients;
uniqueness of the second component is a theorem, not an assumed certificate. -/
def SobolevExpected := ∀ (E : Type w) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (p : ℝ≥0∞) [Fact (1 ≤ p)], ℝ → Type w

abbrev sobolevValue : SobolevExpected := fun E _ _ p _ T =>
  {z : timeLpValue E p T × timeLpValue E p T //
    derivativeValue T (z.1 : ℝ → E) (z.2 : ℝ → E)}

def SobolevNormExpected := ∀ {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (p : ℝ≥0∞) [Fact (1 ≤ p)] (T : ℝ), sobolevValue E p T → ℝ

def sobolevNormValue : SobolevNormExpected := fun _ _ _ z => ‖z.val.1‖ + ‖z.val.2‖

/-- Uniqueness on the open interval, hence uniqueness in every time Lᵖ quotient. -/
def DerivativeUniqueExpected : Prop := ∀ {E : Type w} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E] (T : ℝ) (u g h : ℝ → E),
  derivativeValue T u g → derivativeValue T u h → g =ᵐ[timeMeasureValue T] h

def DerivativeCongrExpected : Prop := ∀ {E : Type w} [NormedAddCommGroup E]
  [NormedSpace ℝ E] (T : ℝ) (u u' g g' : ℝ → E),
  u =ᵐ[timeMeasureValue T] u' → g =ᵐ[timeMeasureValue T] g' →
  (derivativeValue T u g ↔ derivativeValue T u' g')

def SobolevExtExpected : Prop := ∀ {E : Type w} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E] (p : ℝ≥0∞) [Fact (1 ≤ p)] (T : ℝ)
  (u v : sobolevValue E p T), u.val.1 = v.val.1 → u = v

/-- Both Bochner integrals defining the distribution identity are genuine integrals. -/
def TestIntegrabilityExpected : Prop := ∀ {E : Type w} [NormedAddCommGroup E]
  [NormedSpace ℝ E] (T : ℝ) (u g : ℝ → E), derivativeValue T u g →
  ∀ φ, testValue T φ →
    Integrable (fun t => deriv φ t • u t) (timeMeasureValue T) ∧
    Integrable (fun t => φ t • g t) (timeMeasureValue T)

section TripleTime
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def TripleDerivativeExpected := (j : HilbertTriple V H) → (T : ℝ) →
  timeLpValue V 2 T → timeLpValue (StrongDual ℝ V) 2 T → Prop

/-- u' is taken after the canonical embedding V → H → V'. -/
def tripleDerivativeValue : TripleDerivativeExpected (V := V) (H := H) :=
  fun j T u g => derivativeValue T (fun t => intoDualValue j (u t)) g

def EnergySpaceExpected := HilbertTriple V H → ℝ → Type u

/-- L²(V) ∩ W^{1,2}(V') as the graph (u,u'). -/
abbrev energySpaceValue : EnergySpaceExpected (V := V) (H := H) := fun j T =>
  {z : timeLpValue V 2 T × timeLpValue (StrongDual ℝ V) 2 T //
    tripleDerivativeValue j T z.1 z.2}

def EnergyNormExpected := (j : HilbertTriple V H) → (T : ℝ) →
  energySpaceValue j T → ℝ

/-- The sum of the two original L² norms used by the trace theorem. -/
def energyNormValue : EnergyNormExpected (V := V) (H := H) :=
  fun _ _ z => ‖z.val.1‖ + ‖z.val.2‖

def EnergyExtExpected : Prop := ∀ (j : HilbertTriple V H) (T : ℝ)
  (u v : energySpaceValue j T), u.val.1 = v.val.1 → u = v

/-- Scalar testing uses the dual pairing; the H product occurs only after J. -/
def TriplePairingExpected : Prop := ∀ (j : HilbertTriple V H) (T : ℝ)
  (u : timeLpValue V 2 T) (g : timeLpValue (StrongDual ℝ V) 2 T),
  tripleDerivativeValue j T u g → ∀ (v : V) (φ : ℝ → ℝ), testValue T φ →
    (∫ t, deriv φ t * inner ℝ (j.embedding (u t)) (j.embedding v) ∂timeMeasureValue T) =
      -(∫ t, φ t * g t v ∂timeMeasureValue T)

end TripleTime

/- Full closed types for the submission bindings (including all Hilbert hypotheses). -/
def MakeTypeExpected :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    MakeExpected (V := V) (H := H)

def PivotTypeExpected :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    PivotExpected (V := V) (H := H)

def IntoDualTypeExpected :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    IntoDualExpected (V := V) (H := H)

def PairingLawExpected :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    PairingExpected (V := V) (H := H)

def PivotInjectiveLawExpected :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    PivotInjectiveExpected (V := V) (H := H)

def PivotDenseLawExpected :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    PivotDenseExpected (V := V) (H := H)

def IntoDualInjectionLawExpected :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    IntoDualInjectionExpected (V := V) (H := H)

def CompatibilityLawExpected :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    CompatibilityExpected (V := V) (H := H)

def NormBoundsLawExpected :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    NormBoundsExpected (V := V) (H := H)

def TripleDerivativeTypeExpected :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    TripleDerivativeExpected (V := V) (H := H)

def EnergySpaceTypeExpected :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    EnergySpaceExpected (V := V) (H := H)

def EnergyNormTypeExpected :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    EnergyNormExpected (V := V) (H := H)

def EnergyExtLawExpected :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    EnergyExtExpected (V := V) (H := H)

def TriplePairingLawExpected :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    TriplePairingExpected (V := V) (H := H)

end HilbertTripleSpec
end ExpandedFA.Evolution
