import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Evolution.HilbertTriple
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
Independent statement of paper.tex:15096–15133, with item 6 of the
owner-authorized six-boundary erratum. Time is strictly positive. The
embedding, the two Bochner classes, and the distributional derivative are
exactly those of the accepted HilbertTriple interface. No separability or
compact embedding hypothesis is imposed.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal Topology
universe u v

namespace ExpandedFA.Evolution.HilbertTripleTraceSpec

variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A genuine continuous function on the closed time interval. -/
abbrev TraceCurve (H : Type v) [TopologicalSpace H] (T : ℝ) := C(Set.Icc 0 T, H)

/-- Extend by zero only to compare with the existing open-interval L² class.
The extension's values outside the closed interval play no role. -/
def extendCurve {T : ℝ} (f : TraceCurve H T) (t : ℝ) : H :=
  if ht : t ∈ Set.Icc 0 T then f ⟨t, ht⟩ else 0

/-- Agreement with the original V-valued class after the actual injection V→H. -/
def Represents (j : HilbertTriple V H) (T : ℝ)
    (u : HilbertTripleSpec.timeLpValue V 2 T) (f : TraceCurve H T) : Prop :=
  extendCurve f =ᵐ[HilbertTripleSpec.timeMeasureValue T] fun t => j.embedding (u t)

/-- The energy density uses the V',V dual pairing, not an H inner product
on the unembedded derivative. -/
def energyDensity (T : ℝ) (u : HilbertTripleSpec.timeLpValue V 2 T)
    (g : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T) (t : ℝ) : ℝ := g t (u t)

/-- Integrability on the whole open interval in the actual Bochner measure. -/
def PairingIntegrable : Prop := ∀ (T : ℝ)
    (u : HilbertTripleSpec.timeLpValue V 2 T)
    (g : HilbertTripleSpec.timeLpValue (StrongDual ℝ V) 2 T),
  Integrable (energyDensity T u g) (HilbertTripleSpec.timeMeasureValue T)

/-- Uniqueness includes both endpoints and is uniqueness of the curve itself. -/
def RepresentativeUniqueness : Prop := ∀ (j : HilbertTriple V H) (T : ℝ), 0 < T →
  ∀ (u : HilbertTripleSpec.timeLpValue V 2 T) (f g : TraceCurve H T),
    Represents j T u f → Represents j T u g → f = g

/-- Full trace/energy conclusion, including a uniform continuity bound for the
sum of the two original L² norms. The bound on differences directly asserts
continuity into the supremum norm on C([0,T];H), without adding a norm or an
assumed trace certificate to the energy space. -/
def TraceTheorem : Prop := ∀ (j : HilbertTriple V H) (T : ℝ), 0 < T →
  ∃ trace : HilbertTripleSpec.energySpaceValue j T → TraceCurve H T,
    (∀ z, Represents j T z.val.1 (trace z)) ∧
    (∀ z (f : TraceCurve H T), Represents j T z.val.1 f → f = trace z) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ z w,
      ‖trace z - trace w‖ ≤ C * (‖z.val.1 - w.val.1‖ + ‖z.val.2 - w.val.2‖)) ∧
    (∀ z (s t : Set.Icc 0 T),
      IntervalIntegrable (energyDensity T z.val.1 z.val.2) volume s.val t.val ∧
      ‖trace z t‖ ^ 2 - ‖trace z s‖ ^ 2 =
        2 * ∫ r in s.val..t.val, energyDensity T z.val.1 z.val.2 r)

/- Closed proposition types for bindings. -/
def PairingIntegrableExpected : Prop :=
  ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V],
    PairingIntegrable (V := V)

def RepresentativeUniquenessExpected : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    RepresentativeUniqueness (V := V) (H := H)

def TraceTheoremExpected : Prop :=
  ∀ {V : Type u} {H : Type v}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    TraceTheorem (V := V) (H := H)

end ExpandedFA.Evolution.HilbertTripleTraceSpec
