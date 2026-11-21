import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness

/-!
Full conclusion of `fa2:p3:hyperbolic-triple`, paper.tex:15211–15438.
The original real Hilbert spaces and separate norms are retained. The solution
uses the accepted vector distributional derivative graph, including strong
Bochner L² acceleration. Equality of acceleration is a.e.; the two continuous
state representatives agree at every time. No separability or compactness
hypothesis is imposed. The prescribed-data singleton interval is included.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
universe u v

namespace ExpandedFA.Evolution.SymmetricHyperbolicSpec
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec

section Spaces
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The unshifted energy in the source identity. -/
def energy (a : ℝ → Form V) (x : ℝ → V) (y : ℝ → H) (t : ℝ) : ℝ :=
  ‖y t‖ ^ 2 + a t (x t) (x t)

/-- Only the time argument of the form is differentiated. -/
def formPower (T : ℝ) (a : ℝ → Form V) (x : ℝ → V) (t : ℝ) : ℝ :=
  derivWithin (fun r => a r (x t) (x t)) (Set.Icc 0 T) t

/-- Actual derivative and equation regularity are in WeakEnergySolution. -/
def StrongState {j : HilbertTriple V H} {T : ℝ} {a : ℝ → Form V}
    {u₀ : V} {v₀ : H} {f : timeLpValue H 2 T}
    (z : WeakEnergySolution j T a u₀ v₀ f) : Prop :=
  ContinuousOn z.displacement (Set.Icc 0 T) ∧
  ContinuousOn z.velocity (Set.Icc 0 T)

/-- Quantitative well-posedness, with a single constant chosen before the data.
The pointwise bound is equivalent to the displayed supremum bound in the source.
The uniqueness clause even includes all weak-energy competitors. -/
def WellPosedness : Prop := ∀ (j : HilbertTriple V H) (T : ℝ), 0 ≤ T →
  ∀ (a : ℝ → Form V) (α C : ℝ), FormHypotheses j T a α C →
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T),
    ∃ z : WeakEnergySolution j T a u₀ v₀ f,
      StrongState z ∧
      (∀ t ∈ Set.Icc 0 T, ‖z.displacement t‖ ^ 2 + ‖z.velocity t‖ ^ 2 ≤
        K * (‖u₀‖ ^ 2 + ‖v₀‖ ^ 2 + ‖f‖ ^ 2)) ∧
      (∀ w : WeakEnergySolution j T a u₀ v₀ f,
        (∀ t ∈ Set.Icc 0 T, z.displacement t = w.displacement t ∧
          z.velocity t = w.velocity t) ∧
        z.acceleration =ᵐ[timeMeasureValue T] w.acceleration)

/-- Integrability is explicit to exclude totalized nonintegrable integrals. -/
def HasEnergyIdentity {j : HilbertTriple V H} {T : ℝ} {a : ℝ → Form V}
    {u₀ : V} {v₀ : H} {f : timeLpValue H 2 T}
    (z : WeakEnergySolution j T a u₀ v₀ f) : Prop :=
  ∀ s ∈ Set.Icc 0 T, ∀ t ∈ Set.Icc 0 T,
    IntervalIntegrable (fun r => inner ℝ (f r) (z.velocity r)) volume s t ∧
    IntervalIntegrable (formPower T a z.displacement) volume s t ∧
    energy a z.displacement z.velocity t - energy a z.displacement z.velocity s =
      2 * (∫ r in s..t, inner ℝ (f r) (z.velocity r)) +
        ∫ r in s..t, formPower T a z.displacement r

/-- The single common magnitude and scalar time-derivative bound obtained in
paper.tex:15253–15256. This predicate adds no regularity assumption to the
original `FormHypotheses`; it records the bound for a family of admissible forms. -/
def CommonFormBounds (T : ℝ) (a : ℝ → Form V) (M : ℝ) : Prop :=
  ∀ t ∈ Set.Icc 0 T, ∀ x y,
    |a t x y| + |derivWithin (fun r => a r x y) (Set.Icc 0 T) t| ≤
      M * ‖x‖ * ‖y‖

/-- The source's full conclusion uniformly over all form families sharing
the displayed bounds. The constant is chosen after only the fixed embedding,
time horizon, Gårding parameters, and common magnitude/derivative bound M,
and before the form family and all initial data and forcing.
The existing unrestricted per-family conclusions are retained below. -/
def UniformSymmetricHyperbolicEquation : Prop :=
  ∀ (j : HilbertTriple V H) (T : ℝ), 0 ≤ T →
  ∀ (α C M : ℝ), 0 < α → 0 ≤ C → 0 ≤ M →
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (a : ℝ → Form V),
    FormHypotheses j T a α C → CommonFormBounds T a M →
    ∀ (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T),
      ∃ z : WeakEnergySolution j T a u₀ v₀ f,
        StrongState z ∧ HasEnergyIdentity z ∧
        (∀ t ∈ Set.Icc 0 T, ‖z.displacement t‖ ^ 2 + ‖z.velocity t‖ ^ 2 ≤
          K * (‖u₀‖ ^ 2 + ‖v₀‖ ^ 2 + ‖f‖ ^ 2)) ∧
        (∀ w : WeakEnergySolution j T a u₀ v₀ f,
          (∀ t ∈ Set.Icc 0 T, z.displacement t = w.displacement t ∧
            z.velocity t = w.velocity t) ∧
          z.acceleration =ᵐ[timeMeasureValue T] w.acceleration)

def EnergyIdentity : Prop := ∀ (j : HilbertTriple V H) (T : ℝ), 0 ≤ T →
  ∀ (a : ℝ → Form V) (α C : ℝ), FormHypotheses j T a α C →
  ∀ (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (z : WeakEnergySolution j T a u₀ v₀ f), HasEnergyIdentity z

/-- The complete source theorem, not a hypothesis for the auxiliary targets. -/
def SymmetricHyperbolicEquation : Prop := ∀ (j : HilbertTriple V H) (T : ℝ), 0 ≤ T →
  ∀ (a : ℝ → Form V) (α C : ℝ), FormHypotheses j T a α C →
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T),
    ∃ z : WeakEnergySolution j T a u₀ v₀ f,
      StrongState z ∧ HasEnergyIdentity z ∧
      (∀ t ∈ Set.Icc 0 T, ‖z.displacement t‖ ^ 2 + ‖z.velocity t‖ ^ 2 ≤
        K * (‖u₀‖ ^ 2 + ‖v₀‖ ^ 2 + ‖f‖ ^ 2)) ∧
      (∀ w : WeakEnergySolution j T a u₀ v₀ f,
        (∀ t ∈ Set.Icc 0 T, z.displacement t = w.displacement t ∧
          z.velocity t = w.velocity t) ∧
        z.acceleration =ᵐ[timeMeasureValue T] w.acceleration)

/-- The interior scalar chain rule, retained as an auxiliary reduction interface.
It is not included in any form or solution hypothesis. -/
def EnergyDerivative : Prop := ∀ (j : HilbertTriple V H) (T : ℝ), 0 < T →
  ∀ (a : ℝ → Form V) (α C : ℝ), FormHypotheses j T a α C →
  ∀ (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (z : WeakEnergySolution j T a u₀ v₀ f),
    derivativeValue T (energy a z.displacement z.velocity)
      (fun r => 2 * inner ℝ (f r) (z.velocity r) + formPower T a z.displacement r)

end Spaces

/-- Universe-polymorphic wrappers for independent binding checks. -/
def WellPosednessExpected : Prop := ∀ {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
  WellPosedness (V := V) (H := H)

def EnergyIdentityExpected : Prop := ∀ {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
  EnergyIdentity (V := V) (H := H)

def SymmetricHyperbolicEquationExpected : Prop := ∀ {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
  SymmetricHyperbolicEquation (V := V) (H := H)

def UniformSymmetricHyperbolicEquationExpected : Prop := ∀ {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
  UniformSymmetricHyperbolicEquation (V := V) (H := H)

/-- Integrability supporting the endpoint passage. -/
def EnergyTermsIntegrableExpected : Prop := ∀ {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
  ∀ (j : HilbertTriple V H) (T : ℝ), 0 < T →
  ∀ (a : ℝ → Form V) (α C : ℝ), FormHypotheses j T a α C →
  ∀ (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (z : WeakEnergySolution j T a u₀ v₀ f),
    Integrable (energy a z.displacement z.velocity) (timeMeasureValue T) ∧
    Integrable (fun r => inner ℝ (f r) (z.velocity r)) (timeMeasureValue T) ∧
    Integrable (formPower T a z.displacement) (timeMeasureValue T)

/-- Reduction from the scalar chain rule to the all-endpoint identity. -/
def EnergyIdentityOfDerivativeExpected : Prop := ∀ {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
  EnergyDerivative (V := V) (H := H) → EnergyIdentity (V := V) (H := H)

/-- Conditional assembly, not the complete theorem itself. -/
def AssemblyOfDerivativeExpected : Prop := ∀ {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
  EnergyDerivative (V := V) (H := H) →
    SymmetricHyperbolicEquation (V := V) (H := H)

def ZeroTimeEnergyIdentityExpected : Prop := ∀ {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
  ∀ (j : HilbertTriple V H) (a : ℝ → Form V)
    (u₀ : V) (v₀ : H) (f : timeLpValue H 2 0)
    (z : WeakEnergySolution j 0 a u₀ v₀ f), HasEnergyIdentity z

end ExpandedFA.Evolution.SymmetricHyperbolicSpec
