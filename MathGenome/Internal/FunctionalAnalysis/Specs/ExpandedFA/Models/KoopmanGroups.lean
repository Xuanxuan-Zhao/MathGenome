import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.StoneTheorem
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Regular

/-! Koopman clause of paper.tex, `fa2:p3:kooper-wave`.
No finiteness or topology is needed for a flow with assumed strong continuity.
The compact case uses the Borel sigma algebra and a finite regular measure.
The pullbacks act on actual real-valued and complex-valued L² equivalence
classes. Only the complex group carries a self-adjoint Stone generator. -/
noncomputable section
open MeasureTheory Filter Topology

namespace ExpandedFA.Models.KoopmanGroups
universe u

/-- A measurable measure-preserving real flow. Negative time is its inverse;
no continuity in time is included in this definition. -/
structure MeasurePreservingFlow (X : Type u) [MeasurableSpace X] (μ : Measure X) where
  maps : ℝ → X → X
  zero_time : ∀ x, maps 0 x = x
  add_time : ∀ t s x, maps (t + s) x = maps t (maps s x)
  measure_preserving : ∀ t, MeasurePreserving (maps t) μ μ

variable {X : Type u} [MeasurableSpace X] {μ : Measure X}

/-- The actual composition operator on L², well-defined by measure preservation. -/
def pullback (Φ : MeasurePreservingFlow X μ) (t : ℝ) :
    Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ (Φ.maps t) (Φ.measure_preserving t)

/-- Strong continuity is a separate hypothesis, never part of the flow law. -/
def StronglyContinuous (Φ : MeasurePreservingFlow X μ) : Prop :=
  ∀ f : Lp ℂ 2 μ, Continuous (fun t : ℝ => pullback Φ t f)

/-- The real pullback acts on real-valued L², rather than on the underlying
real space of complex-valued L². -/
def realPullback (Φ : MeasurePreservingFlow X μ) (t : ℝ) :
    Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℝ (Φ.maps t) (Φ.measure_preserving t)

def RealStronglyContinuous (Φ : MeasurePreservingFlow X μ) : Prop :=
  ∀ f : Lp ℝ 2 μ, Continuous (fun t : ℝ => realPullback Φ t f)

/-- A strongly continuous orthogonal group on an actual real Hilbert space.
Its operators are surjective real-linear isometries; polarization gives
preservation of the real inner product. No generator is assumed. -/
structure OrthogonalGroup (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] where
  operators : ℝ → H ≃ₗᵢ[ℝ] H
  at_zero : ∀ x, operators 0 x = x
  add_time : ∀ t s x, operators (t + s) x = operators t (operators s x)
  continuous_orbit : ∀ x, Continuous (fun t => operators t x)

def RealRealizesFlow (Φ : MeasurePreservingFlow X μ)
    (U : OrthogonalGroup (Lp ℝ 2 μ)) : Prop :=
  ∀ t f, U.operators t f = realPullback Φ t f

/-- The generated group agrees with the pullbacks on all equivalence classes. -/
def RealizesFlow (Φ : MeasurePreservingFlow X μ)
    (U : Semigroups.Stone.UnitaryGroup (Lp ℂ 2 μ)) : Prop :=
  ∀ t f, U.operators t f = pullback Φ t f

/-- The exact Stone conclusion, including the domain and uniqueness. -/
def HasStoneGenerator (U : Semigroups.Stone.UnitaryGroup (Lp ℂ 2 μ)) : Prop :=
  ∃ A : Unbounded.Operator ℂ (Lp ℂ 2 μ) (Lp ℂ 2 μ),
    Unbounded.SymmetryAndDeficienciesSpec.selfAdjointValue A ∧
    Semigroups.Stone.SpectralExponential A U ∧
    Semigroups.Stone.DerivativeGraph U A ∧
    ∀ B : Unbounded.Operator ℂ (Lp ℂ 2 μ) (Lp ℂ 2 μ),
      Unbounded.SymmetryAndDeficienciesSpec.selfAdjointValue B →
      Semigroups.Stone.SpectralExponential B U → B = A

namespace Spec

def KoopmanTheorem : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X)
    (Φ : MeasurePreservingFlow X μ), StronglyContinuous Φ →
    ∃ U : Semigroups.Stone.UnitaryGroup (Lp ℂ 2 μ), RealizesFlow Φ U ∧ HasStoneGenerator U

def CompactStrongContinuity : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular]
    (Φ : MeasurePreservingFlow X μ),
    Continuous (fun p : ℝ × X => Φ.maps p.1 p.2) → StronglyContinuous Φ

def CompactKoopmanTheorem : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular]
    (Φ : MeasurePreservingFlow X μ),
    Continuous (fun p : ℝ × X => Φ.maps p.1 p.2) →
    ∃ U : Semigroups.Stone.UnitaryGroup (Lp ℂ 2 μ), RealizesFlow Φ U ∧ HasStoneGenerator U

/-- Real-valued L² has the same pullback group conclusion, with orthogonal
operators. The complex Stone assertions above are retained separately. -/
def RealKoopmanGroup : Prop :=
  ∀ (X : Type u) [MeasurableSpace X] (μ : Measure X)
    (Φ : MeasurePreservingFlow X μ), RealStronglyContinuous Φ →
    ∃ U : OrthogonalGroup (Lp ℝ 2 μ), RealRealizesFlow Φ U

def CompactRealStrongContinuity : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular]
    (Φ : MeasurePreservingFlow X μ),
    Continuous (fun p : ℝ × X => Φ.maps p.1 p.2) → RealStronglyContinuous Φ

def CompactRealKoopmanGroup : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] [μ.Regular]
    (Φ : MeasurePreservingFlow X μ),
    Continuous (fun p : ℝ × X => Φ.maps p.1 p.2) →
    ∃ U : OrthogonalGroup (Lp ℝ 2 μ), RealRealizesFlow Φ U

end Spec
end ExpandedFA.Models.KoopmanGroups
