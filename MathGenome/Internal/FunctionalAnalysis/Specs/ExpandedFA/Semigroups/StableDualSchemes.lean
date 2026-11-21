import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.HilbertAdjoint
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.BochnerLpCompleteness
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Independent specification of paper.tex:16515–16572.
The ambient complex Hilbert space need not be separable. Stability and dual
consistency are local at positive step size zero. The conclusions quantify over
every positive step sequence tending to zero and over every weak L² limit.

The time measure is Lebesgue measure restricted to (0,T). `stepL2` is totalized
by zero only when the raw step function is not in L²; the separate membership
obligation below excludes that fallback for every positive step.

Tests are C¹ on the closed time interval, including one-sided derivatives at
its endpoints, and continuous in the sum graph norm of the actual adjoint.
There are no assumed solution certificates, uniqueness, or strong convergence.
-/

noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal

namespace ExpandedFA.Semigroups.StableDualSchemesSpec

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

abbrev timeMeasure (T : ℝ) : Measure ℝ := volume.restrict (Set.Ioo 0 T)
abbrev TimeL2 (H : Type*) [NormedAddCommGroup H] (T : ℝ) :=
  Lp H 2 (timeMeasure T)

def discreteGenerator (C : ℝ → H →L[ℂ] H) (h : ℝ) : H →L[ℂ] H :=
  (h : ℂ)⁻¹ • (C h - ContinuousLinearMap.id ℂ H)

def step (C : ℝ → H →L[ℂ] H) (x : H) (h t : ℝ) : H :=
  (C h ^ ⌊t / h⌋₊) x

open scoped Classical in
def stepL2 (C : ℝ → H →L[ℂ] H) (x : H) (T h : ℝ) : TimeL2 H T :=
  if hf : MemLp (step C x h) 2 (timeMeasure T) then hf.toLp (step C x h) else 0

/-- A stability bound is needed only for all sufficiently small positive h. -/
def Stable (C : ℝ → H →L[ℂ] H) : Prop :=
  ∀ T : ℝ, 0 < T → ∃ B : ℝ, 0 ≤ B ∧
    ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ n : ℕ, (n : ℝ) * h ≤ T → ‖C h ^ n‖ ≤ B

def DualConsistent (G : Unbounded.Operator ℂ H H) (C : ℝ → H →L[ℂ] H) : Prop :=
  ∀ w : (Unbounded.HilbertAdjointSpec.adjointValue G).domain,
    Tendsto (fun h => (discreteGenerator C h).adjoint (w : H))
      (𝓝[>] (0 : ℝ)) (𝓝 (Unbounded.HilbertAdjointSpec.adjointValue G w))

/-- Weak convergence uses all continuous complex-linear functionals on L². -/
def WeaklyConverges {T : ℝ} (v : ℕ → TimeL2 H T) (u : TimeL2 H T) : Prop :=
  ∀ ℓ : TimeL2 H T →L[ℂ] ℂ,
    Tendsto (fun n => ℓ (v n)) atTop (𝓝 (ℓ u))

def AdmissibleTest (G : Unbounded.Operator ℂ H H) (T : ℝ)
    (w : ℝ → Unbounded.GraphDomain (Unbounded.HilbertAdjointSpec.adjointValue G))
    (w' : ℝ → H) : Prop :=
  ContinuousOn w (Set.Icc 0 T) ∧ ContinuousOn w' (Set.Icc 0 T) ∧
    (∀ t ∈ Set.Icc 0 T, HasDerivWithinAt
      (fun s => (Unbounded.GraphDomain.toDomain _ (w s) : H)) (w' t) (Set.Icc 0 T) t) ∧
    (Unbounded.GraphDomain.toDomain _ (w T) : H) = 0

def WeakSolution (G : Unbounded.Operator ℂ H H) (x : H) (T : ℝ)
    (u : TimeL2 H T) : Prop :=
  ∀ (w : ℝ → Unbounded.GraphDomain (Unbounded.HilbertAdjointSpec.adjointValue G))
    (w' : ℝ → H), AdmissibleTest G T w w' →
      (∫ t, (inner ℂ (w' t) (u t) +
        inner ℂ (Unbounded.HilbertAdjointSpec.adjointValue G
          (Unbounded.GraphDomain.toDomain _ (w t))) (u t)) ∂timeMeasure T) +
        inner ℂ (Unbounded.GraphDomain.toDomain _ (w 0) : H) x = 0

def StepMembershipExpected : Prop :=
  ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (C : ℝ → H →L[ℂ] H) (x : H) (T h : ℝ), 0 < h →
    MemLp (step C x h) 2 (timeMeasure T)

def SubsequenceExpected : Prop :=
  ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (G : Unbounded.Operator ℂ H H) (C : ℝ → H →L[ℂ] H),
    G.IsClosed → Dense (G.domain : Set H) →
    Dense ((Unbounded.HilbertAdjointSpec.adjointValue G).domain : Set H) →
    Stable C → DualConsistent G C → ∀ (x : H) (T : ℝ), 0 ≤ T →
    ∀ h : ℕ → ℝ, (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
      ∃ (φ : ℕ → ℕ) (u : TimeL2 H T), StrictMono φ ∧
        WeaklyConverges (fun n => stepL2 C x T (h (φ n))) u

def LimitExpected : Prop :=
  ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (G : Unbounded.Operator ℂ H H) (C : ℝ → H →L[ℂ] H),
    G.IsClosed → Dense (G.domain : Set H) →
    Dense ((Unbounded.HilbertAdjointSpec.adjointValue G).domain : Set H) →
    Stable C → DualConsistent G C → ∀ (x : H) (T : ℝ), 0 ≤ T →
    ∀ h : ℕ → ℝ, (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
    ∀ u : TimeL2 H T,
      WeaklyConverges (fun n => stepL2 C x T (h n)) u →
        MemLp (fun t => u t) ∞ (timeMeasure T) ∧ WeakSolution G x T u

/-- The essential-bound clause, also recorded separately for incremental work. -/
def LimitBoundExpected : Prop :=
  ∀ {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (G : Unbounded.Operator ℂ H H) (C : ℝ → H →L[ℂ] H),
    G.IsClosed → Dense (G.domain : Set H) →
    Dense ((Unbounded.HilbertAdjointSpec.adjointValue G).domain : Set H) →
    Stable C → DualConsistent G C → ∀ (x : H) (T : ℝ), 0 ≤ T →
    ∀ h : ℕ → ℝ, (∀ n, 0 < h n) → Tendsto h atTop (𝓝 0) →
    ∀ u : TimeL2 H T,
      WeaklyConverges (fun n => stepL2 C x T (h n)) u →
        MemLp (fun t => u t) ∞ (timeMeasure T)

end ExpandedFA.Semigroups.StableDualSchemesSpec
