import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.C0SemigroupAndGenerator
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Independent obligations from the growth and generator part of
`fa2:p3:semigroup-basics`, paper.tex 14443–14474. No regularity beyond the
canonical C₀ axioms is assumed. Derivatives use real time, including the right
endpoint derivative at zero. Graph continuity supplies a lift
into the canonical sum-graph-norm domain, with both graph coordinates fixed.
The Laplace resolvent and uniqueness portions are allocated separately. -/

noncomputable section
open Filter Topology MeasureTheory
open scoped NNReal

namespace ExpandedFA.Semigroups.SemigroupGrowthSpec

variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

abbrev A (T : C0Semigroup 𝕜 X) := C0SemigroupSpec.generatorValue T

def StrongContinuity : Prop := ∀ (T : C0Semigroup 𝕜 X) (x : X),
  Continuous (fun t : ℝ≥0 => T.operators t x)

def ExponentialGrowth : Prop := ∀ T : C0Semigroup 𝕜 X,
  ∃ M ω : ℝ, C0SemigroupSpec.exponentialBoundValue T M ω

def GeneratorClosed : Prop := ∀ T : C0Semigroup 𝕜 X,
  Unbounded.OperatorDomainsSpec.closedValue (A T)

def GeneratorDense : Prop := ∀ T : C0Semigroup 𝕜 X,
  Unbounded.OperatorDomainsSpec.denseValue (A T)

def DomainInvariant : Prop := ∀ (T : C0Semigroup 𝕜 X) (t : ℝ≥0) (x : X),
  x ∈ (A T).domain → T.operators t x ∈ (A T).domain

def GeneratorCommutes : Prop := ∀ (T : C0Semigroup 𝕜 X) (t : ℝ≥0)
  (x : (A T).domain) (hx : T.operators t x ∈ (A T).domain),
  A T ⟨T.operators t x, hx⟩ = T.operators t (A T x)

def OrbitDerivative : Prop := ∀ (T : C0Semigroup 𝕜 X) (x : (A T).domain),
  letI : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
  ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt (fun s : ℝ => T.operators s.toNNReal x)
      (T.operators t.toNNReal (A T x)) (Set.Ici 0) t

/-- This supplies an actual orbit continuous in the sum graph norm. -/
def GraphContinuity : Prop := ∀ (T : C0Semigroup 𝕜 X) (x : (A T).domain),
  ∃ u : ℝ≥0 → Unbounded.GraphDomain (A T),
    (∀ t, (Unbounded.GraphDomain.toDomain (A T) (u t) : X) = T.operators t x) ∧
    (∀ t, A T (Unbounded.GraphDomain.toDomain (A T) (u t)) =
      T.operators t (A T x)) ∧ Continuous u

def IntegratedDerivative : Prop := ∀ (T : C0Semigroup 𝕜 X) (x : (A T).domain),
  letI : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
  ∀ t : ℝ≥0, T.operators t x - (x : X) =
    ∫ s in (0 : ℝ)..(t : ℝ), T.operators s.toNNReal (A T x)

/-! Closed, fully quantified expected theorem types for the submission bindings. -/

def StrongContinuityExpected : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    StrongContinuity (𝕜 := 𝕜) (X := X)

def ExponentialGrowthExpected : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    ExponentialGrowth (𝕜 := 𝕜) (X := X)

def GeneratorClosedExpected : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    GeneratorClosed (𝕜 := 𝕜) (X := X)

def GeneratorDenseExpected : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    GeneratorDense (𝕜 := 𝕜) (X := X)

def DomainInvariantExpected : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    DomainInvariant (𝕜 := 𝕜) (X := X)

def GeneratorCommutesExpected : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    GeneratorCommutes (𝕜 := 𝕜) (X := X)

def OrbitDerivativeExpected : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    OrbitDerivative (𝕜 := 𝕜) (X := X)

def GraphContinuityExpected : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    GraphContinuity (𝕜 := 𝕜) (X := X)

def IntegratedDerivativeExpected : Prop :=
  ∀ {𝕜 X : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X],
    IntegratedDerivative (𝕜 := 𝕜) (X := X)

end ExpandedFA.Semigroups.SemigroupGrowthSpec
