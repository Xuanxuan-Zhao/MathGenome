import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.C0SemigroupAndGenerator
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.HilbertAdjoint
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.MeasurableSpectralCalculus
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Independent statements for `fa2:p3:selfadjoint-smoothing`, paper.tex
15178–15201. Powers are the shared iterated partial products, with their
actual domains. Both real and complex Hilbert spaces and the zero space are
included. The heat semigroup is characterized by its full derivative generator
−L; uniqueness of this characterization is the upstream generator theorem. -/
noncomputable section
open Set Filter Topology
open scoped NNReal ContDiff
namespace ExpandedFA.Semigroups.SelfAdjointSmoothing
open Unbounded
universe u
variable {𝕜 : Type*} [RCLike 𝕜] {H : Type u}
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- No spectral representation, domain regularity, or smoothing is assumed. -/
def NonnegativeSelfAdjoint (L : Operator 𝕜 H H) : Prop :=
  Dense (L.domain : Set H) ∧ HilbertAdjointSpec.adjointValue L = L ∧
    ∀ x : L.domain, 0 ≤ RCLike.re (inner 𝕜 (x : H) (L x))

/-- A classical solution is required to be continuous at its initial time,
and to solve the equation in H at every strictly positive time. -/
def ClassicalSolution (L : Operator 𝕜 H H) (x : H) (u : ℝ → H) : Prop :=
  letI := NormedSpace.restrictScalars ℝ 𝕜 H
  u 0 = x ∧ ContinuousWithinAt u (Ici 0) 0 ∧
    ∀ t : ℝ, 0 < t → ∃ ht : u t ∈ L.domain,
      HasDerivAt u (-(L ⟨u t, ht⟩)) t

/-- A bounded operator realizing L^m T(t) on every vector, with the sharp
constant. Graph membership includes the precise partial-product domain. -/
def PowerSmoothing (L : Operator 𝕜 H H) (T : C0Semigroup 𝕜 H) : Prop :=
  ∀ (t : ℝ≥0), 0 < t → ∀ (m : ℕ), 1 ≤ m →
    ∃ B : H →L[𝕜] H,
      (∀ x : H, (T.operators t x, B x) ∈ (OperatorDomainsSpec.powerValue L m).graph) ∧
      ‖B‖ ≤ ((m : ℝ) / (Real.exp 1 * (t : ℝ))) ^ m

/-- All conclusions for the same semigroup, including the improved bound
for every strictly positive lower numerical bound. -/
def SmoothingConclusion (L : Operator 𝕜 H H) (T : C0Semigroup 𝕜 H) : Prop :=
  letI := NormedSpace.restrictScalars ℝ 𝕜 H
  C0SemigroupSpec.generatorValue T = -L ∧
  (∀ t, IsSelfAdjoint (T.operators t) ∧ ‖T.operators t‖ ≤ 1) ∧
  PowerSmoothing L T ∧
  (∀ x : H, ContDiffOn ℝ ∞ (fun t : ℝ => T.operators t.toNNReal x) (Ioi 0)) ∧
  (∀ x : H, ClassicalSolution L x (fun t : ℝ => T.operators t.toNNReal x)) ∧
  (∀ (x : H) (u : ℝ → H), ClassicalSolution L x u →
    ∀ t : ℝ, 0 ≤ t → u t = T.operators t.toNNReal x) ∧
  (∀ c : ℝ, 0 < c →
    (∀ x : L.domain, c * ‖(x : H)‖ ^ 2 ≤ RCLike.re (inner 𝕜 (x : H) (L x))) →
    ∀ t : ℝ≥0, ‖T.operators t‖ ≤ Real.exp (-c * (t : ℝ)))

namespace Spec

/-- On complex H the notation exp(-tL) is also identified with the actual
unbounded measurable calculus, including its everywhere-defined domain. -/
def ComplexHeatRepresentation {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (L : Operator ℂ H H)
    (T : C0Semigroup ℂ H) : Prop :=
  ∃ (E : SpectralMeasure.ProjectionValuedMeasure ℂ H)
    (C : MeasurableSpectralCalculus.BoundedRealization E),
    MeasurableSpectralCalculus.measurableIntegral C id = L ∧
    ∀ t : ℝ≥0, MeasurableSpectralCalculus.measurableIntegral C
      (fun z => Complex.exp (-(t : ℂ) * z)) = (T.operators t).toLinearMap.toPMap ⊤

/-- Both scalar fields in the manuscript are required, separately. -/
def RealTheorem : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (L : Operator ℝ H H), NonnegativeSelfAdjoint L →
      ∃ T : C0Semigroup ℝ H, SmoothingConclusion L T

def ComplexTheorem : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (L : Operator ℂ H H), NonnegativeSelfAdjoint L →
      ∃ T : C0Semigroup ℂ H, SmoothingConclusion L T ∧ ComplexHeatRepresentation L T

def FullTheorem : Prop := RealTheorem.{u} ∧ ComplexTheorem.{u}

def ClassicalUniqueness : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] (L : Operator 𝕜 H H),
    (∀ x : L.domain, 0 ≤ RCLike.re (inner 𝕜 (x : H) (L x))) →
    ∀ (x : H) (u v : ℝ → H), ClassicalSolution L x u → ClassicalSolution L x v →
      ∀ t : ℝ, 0 ≤ t → u t = v t

def ScalarEstimate : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ t : ℝ, 0 < t → ∀ r : ℝ, 0 ≤ r →
    r ^ m * Real.exp (-t * r) ≤ ((m : ℝ) / (Real.exp 1 * t)) ^ m

end Spec
end ExpandedFA.Semigroups.SelfAdjointSmoothing
