import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.LocalGraphAndAmbientInverse
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-! Independent statements for the remainder of d04:14:charts.
The chart representation and intrinsic boundary are the shared upstream objects.
Regularity at a boundary point means local Euclidean extendibility. -/
noncomputable section
open Set
open scoped ContDiff
namespace Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
namespace Model

def chartOverlap {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c d : EmbeddedChart r k n M) : Set (E k) :=
  c.source ∩ c.toFun ⁻¹' d.ambient

def chartTransition {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c d : EmbeddedChart r k n M) : E k → E k := d.invFun ∘ c.toFun

def IsBoundaryParameter {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) (u : E k) : Prop :=
  c.half = true ∧ u ∈ flatBoundary k

/-- Parameter velocities of short inward rays, including the zero vector. -/
def inwardParameterCone {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) (u : E k) : Set (E k) := by
  classical
  exact if IsBoundaryParameter c u then halfSpace k else univ

/-- The same embedded-chart definition, with all centers represented by open
Euclidean charts. This expresses 'without boundary' without assuming the
chart-independence theorem being proved. -/
def IsBoundarylessEmbeddedManifold (r : ℕ∞ω) (k : ℕ) {n : ℕ}
    (M : Set (E n)) : Prop :=
  ManifoldRegularity r ∧ k ≤ n ∧ ∀ x ∈ M,
    ∃ (c : EmbeddedChart r k n M) (u : E k),
      c.half = false ∧ u ∈ c.source ∧ c.toFun u = x

end Model
open Model

abbrev chartOverlapType := {r : ℕ∞ω} → {k n : ℕ} → {M : Set (E n)} →
  EmbeddedChart r k n M → EmbeddedChart r k n M → Set (E k)
def chartOverlapValue : chartOverlapType := @Model.chartOverlap
abbrev chartTransitionType := {r : ℕ∞ω} → {k n : ℕ} → {M : Set (E n)} →
  EmbeddedChart r k n M → EmbeddedChart r k n M → E k → E k
def chartTransitionValue : chartTransitionType := @Model.chartTransition
abbrev IsBoundaryParameterType := {r : ℕ∞ω} → {k n : ℕ} → {M : Set (E n)} →
  EmbeddedChart r k n M → E k → Prop
def IsBoundaryParameterValue : IsBoundaryParameterType := @Model.IsBoundaryParameter
abbrev inwardParameterConeType := {r : ℕ∞ω} → {k n : ℕ} → {M : Set (E n)} →
  EmbeddedChart r k n M → E k → Set (E k)
def inwardParameterConeValue : inwardParameterConeType := @Model.inwardParameterCone
abbrev IsBoundarylessEmbeddedManifoldType := ℕ∞ω → ℕ → {n : ℕ} → Set (E n) → Prop
def IsBoundarylessEmbeddedManifoldValue : IsBoundarylessEmbeddedManifoldType :=
  @Model.IsBoundarylessEmbeddedManifold

/-- The local graph part of the source is covered by the authorized prerequisite. -/
def local_graphType : Prop :=
  Specs.D04.C14.LocalGraphAndAmbientInverse.local_graph_and_ambient_inverseType

def chart_inverse_extensionType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (c : EmbeddedChart r k n M),
    ManifoldRegularity r → k ≤ n → ∀ u ∈ c.source,
    ∃ (O : Set (E n)) (J : E n → E k), IsOpen O ∧ c.toFun u ∈ O ∧
      ContDiffOn ℝ r J O ∧ EqOn J c.invFun ((M ∩ c.ambient) ∩ O)

def chart_transition_regularType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (c d : EmbeddedChart r k n M),
    ManifoldRegularity r → k ≤ n →
    ContDiffOn ℝ r (chartTransition c d) (chartOverlap c d) ∧
    (∀ u ∈ chartOverlap c d, ∃ (W : Set (E k)) (F : E k → E k),
      IsOpen W ∧ u ∈ W ∧ ContDiffOn ℝ r F W ∧
      EqOn F (chartTransition c d) (chartOverlap c d ∩ W))

def chart_transition_derivativesType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (c d : EmbeddedChart r k n M),
    ManifoldRegularity r → k ≤ n → ∀ u ∈ chartOverlap c d,
    ∃ A : E k ≃L[ℝ] E k,
      HasFDerivWithinAt (chartTransition c d) A.toContinuousLinearMap
        (chartOverlap c d) u ∧
      HasFDerivWithinAt (chartTransition d c) A.symm.toContinuousLinearMap
        (chartOverlap d c) (chartTransition c d u)

def chart_transition_boundaryType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (c d : EmbeddedChart r k n M),
    ManifoldRegularity r → k ≤ n → ∀ u ∈ chartOverlap c d,
      IsBoundaryParameter c u ↔ IsBoundaryParameter d (chartTransition c d u)

def chart_intrinsicBoundaryType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (c : EmbeddedChart r k n M),
    ManifoldRegularity r → k ≤ n → ∀ u ∈ c.source,
      c.toFun u ∈ intrinsicBoundary r k M ↔ IsBoundaryParameter c u

def inwardParameterCone_eq_posTangentConeType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (c d : EmbeddedChart r k n M),
    ∀ u ∈ chartOverlap c d,
      inwardParameterCone c u = posTangentConeAt (chartOverlap c d) u

def boundaryless_iffType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)},
    IsBoundarylessEmbeddedManifold r k M ↔
      IsEmbeddedManifold r k M ∧ intrinsicBoundary r k M = ∅

def chart_transition_conesType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (c d : EmbeddedChart r k n M),
    ManifoldRegularity r → k ≤ n → ∀ u ∈ chartOverlap c d,
    ∀ A : E k ≃L[ℝ] E k,
      HasFDerivWithinAt (chartTransition c d) A.toContinuousLinearMap
        (chartOverlap c d) u →
      A '' inwardParameterCone c u = inwardParameterCone d (chartTransition c d u) ∧
      (IsBoundaryParameter c u → A '' flatBoundary k = flatBoundary k)

def intrinsic_boundary_manifoldType : Prop :=
  ∀ {r : ℕ∞ω} {d n : ℕ} {M : Set (E n)},
    IsEmbeddedManifold r (d+1) M →
      IsBoundarylessEmbeddedManifold r d (intrinsicBoundary r (d+1) M)

def intrinsic_interior_manifoldType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}, IsEmbeddedManifold r k M →
    IsBoundarylessEmbeddedManifold r k (M \ intrinsicBoundary r k M)

def intrinsic_boundary_zeroType : Prop :=
  ∀ (r : ℕ∞ω) {n : ℕ} (M : Set (E n)), intrinsicBoundary r 0 M = ∅

end Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary
