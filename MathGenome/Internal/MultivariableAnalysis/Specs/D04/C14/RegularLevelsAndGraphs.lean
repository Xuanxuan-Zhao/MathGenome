import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Independent propositions for d04:14:level. The zero set is relative to the
stated open domain. Rank means the dimension of the range of the actual derivative.
The graph assertions allow arbitrary linear coordinates, including the standard
product coordinates. No choice of implicit function or chart is assumed. -/
noncomputable section
open Set
open scoped ContDiff
namespace Specs.D04.C14.RegularLevelsAndGraphs
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model

namespace Model

def graphSet {k q n : ℕ} (e : E n ≃L[ℝ] E k × E q)
    (A : Set (E k)) (h : E k → E q) : Set (E n) :=
  {x | (e x).1 ∈ A ∧ (e x).2 = h (e x).1}

def graphDefining {k q n : ℕ} (e : E n ≃L[ℝ] E k × E q)
    (h : E k → E q) (x : E n) : E q := (e x).2 - h (e x).1

end Model
open Model

def regular_zero_setType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} (O : Set (E n)) (g : E n → E (n-k)),
    ManifoldRegularity r → k ≤ n → IsOpen O → ContDiffOn ℝ r g O →
    (∀ x ∈ O, g x = 0 → Module.finrank ℝ (LinearMap.range (fderiv ℝ g x).toLinearMap) = n-k) →
    IsBoundarylessEmbeddedManifold r k (O ∩ g ⁻¹' {0})

/-- The local defining function is a submersion throughout its open domain,
not merely along the part of the zero set through the marked point. -/
def chart_local_regular_levelType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)} (c : EmbeddedChart r k n M)
    (u : E k), ManifoldRegularity r → k ≤ n → u ∈ c.source →
    ¬ IsBoundaryParameter c u →
    ∃ (O : Set (E n)) (g : E n → E (n-k)),
      IsOpen O ∧ c.toFun u ∈ O ∧ O ⊆ c.ambient ∧ ContDiffOn ℝ r g O ∧
      M ∩ O = O ∩ g ⁻¹' {0} ∧ ∀ x ∈ O, Function.Surjective (fderiv ℝ g x)

/-- A graph in product coordinates. The formula evaluated at a coordinate
increment (v,w) is exactly the block derivative [-Dh,I]. -/
def graph_definingType : Prop :=
  ∀ {r : ℕ∞ω} {k q n : ℕ} (e : E n ≃L[ℝ] E k × E q)
    (A : Set (E k)) (h : E k → E q),
    ManifoldRegularity r → IsOpen A → ContDiffOn ℝ r h A →
    ContDiffOn ℝ r (graphDefining e h) {x | (e x).1 ∈ A} ∧
    graphSet e A h = {x | (e x).1 ∈ A} ∩ (graphDefining e h) ⁻¹' {0} ∧
    ∀ x, (e x).1 ∈ A →
      HasFDerivAt (graphDefining e h)
        ((ContinuousLinearMap.snd ℝ (E k) (E q)).comp e.toContinuousLinearMap -
          (fderiv ℝ h (e x).1).comp
            ((ContinuousLinearMap.fst ℝ (E k) (E q)).comp e.toContinuousLinearMap)) x ∧
      (∀ v w, fderiv ℝ (graphDefining e h) x (e.symm (v,w)) =
        w - fderiv ℝ h (e x).1 v) ∧ Function.Surjective (fderiv ℝ (graphDefining e h) x)

def graph_manifoldType : Prop :=
  ∀ {r : ℕ∞ω} {k q : ℕ} (e : E (k+q) ≃L[ℝ] E k × E q)
    (A : Set (E k)) (h : E k → E q),
    ManifoldRegularity r → IsOpen A → ContDiffOn ℝ r h A →
    IsBoundarylessEmbeddedManifold r k (graphSet e A h)

/-- Specialization to the canonical split into the first k and last q
coordinates. This explicitly includes ordinary graphs in R^(k+q). -/
def standard_graph_manifoldType : Prop :=
  ∀ {r : ℕ∞ω} {k q : ℕ} (A : Set (E k)) (h : E k → E q),
    ManifoldRegularity r → IsOpen A → ContDiffOn ℝ r h A →
    IsBoundarylessEmbeddedManifold r k
      (graphSet (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := k) (m := q)) A h)

/-- The two extreme dimensions retain their ordinary geometric meaning. -/
def regular_zero_dim_discreteType : Prop :=
  ∀ {r : ℕ∞ω} {n : ℕ} (O : Set (E n)) (g : E n → E n),
    ManifoldRegularity r → IsOpen O → ContDiffOn ℝ r g O →
    (∀ x ∈ O, g x = 0 → Function.Surjective (fderiv ℝ g x)) →
    IsDiscrete (O ∩ g ⁻¹' {0})

def zero_codimensionType : Prop :=
  ∀ {r : ℕ∞ω} {n : ℕ} (O : Set (E n)) (g : E n → E 0),
    ManifoldRegularity r → IsOpen O →
    O ∩ g ⁻¹' {0} = O ∧ IsBoundarylessEmbeddedManifold r n O

end Specs.D04.C14.RegularLevelsAndGraphs
