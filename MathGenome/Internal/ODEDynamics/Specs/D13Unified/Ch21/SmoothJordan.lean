import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch21.Collar
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch21.IndexProperties
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Connected.Basic

/-! Independent statement of paper.tex, Theorem d13:21:smooth-jordan.
The plane is the shared oriented Euclidean plane ℂ and the circle is ℝ/ℤ.
No collar or separation certificate is an extra hypothesis. -/
namespace Specs.D13Unified.Ch21.SmoothJordan
noncomputable section
open Set
open Specs.D13Unified.Ch21.Collar
open Specs.D13Unified.Ch21.IndexProperties

/-- The usual local graph definition, in affine real linear coordinates.
The rectangle contains the boundary point, the graph is C¹ throughout its
horizontal interval, and the open set occupies exactly its lower side. -/
def LocalGraphBoundary (Ω : Set ℂ) (p : ℂ) : Prop :=
  ∃ L : ℂ ≃L[ℝ] (ℝ × ℝ), ∃ b c : ℝ, 0 < b ∧ 0 < c ∧
    ∃ f : ℝ → ℝ, ContDiffOn ℝ 1 f (Ioo (-b) b) ∧ f 0 = 0 ∧
      (∀ x ∈ Ioo (-b) b, f x ∈ Ioo (-c) c) ∧
      ∀ z : ℂ, L (z - p) ∈ Ioo (-b) b ×ˢ Ioo (-c) c →
        (z ∈ frontier Ω ↔ (L (z - p)).2 = f (L (z - p)).1) ∧
        (z ∈ Ω ↔ (L (z - p)).2 < f (L (z - p)).1)

def HasC1Boundary (Ω : Set ℂ) : Prop :=
  ∀ p ∈ frontier Ω, LocalGraphBoundary Ω p

/-- Both sets are actual components, and these exhaust all components. -/
def TwoComponents (S Ω E : Set ℂ) : Prop :=
  Ω.Nonempty ∧ E.Nonempty ∧ Disjoint Ω E ∧ Ω ∪ E = S ∧
    (∀ p ∈ Ω, connectedComponentIn S p = Ω) ∧
    (∀ p ∈ E, connectedComponentIn S p = E)

/-- Bundling adds only the continuity already implied by the C¹ hypothesis. -/
def regularLoopMap (γ : Circle → ℂ) (hγ : RegularEmbeddedLoop γ) : C(Circle, ℂ) :=
  ⟨γ, isQuotientMap_quotient_mk'.continuous_iff.mpr hγ.1.continuous⟩

def smooth_jordanStatement : Prop :=
  ∀ (γ : Circle → ℂ) (hγ : RegularEmbeddedLoop γ),
    ∃ Ω E : Set ℂ,
      TwoComponents (range γ)ᶜ Ω E ∧
      IsOpen Ω ∧ IsOpen E ∧ IsPathConnected Ω ∧ IsPathConnected E ∧
      Bornology.IsBounded Ω ∧ ¬ Bornology.IsBounded E ∧
      frontier Ω = range γ ∧ frontier E = range γ ∧
      closure Ω = Ω ∪ range γ ∧ HasC1Boundary Ω ∧
      (∀ p ∈ E, index (circleLoop (regularLoopMap γ hγ)) p = 0) ∧
      (∃ k : ℤ, (k = 1 ∨ k = -1) ∧
        ∀ p ∈ Ω, index (circleLoop (regularLoopMap γ hγ)) p = k)

/-- Proven portion, with collar-side assignment retained for the local boundary proof. -/
def topological_jordanStatement : Prop :=
  ∀ (γ : Circle → ℂ) (hγ : RegularEmbeddedLoop γ),
    ∃ Ω E : Set ℂ,
      TwoComponents (range γ)ᶜ Ω E ∧
      IsOpen Ω ∧ IsOpen E ∧ IsPathConnected Ω ∧ IsPathConnected E ∧
      Bornology.IsBounded Ω ∧ ¬ Bornology.IsBounded E ∧
      frontier Ω = range γ ∧ frontier E = range γ ∧
      closure Ω = Ω ∪ range γ ∧
      (∀ p ∈ E, index (circleLoop (regularLoopMap γ hγ)) p = 0) ∧
      (∃ k : ℤ, (k = 1 ∨ k = -1) ∧
        ∀ p ∈ Ω, index (circleLoop (regularLoopMap γ hγ)) p = k) ∧
      (∃ v a, IsCollar γ v a ∧
        ((positiveSide γ v a ⊆ Ω ∧ negativeSide γ v a ⊆ E) ∨
          (positiveSide γ v a ⊆ E ∧ negativeSide γ v a ⊆ Ω)))

end
end Specs.D13Unified.Ch21.SmoothJordan
