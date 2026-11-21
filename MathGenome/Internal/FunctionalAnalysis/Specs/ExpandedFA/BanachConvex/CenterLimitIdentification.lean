import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.AsymptoticCenters
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Projection
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

/-! The remaining limit identifications in `fa2:p2:asymptotic-center`
(paper.tex, theorem and final paragraph of its proof). Radii and centers are
those of the accepted asymptotic-center interface. Weak convergence uses the native weak space, whose initial topology tests
against every continuous scalar-linear functional for the original norm.
Real convexity uses the shared realification, including for complex Hilbert spaces.
The other center assertions are supplied by the two upstream center modules. -/
namespace ExpandedFA.BanachConvex.CenterLimitIdentification.Spec
open Set Filter
universe u v
noncomputable section

def StrongRadius : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] (s : ℕ → X) (a : X),
    Tendsto s atTop (nhds a) → ∀ x,
      AsymptoticCenters.radius s x = ‖x - a‖

/-- Closedness also supplies membership of the strong limit. No convexity is needed. -/
def StrongCenter : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] (C : Set X) (s : ℕ → X) (a : X),
    IsClosed C → (∀ n, s n ∈ C) → Tendsto s atTop (nhds a) →
    a ∈ C ∧ AsymptoticCenters.IsCenter C s a ∧
      ∀ c, AsymptoticCenters.IsCenter C s c → c = a

def WeakHilbertRadius : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (s : ℕ → H) (a : H), Bornology.IsBounded (range s) →
    (Tendsto (fun n => toWeakSpace 𝕜 H (s n)) atTop
      (nhds (toWeakSpace 𝕜 H a))) →
    ∀ x, AsymptoticCenters.radius s x ^ 2 =
      ‖x - a‖ ^ 2 + limsup (fun n => ‖s n - a‖ ^ 2) atTop

/-- Closed real-convex subsets of a Hilbert space contain weak sequence limits. -/
def WeakLimitMembership : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (C : Set H) (s : ℕ → H) (a : H), C.Nonempty → IsClosed C →
    Hilbert.Conventions.Spec.RealConvexValue 𝕜 H C → (∀ n, s n ∈ C) →
    (Tendsto (fun n => toWeakSpace 𝕜 H (s n)) atTop
      (nhds (toWeakSpace 𝕜 H a))) → a ∈ C

def WeakHilbertCenter : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (C : Set H) (s : ℕ → H) (a : H), C.Nonempty → IsClosed C →
    Hilbert.Conventions.Spec.RealConvexValue 𝕜 H C →
    Bornology.IsBounded (range s) → (∀ n, s n ∈ C) →
    (Tendsto (fun n => toWeakSpace 𝕜 H (s n)) atTop
      (nhds (toWeakSpace 𝕜 H a))) →
    a ∈ C ∧ AsymptoticCenters.IsCenter C s a ∧
      ∀ c, AsymptoticCenters.IsCenter C s c → c = a

end
end ExpandedFA.BanachConvex.CenterLimitIdentification.Spec
