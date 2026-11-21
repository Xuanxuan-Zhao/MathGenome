import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Topology.Constructions

/-!
Independent statements for the openness assertion of paper.tex:1382–1395,
D12.05.06. Nonconstancy is on the stated domain, not on the total extension
of the function outside it. The subtype formulation quantifies over all
relatively open subsets, with images open in the ambient complex plane.
-/

open Filter Set
open scoped Topology

namespace Specs.D12Complex.Ch05.OpenMapping
open _root_.D12Complex

/-- Connectedness and the identity theorem exclude every constant germ. -/
def not_locally_constant_of_nonconstant_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ),
    IsDomain Ω → HolomorphicOn Ω f →
    (¬ ∃ c : ℂ, ∀ z ∈ Ω, f z = c) →
    ∀ a ∈ Ω, ¬ (∀ᶠ z in 𝓝 a, f z = f a)

/-- The image of each arbitrarily small open source neighborhood contains
a disk centered at the image of its chosen point. -/
def exists_image_ball_of_nonconstant_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ),
    IsDomain Ω → HolomorphicOn Ω f →
    (¬ ∃ c : ℂ, ∀ z ∈ Ω, f z = c) →
    ∀ (U : Set ℂ), IsOpen U → U ⊆ Ω → ∀ a ∈ U,
      ∃ ε : ℝ, 0 < ε ∧ Metric.ball (f a) ε ⊆ f '' U

/-- Images of open subsets of the domain are open in ℂ. -/
def image_open_of_nonconstant_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ),
    IsDomain Ω → HolomorphicOn Ω f →
    (¬ ∃ c : ℂ, ∀ z ∈ Ω, f z = c) →
    ∀ (U : Set ℂ), IsOpen U → U ⊆ Ω → IsOpen (f '' U)

/-- A nonconstant holomorphic function on a domain is an open map from
the domain with its relative topology to the ambient complex plane. -/
def isOpenMap_of_nonconstant_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ),
    IsDomain Ω → HolomorphicOn Ω f →
    (¬ ∃ c : ℂ, ∀ z ∈ Ω, f z = c) →
    IsOpenMap (fun z : Ω => f z)

end Specs.D12Complex.Ch05.OpenMapping
