import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.LocalExtr

/-!
Independent statements for paper.tex:1423–1453 (the bounded-domain part of
D12.06.01). The boundary limsup condition is written in its epsilon form:
for each ε > 0, eventually within Ω at ξ, ‖f z‖ < M + ε. This permits
arbitrary boundary behavior below the bound and assumes no boundary extension.
The continuous-closure statements include attainment, the interior bound,
and equality of the maxima, expressed as suprema of the norm images.
-/

open Set Filter
open scoped Topology

namespace Specs.D12Complex.Ch06.BoundaryModulus
open _root_.D12Complex

def norm_le_of_boundary_limsup_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ) (M : ℝ),
    IsDomain Ω → Bornology.IsBounded Ω → HolomorphicOn Ω f → 0 ≤ M →
    (∀ ξ ∈ frontier Ω, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ z in 𝓝[Ω] ξ, ‖f z‖ < M + ε) →
    ∀ z ∈ Ω, ‖f z‖ ≤ M

def exists_boundary_maximum_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ),
    IsDomain Ω → Bornology.IsBounded Ω → HolomorphicOn Ω f →
    ContinuousOn f (closure Ω) →
    ∃ ξ ∈ frontier Ω, IsMaxOn (fun z => ‖f z‖) (closure Ω) ξ

def norm_le_boundary_maximum_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ),
    IsDomain Ω → Bornology.IsBounded Ω → HolomorphicOn Ω f →
    ContinuousOn f (closure Ω) →
    ∀ z ∈ closure Ω, ‖f z‖ ≤ sSup ((fun w => ‖f w‖) '' frontier Ω)

def maximum_closure_eq_boundary_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ),
    IsDomain Ω → Bornology.IsBounded Ω → HolomorphicOn Ω f →
    ContinuousOn f (closure Ω) →
    sSup ((fun z => ‖f z‖) '' closure Ω) =
      sSup ((fun z => ‖f z‖) '' frontier Ω)

end Specs.D12Complex.Ch06.BoundaryModulus
