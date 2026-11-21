import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch21.SmoothJordan
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! Independent specification of paper.tex, Corollary d13:21:domain-interior.
The shared oriented Euclidean plane is ℂ. Contractibility below is free
loop contractibility: the basepoint may move throughout the contraction.
An interior is an actual bounded connected component of the curve complement,
not a supplied winding-index or containment certificate. -/
namespace Specs.D13Unified.Ch21.DomainInterior
noncomputable section
open Set unitInterval
open Specs.D13Unified.Ch21.Collar
open Specs.D13Unified.Ch21.IndexProperties

/-- The source's convention for a simply connected domain. -/
def SourceSimplyConnected (U : Set ℂ) : Prop :=
  IsPathConnected U ∧ ∀ α : Loop, range α ⊆ U →
    ∃ z ∈ U, ∃ H : C(I × I, ℂ),
      (∀ t, H (0, t) = α t) ∧ (∀ t, H (1, t) = z) ∧
      (∀ s, H (s, 0) = H (s, 1)) ∧ ∀ s t, H (s, t) ∈ U

/-- Being a bounded connected component of the complement, with a point in
that complement. Jordan separation proves existence and uniqueness. -/
def BoundedInterior (γ : Circle → ℂ) (Ω : Set ℂ) : Prop :=
  ∃ p ∈ (range γ)ᶜ, connectedComponentIn (range γ)ᶜ p = Ω ∧
    Bornology.IsBounded Ω

def SourceSimplyConnectedType := Set ℂ → Prop
def BoundedInteriorType := (Circle → ℂ) → Set ℂ → Prop

/-- Mathlib's subtype convention is equivalent to path connectedness and
based loop contractions in the set. This records the exact library bridge. -/
def library_simply_connected_iffStatement : Prop :=
  ∀ U : Set ℂ, IsSimplyConnected U ↔
    IsPathConnected U ∧ ∀ x : ℂ, ∀ α : Path x x, (∀ t, α t ∈ U) →
      ∃ H : α.Homotopy (Path.refl x), ∀ t, H t ∈ U

/-- Based contractions provided by the library are also free contractions.
The main source theorem below uses free contractions directly. -/
def library_implies_sourceStatement : Prop :=
  ∀ U : Set ℂ, IsSimplyConnected U → SourceSimplyConnected U

def index_zero_outside_domainStatement : Prop :=
  ∀ (U : Set ℂ), SourceSimplyConnected U →
    ∀ α : Loop, range α ⊆ U → ∀ p : ℂ, p ∉ U → index α p = 0

/-- Universal form: every bounded component supplied by Jordan separation
has both the interior and the entire closure in the original domain. -/
def domain_interiorStatement : Prop :=
  ∀ U : Set ℂ, IsOpen U → SourceSimplyConnected U →
    ∀ (γ : Circle → ℂ), RegularEmbeddedLoop γ → range γ ⊆ U →
      ∀ Ω : Set ℂ, BoundedInterior γ Ω → Ω ⊆ U ∧ closure Ω ⊆ U

/-- Existence is retained as well, so no extra component-existence hypothesis
is required to apply the source corollary. -/
def exists_domain_interiorStatement : Prop :=
  ∀ U : Set ℂ, IsOpen U → SourceSimplyConnected U →
    ∀ (γ : Circle → ℂ), RegularEmbeddedLoop γ → range γ ⊆ U →
      ∃ Ω : Set ℂ, BoundedInterior γ Ω ∧ Ω ⊆ U ∧ closure Ω ⊆ U

/-- The usual library formulation, under the same open-domain hypothesis. -/
def domain_interior_of_isSimplyConnectedStatement : Prop :=
  ∀ U : Set ℂ, IsOpen U → IsSimplyConnected U →
    ∀ (γ : Circle → ℂ), RegularEmbeddedLoop γ → range γ ⊆ U →
      ∀ Ω : Set ℂ, BoundedInterior γ Ω → Ω ⊆ U ∧ closure Ω ⊆ U

end
end Specs.D13Unified.Ch21.DomainInterior
