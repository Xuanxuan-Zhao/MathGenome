import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.UnitInterval

/-! The covering definition and the path-lifting obligation from paper.tex,
Theorem d12:20-05.  All spaces are arbitrary topological spaces. -/

namespace D12Complex.Ch20

universe u v

/-- Every base point has an open neighborhood whose inverse image is a
disjoint union of open sheets. On each sheet the given map is a homeomorphism
onto that neighborhood. Empty families of sheets are allowed. -/
def IsCovering {E : Type u} {B : Type v} [TopologicalSpace E]
    [TopologicalSpace B] (p : E → B) : Prop :=
  ∀ b : B, ∃ U : Set B, b ∈ U ∧ IsOpen U ∧
    ∃ sheets : Set (Set E),
      (∀ V ∈ sheets, IsOpen V) ∧ sheets.Pairwise Disjoint ∧
      ⋃₀ sheets = p ⁻¹' U ∧
      ∀ V ∈ sheets, ∃ h : V ≃ₜ U, ∀ e : V, (h e : B) = p e

end D12Complex.Ch20

namespace Specs.D12Complex.Ch20.CoveringPaths

open unitInterval

universe u v

/-- The explicit open-sheet condition implies Mathlib's evenly covered
neighborhood condition, including possibly empty fibers. -/
def covering_bridge : Prop :=
  ∀ {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B), D12Complex.Ch20.IsCovering p → IsCoveringMap p

/-- A continuous path on the whole closed real unit interval has exactly one
continuous lift with the prescribed initial value. Uniqueness is equality of
functions on the entire interval. -/
def path_lifting : Prop :=
  ∀ {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B), D12Complex.Ch20.IsCovering p →
    ∀ (γ : I → B), Continuous γ → ∀ e₀ : E, p e₀ = γ 0 →
      ∃! Γ : I → E, Continuous Γ ∧ Γ 0 = e₀ ∧ p ∘ Γ = γ

end Specs.D12Complex.Ch20.CoveringPaths
