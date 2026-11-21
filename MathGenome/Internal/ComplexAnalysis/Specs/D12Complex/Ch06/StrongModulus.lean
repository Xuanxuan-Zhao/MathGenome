import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Topology.Order.LocalExtr

/-!
Independent statements for the strong maximum and minimum modulus principles,
paper.tex:1423–1434 (D12.06.01). Local extrema use the relative topology of Ω.
Holomorphy is the shared weak holomorphy predicate, and constancy is only on Ω.
-/

open Set

namespace Specs.D12Complex.Ch06.StrongModulus
open _root_.D12Complex

/-- An interior local maximum of the modulus forces constancy on the domain. -/
def constant_of_local_maximum_modulus_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ) (a : ℂ),
    IsDomain Ω → HolomorphicOn Ω f → a ∈ Ω →
    IsLocalMaxOn (fun z => ‖f z‖) Ω a →
    ∀ z ∈ Ω, f z = f a

/-- For a zero-free holomorphic function, an interior local minimum of the
modulus also forces constancy on the domain. -/
def constant_of_local_minimum_modulus_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ) (a : ℂ),
    IsDomain Ω → HolomorphicOn Ω f → (∀ z ∈ Ω, f z ≠ 0) → a ∈ Ω →
    IsLocalMinOn (fun z => ‖f z‖) Ω a →
    ∀ z ∈ Ω, f z = f a

end Specs.D12Complex.Ch06.StrongModulus
