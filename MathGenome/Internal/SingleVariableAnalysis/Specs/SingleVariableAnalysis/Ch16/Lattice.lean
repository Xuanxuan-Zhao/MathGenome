import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Lattice
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Finset.Lattice.Fold

/-!
Independent types for K03.16.lattice (paper.tex:3908–3920).
The topology on C(K,ℝ) is the canonical supremum-norm topology on the compact
real subtype. A `Subalgebra ℝ` contains all real constants. Finite extrema
are indexed by nonempty finite sets, since ℝ has no empty maximum/minimum.
No nonemptiness of K is required. `absPolynomialApproximation` records both
the interval approximation and its substitution into a closure element,
for every M ≥ ‖f‖, including M = 0.
-/
noncomputable section
open scoped Topology
namespace Specs.SingleVariableAnalysis.Ch16.Lattice

def closureAlgebra : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (A : Subalgebra ℝ C(K, ℝ)),
    ∃ B : Subalgebra ℝ C(K, ℝ), (B : Set C(K, ℝ)) = closure (A : Set C(K, ℝ))

def absPolynomialApproximation : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (A : Subalgebra ℝ C(K, ℝ))
    (f : C(K, ℝ)), f ∈ closure (A : Set C(K, ℝ)) →
    ∀ (M : ℝ), ‖f‖ ≤ M → ∀ ε : ℝ, 0 < ε →
    ∃ p : Polynomial ℝ,
      ‖(⟨fun t => |(t : ℝ)|, continuous_subtype_val.abs⟩ :
        C(Set.Icc (-M) M, ℝ)) - p.toContinuousMapOn (Set.Icc (-M) M)‖ < ε ∧
      Polynomial.aeval f p ∈ closure (A : Set C(K, ℝ)) ∧
      ‖Polynomial.aeval f p - |f|‖ < ε

def closureAbs : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (A : Subalgebra ℝ C(K, ℝ))
    (f : C(K, ℝ)), f ∈ closure (A : Set C(K, ℝ)) →
      |f| ∈ closure (A : Set C(K, ℝ))

def closureMaxMin : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (A : Subalgebra ℝ C(K, ℝ))
    (f g : C(K, ℝ)), f ∈ closure (A : Set C(K, ℝ)) →
    g ∈ closure (A : Set C(K, ℝ)) →
      f ⊔ g ∈ closure (A : Set C(K, ℝ)) ∧
      f ⊓ g ∈ closure (A : Set C(K, ℝ))

def closureFiniteMaxMin : Prop :=
  ∀ (K : Set ℝ) [CompactSpace K] (A : Subalgebra ℝ C(K, ℝ))
    (ι : Type) (s : Finset ι) (hs : s.Nonempty) (f : ι → C(K, ℝ)),
    (∀ i ∈ s, f i ∈ closure (A : Set C(K, ℝ))) →
      s.sup' hs f ∈ closure (A : Set C(K, ℝ)) ∧
      s.inf' hs f ∈ closure (A : Set C(K, ℝ))

end Specs.SingleVariableAnalysis.Ch16.Lattice
