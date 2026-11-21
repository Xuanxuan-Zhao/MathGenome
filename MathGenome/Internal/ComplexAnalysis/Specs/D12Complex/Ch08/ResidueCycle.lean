import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.Residue
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch04.FiniteCycleCauchy
import Mathlib.Topology.DiscreteSubset

/-! The cycle residue theorem, paper.tex:1949–1989 (D12.08.02).
Relative closedness is expressed in the subspace Ω. Discreteness is ordinary
subspace discreteness of A. The functions and cycles are the shared objects;
no pole, meromorphy, simplicity, connectedness, or boundary extension is assumed.
-/
noncomputable section
open Set
open scoped BigOperators

namespace Specs.D12Complex.Ch08.ResidueCycle
open _root_.D12Complex

def finite_nonzero_indices_type : Prop :=
  ∀ (Ω A : Set ℂ) (Γ : IntegralCycle),
    IsOpen Ω → A ⊆ Ω →
    IsClosed ((Subtype.val : Ω → ℂ) ⁻¹' A) → IsDiscrete A →
    Γ.trace ⊆ Ω → Disjoint Γ.trace A →
    (∀ w, w ∉ Ω → Γ.index w = 0) →
    {a | a ∈ A ∧ Γ.index a ≠ 0}.Finite

/-- The finset is exactly the set of singularities with nonzero index.
Thus the displayed finite sum is the sum over A with every zero-index term
removed, including when A or the active cycle is empty. -/
def residue_theorem_type : Prop :=
  ∀ (Ω A : Set ℂ) (f : ℂ → ℂ) (Γ : IntegralCycle),
    IsOpen Ω → A ⊆ Ω →
    IsClosed ((Subtype.val : Ω → ℂ) ⁻¹' A) → IsDiscrete A →
    HolomorphicOn (Ω \ A) f →
    Γ.trace ⊆ Ω → Disjoint Γ.trace A →
    (∀ w, w ∉ Ω → Γ.index w = 0) →
    ∃ s : Finset ℂ,
      (∀ a, a ∈ s ↔ a ∈ A ∧ Γ.index a ≠ 0) ∧
      Γ.integral f = (2 * Real.pi * Complex.I : ℂ) *
        ∑ a ∈ s, Γ.index a * Residue.residue f a

end Specs.D12Complex.Ch08.ResidueCycle
