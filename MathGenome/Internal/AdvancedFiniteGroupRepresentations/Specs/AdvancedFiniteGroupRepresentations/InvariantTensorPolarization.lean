import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.EndomorphismTensor
import Mathlib.Data.Fintype.Perm

/-!
FR-D03, polarization step (source lines 1358–1377).

`Fin n` is the zero-based version of the source's index set {1,...,n}; all
finsets of `Fin n` are exactly its subsets. The slot action is the upstream
left action, and the polarization sum uses permutations without inverses.

These statements are valid for every complex vector space and every degree,
so specialize in particular to W = End_ℂ(V) in the source's d,n ≥ 1 case.
The averaging coefficient is the inverse of n!, with no assumed certificate.
-/
noncomputable section
open scoped BigOperators
universe u
namespace Specs.AdvancedFiniteGroupRepresentations

/-- Full inclusion-exclusion identity, including its precise signs and indexing. -/
def tensor_polarizationType : Prop :=
  ∀ (W : Type u) [AddCommGroup W] [Module ℂ W] (n : ℕ) (T : Fin n → W),
    (∑ J : Finset (Fin n), (-1 : ℂ) ^ (n - J.card) •
      pureTensor W n (fun _ => ∑ j ∈ J, T j)) =
      ∑ σ : SymmetricGroup n, pureTensor W n (fun i => T (σ i))

/-- The average over S_n is invariant. -/
def tensor_average_invariantType : Prop :=
  ∀ (W : Type u) [AddCommGroup W] [Module ℂ W] (n : ℕ)
    (t : TensorPower W n) (τ : SymmetricGroup n),
    slotOperator W n τ ((n.factorial : ℂ)⁻¹ • ∑ σ : SymmetricGroup n,
      slotOperator W n σ t) =
      (n.factorial : ℂ)⁻¹ • ∑ σ : SymmetricGroup n, slotOperator W n σ t

/-- Every invariant tensor is its own average. -/
def tensor_average_eq_selfType : Prop :=
  ∀ (W : Type u) [AddCommGroup W] [Module ℂ W] (n : ℕ) (t : TensorPower W n),
    (∀ σ : SymmetricGroup n, slotOperator W n σ t = t) →
      (n.factorial : ℂ)⁻¹ • (∑ σ : SymmetricGroup n, slotOperator W n σ t) = t

/-- The fixed tensors are exactly the span of the pure powers. -/
def tensor_invariant_iff_mem_purePowerSpanType : Prop :=
  ∀ (W : Type u) [AddCommGroup W] [Module ℂ W] (n : ℕ) (t : TensorPower W n),
    (∀ σ : SymmetricGroup n, slotOperator W n σ t = t) ↔
      t ∈ Submodule.span ℂ (Set.range (fun T : W => pureTensor W n (fun _ => T)))

/-- The required subspace equality for the canonical endomorphism tensor interface. -/
def endomorphismTensor_invariants_spanType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (n : ℕ),
    {t : EndomorphismTensor V n | IsInvariantEndomorphismTensor V n t} =
      (Submodule.span ℂ (Set.range (fun T : Module.End ℂ V =>
        pureTensor (Module.End ℂ V) n (fun _ => T))) : Set (EndomorphismTensor V n))

end Specs.AdvancedFiniteGroupRepresentations
