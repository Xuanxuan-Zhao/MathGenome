import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SubmoduleTheorem
import Mathlib.RepresentationTheory.Intertwining

/-! FR A07, source lines 350–374. The actions below are required to be the
restriction of the original tabloid permutation action. No classification or
completeness certificate is assumed. All partitions, including zero, occur. -/
noncomputable section
universe u
namespace Specs.AdvancedFiniteGroupRepresentations

def InheritedSpechtAction {n : ℕ} (p : Partition n)
    (σ : Representation ℂ (SymmetricGroup n) (SpechtModule p)) : Prop :=
  ∀ g v, (σ g v).val = permutationRepresentation p g v.val

def InheritedSpechtActionType := ∀ {n : ℕ} (p : Partition n),
  Representation ℂ (SymmetricGroup n) (SpechtModule p) → Prop

def classification_irreducibleType : Prop :=
  ∀ {n : ℕ} (p : Partition n)
    (σ : Representation ℂ (SymmetricGroup n) (SpechtModule p)),
    InheritedSpechtAction p σ → σ.IsIrreducible

def classification_distinctType : Prop :=
  ∀ {n : ℕ} (p q : Partition n)
    (σ : Representation ℂ (SymmetricGroup n) (SpechtModule p))
    (τ : Representation ℂ (SymmetricGroup n) (SpechtModule q)),
    InheritedSpechtAction p σ → InheritedSpechtAction q τ →
    Nonempty (σ.Equiv τ) → p = q

def classification_exhaustiveType : Prop :=
  ∀ {n : ℕ} (V : Type u) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ (SymmetricGroup n) V),
    ρ.IsIrreducible → ∃! p : Partition n,
      ∃ σ : Representation ℂ (SymmetricGroup n) (SpechtModule p),
        InheritedSpechtAction p σ ∧ Nonempty (σ.Equiv ρ)

/-- `indiscrete n` is the partition (n) for n > 0. -/
def classification_rowType : Prop :=
  ∀ (n : ℕ), 0 < n →
    ∀ σ : Representation ℂ (SymmetricGroup n) (SpechtModule (Nat.Partition.indiscrete n)),
      InheritedSpechtAction _ σ →
      ∃ e : SpechtModule (Nat.Partition.indiscrete n) ≃ₗ[ℂ] ℂ,
        ∀ g v, e (σ g v) = e v

/-- The conjugate of (n) has n parts equal to 1. The displayed equivariance
identifies its Specht module with the complex sign line. -/
def classification_columnType : Prop :=
  ∀ (n : ℕ), 0 < n →
    ∀ σ : Representation ℂ (SymmetricGroup n)
      (SpechtModule (transpose (Nat.Partition.indiscrete n))),
      InheritedSpechtAction _ σ →
      ∃ e : SpechtModule (transpose (Nat.Partition.indiscrete n)) ≃ₗ[ℂ] ℂ,
        ∀ g v, e (σ g v) = permutationSign g * e v

def classification_emptyType : Prop :=
  ∀ σ : Representation ℂ (SymmetricGroup 0) (SpechtModule emptyPartition),
    InheritedSpechtAction _ σ →
      ∃ e : SpechtModule emptyPartition ≃ₗ[ℂ] ℂ,
        ∀ g v, e (σ g v) = e v

end Specs.AdvancedFiniteGroupRepresentations
