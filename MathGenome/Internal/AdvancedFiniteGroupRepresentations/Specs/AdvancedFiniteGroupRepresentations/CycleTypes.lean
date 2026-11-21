import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.Partitions
import Mathlib.GroupTheory.Perm.Centralizer

open scoped BigOperators

namespace Specs.AdvancedFiniteGroupRepresentations

/-- All cycle lengths, including a part of size one for each fixed label. -/
def cyclePartition {n : ℕ} (σ : SymmetricGroup n) : Partition n where
  parts := σ.partition.parts
  parts_pos := σ.partition.parts_pos
  parts_sum := by simpa only [Fintype.card_fin] using σ.partition.parts_sum

def cyclePartitionType := {n : ℕ} → SymmetricGroup n → Partition n

def cycleMultiplicity {n : ℕ} (ν : Partition n) (j : ℕ) : ℕ := ν.parts.count j

def cycleMultiplicityType := {n : ℕ} → Partition n → ℕ → ℕ

/-- The product over the positive cycle lengths that occur. Absent lengths
contribute one, so this is the finite version of the printed infinite product. -/
def centralizerFactor {n : ℕ} (ν : Partition n) : ℕ :=
  ∏ j ∈ ν.parts.toFinset, j ^ cycleMultiplicity ν j * (cycleMultiplicity ν j).factorial

def centralizerFactorType := {n : ℕ} → Partition n → ℕ

def conjugacyCyclePartition {n : ℕ} : ConjClasses (SymmetricGroup n) → Partition n :=
  Quotient.lift cyclePartition (by
    intro σ τ h
    apply Nat.Partition.ext
    change σ.partition.parts = τ.partition.parts
    exact congrArg Nat.Partition.parts (Equiv.Perm.partition_eq_of_isConj.mp h))

def conjugacyCyclePartitionType := {n : ℕ} → ConjClasses (SymmetricGroup n) → Partition n

def cyclePartition_partsType : Prop := ∀ {n} (σ : SymmetricGroup n),
  (cyclePartition σ).parts = σ.cycleType + Multiset.replicate (n - σ.support.card) 1

def fixedPoint_multiplicityType : Prop := ∀ {n} (σ : SymmetricGroup n),
  cycleMultiplicity (cyclePartition σ) 1 = Fintype.card (Function.fixedPoints σ)

def isConj_iff_cyclePartition_eqType : Prop := ∀ {n} (σ τ : SymmetricGroup n),
  IsConj σ τ ↔ cyclePartition σ = cyclePartition τ

def cyclePartition_surjectiveType : Prop := ∀ n, Function.Surjective (@cyclePartition n)

def conjugacyCyclePartition_mkType : Prop := ∀ {n} (σ : SymmetricGroup n),
  conjugacyCyclePartition (ConjClasses.mk σ) = cyclePartition σ

def conjugacyCyclePartition_bijectiveType : Prop := ∀ n,
  Function.Bijective (@conjugacyCyclePartition n)

def centralizer_cardType : Prop := ∀ {n} (σ : SymmetricGroup n),
  Nat.card (Subgroup.centralizer ({σ} : Set (SymmetricGroup n))) =
    centralizerFactor (cyclePartition σ)

def conjugacyClass_cardType : Prop := ∀ {n} (σ : SymmetricGroup n),
  Nat.card {τ : SymmetricGroup n // IsConj σ τ} =
    n.factorial / centralizerFactor (cyclePartition σ)

def centralizer_card_of_typeType : Prop := ∀ {n} (ν : Partition n) (σ : SymmetricGroup n),
  cyclePartition σ = ν →
  Nat.card (Subgroup.centralizer ({σ} : Set (SymmetricGroup n))) = centralizerFactor ν

def conjugacyClass_card_of_typeType : Prop := ∀ {n} (ν : Partition n) (σ : SymmetricGroup n),
  cyclePartition σ = ν →
  Nat.card {τ : SymmetricGroup n // IsConj σ τ} = n.factorial / centralizerFactor ν

def empty_centralizerFactorType : Prop := centralizerFactor emptyPartition = 1

def zero_cyclePartitionType : Prop := ∀ σ : SymmetricGroup 0, cyclePartition σ = emptyPartition

def zero_cardinalitiesType : Prop := ∀ σ : SymmetricGroup 0,
  Nat.card (Subgroup.centralizer ({σ} : Set (SymmetricGroup 0))) = 1 ∧
  Nat.card {τ : SymmetricGroup 0 // IsConj σ τ} = 1

end Specs.AdvancedFiniteGroupRepresentations
