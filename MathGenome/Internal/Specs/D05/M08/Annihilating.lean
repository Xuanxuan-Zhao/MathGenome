import MathGenome.Internal.Specs.D05.M08.Evaluation
import MathGenome.Internal.Specs.D05.M03.HomDimension
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Ideal.Maps

/-! Independent specifications for K05.08.annihilating (paper.tex:1134–1135).
The ideal is in the commutative scalar polynomial ring; its evaluation target
is the canonical endomorphism algebra, with no commutativity or nontriviality
assumption. Finite dimension is used only for the existence assertions.
-/

noncomputable section
namespace Specs.D05.M08.Annihilating
open scoped BigOperators

def annihilator_type :=
  ∀ (K V : Type*) [Field K] [AddCommGroup V] [Module K V],
    Module.End K V → Ideal (Polynomial K)

def annihilator_value : annihilator_type :=
  fun K V _ _ _ T => RingHom.ker (Evaluation.evaluation_value K V T).toRingHom

def mem_annihilator : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (p : Polynomial K),
    p ∈ annihilator_value K V T ↔ Evaluation.evaluation_value K V T p = 0

def add_mem : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (p q : Polynomial K),
    p ∈ annihilator_value K V T → q ∈ annihilator_value K V T →
      p + q ∈ annihilator_value K V T

def neg_mem : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (p : Polynomial K),
    p ∈ annihilator_value K V T → -p ∈ annihilator_value K V T

def mul_mem : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : Module.End K V) (p q : Polynomial K),
    p ∈ annihilator_value K V T → q * p ∈ annihilator_value K V T

def end_dimension : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V],
    Module.finrank K (Module.End K V) = (Module.finrank K V) ^ 2

/-- The indexed list has n²+1 occurrences even when powers coincide. -/
def powers_dependent : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    ¬ LinearIndependent K (fun j : Fin ((Module.finrank K V) ^ 2 + 1) => T ^ (j : ℕ))

def powers_relation : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    ∃ a : Fin ((Module.finrank K V) ^ 2 + 1) → K,
      (∃ j, a j ≠ 0) ∧ (∑ j, a j • T ^ (j : ℕ)) = 0

/-- The finite relation gives a nonzero formal polynomial, with the stated
n² degree bound. This includes n=0, when a nonzero constant works. -/
def exists_nonzero_annihilator : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    ∃ p : Polynomial K, p ≠ 0 ∧ p.natDegree ≤ (Module.finrank K V) ^ 2 ∧
      p ∈ annihilator_value K V T

def ideal_ne_bot : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    annihilator_value K V T ≠ ⊥

def zero_dimension : Prop :=
  ∀ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (T : Module.End K V),
    Module.finrank K V = 0 →
      (LinearMap.id : Module.End K V) = 0 ∧
      (∀ p : Polynomial K, Evaluation.evaluation_value K V T p = 0) ∧
      annihilator_value K V T = ⊤

end Specs.D05.M08.Annihilating
