import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.FiniteFields.RootFields
import Mathlib.Data.Nat.Factorial.Basic

/-!
Independent specification of FT-E03, notes/003/advanced-field-theory.tex,
Corollary E03 and its stated consequences (1108–1128).
All fields are literal intermediate fields of the specified algebraic closure.
The two set unions range over positive indices, including index one.
-/

universe u v
namespace Specs.AdvancedFieldTheory

def finite_intermediateField_eq_rootField_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω],
  ∀ (F : IntermediateField k Ω) [FiniteDimensional k F],
    0 < Module.finrank k F ∧ F = rootField k Ω (Module.finrank k F)

def finite_intermediateField_iff_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω],
  ∀ (F : IntermediateField k Ω), FiniteDimensional k F ↔
    ∃ n : ℕ, 0 < n ∧ F = rootField k Ω n

def finite_intermediateField_finite_iff_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω],
  ∀ (F : IntermediateField k Ω), Finite F ↔
    ∃ n : ℕ, 0 < n ∧ F = rootField k Ω n

def mem_some_finiteRootField_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω],
  ∀ x : Ω, ∃ n : ℕ, 0 < n ∧ x ∈ rootField k Ω n

def finiteRootField_iUnion_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω],
  (⋃ n : ℕ, ⋃ (_ : 0 < n), (rootField k Ω n : Set Ω)) = Set.univ

def factorial_indices_cofinal_type : Prop :=
  ∀ n : ℕ, 0 < n → ∃ j : ℕ, 0 < j ∧ n ∣ j.factorial

def factorialRootFields_directed_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω],
  Directed (· ≤ ·) (fun j : {j : ℕ // 0 < j} => rootField k Ω j.val.factorial)

def mem_some_factorialRootField_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω],
  ∀ x : Ω, ∃ j : ℕ, 0 < j ∧ x ∈ rootField k Ω j.factorial

def finiteRootField_factorial_iUnion_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω],
  (⋃ j : ℕ, ⋃ (_ : 0 < j), (rootField k Ω j.factorial : Set Ω)) = Set.univ

def algebraicClosure_isGalois_type : Prop := ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω], IsGalois k Ω

def finite_galois_intermediateField_iff_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω],
  ∀ (F : IntermediateField k Ω),
    (FiniteDimensional k F ∧ IsGalois k F) ↔
      ∃ n : ℕ, 0 < n ∧ F = rootField k Ω n

end Specs.AdvancedFieldTheory
