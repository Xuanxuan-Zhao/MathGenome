import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
Independent specification of FT-E01, notes/003/advanced-field-theory.tex,
chapter 4 introduction and Proposition E01 (1048–1080). The algebra structure
records the chosen inclusion into the one fixed algebraic closure.
-/

universe u v
noncomputable section

namespace Specs.AdvancedFieldTheory

/-- The literal fixed elements of the n-fold q-power endomorphism in the
chosen ambient field. The definition is coherent for all n; results use n > 0. -/
def rootField (k : Type u) (Ω : Type v) [Field k] [Fintype k]
    [Field Ω] [Algebra k Ω] (n : ℕ) : IntermediateField k Ω where
  __ := (((FiniteField.frobeniusAlgHom k Ω) ^ n).toRingHom).eqLocusField
    (RingHom.id Ω)
  algebraMap_mem' a := ((FiniteField.frobeniusAlgHom k Ω) ^ n).commutes a

set_option linter.checkUnivs false in
def finiteRootField_type := ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k]
    [Field Ω] [Algebra k Ω], ℕ → IntermediateField k Ω

def finiteRootField_value : finiteRootField_type := rootField

def mem_finiteRootField_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    (n : ℕ) (x : Ω), x ∈ rootField k Ω n ↔ x ^ (Fintype.card k ^ n) = x

def finiteRootField_contains_base_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    (n : ℕ) (a : k), algebraMap k Ω a ∈ rootField k Ω n

def finiteRootField_operations_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    (n : ℕ),
    (0 : Ω) ∈ rootField k Ω n ∧ (1 : Ω) ∈ rootField k Ω n ∧
    (∀ x y : Ω, x ∈ rootField k Ω n → y ∈ rootField k Ω n →
      x + y ∈ rootField k Ω n) ∧
    (∀ x y : Ω, x ∈ rootField k Ω n → y ∈ rootField k Ω n →
      x - y ∈ rootField k Ω n) ∧
    (∀ x y : Ω, x ∈ rootField k Ω n → y ∈ rootField k Ω n →
      x * y ∈ rootField k Ω n) ∧
    (∀ x : Ω, x ∈ rootField k Ω n → x⁻¹ ∈ rootField k Ω n)

def finiteRootField_rootSet_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    (n : ℕ), 0 < n →
    (Polynomial.X ^ (Fintype.card k ^ n) - Polynomial.X : Polynomial k).rootSet Ω =
      (rootField k Ω n : Set Ω)

def finiteRootField_card_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (n : ℕ), 0 < n →
    Nat.card (rootField k Ω n) = Fintype.card k ^ n

def finiteRootField_finrank_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (n : ℕ), 0 < n → Module.finrank k (rootField k Ω n) = n

def finiteRootField_finite_galois_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (n : ℕ), 0 < n →
    FiniteDimensional k (rootField k Ω n) ∧ IsGalois k (rootField k Ω n)

def finiteRootField_isSplittingField_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (n : ℕ), 0 < n →
    Polynomial.IsSplittingField k (rootField k Ω n)
      (Polynomial.X ^ (Fintype.card k ^ n) - Polynomial.X : Polynomial k)

/-- No k-algebra or containment of k is assumed for the competing subfield. -/
def finiteRootField_unique_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (n : ℕ), 0 < n → ∀ (S : Subfield Ω),
    Nat.card S = Fintype.card k ^ n → S = (rootField k Ω n).toSubfield

def finiteRootField_one_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω], rootField k Ω 1 = ⊥

end Specs.AdvancedFieldTheory
