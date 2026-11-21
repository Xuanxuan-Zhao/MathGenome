import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.FiniteFields.GlobalFrobenius
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.FiniteFields.DivisorLattice
import Mathlib.FieldTheory.Galois.Basic

/-!
Independent specification of FT-E04B, Theorem E04, finite and relative
assertions (notes/003/advanced-field-theory.tex:1131–1160).
All layers are literal subfields of the same algebraic closure. The relative
Galois group is represented canonically as the subgroup of Gal(k_n/k) fixing
the image of k_m pointwise; `IntermediateField.fixingSubgroupEquiv` identifies
it with the intrinsic automorphism group over that image field.
-/

universe u v
noncomputable section
namespace Specs.AdvancedFieldTheory

variable (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]

/-- The q-power automorphism on the actual root field. Its ambient action is
specified below to be the restriction of the distinguished global Frobenius. -/
def layerFrobenius (n : ℕ) : rootField k Ω n ≃ₐ[k] rootField k Ω n :=
  FiniteField.frobeniusAlgEquivOfAlgebraic k (rootField k Ω n)

/-- Gal(k_n/k_m), as the pointwise stabilizer of the literal inclusion. -/
def relativeLayerGroup {m n : ℕ} (h : m ∣ n) :
    Subgroup (rootField k Ω n ≃ₐ[k] rootField k Ω n) :=
  (rootFieldInclusion k Ω h).fieldRange.fixingSubgroup

set_option linter.checkUnivs false in
def finiteFrobenius_type :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (n : ℕ), rootField k Ω n ≃ₐ[k] rootField k Ω n

def finiteFrobenius_value : finiteFrobenius_type := layerFrobenius

set_option linter.checkUnivs false in
def finiteRelativeGaloisGroup_type :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    {m n : ℕ}, m ∣ n →
      Subgroup (rootField k Ω n ≃ₐ[k] rootField k Ω n)

def finiteRelativeGaloisGroup_value : finiteRelativeGaloisGroup_type := relativeLayerGroup

def finiteFrobenius_coe_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (n : ℕ) (x : rootField k Ω n),
    (layerFrobenius k Ω n x : Ω) = globalFrobenius_value k Ω (x : Ω)

def finiteFrobenius_pow_coe_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (n d : ℕ) (x : rootField k Ω n),
    ((layerFrobenius k Ω n ^ d) x : Ω) = (globalFrobenius_value k Ω ^ d) (x : Ω)

def finiteFrobenius_orderOf_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (n : ℕ), 0 < n → orderOf (layerFrobenius k Ω n) = n

def finiteFrobenius_generates_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (n : ℕ), 0 < n → Subgroup.zpowers (layerFrobenius k Ω n) = ⊤

def finiteGaloisGroup_card_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (n : ℕ), 0 < n →
      Nat.card (rootField k Ω n ≃ₐ[k] rootField k Ω n) = n

def mem_finiteRelativeGaloisGroup_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    {m n : ℕ} (h : m ∣ n)
    (σ : rootField k Ω n ≃ₐ[k] rootField k Ω n),
    σ ∈ relativeLayerGroup k Ω h ↔
      ∀ x : rootField k Ω m, σ (rootFieldInclusion k Ω h x) = rootFieldInclusion k Ω h x

def finiteFrobenius_pow_orderOf_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (m n : ℕ), 0 < m → 0 < n → m ∣ n →
      orderOf (layerFrobenius k Ω n ^ m) = n / m

def finiteRelativeGaloisGroup_eq_zpowers_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (m n : ℕ) (_hm : 0 < m) (_hn : 0 < n) (h : m ∣ n),
    relativeLayerGroup k Ω h = Subgroup.zpowers (layerFrobenius k Ω n ^ m)

def finiteRelativeGaloisGroup_card_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (m n : ℕ) (_hm : 0 < m) (_hn : 0 < n) (h : m ∣ n),
    Nat.card (relativeLayerGroup k Ω h) = n / m

end Specs.AdvancedFieldTheory
