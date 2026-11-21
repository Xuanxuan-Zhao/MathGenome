import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.FiniteFields.OpenSubgroupClassification
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.GroupTheory.Index

/-! FT-E09, notes/003/advanced-field-theory.tex:1298–1323.
The union is taken inside the specified algebraic closure, with r = 0 included.
Infinite degree means failure of finite dimensionality, not cardinal infinitude.
The residue subgroup uses the very coordinate map of E06.
-/
universe u v
noncomputable section
namespace Specs.AdvancedFieldTheory.PrimePowerTower
open AdvancedFieldTheory.ProfiniteIntegers.ResidueSystem
open Specs.AdvancedFieldTheory.OpenSubgroups

def tower (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω]
    [Algebra k Ω] (ℓ : ℕ) : IntermediateField k Ω :=
  ⨆ r : ℕ, rootField k Ω (ℓ ^ r)

def residues (ℓ : ℕ) : AddSubgroup ResidueFamily :=
  ⨅ r : ℕ, (nsmulAddMonoidHom (α := ResidueFamily) (ℓ ^ r)).range

def tower_type := ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k]
  [Field Ω] [Algebra k Ω], ℕ → IntermediateField k Ω

def tower_value : tower_type := tower

def residues_type := ℕ → AddSubgroup ResidueFamily

def residues_value : residues_type := residues

def fieldProperties_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (ℓ : ℕ), ℓ.Prime →
    Monotone (fun r : ℕ => rootField k Ω (ℓ ^ r)) ∧
    (tower k Ω ℓ : Set Ω) = ⋃ r : ℕ, (rootField k Ω (ℓ ^ r) : Set Ω) ∧
    rootField k Ω (ℓ ^ 0) = ⊥ ∧
    (∀ a : k, algebraMap k Ω a ∈ tower k Ω ℓ) ∧
    ¬ FiniteDimensional k (tower k Ω ℓ) ∧
    (∀ s : ℕ, s.Prime → s ≠ ℓ → ¬ rootField k Ω s ≤ tower k Ω ℓ) ∧
    (∃ s : ℕ, s.Prime ∧ s ≠ ℓ ∧ ¬ rootField k Ω s ≤ tower k Ω ℓ) ∧
    tower k Ω ℓ ≠ ⊤

/-- All assertions for any E06 coordinate map; in particular for the unique
arithmetic-Frobenius map, unconditionally instantiated below. Index zero is
Mathlib's convention for an infinite set of cosets. -/
def SubgroupProperties {k : Type u} {Ω : Type v} [Field k] [Fintype k]
    [Field Ω] [Algebra k Ω] (ℓ : ℕ)
    (e : (Ω ≃ₐ[k] Ω) ≃ₜ* Multiplicative ResidueFamily) : Prop :=
  (tower k Ω ℓ).fixingSubgroup = ⨅ r : ℕ, (rootField k Ω (ℓ ^ r)).fixingSubgroup ∧
  pullback e (residues ℓ) = (tower k Ω ℓ).fixingSubgroup ∧
  IsClosed ((tower k Ω ℓ).fixingSubgroup : Set (Ω ≃ₐ[k] Ω)) ∧
  ¬ IsOpen ((tower k Ω ℓ).fixingSubgroup : Set (Ω ≃ₐ[k] Ω)) ∧
  Infinite ((Ω ≃ₐ[k] Ω) ⧸ (tower k Ω ℓ).fixingSubgroup) ∧
  (tower k Ω ℓ).fixingSubgroup.index = 0 ∧
  IsClosed (residues ℓ : Set ResidueFamily) ∧
  ¬ IsOpen (residues ℓ : Set ResidueFamily) ∧
  Infinite (ResidueFamily ⧸ residues ℓ) ∧ (residues ℓ).index = 0

def subgroupProperties_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (ℓ : ℕ), ℓ.Prime →
    ∀ (coords : Coordinates k Ω)
      (e : (Ω ≃ₐ[k] Ω) ≃ₜ* Multiplicative ResidueFamily),
      CoordinateAction coords e → SubgroupProperties ℓ e

def arithmeticExample_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (ℓ : ℕ), ℓ.Prime →
    ∃ coords : Coordinates k Ω,
      (∀ (n : ℕ+) (a : ℤ), coords n (Multiplicative.ofAdd (a : ZMod (n : ℕ))) =
        layerFrobenius k Ω n ^ a) ∧
      ∃ e : (Ω ≃ₐ[k] Ω) ≃ₜ* Multiplicative ResidueFamily,
        CoordinateAction coords e ∧
        e (globalFrobenius_value k Ω) = Multiplicative.ofAdd (integerResidues 1) ∧
        SubgroupProperties ℓ e

end Specs.AdvancedFieldTheory.PrimePowerTower
