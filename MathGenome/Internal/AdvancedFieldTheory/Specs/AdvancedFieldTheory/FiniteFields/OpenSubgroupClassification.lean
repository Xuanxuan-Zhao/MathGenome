import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.FiniteFields.AbsoluteGaloisGroup
import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.ProfiniteIntegers.ProjectionKernels
import Mathlib.Topology.Algebra.OpenSubgroup

/-! FT-E08, advanced-field-theory.tex:1255–1297.
The fixed fields are literal intermediate fields in the specified closure.
The assertions hold for every equivalence with the E06 coordinate action,
hence in particular for its unique arithmetic-Frobenius equivalence Θ.
No choice of a new abstract isomorphism is involved. -/
universe u v
noncomputable section
namespace Specs.AdvancedFieldTheory.OpenSubgroups
open AdvancedFieldTheory.ProfiniteIntegers.ResidueSystem

abbrev Coordinates (k : Type u) (Ω : Type v) [Field k] [Fintype k]
    [Field Ω] [Algebra k Ω] :=
  ∀ n : ℕ+, Multiplicative (ZMod (n : ℕ)) ≃* (rootField k Ω n ≃ₐ[k] rootField k Ω n)

/-- Exactly the restriction-coordinate equation in E06. This property is
weaker than prescribing arithmetic Frobenius and thus gives stronger results. -/
def CoordinateAction {k : Type u} {Ω : Type v} [Field k] [Fintype k]
    [Field Ω] [Algebra k Ω] (coords : Coordinates k Ω)
    (e : (Ω ≃ₐ[k] Ω) ≃ₜ* Multiplicative ResidueFamily) : Prop :=
  ∀ (σ : Ω ≃ₐ[k] Ω) (n : ℕ+) (x : rootField k Ω n),
    (coords n (Multiplicative.ofAdd (coordinate n (e σ).toAdd)) x : Ω) = σ (x : Ω)

/-- Transport of an additive subgroup back to Gal(Ω/k) under this very e. -/
abbrev pullback {k : Type u} {Ω : Type v} [Field k] [Field Ω] [Algebra k Ω]
    (e : (Ω ≃ₐ[k] Ω) ≃ₜ* Multiplicative ResidueFamily)
    (H : AddSubgroup ResidueFamily) : Subgroup (Ω ≃ₐ[k] Ω) :=
  H.toSubgroup.comap e.toMonoidHom

/-- An unconditional instantiation at the actual unique E06 map: the
arithmetic Frobenius coordinates, their action and normalization are retained. -/
def arithmeticKernelCorrespondence_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω],
    ∃ coords : Coordinates k Ω,
      (∀ (n : ℕ+) (a : ℤ),
        coords n (Multiplicative.ofAdd (a : ZMod (n : ℕ))) = layerFrobenius k Ω n ^ a) ∧
      ∃! e : (Ω ≃ₐ[k] Ω) ≃ₜ* Multiplicative ResidueFamily,
        (CoordinateAction coords e ∧
          e (globalFrobenius_value k Ω) = Multiplicative.ofAdd (integerResidues 1)) ∧
        ∀ n : ℕ+, pullback e (coordinate n).ker = (rootField k Ω n).fixingSubgroup

def layerProperties_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (coords : Coordinates k Ω)
    (e : (Ω ≃ₐ[k] Ω) ≃ₜ* Multiplicative ResidueFamily),
    CoordinateAction coords e → ∀ n : ℕ+,
      (coordinate n).ker = (nsmulAddMonoidHom (α := ResidueFamily) (n : ℕ)).range ∧
      pullback e (coordinate n).ker = (rootField k Ω n).fixingSubgroup ∧
      (coordinate n).ker.index = (n : ℕ) ∧
      (rootField k Ω n).fixingSubgroup.index = (n : ℕ) ∧
      IntermediateField.fixedField (pullback e (coordinate n).ker) = rootField k Ω n ∧
      IsOpen ((coordinate n).ker : Set ResidueFamily) ∧
      IsOpen ((rootField k Ω n).fixingSubgroup : Set (Ω ≃ₐ[k] Ω))

def galoisClassification_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (H : Subgroup (Ω ≃ₐ[k] Ω)),
    IsOpen (H : Set (Ω ≃ₐ[k] Ω)) →
      ∃ n : ℕ+, H = (rootField k Ω n).fixingSubgroup ∧
        (∀ m : ℕ+, H = (rootField k Ω m).fixingSubgroup → m = n) ∧
        FiniteDimensional k (IntermediateField.fixedField H) ∧
        Module.finrank k (IntermediateField.fixedField H) = (n : ℕ)

def residueClassification_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (coords : Coordinates k Ω)
    (e : (Ω ≃ₐ[k] Ω) ≃ₜ* Multiplicative ResidueFamily),
    CoordinateAction coords e → ∀ (H : AddSubgroup ResidueFamily),
      IsOpen (H : Set ResidueFamily) →
        ∃ n : ℕ+, H = (coordinate n).ker ∧
          (∀ m : ℕ+, H = (coordinate m).ker → m = n) ∧
          H = (nsmulAddMonoidHom (α := ResidueFamily) (n : ℕ)).range ∧
          H.index = (n : ℕ) ∧
          FiniteDimensional k (IntermediateField.fixedField (pullback e H)) ∧
          Module.finrank k (IntermediateField.fixedField (pullback e H)) = (n : ℕ)

def modulusOne_type : Prop :=
  ∀ (k : Type u) (Ω : Type v) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω],
    (coordinate 1).ker = ⊤ ∧ (rootField k Ω 1).fixingSubgroup = ⊤ ∧
      rootField k Ω 1 = ⊥

end Specs.AdvancedFieldTheory.OpenSubgroups
