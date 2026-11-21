import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.PolynomialHomogeneousDecomposition
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SchurWeylDuality
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.LengthBound
import Mathlib.RepresentationTheory.Semisimple

/-! FR-D11, source lines 1742–1808. Polynomial always means polynomial in
matrix entries, with natural degrees. There is no determinant inverse.
The algebra in the descent statement is the actual subalgebra of End(V^⊗n).
These statements include the zero vector space and the zeroth tensor power. -/
noncomputable section
universe u v
namespace Specs.AdvancedFiniteGroupRepresentations

/-- The canonical group homomorphism into the actual tensor-image algebra. -/
def tensorImageElement (V : Type u) [AddCommGroup V] [Module ℂ V]
    (n : ℕ) (g : LinearGroup V) : tensorB V n :=
  ⟨diagonalOperator V n g, Algebra.subset_adjoin ⟨g, rfl⟩⟩

def tensorImageElementType :=
  (V : Type u) → [AddCommGroup V] → [Module ℂ V] →
  (n : ℕ) → LinearGroup V → tensorB V n

/-- Every degree-n polynomial action descends to B, with its specified action
on each generator. This includes preservation of the identity. -/
def homogeneous_factorizationType : Prop :=
  ∀ (V : Type u) (W : Type v) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (d m n : ℕ)
    (b : Module.Basis (Fin d) ℂ V) (c : Module.Basis (Fin m) ℂ W)
    (ρ : Representation ℂ (LinearGroup V) W),
    IsHomogeneousRepresentation b c ρ n →
    ∃ Φ : tensorB V n →ₐ[ℂ] Module.End ℂ W,
      ∀ g, Φ (tensorImageElement V n g) = ρ g

/-- The actual canonical multiplicity spaces carry homogeneous polynomial
actions, in every finite basis, including the zero spaces. -/
def tensorMultiplicity_homogeneousType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (d : ℕ) (b : Module.Basis (Fin d) ℂ V) {n : ℕ} (p : Partition n)
    (m : ℕ) (c : Module.Basis (Fin m) ℂ (TensorMultiplicity V p)),
    IsHomogeneousRepresentation b c (multiplicityRepresentation V p) n

/-- Complete reducibility is the existence of an invariant complement for
every invariant subspace, using the usual representation lattice. -/
def homogeneous_complete_reducibilityType : Prop :=
  ∀ (V : Type u) (W : Type v) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (d m n : ℕ)
    (b : Module.Basis (Fin d) ℂ V) (c : Module.Basis (Fin m) ℂ W)
    (ρ : Representation ℂ (LinearGroup V) W),
    IsHomogeneousRepresentation b c ρ n → ρ.IsSemisimpleRepresentation

/-- Both directions classify all simple objects, up to genuine equivariant
linear equivalence to the original Hom-defined multiplicity space. -/
def homogeneous_simple_classificationType : Prop :=
  ∀ (V : Type u) (W : Type v) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (d m n : ℕ)
    (b : Module.Basis (Fin d) ℂ V) (c : Module.Basis (Fin m) ℂ W)
    (ρ : Representation ℂ (LinearGroup V) W),
    IsHomogeneousRepresentation b c ρ n →
    (ρ.IsIrreducible ↔ ∃ p : Partition n, length p ≤ d ∧
      Nonempty (Representation.Equiv ρ (multiplicityRepresentation V p)))

def canonical_polynomial_simpleType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (d : ℕ) (b : Module.Basis (Fin d) ℂ V) {n : ℕ} (p : Partition n),
    length p ≤ d →
    Nontrivial (TensorMultiplicity V p) ∧ (multiplicityRepresentation V p).IsIrreducible ∧
    ∀ (m : ℕ) (c : Module.Basis (Fin m) ℂ (TensorMultiplicity V p)),
      IsHomogeneousRepresentation b c (multiplicityRepresentation V p) n

def canonical_polynomial_nonisomorphicType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (d : ℕ) (b : Module.Basis (Fin d) ℂ V) {n : ℕ} (p q : Partition n),
    length p ≤ d → length q ≤ d → p ≠ q →
    ¬ Nonempty (Representation.Equiv (multiplicityRepresentation V p)
      (multiplicityRepresentation V q))

/-- Every polynomial representation has the full homogeneous decomposition
specified upstream, including its invariant summands and polynomial entries. -/
def polynomial_homogeneous_splittingType : Prop := homogeneous_decompositionType.{u,v}

/-- In dimension zero the simple degree-zero object is the trivial complex
line, and positive-degree homogeneous representations have zero space. -/
def zero_dimension_polynomial_boundaryType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V],
    (∃ e : TensorMultiplicity V emptyPartition ≃ₗ[ℂ] ℂ,
      ∀ (g : LinearGroup V) (f : TensorMultiplicity V emptyPartition),
        e (tensorMultiplicityOperator V emptyPartition g f) = e f) ∧
    ∀ (W : Type v) [AddCommGroup W] [Module ℂ W] (m : ℕ)
      (b : Module.Basis (Fin 0) ℂ V) (c : Module.Basis (Fin m) ℂ W)
      (ρ : Representation ℂ (LinearGroup V) W),
      IsHomogeneousRepresentation b c ρ 0 ∧
      ∀ n, 0 < n → IsHomogeneousRepresentation b c ρ n → Subsingleton W

end Specs.AdvancedFiniteGroupRepresentations
