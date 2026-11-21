import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.StandardIndependence
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.Straightening
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Lift

/-! FR-B03, source lines 560–578. All shapes, including the empty shape,
use the upstream tabloids and Specht submodule. Rational polytabloids are
the signed column sums in the rational permutation module. -/
noncomputable section
open scoped BigOperators TensorProduct
namespace Specs.AdvancedFiniteGroupRepresentations

abbrev RationalPermutationModule {n : ℕ} (p : Partition n) := MonoidAlgebra ℚ (Tabloid p)

def rationalPermutationRepresentation {n : ℕ} (p : Partition n) :
    Representation ℚ (SymmetricGroup n) (RationalPermutationModule p) :=
  Representation.ofMulAction ℚ (SymmetricGroup n) (Tabloid p)

def rationalPolytabloid {n : ℕ} {p : Partition n} (t : Tableau p) :
    RationalPermutationModule p :=
  ∑ c : columnSubgroup t,
    MonoidAlgebra.single (tabloid (c.val • t)) ((Equiv.Perm.sign c.val : ℤ) : ℚ)

def rationalSpechtSpan {n : ℕ} (p : Partition n) :
    Submodule ℚ (RationalPermutationModule p) :=
  Submodule.span ℚ (Set.range (rationalPolytabloid (p := p)))

abbrev RationalSpechtModule {n : ℕ} (p : Partition n) := ↥(rationalSpechtSpan p)

def rationalEmbedding {n : ℕ} (p : Partition n) :
    RationalPermutationModule p →ₗ[ℚ] PermutationModule p :=
  ((MonoidAlgebra.coeffLinearEquiv ℂ).symm.restrictScalars ℚ).toLinearMap.comp
    ((Finsupp.mapRange.linearMap (Algebra.linearMap ℚ ℂ)).comp
      (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap)

def RationalPermutationModuleType := {n : ℕ} → Partition n → Type

def rationalPermutationRepresentationType := ∀ {n : ℕ} (p : Partition n),
  Representation ℚ (SymmetricGroup n) (RationalPermutationModule p)

def rationalPolytabloidType := {n : ℕ} → {p : Partition n} → Tableau p → RationalPermutationModule p

def rationalSpechtSpanType := ∀ {n : ℕ} (p : Partition n), Submodule ℚ (RationalPermutationModule p)

def RationalSpechtModuleType := {n : ℕ} → Partition n → Type

def rationalEmbeddingType := ∀ {n : ℕ} (p : Partition n),
  RationalPermutationModule p →ₗ[ℚ] PermutationModule p

def standard_basisType : Prop := ∀ {n : ℕ} (p : Partition n),
  ∃ b : Module.Basis (StandardTableau p) ℂ (SpechtModule p),
    ∀ t, (b t).val = polytabloid t.val

def specht_finrankType : Prop := ∀ {n : ℕ} (p : Partition n),
  Module.finrank ℂ (SpechtModule p) = standardTableauCount p

def rationalEmbedding_polytabloidType : Prop := ∀ {n : ℕ} {p : Partition n} (t : Tableau p),
  rationalEmbedding p (rationalPolytabloid t) = polytabloid t

def rational_standard_basisType : Prop := ∀ {n : ℕ} (p : Partition n),
  ∃ b : Module.Basis (StandardTableau p) ℚ (RationalSpechtModule p),
    ∀ t, (b t).val = rationalPolytabloid t.val

def rational_specht_finrankType : Prop := ∀ {n : ℕ} (p : Partition n),
  Module.finrank ℚ (RationalSpechtModule p) = standardTableauCount p

/-- The actions are inherited from the actual tabloid actions. The equivalence
is the scalar-extension map on every pure tensor, not merely an abstract
isomorphism of vector spaces with equal dimensions. -/
def rational_modelType : Prop := ∀ {n : ℕ} (p : Partition n),
  ∃ (ρQ : Representation ℚ (SymmetricGroup n) (RationalSpechtModule p))
    (ρC : Representation ℂ (SymmetricGroup n) (SpechtModule p))
    (e : (ℂ ⊗[ℚ] RationalSpechtModule p) ≃ₗ[ℂ] SpechtModule p),
    (∀ g v, (ρQ g v).val = rationalPermutationRepresentation p g v.val) ∧
    (∀ g v, (ρC g v).val = permutationRepresentation p g v.val) ∧
    (∀ z v, (e (z ⊗ₜ[ℚ] v)).val = z • rationalEmbedding p v.val) ∧
    (∀ g x, e ((ρQ g).baseChange ℂ x) = ρC g (e x))

end Specs.AdvancedFiniteGroupRepresentations
