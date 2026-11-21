import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Symmetric.Algebra
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

namespace Specs.Alg01SymmetricWitt.Symmetric.Grading

open scoped DirectSum
open Specs.Alg01SymmetricWitt.Symmetric.Algebra

universe u v

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

/-- The relations between pure tensors that differ by a single adjacent transposition. -/
def adjacentRelations (n : ℕ) : Submodule R (TensorPower R n M) :=
  Submodule.span R {t | ∃ (x : Fin n → M) (i j : Fin n), j.val = i.val + 1 ∧
    t = PiTensorProduct.tprod R x - PiTensorProduct.tprod R (x ∘ Equiv.swap i j)}

/-- The relations between pure tensors that differ by any permutation of the factors. -/
def permutationRelations (n : ℕ) : Submodule R (TensorPower R n M) :=
  Submodule.span R {t | ∃ (x : Fin n → M) (σ : Equiv.Perm (Fin n)),
    t = PiTensorProduct.tprod R x - PiTensorProduct.tprod R (x ∘ σ)}

/-- The canonical tensor-power quotient map with its codomain restricted to the degree. -/
def degreeQuotientMap (n : ℕ) : TensorPower R n M →ₗ[R] degree R M n :=
  (degreeMap R M n).rangeRestrict

set_option linter.checkUnivs false

def degreeQuotientMapType :=
  ∀ (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ),
    TensorPower R n M →ₗ[R] degree R M n

def adjacentRelationsType :=
  ∀ (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ),
    Submodule R (TensorPower R n M)

def permutationRelationsType :=
  ∀ (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ),
    Submodule R (TensorPower R n M)

/-- In the canonical tensor grading, every component of an ideal element belongs to the ideal. -/
def idealHomogeneous : Prop :=
  ∀ (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (t : TensorAlgebra R M), t ∈ commutatorIdeal R M →
    ∀ n : ℕ, TensorPower.toTensorAlgebra (TensorAlgebra.equivDirectSum t n) ∈ commutatorIdeal R M

/-- The full kernel description, valid also in the two degrees with no adjacent swaps. -/
def degreeKernel : Prop :=
  ∀ (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ),
    LinearMap.ker (degreeMap R M n) = adjacentRelations R M n

def adjacent_eq_permutation : Prop :=
  ∀ (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ),
    adjacentRelations R M n = permutationRelations R M n

def lowDegreeKernels : Prop :=
  ∀ (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M],
    LinearMap.ker (degreeMap R M 0) = ⊥ ∧ LinearMap.ker (degreeMap R M 1) = ⊥

/-- The quotient by adjacent swaps is the actual degree submodule, via the canonical map. -/
def degreeQuotient : Prop :=
  ∀ (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] (n : ℕ),
    ∃ e : (TensorPower R n M ⧸ adjacentRelations R M n) ≃ₗ[R] degree R M n,
      ∀ t : TensorPower R n M,
        e ((adjacentRelations R M n).mkQ t) = degreeQuotientMap R M n t

/-- The actual degree submodules form an internal graded algebra. Its decomposition of the
canonical quotient map is obtained by applying the degree maps to the tensor components. -/
def grading : Prop :=
  ∀ (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M],
    ∃ g : GradedAlgebra (degree R M),
      letI := g
      ∀ t : TensorAlgebra R M,
        DirectSum.decomposeAlgEquiv (degree R M) (SymmetricAlgebra.algHom R M t) =
          DirectSum.lmap (degreeQuotientMap R M)
            (TensorAlgebra.equivDirectSum t)

def degreeZero : Prop :=
  ∀ (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M],
    ∃ g : GradedAlgebra (degree R M),
      letI := g
      ∃ e : R ≃ₐ[R] degree R M 0, ∀ r : R,
        (e r : SymmetricAlgebra R M) = algebraMap R (SymmetricAlgebra R M) r

def degreeOne : Prop :=
  ∀ (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M],
    ∃ e : M ≃ₗ[R] degree R M 1, ∀ m : M,
      (e m : SymmetricAlgebra R M) = SymmetricAlgebra.ι R M m

end Specs.Alg01SymmetricWitt.Symmetric.Grading
