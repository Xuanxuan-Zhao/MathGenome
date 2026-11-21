import MathGenome.Internal.Specs.D07.Ch16.MapsSubmodules
import MathGenome.Internal.Specs.D07.Ch08.IdealDefinition
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Matrix.Action
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
Independent specification for K07.16.quotients_isomorphism,
paper.tex:2958–2980. Quotients are the canonical additive coset quotients,
with the induced unital left action. The general quotient statements use
arbitrary associative unital rings, including the zero ring, and arbitrary
modules, including zero modules. No finite generation hypothesis is added.

`generatorAnnihilator m` is the kernel of the actual linear map r ↦ r • m;
it is a left ideal over an arbitrary ring. The cyclic isomorphism below uses
a commutative ring, so its source is also the usual quotient ring R/I,
viewed solely as an R-module. No multiplication on M is required.

The last three statements use the library's standard matrix action on column
vectors, not entrywise scalar multiplication. Indices 0 and 1 represent the
source's indices 1 and 2. They verify that e₁ is a generator, identify its
annihilator, and exhibit the failure of right absorption.
-/

universe u v w

namespace Specs.D07.Ch16.QuotientsIsomorphism

/-- The left ideal annihilating a single vector; it need not be two-sided. -/
def generatorAnnihilator {R : Type u} [Ring R] {M : Type v}
    [AddCommGroup M] [Module R M] (m : M) : Ideal R :=
  LinearMap.ker (LinearMap.toSpanSingleton R M m)

/-- First standard column vector in the standard two-dimensional module. -/
def firstVector (F : Type u) [Zero F] [One F] : Fin 2 → F :=
  Pi.single 0 1

/-- The quotient has the prescribed operations and the four source module axioms. -/
def QuotientOperations : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    (N : Submodule R M),
    (∀ x y : M, N.mkQ (x + y) = N.mkQ x + N.mkQ y) ∧
    (∀ (r : R) (x : M), r • N.mkQ x = N.mkQ (r • x)) ∧
    Definition.ModuleLaws R (M ⧸ N)

/-- Scalar action preserves the coset relation, including the m+n formulation. -/
def RepresentativeIndependence : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    (N : Submodule R M) (r : R) (x y : M),
    (x - y ∈ N → r • x - r • y ∈ N ∧ N.mkQ (r • x) = N.mkQ (r • y)) ∧
    (∀ n ∈ N, N.mkQ (r • (x + n)) = N.mkQ (r • x))

def QuotientProjection : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    (N : Submodule R M),
    Function.Surjective N.mkQ ∧ LinearMap.ker N.mkQ = N ∧
    ∀ x y : M, N.mkQ x = N.mkQ y ↔ x - y ∈ N

/-- The unique factor map has precisely the formula in the source. -/
def QuotientLift : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    (L : Type w) [AddCommGroup L] [Module R L]
    (N : Submodule R M) (f : M →ₗ[R] L), N ≤ LinearMap.ker f →
    ∃ g : (M ⧸ N) →ₗ[R] L,
      (∀ x : M, g (N.mkQ x) = f x) ∧ g.comp N.mkQ = f ∧
      ∀ h : (M ⧸ N) →ₗ[R] L, h.comp N.mkQ = f → h = g

/-- Equality of values is exactly equality modulo the kernel. -/
def KernelCosets : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    (L : Type w) [AddCommGroup L] [Module R L]
    (f : M →ₗ[R] L) (x y : M),
    f x = f y ↔ x - y ∈ LinearMap.ker f

/-- The first isomorphism theorem with the specified map on representatives. -/
def FirstIsomorphism : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    (L : Type w) [AddCommGroup L] [Module R L] (f : M →ₗ[R] L),
    ∃ e : (M ⧸ LinearMap.ker f) ≃ₗ[R] LinearMap.range f,
      ∀ x : M, (e ((LinearMap.ker f).mkQ x) : L) = f x

/-- The generator map, its exact kernel, and its surjectivity criterion. -/
def GeneratorPresentation : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    (m : M),
    (∀ r : R, LinearMap.toSpanSingleton R M m r = r • m) ∧
    (∀ r : R, r ∈ generatorAnnihilator m ↔ r • m = 0) ∧
    LinearMap.ker (LinearMap.toSpanSingleton R M m) = generatorAnnihilator m ∧
    ((∀ x : M, ∃ r : R, r • m = x) ↔
      Function.Surjective (LinearMap.toSpanSingleton R M m))

/-- R/I is the usual quotient ring, with its induced R-module structure. -/
def CyclicQuotient : Prop :=
  ∀ (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (m : M), (∀ x : M, ∃ r : R, r • m = x) →
    ∃ e : (R ⧸ generatorAnnihilator m) ≃ₗ[R] M,
      ∀ r : R, e (Ideal.Quotient.mk (generatorAnnihilator m) r) = r • m

/-- e₁ generates the standard matrix module. -/
def MatrixGenerator : Prop :=
  ∀ (F : Type u) [Field F] (v : Fin 2 → F),
    ∃ A : Matrix (Fin 2) (Fin 2) F, A • firstVector F = v

/-- The annihilator consists exactly of matrices with first column zero. -/
def MatrixAnnihilator : Prop :=
  ∀ (F : Type u) [Field F] (A : Matrix (Fin 2) (Fin 2) F),
    (A ∈ generatorAnnihilator (R := Matrix (Fin 2) (Fin 2) F) (firstVector F) ↔ ∀ i, A i 0 = 0) ∧
    Ch08.IdealDefinition.IsLeftIdeal
      (generatorAnnihilator (R := Matrix (Fin 2) (Fin 2) F) (firstVector F)).toAddSubgroup

/-- Explicit witnesses, and the resulting failure of right and two-sided absorption. -/
def MatrixAnnihilatorNotTwoSided : Prop :=
  ∀ (F : Type u) [Field F],
    Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : F) ∈ generatorAnnihilator (R := Matrix (Fin 2) (Fin 2) F) (firstVector F) ∧
    Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : F) * Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : F) =
      Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : F) ∧
    Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : F) ∉ generatorAnnihilator (R := Matrix (Fin 2) (Fin 2) F) (firstVector F) ∧
    ¬ Ch08.IdealDefinition.IsRightIdeal
      (generatorAnnihilator (R := Matrix (Fin 2) (Fin 2) F) (firstVector F)).toAddSubgroup ∧
    ¬ (generatorAnnihilator (R := Matrix (Fin 2) (Fin 2) F) (firstVector F)).IsTwoSided

end Specs.D07.Ch16.QuotientsIsomorphism
