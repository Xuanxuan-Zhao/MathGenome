import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Symmetric.Grading

namespace Specs.Alg01SymmetricWitt.Symmetric.Multilinear

open Specs.Alg01SymmetricWitt.Symmetric.Algebra
open Specs.Alg01SymmetricWitt.Symmetric.Grading (degreeQuotientMap)

universe u v v' w w'

/-- Multilinear maps invariant under precomposition by any permutation of the inputs. -/
def SymmetricMultilinearMap (R : Type u) (M : Type v) (N : Type w)
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (n : ℕ) :=
  { f : MultilinearMap R (fun _ : Fin n => M) N //
      ∀ (x : Fin n → M) (σ : Equiv.Perm (Fin n)), f (x ∘ σ) = f x }

/-- The bijection and its inverse on the canonical pure products. -/
def universal : Prop :=
  ∀ (R : Type u) (M : Type v) (N : Type w)
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (n : ℕ),
    ∃ e : (degree R M n →ₗ[R] N) ≃ SymmetricMultilinearMap R M N n,
      (∀ g, (e g).val = g.compMultilinearMap (pureProduct R M n)) ∧
      (∀ f x, e.symm f (pureProduct R M n x) = f.val x)

/-- On the empty tuple the correspondence is evaluation at the unit. -/
def degreeZero : Prop :=
  ∀ (R : Type u) (M : Type v) (N : Type w)
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N],
    ∃ e : SymmetricMultilinearMap R M N 0 ≃ N, ∃ unit : degree R M 0,
      (unit : SymmetricAlgebra R M) = 1 ∧
      (∀ f, e f = f.val (fun i => Fin.elim0 i)) ∧
      (∀ (g : degree R M 0 →ₗ[R] N) f,
        f.val = g.compMultilinearMap (pureProduct R M 0) → e f = g unit)

/-- The one-input correspondence recovers every linear map along the generator inclusion. -/
def degreeOne : Prop :=
  ∀ (R : Type u) (M : Type v) (N : Type w)
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N],
    ∃ e : SymmetricMultilinearMap R M N 1 ≃ (M →ₗ[R] N), ∃ i : M ≃ₗ[R] degree R M 1,
      (∀ x : M, (i x : SymmetricAlgebra R M) = SymmetricAlgebra.ι R M x) ∧
      (∀ f x, e f x = f.val (fun _ => x)) ∧
      (∀ (g : degree R M 1 →ₗ[R] N) f,
        f.val = g.compMultilinearMap (pureProduct R M 1) → e f = g.comp i.toLinearMap)

/-- Postcomposition by a linear map on the codomain commutes with restriction to pure products. -/
def naturalityTarget : Prop :=
  ∀ (R : Type u) (M : Type v) (N : Type w) (N' : Type w')
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R N'] (n : ℕ) (h : N →ₗ[R] N') (g : degree R M n →ₗ[R] N),
    (h.comp g).compMultilinearMap (pureProduct R M n) =
      h.compMultilinearMap (g.compMultilinearMap (pureProduct R M n))

/-- The map on the degree submodule induced by a linear map of generators. -/
def inducedDegreeMap : Prop :=
  ∀ (R : Type u) (M : Type v) (M' : Type v')
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (n : ℕ) (h : M →ₗ[R] M'),
    ∃! F : degree R M n →ₗ[R] degree R M' n,
      (∀ x : Fin n → M, F (pureProduct R M n x) = pureProduct R M' n (fun i => h (x i))) ∧
      F.comp (degreeQuotientMap R M n) =
        (degreeQuotientMap R M' n).comp (PiTensorProduct.map (fun _ : Fin n => h))

/-- Precomposition by the induced map agrees with applying the linear map in every input. -/
def naturalitySource : Prop :=
  ∀ (R : Type u) (M : Type v) (M' : Type v') (N : Type w)
    [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup N] [Module R N] (n : ℕ) (h : M →ₗ[R] M')
    (F : degree R M n →ₗ[R] degree R M' n),
    (∀ x : Fin n → M, F (pureProduct R M n x) = pureProduct R M' n (fun i => h (x i))) →
    ∀ g : degree R M' n →ₗ[R] N,
      (g.comp F).compMultilinearMap (pureProduct R M n) =
        (g.compMultilinearMap (pureProduct R M' n)).compLinearMap (fun _ => h)

end Specs.Alg01SymmetricWitt.Symmetric.Multilinear
