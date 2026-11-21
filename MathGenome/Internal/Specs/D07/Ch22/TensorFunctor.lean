import MathGenome.Internal.Specs.D07.Ch22.TensorConstruction
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
Independent specification of K07.22.tensor_functor, paper.tex:6764–6794.
All modules are arbitrary unital modules over a commutative unital ring;
no nontriviality, freeness, dimension, or finiteness assumptions are imposed.
The tensor is the canonical tensor identified with the balanced quotient by
K07.22.tensor_construction. Tensor maps and canonical equivalences below are
Mathlib's actual linear maps and equivalences, not merely functions.
Existence and uniqueness statements specify the elementary forward and
inverse formulas. Naturality statements specify equality of linear maps.
-/

universe u v w t a b c d e f q
namespace Specs.D07.Ch22.TensorFunctor
open scoped TensorProduct

/-- The unique induced linear map, specified on all elementary tensors. -/
def MapConstruction : Prop :=
  ∀ (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (M' : Type a) [AddCommGroup M'] [Module R M']
    (N' : Type b) [AddCommGroup N'] [Module R N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N'),
    ∃! F : (M ⊗[R] N) →ₗ[R] (M' ⊗[R] N'),
      ∀ m n, F (m ⊗ₜ[R] n) = f m ⊗ₜ[R] g n

/-- The canonical induced map has the source formula. -/
def MapFormula : Prop :=
  ∀ (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (M' : Type a) [AddCommGroup M'] [Module R M']
    (N' : Type b) [AddCommGroup N'] [Module R N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N') (m : M) (n : N),
    TensorProduct.map f g (m ⊗ₜ[R] n) = f m ⊗ₜ[R] g n

/-- Tensoring respects composition in both variables. -/
def MapComposition : Prop :=
  ∀ (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (M' : Type a) [AddCommGroup M'] [Module R M']
    (N' : Type b) [AddCommGroup N'] [Module R N']
    (M'' : Type d) [AddCommGroup M''] [Module R M'']
    (N'' : Type e) [AddCommGroup N''] [Module R N'']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    (f' : M' →ₗ[R] M'') (g' : N' →ₗ[R] N''),
    TensorProduct.map (f'.comp f) (g'.comp g) =
      (TensorProduct.map f' g').comp (TensorProduct.map f g)

/-- Tensoring the two identities gives the identity of the tensor. -/
def MapIdentity : Prop :=
  ∀ (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N],
    TensorProduct.map (LinearMap.id : M →ₗ[R] M) (LinearMap.id : N →ₗ[R] N) =
      (LinearMap.id : (M ⊗[R] N) →ₗ[R] (M ⊗[R] N))

/-- Additivity and preservation of zero in each map separately. -/
def MapAdditivity : Prop :=
  ∀ (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (M' : Type a) [AddCommGroup M'] [Module R M']
    (N' : Type b) [AddCommGroup N'] [Module R N']
    (f f' : M →ₗ[R] M') (g g' : N →ₗ[R] N'),
    TensorProduct.map (f + f') g = TensorProduct.map f g + TensorProduct.map f' g ∧
    TensorProduct.map f (g + g') = TensorProduct.map f g + TensorProduct.map f g' ∧
    TensorProduct.map (0 : M →ₗ[R] M') g = 0 ∧
    TensorProduct.map f (0 : N →ₗ[R] N') = 0

/-- Linear maps out of a tensor agree if they agree on elementary tensors. -/
def TensorExt : Prop :=
  ∀ (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (P : Type t) [AddCommGroup P] [Module R P]
    (F G : (M ⊗[R] N) →ₗ[R] P),
    (∀ m n, F (m ⊗ₜ[R] n) = G (m ⊗ₜ[R] n)) → F = G

/-- The unique swap equivalence with its forward and inverse formulas. -/
def CommIsomorphism : Prop :=
  ∀ (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N],
    ∃! E : (M ⊗[R] N) ≃ₗ[R] (N ⊗[R] M),
      (∀ m n, E (m ⊗ₜ[R] n) = n ⊗ₜ[R] m) ∧
      (∀ n m, E.symm (n ⊗ₜ[R] m) = m ⊗ₜ[R] n)

/-- Swapping twice is the identity on the whole tensor product. -/
def CommInvolution : Prop :=
  ∀ (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N],
    (TensorProduct.comm R N M).toLinearMap.comp
      (TensorProduct.comm R M N).toLinearMap =
      (LinearMap.id : (M ⊗[R] N) →ₗ[R] (M ⊗[R] N))

/-- The swap commutes with tensoring any pair of linear maps. -/
def CommNaturality : Prop :=
  ∀ (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (M' : Type a) [AddCommGroup M'] [Module R M']
    (N' : Type b) [AddCommGroup N'] [Module R N']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N'),
    (TensorProduct.map g f).comp (TensorProduct.comm R M N).toLinearMap =
      (TensorProduct.comm R M' N').toLinearMap.comp (TensorProduct.map f g)

/-- The unique associator, with both elementary triple formulas. -/
def AssocIsomorphism : Prop :=
  ∀ (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (P : Type t) [AddCommGroup P] [Module R P],
    ∃! E : ((M ⊗[R] N) ⊗[R] P) ≃ₗ[R] (M ⊗[R] (N ⊗[R] P)),
      (∀ m n p, E ((m ⊗ₜ[R] n) ⊗ₜ[R] p) = m ⊗ₜ[R] (n ⊗ₜ[R] p)) ∧
      (∀ m n p, E.symm (m ⊗ₜ[R] (n ⊗ₜ[R] p)) = (m ⊗ₜ[R] n) ⊗ₜ[R] p)

/-- Elementary triples generate the underlying abelian groups in both bracketings. -/
def IteratedGenerators : Prop :=
  ∀ (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (P : Type t) [AddCommGroup P] [Module R P],
    AddSubgroup.closure {x : (M ⊗[R] N) ⊗[R] P |
      ∃ m n p, (m ⊗ₜ[R] n) ⊗ₜ[R] p = x} = ⊤ ∧
    AddSubgroup.closure {x : M ⊗[R] (N ⊗[R] P) |
      ∃ m n p, m ⊗ₜ[R] (n ⊗ₜ[R] p) = x} = ⊤

/-- Agreement on elementary triples determines maps from either bracketing. -/
def IteratedExt : Prop :=
  ∀ (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (P : Type t) [AddCommGroup P] [Module R P]
    (Q : Type q) [AddCommGroup Q] [Module R Q],
    (∀ F G : ((M ⊗[R] N) ⊗[R] P) →ₗ[R] Q,
      (∀ m n p, F ((m ⊗ₜ[R] n) ⊗ₜ[R] p) = G ((m ⊗ₜ[R] n) ⊗ₜ[R] p)) → F = G) ∧
    (∀ F G : (M ⊗[R] (N ⊗[R] P)) →ₗ[R] Q,
      (∀ m n p, F (m ⊗ₜ[R] (n ⊗ₜ[R] p)) = G (m ⊗ₜ[R] (n ⊗ₜ[R] p))) → F = G)

/-- Rebracketing commutes with tensoring three arbitrary linear maps. -/
def AssocNaturality : Prop :=
  ∀ (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (N : Type w) [AddCommGroup N] [Module R N]
    (P : Type t) [AddCommGroup P] [Module R P]
    (M' : Type a) [AddCommGroup M'] [Module R M']
    (N' : Type b) [AddCommGroup N'] [Module R N']
    (P' : Type c) [AddCommGroup P'] [Module R P']
    (f : M →ₗ[R] M') (g : N →ₗ[R] N') (h : P →ₗ[R] P'),
    (TensorProduct.map f (TensorProduct.map g h)).comp
      (TensorProduct.assoc R M N P).toLinearMap =
    (TensorProduct.assoc R M' N' P').toLinearMap.comp
      (TensorProduct.map (TensorProduct.map f g) h)

/-- The unique unit equivalence sends r tensor m to rm, and its inverse sends m to 1 tensor m. -/
def UnitIsomorphism : Prop :=
  ∀ (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M],
    ∃! E : (R ⊗[R] M) ≃ₗ[R] M,
      (∀ (r : R) m, E (r ⊗ₜ[R] m) = r • m) ∧
      (∀ m, E.symm m = (1 : R) ⊗ₜ[R] m)

/-- The balancing identity used to check the unit inverse, also valid for the zero ring. -/
def UnitBalance : Prop :=
  ∀ (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (r : R) (m : M),
    (1 : R) ⊗ₜ[R] (r • m) = r ⊗ₜ[R] m

/-- The left unit equivalence commutes with every linear map of modules. -/
def UnitNaturality : Prop :=
  ∀ (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (M' : Type a) [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M'),
    (TensorProduct.lid R M').toLinearMap.comp
      (TensorProduct.map (LinearMap.id : R →ₗ[R] R) f) =
      f.comp (TensorProduct.lid R M).toLinearMap

end Specs.D07.Ch22.TensorFunctor
