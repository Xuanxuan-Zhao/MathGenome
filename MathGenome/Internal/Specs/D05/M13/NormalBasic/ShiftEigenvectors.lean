import MathGenome.Internal.Specs.D05.M13.Normal
import MathGenome.Internal.Specs.D05.M09.Eigenspace

/-!
Independent statements for the shift/eigenvector stage of K05.13.normal_basic
(paper.tex:2155–2181). The shared normality predicate is TT† = T†T and
`D05.firstInner u v = inner F v u` is the paper's first-slot-linear product.
No eigenbasis, nonzero-vector, positive-dimension, or splitting assumption is used.
-/

namespace Specs.D05.M13.NormalBasic.ShiftEigenvectors

universe u v

/-- The adjoint of a scalar shift, for every endomorphism. -/
def adjoint_shift : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : Module.End F V) (μ : F),
    LinearMap.adjoint (T - μ • LinearMap.id) =
      LinearMap.adjoint T - starRingEnd F μ • LinearMap.id

/-- Every scalar shift of a normal map is normal over the same field. -/
def shift_normal : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : Module.End F V),
    _root_.D05.normalOperator T → ∀ μ : F,
      _root_.D05.normalOperator (T - μ • LinearMap.id)

/-- The equivalence is for all vectors, including zero. -/
def eigenvector_equation_iff : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : Module.End F V),
    _root_.D05.normalOperator T → ∀ (μ : F) (x : V),
      T x = μ • x ↔ LinearMap.adjoint T x = starRingEnd F μ • x

/-- Equality of the actual eigenspace submodules, with conjugated eigenvalue. -/
def eigenspace_adjoint : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : Module.End F V),
    _root_.D05.normalOperator T → ∀ μ : F,
      T.eigenspace μ = Module.End.eigenspace (LinearMap.adjoint T) (starRingEnd F μ)

/-- Orthogonality expressed in precisely the paper's inner-product convention. -/
def eigenvectors_orthogonal : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : Module.End F V),
    _root_.D05.normalOperator T → ∀ (α β : F), α ≠ β →
      ∀ (x y : V), T x = α • x → T y = β • y →
        _root_.D05.firstInner (F := F) x y = 0

/-- Distinct eigenspaces are orthogonal as subspaces, also over the reals. -/
def eigenspaces_orthogonal : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : Module.End F V),
    _root_.D05.normalOperator T → ∀ (α β : F), α ≠ β →
      T.eigenspace α ≤ (T.eigenspace β).orthogonal

end Specs.D05.M13.NormalBasic.ShiftEigenvectors
