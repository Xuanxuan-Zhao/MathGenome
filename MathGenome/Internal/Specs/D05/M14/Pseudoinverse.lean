import MathGenome.Internal.Specs.D05.M03.Isomorphism
import MathGenome.Internal.Specs.D05.M12.Projection
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
K05.14.pseudoinverse, paper.tex:2472–2486.
All spaces are finite dimensional over R or C (uniformly `RCLike`), including
zero spaces. Orthogonality and projection are the existing shared objects.
`LinearMap.leftInverse` is used only as a total library construction: the
implementation must prove that the actual restricted map is bijective and that
this chosen left inverse is its two-sided inverse. No such certificate is assumed.
-/

noncomputable section

namespace D05

variable {F V W : Type*} [RCLike F]
  [NormedAddCommGroup V] [InnerProductSpace F V]
  [NormedAddCommGroup W] [InnerProductSpace F W]

/-- T restricted to the perpendicular of its kernel, with codomain its image. -/
def pseudoinverseRestriction (T : V →ₗ[F] W) :
    T.ker.orthogonal →ₗ[F] T.range :=
  T.rangeRestrict.comp T.ker.orthogonal.subtype

/-- The shared orthogonal projection with its codomain restricted to the range. -/
def pseudoinverseRangeProjection [FiniteDimensional F W] (T : V →ₗ[F] W) :
    W →ₗ[F] T.range :=
  (orthogonalProjection T.range).codRestrict T.range (by
    intro w
    let : CompleteSpace T.range := FiniteDimensional.complete F T.range
    exact T.range.starProjection_apply_mem w)

/-- Project onto the image, apply the inverse restriction, and include into V. -/
def pseudoinverse [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] W) : W →ₗ[F] V :=
  T.ker.orthogonal.subtype.comp
    ((pseudoinverseRestriction T).leftInverse.comp (pseudoinverseRangeProjection T))

end D05

namespace Specs.D05.M14.Pseudoinverse

universe u v w

def restriction_type : Type (max (u + 1) (v + 1) (w + 1)) :=
  {F : Type u} → {V : Type v} → {W : Type w} → [RCLike F] →
    [NormedAddCommGroup V] → [InnerProductSpace F V] →
    [NormedAddCommGroup W] → [InnerProductSpace F W] →
    (T : V →ₗ[F] W) → T.ker.orthogonal →ₗ[F] T.range

def restriction_value : restriction_type.{u, v, w} :=
  fun T => T.rangeRestrict.comp T.ker.orthogonal.subtype

def pseudoinverse_type : Type (max (u + 1) (v + 1) (w + 1)) :=
  {F : Type u} → {V : Type v} → {W : Type w} → [RCLike F] →
    [NormedAddCommGroup V] → [InnerProductSpace F V] →
    [NormedAddCommGroup W] → [InnerProductSpace F W] →
    [FiniteDimensional F V] → [FiniteDimensional F W] →
    (V →ₗ[F] W) → W →ₗ[F] V

def pseudoinverse_value : pseudoinverse_type.{u, v, w} := fun T =>
  T.ker.orthogonal.subtype.comp
    ((_root_.D05.pseudoinverseRestriction T).leftInverse.comp
      (_root_.D05.pseudoinverseRangeProjection T))

def restriction_bijective : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    Function.Bijective (_root_.D05.pseudoinverseRestriction T)

def restriction_isomorphism : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    ∃ e : T.ker.orthogonal ≃ₗ[F] T.range,
      e.toLinearMap = _root_.D05.pseudoinverseRestriction T

def restriction_inverse : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    ((_root_.D05.pseudoinverseRestriction T).leftInverse.comp
      (_root_.D05.pseudoinverseRestriction T) = LinearMap.id) ∧
    ((_root_.D05.pseudoinverseRestriction T).comp
      (_root_.D05.pseudoinverseRestriction T).leftInverse = LinearMap.id)

def construction_formula : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W)
    (e : T.ker.orthogonal ≃ₗ[F] T.range)
    (_he : e.toLinearMap = _root_.D05.pseudoinverseRestriction T) (w : W),
    _root_.D05.pseudoinverse T w =
      (e.symm (_root_.D05.pseudoinverseRangeProjection T w) : V)

def mem_kernel_orthogonal : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W) (w : W),
    _root_.D05.pseudoinverse T w ∈ T.ker.orthogonal

def map_pseudoinverse : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W) (w : W),
    T (_root_.D05.pseudoinverse T w) = _root_.D05.orthogonalProjection T.range w

def characterization : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W) (w : W) (v : V),
    v = _root_.D05.pseudoinverse T w ↔
      v ∈ T.ker.orthogonal ∧ T v = _root_.D05.orthogonalProjection T.range w

def unique_linear_map : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W),
    ∃! S : W →ₗ[F] V, ∀ w : W,
      S w ∈ T.ker.orthogonal ∧ T (S w) = _root_.D05.orthogonalProjection T.range w

def basis_independence : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W) (S : W →ₗ[F] V),
    (∀ w : W, S w ∈ T.ker.orthogonal ∧
      T (S w) = _root_.D05.orthogonalProjection T.range w) →
    S = _root_.D05.pseudoinverse T

def map_add : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W) (x y : W),
    _root_.D05.pseudoinverse T (x + y) =
      _root_.D05.pseudoinverse T x + _root_.D05.pseudoinverse T y

def map_smul : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W) (a : F) (w : W),
    _root_.D05.pseudoinverse T (a • w) = a • _root_.D05.pseudoinverse T w

def zero_restriction_spaces : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W],
    (LinearMap.ker (0 : V →ₗ[F] W)).orthogonal = ⊥ ∧
      LinearMap.range (0 : V →ₗ[F] W) = ⊥

def pseudoinverse_zero : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W],
    _root_.D05.pseudoinverse (0 : V →ₗ[F] W) = 0

end Specs.D05.M14.Pseudoinverse
