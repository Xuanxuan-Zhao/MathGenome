import MathGenome.Internal.Specs.D05.M07.Dual
import MathGenome.Internal.Specs.D05.M12.OnBasis
import MathGenome.Internal.Specs.D05.M12.FourierParseval

/-!
Independent specifications for K05.12.riesz, paper.tex:2061–2068.
The dual is the algebraic dual, with no continuity condition. The canonical
map uses `innerₛₗ`: its value at `w`, evaluated at `v`, is `inner F w v`,
which is exactly the shared first-slot-linear `D05.firstInner v w`.
No completeness is assumed. Finite dimension is required for surjectivity
and representation of arbitrary functionals, but not for the map or uniqueness.
-/

namespace Specs.D05.M12.Riesz

universe u v

/-- Type of the canonical conjugate-linear map to the algebraic dual. -/
def rieszMap_type : Type (max (u + 1) (v + 1)) :=
  (F : Type u) → (V : Type v) → [RCLike F] → [NormedAddCommGroup V] →
    [InnerProductSpace F V] → V →ₗ⋆[F] Module.Dual F V

def rieszMap_value : rieszMap_type.{u, v} := fun F _ _ _ _ => innerₛₗ F

/-- Exact bridge from the algebraic sesquilinear map to the paper convention. -/
def map_apply : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (w v : V), innerₛₗ F w v = _root_.D05.firstInner (F := F) v w

/-- The explicit representing vector in any finite orthonormal basis. -/
def representation_in_basis : Prop :=
  ∀ {F V I : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [Fintype I] (b : Module.Basis I F V),
    _root_.D05.orthonormalFamily (F := F) b →
    ∀ (φ : Module.Dual F V) (v : V),
      φ v = _root_.D05.firstInner (F := F) v (∑ j, starRingEnd F (φ (b j)) • b j)

/-- Uniqueness requires neither finite dimension nor completeness. -/
def representing_vector_unique : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (φ : Module.Dual F V) (w z : V),
    (∀ v, φ v = _root_.D05.firstInner (F := F) v w) →
    (∀ v, φ v = _root_.D05.firstInner (F := F) v z) → w = z

/-- Every algebraic linear functional has exactly one representing vector. -/
def exists_unique_representation : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V] (φ : Module.Dual F V),
    ∃! w : V, ∀ v : V, φ v = _root_.D05.firstInner (F := F) v w

/-- The canonical correspondence is a bijection onto the algebraic dual. -/
def rieszMap_bijective : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [FiniteDimensional F V], Function.Bijective (innerₛₗ F (E := V))

/-- In particular, over ℂ the scalars on functionals are conjugated. -/
def conjugate_linear : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    (a b : F) (w z : V),
    innerₛₗ F (a • w + b • z) =
      starRingEnd F a • innerₛₗ F w + starRingEnd F b • innerₛₗ F z

/-- Over ℝ conjugation is the identity, so the same correspondence is linear. -/
def real_linear : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (a b : ℝ) (w z : V),
    innerₛₗ ℝ (a • w + b • z) = a • innerₛₗ ℝ w + b • innerₛₗ ℝ z

/-- On a zero space the functional is zero, zero represents it, and every
representing vector is zero. A subsingleton module is precisely a zero space. -/
def zero_space : Prop :=
  ∀ {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]
    [Subsingleton V] (φ : Module.Dual F V),
    φ = 0 ∧ (∀ v, φ v = _root_.D05.firstInner (F := F) v 0) ∧
      (∀ w : V, (∀ v, φ v = _root_.D05.firstInner (F := F) v w) → w = 0)

end Specs.D05.M12.Riesz
