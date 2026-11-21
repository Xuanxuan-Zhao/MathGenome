import MathGenome.Internal.Specs.D05.M14.Pseudoinverse
import MathGenome.Internal.Specs.D05.M13.AdjointLaws

/-!
Independent statements for the converse in K05.14.penrose, paper.tex:2488–2503.
We use the shared inverse-restriction pseudoinverse, ambient orthogonal projection,
and Mathlib adjoint (already bridged to the paper's first-slot-linear convention).
All spaces are finite dimensional over `RCLike`, with zero dimensions included.
The candidate is an arbitrary linear map; its only assumptions in the uniqueness
statement are the four displayed Penrose equations.
-/

noncomputable section
namespace Specs.D05.M14.Penrose.Uniqueness

/-- A self-adjoint idempotent is projection onto its range, and that range
is exactly the perpendicular of its kernel. -/
def self_adjoint_idempotent_projection : Prop :=
  ∀ {F V : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V] [FiniteDimensional F V]
    (P : V →ₗ[F] V), P.comp P = P → LinearMap.adjoint P = P →
    P = _root_.D05.orthogonalProjection P.range ∧ P.range = P.ker.orthogonal

/-- The first and third equations already identify TX. -/
def candidate_range_projection : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] W) (X : W →ₗ[F] V),
    (T.comp X).comp T = T →
    LinearMap.adjoint (T.comp X) = T.comp X →
    T.comp X = _root_.D05.orthogonalProjection T.range

/-- The first and fourth equations already identify XT. -/
def candidate_kernel_projection : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] W) (X : W →ₗ[F] V),
    (T.comp X).comp T = T →
    LinearMap.adjoint (X.comp T) = X.comp T →
    X.comp T = _root_.D05.orthogonalProjection T.ker.orthogonal

/-- The candidate satisfies both conditions of the intrinsic characterization. -/
def candidate_characterization : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] W) (X : W →ₗ[F] V),
    (T.comp X).comp T = T →
    (X.comp T).comp X = X →
    LinearMap.adjoint (T.comp X) = T.comp X →
    LinearMap.adjoint (X.comp T) = X.comp T →
    ∀ w : W, X w ∈ T.ker.orthogonal ∧
      T (X w) = _root_.D05.orthogonalProjection T.range w

/-- The four equations characterize the existing pseudoinverse among all X. -/
def uniqueness : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (T : V →ₗ[F] W) (X : W →ₗ[F] V),
    (T.comp X).comp T = T →
    (X.comp T).comp X = X →
    LinearMap.adjoint (T.comp X) = T.comp X →
    LinearMap.adjoint (X.comp T) = X.comp T →
    X = _root_.D05.pseudoinverse T

end Specs.D05.M14.Penrose.Uniqueness
