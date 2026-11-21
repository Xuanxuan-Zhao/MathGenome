import MathGenome.Internal.Specs.D05.M14.Pseudoinverse

/-!
Independent statements for K05.14.least_squares, paper.tex:2505–2516.
The scalar field is real or complex, expressed uniformly by `RCLike`.
The pseudoinverse and orthogonal projection are the existing shared constructions.
Both spaces are finite dimensional; neither is assumed to have positive dimension.
A minimizer means a global minimum of the residual norm over every vector of V.
The affine description, minimum-norm uniqueness, and injectivity criterion are
separate conclusions. No minimizer or inverse certificate is assumed.
-/

namespace Specs.D05.M14.LeastSquares

/-- Minimizing the residual is exactly projecting onto the image. -/
def minimizer_iff_projection : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W) (w : W) (v : V),
    (∀ u : V, ‖T v - w‖ ≤ ‖T u - w‖) ↔
      T v = _root_.D05.orthogonalProjection T.range w

/-- All minimizers, expressed as a difference in the kernel. -/
def minimizer_iff_kernel : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W) (w : W) (v : V),
    (∀ u : V, ‖T v - w‖ ≤ ‖T u - w‖) ↔
      v - _root_.D05.pseudoinverse T w ∈ T.ker

/-- The full affine set T⁺w + ker T, with both directions asserted. -/
def minimizer_iff_exists_kernel : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W) (w : W) (v : V),
    (∀ u : V, ‖T v - w‖ ≤ ‖T u - w‖) ↔
      ∃ k : V, k ∈ T.ker ∧ v = _root_.D05.pseudoinverse T w + k

/-- The pseudoinverse always attains the residual minimum. -/
def pseudoinverse_minimizes : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W) (w : W),
    ∀ u : V, ‖T (_root_.D05.pseudoinverse T w) - w‖ ≤ ‖T u - w‖

/-- Pythagoras along the entire affine set of minimizers. -/
def norm_add_kernel_sq : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W) (w : W) (k : V), k ∈ T.ker →
    ‖_root_.D05.pseudoinverse T w + k‖ ^ 2 =
      ‖_root_.D05.pseudoinverse T w‖ ^ 2 + ‖k‖ ^ 2

/-- T⁺w has the smallest norm among all residual minimizers. -/
def minimum_norm : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W) (w : W) (v : V),
    (∀ u : V, ‖T v - w‖ ≤ ‖T u - w‖) →
      ‖_root_.D05.pseudoinverse T w‖ ≤ ‖v‖

/-- Equality in the minimum-norm inequality forces precisely T⁺w. -/
def norm_eq_iff : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W) (w : W) (v : V),
    (∀ u : V, ‖T v - w‖ ≤ ‖T u - w‖) →
      (‖v‖ = ‖_root_.D05.pseudoinverse T w‖ ↔ v = _root_.D05.pseudoinverse T w)

/-- Existence and uniqueness of the minimum-norm least-squares solution. -/
def exists_unique_minimum_norm : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W) (w : W),
    ∃! v : V, (∀ u : V, ‖T v - w‖ ≤ ‖T u - w‖) ∧
      ∀ u : V, (∀ z : V, ‖T u - w‖ ≤ ‖T z - w‖) → ‖v‖ ≤ ‖u‖

/-- For each w, the residual minimizer is unique exactly when T is injective. -/
def unique_iff_injective : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W] (T : V →ₗ[F] W) (w : W),
    (∃! v : V, ∀ u : V, ‖T v - w‖ ≤ ‖T u - w‖) ↔ Function.Injective T

/-- For T = 0 every vector minimizes, and only zero has minimum norm. -/
def zero_map : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W],
    ∀ (w : W) (v : V),
      _root_.D05.pseudoinverse (0 : V →ₗ[F] W) w = 0 ∧
      ‖(0 : V →ₗ[F] W) v - w‖ = ‖w‖ ∧
      (∀ u : V, ‖(0 : V →ₗ[F] W) v - w‖ ≤ ‖(0 : V →ₗ[F] W) u - w‖) ∧
      (‖v‖ = ‖_root_.D05.pseudoinverse (0 : V →ₗ[F] W) w‖ ↔ v = 0)

end Specs.D05.M14.LeastSquares
