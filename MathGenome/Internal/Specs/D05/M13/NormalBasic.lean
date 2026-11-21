import MathGenome.Internal.Specs.D05.M13.NormalBasic.NormKernel
import MathGenome.Internal.Specs.D05.M13.NormalBasic.ShiftEigenvectors

/-!
Independent statements for K05.13.normal_basic, paper.tex:2155–2181.
The first-slot-linear inner product, algebraic adjoint and normality predicate
are the shared upstream objects. All real/complex statements include zero spaces.
The complex parts below are the explicit scalar divisions from the paper,
with no normality assumption for their construction or uniqueness.
-/

namespace Specs.D05.M13.NormalBasic

universe u v

def normal_iff_norm_adjoint : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.normalOperator T ↔ ∀ x : V, ‖T x‖ = ‖LinearMap.adjoint T x‖

def ker_eq_ker_adjoint : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.normalOperator T → LinearMap.ker T = LinearMap.ker (LinearMap.adjoint T)

def range_eq_range_adjoint : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.normalOperator T →
      LinearMap.range T = LinearMap.range (LinearMap.adjoint T)

def range_eq_orthogonal_ker : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.normalOperator T → LinearMap.range T = (LinearMap.ker T).orthogonal

def orthogonal_direct_sum : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.normalOperator T →
      Specs.D05.M06.DirectSum.UniqueDecomposition
        (fun b : Bool => if b then LinearMap.range T else LinearMap.ker T) ∧
      ∀ x ∈ LinearMap.ker T, ∀ y ∈ LinearMap.range T,
        _root_.D05.firstInner (F := F) x y = 0

def exists_unique_components : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : V →ₗ[F] V),
    _root_.D05.normalOperator T → ∀ x : V,
      ∃! p : LinearMap.ker T × LinearMap.range T, (p.1 : V) + (p.2 : V) = x

def adjoint_shift : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : Module.End F V) (μ : F),
    LinearMap.adjoint (T - μ • LinearMap.id) =
      LinearMap.adjoint T - starRingEnd F μ • LinearMap.id

def shift_normal : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : Module.End F V),
    _root_.D05.normalOperator T → ∀ μ : F,
      _root_.D05.normalOperator (T - μ • LinearMap.id)

def eigenvector_equation_iff : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : Module.End F V),
    _root_.D05.normalOperator T → ∀ (μ : F) (x : V),
      T x = μ • x ↔ LinearMap.adjoint T x = starRingEnd F μ • x

def eigenspace_adjoint : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : Module.End F V),
    _root_.D05.normalOperator T → ∀ μ : F,
      T.eigenspace μ = Module.End.eigenspace (LinearMap.adjoint T) (starRingEnd F μ)

def eigenvectors_orthogonal : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : Module.End F V),
    _root_.D05.normalOperator T → ∀ (α β : F), α ≠ β →
      ∀ (x y : V), T x = α • x → T y = β • y →
        _root_.D05.firstInner (F := F) x y = 0

def eigenspaces_orthogonal : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V] (T : Module.End F V),
    _root_.D05.normalOperator T → ∀ (α β : F), α ≠ β →
      T.eigenspace α ≤ (T.eigenspace β).orthogonal

/-- A = (T + T†)/2 is self-adjoint for every complex T. -/
def real_part_selfAdjoint : Prop :=
  ∀ {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V),
    _root_.D05.selfAdjoint ((2 : ℂ)⁻¹ • (T + LinearMap.adjoint T))

/-- B = (T - T†)/(2i) is self-adjoint for every complex T. -/
def imag_part_selfAdjoint : Prop :=
  ∀ {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V),
    _root_.D05.selfAdjoint ((2 * Complex.I)⁻¹ • (T - LinearMap.adjoint T))

/-- The specified parts reconstruct T. -/
def complex_decomposition : Prop :=
  ∀ {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V),
    T = (2 : ℂ)⁻¹ • (T + LinearMap.adjoint T) +
      Complex.I • ((2 * Complex.I)⁻¹ • (T - LinearMap.adjoint T))

/-- The explicit commutator identity, before assuming normality. -/
def parts_commutator : Prop :=
  ∀ {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V),
    let A := (2 : ℂ)⁻¹ • (T + LinearMap.adjoint T)
    let B := (2 * Complex.I)⁻¹ • (T - LinearMap.adjoint T)
    A.comp B - B.comp A = (2 * Complex.I)⁻¹ •
      ((LinearMap.adjoint T).comp T - T.comp (LinearMap.adjoint T))

/-- Normality is exactly commutation of the specified self-adjoint parts. -/
def normal_iff_parts_commute : Prop :=
  ∀ {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T : V →ₗ[ℂ] V),
    let A := (2 : ℂ)⁻¹ • (T + LinearMap.adjoint T)
    let B := (2 * Complex.I)⁻¹ • (T - LinearMap.adjoint T)
    _root_.D05.normalOperator T ↔ A.comp B = B.comp A

/-- Every self-adjoint decomposition has the stated parts, uniquely. -/
def complex_parts_unique : Prop :=
  ∀ {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (T A B : V →ₗ[ℂ] V),
    _root_.D05.selfAdjoint A → _root_.D05.selfAdjoint B →
    T = A + Complex.I • B →
      A = (2 : ℂ)⁻¹ • (T + LinearMap.adjoint T) ∧
      B = (2 * Complex.I)⁻¹ • (T - LinearMap.adjoint T)

end Specs.D05.M13.NormalBasic
