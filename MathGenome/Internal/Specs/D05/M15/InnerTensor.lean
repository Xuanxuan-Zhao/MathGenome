import MathGenome.Internal.Specs.D05.M12.InnerProduct
import MathGenome.Internal.Specs.D05.M12.OnBasis
import MathGenome.Internal.Specs.D05.M15.TensorBasis
import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
Independent statements for K05.15.inner_tensor, paper.tex:2852–2861.
The tensor product is algebraic. The shared `D05.firstInner` reverses Mathlib's
slots. `coordinateForm` is exactly the paper's finite coefficient formula;
no orthonormality or desired product rule is built into its definition.
`RCLike` handles the real and complex cases together. No completeness or
nonzero-dimension hypothesis is imposed. Several statements are proved for
arbitrary-dimensional factors, which includes the stated finite-dimensional case.
The later paragraph on general bilinear pairings is a separate obligation.
-/

noncomputable section
open scoped TensorProduct

namespace D05

/-- Pull back the finite-coordinate inner product through the product basis. -/
def tensorCoordinateInner {F V W I J : Type*} [RCLike F]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [Fintype I] [Fintype J] (e : Module.Basis I F V) (f : Module.Basis J F W)
    (z t : V ⊗[F] W) : F :=
  coordinateInner ((e.tensorProduct f).equivFun z) ((e.tensorProduct f).equivFun t)

end D05

namespace Specs.D05.M15.InnerTensor

/-- Type and defining value of the coordinate construction, independently of proofs. -/
def coordinateForm_type : Type _ :=
  {F V W I J : Type*} → [RCLike F] →
    [AddCommGroup V] → [Module F V] → [AddCommGroup W] → [Module F W] →
    [Fintype I] → [Fintype J] → Module.Basis I F V → Module.Basis J F W →
    (V ⊗[F] W) → (V ⊗[F] W) → F

def coordinateForm_value : coordinateForm_type :=
  fun {F} _ _ _ _ _ _ _ _ _ _ _ e f z t =>
    ∑ p : _ × _, (e.tensorProduct f).repr z p *
      starRingEnd F ((e.tensorProduct f).repr t p)

/-- Unique coordinates make the raw coordinate formula positive definite,
first-slot linear and conjugate symmetric, for any finite product basis. -/
def coordinate_axioms : Prop :=
  ∀ {F V W I J : Type*} [RCLike F]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [Fintype I] [Fintype J] (e : Module.Basis I F V) (f : Module.Basis J F W),
    _root_.D05.IsFirstInnerProduct (_root_.D05.tensorCoordinateInner e f)

/-- The displayed formula on arbitrary coefficient arrays, including empty arrays. -/
def coordinate_expansion : Prop :=
  ∀ {F V W I J : Type*} [RCLike F]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [Fintype I] [Fintype J] (e : Module.Basis I F V) (f : Module.Basis J F W)
    (c d : I × J → F),
    _root_.D05.tensorCoordinateInner e f
      (∑ p, c p • (e p.1 ⊗ₜ[F] f p.2))
      (∑ p, d p • (e p.1 ⊗ₜ[F] f p.2)) =
      ∑ p, c p * starRingEnd F (d p)

/-- The canonical tensor inner product obeys all four shared paper axioms. -/
def canonical_axioms : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W],
    _root_.D05.IsFirstInnerProduct
      (_root_.D05.firstInner (F := F) (V := V ⊗[F] W))

/-- The elementary-tensor product rule in the paper's slot convention. -/
def pure_tensor : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    (v v' : V) (w w' : W),
    _root_.D05.firstInner (v ⊗ₜ[F] w) (v' ⊗ₜ[F] w') =
      _root_.D05.firstInner (F := F) v v' * _root_.D05.firstInner (F := F) w w'

/-- Any two orthonormal bases give the canonical form on every tensor. -/
def coordinate_eq_canonical : Prop :=
  ∀ {F V W I J : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [Fintype I] [Fintype J] (e : Module.Basis I F V) (f : Module.Basis J F W),
    _root_.D05.orthonormalFamily (F := F) e →
    _root_.D05.orthonormalFamily (F := F) f →
    ∀ z t : V ⊗[F] W,
      _root_.D05.tensorCoordinateInner e f z t = _root_.D05.firstInner (F := F) z t

/-- Uniqueness needs only sesquilinearity and the product rule; conjugate
symmetry and positivity are conclusions of the construction, not extra premises. -/
def sesquilinear_unique : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    (h : (V ⊗[F] W) → (V ⊗[F] W) → F),
    (∀ (a b : F) (x y z : V ⊗[F] W),
      h (a • x + b • y) z = a * h x z + b * h y z) →
    (∀ (a b : F) (x y z : V ⊗[F] W),
      h x (a • y + b • z) = starRingEnd F a * h x y + starRingEnd F b * h x z) →
    (∀ (v v' : V) (w w' : W), h (v ⊗ₜ[F] w) (v' ⊗ₜ[F] w') =
      _root_.D05.firstInner (F := F) v v' * _root_.D05.firstInner (F := F) w w') →
    h = _root_.D05.firstInner (F := F)

/-- Existence and uniqueness on every finite-dimensional real or complex
pair of inner-product spaces, including zero factors. -/
def exists_unique : Prop :=
  ∀ {F V W : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [FiniteDimensional F V] [FiniteDimensional F W],
    ∃! h : (V ⊗[F] W) → (V ⊗[F] W) → F,
      _root_.D05.IsFirstInnerProduct h ∧
      ∀ (v v' : V) (w w' : W), h (v ⊗ₜ[F] w) (v' ⊗ₜ[F] w') =
        _root_.D05.firstInner (F := F) v v' * _root_.D05.firstInner (F := F) w w'

/-- Independence of both chosen bases, even when their index types differ. -/
def basis_independence : Prop :=
  ∀ {F V W I J I' J' : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
    (e : Module.Basis I F V) (f : Module.Basis J F W)
    (e' : Module.Basis I' F V) (f' : Module.Basis J' F W),
    _root_.D05.orthonormalFamily (F := F) e →
    _root_.D05.orthonormalFamily (F := F) f →
    _root_.D05.orthonormalFamily (F := F) e' →
    _root_.D05.orthonormalFamily (F := F) f' →
    _root_.D05.tensorCoordinateInner e f = _root_.D05.tensorCoordinateInner e' f'

/-- The actual elementary-tensor product basis of any two orthonormal bases
is orthonormal for the canonical product form. -/
def orthonormal_tensor_basis : Prop :=
  ∀ {F V W I J : Type*} [RCLike F]
    [NormedAddCommGroup V] [InnerProductSpace F V]
    [NormedAddCommGroup W] [InnerProductSpace F W]
    (e : Module.Basis I F V) (f : Module.Basis J F W),
    _root_.D05.orthonormalFamily (F := F) e →
    _root_.D05.orthonormalFamily (F := F) f →
    ∃ B : Module.Basis (I × J) F (V ⊗[F] W),
      (∀ p, B p = e p.1 ⊗ₜ[F] f p.2) ∧
      _root_.D05.orthonormalFamily (F := F) B

end Specs.D05.M15.InnerTensor
