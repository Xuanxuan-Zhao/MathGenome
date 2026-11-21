import MathGenome.Internal.Specs.D05.M15.SymmetricBasis
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-! Statements for paper.tex:3189–3190. Binary external sums are represented by
products of modules. All symmetric powers are the upstream adjacent-swap
quotients, including degree zero. Tensor multiplication is the ordinary one. -/
noncomputable section
namespace Specs.D05.M15.SymmetricDirectSum
open scoped TensorProduct
open Specs.D05.M15.Symmetric
open Specs.D05.M15.SymmetricBasis (powerInclusion)

variable (K V W : Type*) [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Symmetric functor applied to the first summand inclusion. -/
def leftMap : symmetricAlgebra K V →ₐ[K] symmetricAlgebra K (V × W) :=
  _root_.SymmetricAlgebra.lift
    ((_root_.SymmetricAlgebra.ι K (V × W)).comp (LinearMap.inl K V W))

/-- Symmetric functor applied to the second summand inclusion. -/
def rightMap : symmetricAlgebra K W →ₐ[K] symmetricAlgebra K (V × W) :=
  _root_.SymmetricAlgebra.lift
    ((_root_.SymmetricAlgebra.ι K (V × W)).comp (LinearMap.inr K V W))

def forward : symmetricAlgebra K (V × W) →ₐ[K]
    symmetricAlgebra K V ⊗[K] symmetricAlgebra K W :=
  _root_.SymmetricAlgebra.lift
    (((Algebra.TensorProduct.includeLeft.toLinearMap).comp
        (_root_.SymmetricAlgebra.ι K V)).coprod
      ((Algebra.TensorProduct.includeRight.toLinearMap).comp
        (_root_.SymmetricAlgebra.ι K W)))

def backward : (symmetricAlgebra K V ⊗[K] symmetricAlgebra K W) →ₐ[K]
    symmetricAlgebra K (V × W) :=
  Algebra.TensorProduct.lift (leftMap K V W) (rightMap K V W)
    (fun _ _ => Commute.all _ _)

/-- The ordered pairs of nonnegative degrees whose total is p. -/
abbrev DegreePairs (p : ℕ) := {ij : ℕ × ℕ // ij.1 + ij.2 = p}

/-- The actual direct sum of tensor products of upstream quotient powers. -/
abbrev DegreeSum (p : ℕ) := _root_.DirectSum (DegreePairs p)
  (fun ij => symmetricPower K V ij.val.1 ⊗[K] symmetricPower K W ij.val.2)

/-- Includes each bidegree by tensoring the two canonical power inclusions. -/
def degreeInclusion (p : ℕ) : DegreeSum K V W p →ₗ[K]
    symmetricAlgebra K V ⊗[K] symmetricAlgebra K W :=
  _root_.DirectSum.toModule K _ _ (fun ij =>
    TensorProduct.map (powerInclusion ij.val.1) (powerInclusion ij.val.2))

def forward_type := ∀ (K V W : Type*) [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W], symmetricAlgebra K (V × W) →ₐ[K]
    symmetricAlgebra K V ⊗[K] symmetricAlgebra K W

def forward_value : forward_type := forward

def backward_type := ∀ (K V W : Type*) [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W],
  (symmetricAlgebra K V ⊗[K] symmetricAlgebra K W) →ₐ[K] symmetricAlgebra K (V × W)

def backward_value : backward_type := backward

/-- Unsigned ordinary tensor multiplication and commutativity. -/
def tensor_multiplication : Prop := ∀ (K V W : Type*) [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  (a c : symmetricAlgebra K V) (b d : symmetricAlgebra K W),
  (a ⊗ₜ[K] b) * (c ⊗ₜ[K] d) = (a*c) ⊗ₜ[K] (b*d) ∧
  (a ⊗ₜ[K] b) * (c ⊗ₜ[K] d) = (c ⊗ₜ[K] d) * (a ⊗ₜ[K] b)

/-- Commutativity holds for arbitrary finite sums of pure tensors as well. -/
def tensor_commutative : Prop := ∀ (K V W : Type*) [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  (x y : symmetricAlgebra K V ⊗[K] symmetricAlgebra K W), x*y = y*x

def forward_generator : Prop := ∀ (K V W : Type*) [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] (v : V) (w : W),
  forward K V W (_root_.SymmetricAlgebra.ι K (V × W) (v,w)) =
    (_root_.SymmetricAlgebra.ι K V v) ⊗ₜ[K] 1 + 1 ⊗ₜ[K] (_root_.SymmetricAlgebra.ι K W w)

def backward_tmul : Prop := ∀ (K V W : Type*) [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  (a : symmetricAlgebra K V) (b : symmetricAlgebra K W),
  backward K V W (a ⊗ₜ[K] b) = leftMap K V W a * rightMap K V W b

/-- Both composites, and an equivalence with exactly these forward/inverse maps. -/
def algebra_equiv : Prop := ∀ (K V W : Type*) [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W],
  ∃ e : symmetricAlgebra K (V × W) ≃ₐ[K]
      symmetricAlgebra K V ⊗[K] symmetricAlgebra K W,
    e.toAlgHom = forward K V W ∧ e.symm.toAlgHom = backward K V W

/-- Restriction of the same algebra map in every degree. The equality specifies
its compatibility with the canonical inclusions, rather than an unrelated
abstract linear isomorphism. It also specifies the inverse by injectivity. -/
def degree_decomposition : Prop := ∀ (K V W : Type*) [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] (p : ℕ),
  Function.Injective (degreeInclusion K V W p) ∧
  ∃ e : symmetricPower K (V × W) p ≃ₗ[K] DegreeSum K V W p,
    ∀ q, degreeInclusion K V W p (e q) =
      forward K V W (powerInclusion (K := K) (V := V × W) p q)

end Specs.D05.M15.SymmetricDirectSum
