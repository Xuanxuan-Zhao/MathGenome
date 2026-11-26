import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels
import Mathlib.RingTheory.MvPolynomial.Homogeneous

open CategoryTheory MulOpposite
open scoped TensorProduct Matrix

universe u v w

namespace LinearAlgebraicGroups.Specs.AnisotropicSymplecticInvolutionTensors

open SymplecticDivisionForms
open Arithmetic.SymplecticIsometryDescent (isometryPoints)

/-- Isotropy of an idempotent is for the original algebra involution. -/
def OrthogonalAdjointIdempotents : Prop :=
  ∀ {A : Type u} [Ring A] (σ : A ≃+* Aᵐᵒᵖ),
    let s (x : A) := unop (σ x)
    Function.Involutive s →
    ∀ z e : A, z + s z = 1 → e ≠ 0 → e * e = e → s e * e = 0 →
    ∃ p : A, p ≠ 0 ∧ p * p = p ∧ s p * p = 0 ∧ p * s p = 0

abbrev SplitCocharacter {k A : Type u} [Field k] [Ring A] [Algebra k A]
    (s : Arithmetic.SymplecticIsometryDescent.Involution k A) :=
  StandardGroups.multiplicativePoints k ⟶ isometryPoints s

/-- Split anisotropy is the absence of a rank-one split torus.
A closed embedding of the multiplicative group is tested by injection on
all commutative test algebras. -/
def IsAnisotropic {k A : Type u} [Field k] [Ring A] [Algebra k A]
    (s : Arithmetic.SymplecticIsometryDescent.Involution k A) : Prop :=
  ¬ ∃ c : SplitCocharacter s, ∀ R : TestAlgebra k, Function.Injective (c.app R)

/-- Orthogonal adjoint projectors defining a split multiplicative subgroup
on every test algebra. -/
def SplitTorusWitness {k A : Type u} [Field k] [Ring A] [Algebra k A]
    (s : Arithmetic.SymplecticIsometryDescent.Involution k A) : Prop :=
  ∃ (p : A) (c : SplitCocharacter s), p ≠ 0 ∧ p * p = p ∧
      s.toLinearMap p * p = 0 ∧ p * s.toLinearMap p = 0 ∧
      ∀ R : TestAlgebra k, Function.Injective (c.app R) ∧
        ∀ t : Rˣ,
          ((c.app R t).val : R ⊗[k] A) =
            (Units.val t ⊗ₜ[k] p) + (Units.val t⁻¹ ⊗ₜ[k] s.toLinearMap p) +
              ((1 : R) ⊗ₜ[k] (1 - p - s.toLinearMap p))

/-- Trace one and an isotropic idempotent produce a split multiplicative subgroup. -/
def IsotropicIdempotentSplitTorus : Prop :=
  ∀ {k A : Type u} [Field k] [Ring A] [Algebra k A]
    (s : Arithmetic.SymplecticIsometryDescent.Involution k A) (z e : A),
    z + s.toLinearMap z = 1 → e ≠ 0 → e * e = e → s.toLinearMap e * e = 0 →
      SplitTorusWitness s

/-- The symplectic splitting supplies trace one over the ground field. -/
def SymplecticIsotropicIdempotentSplitTorus : Prop :=
  ∀ {k A K : Type u} [Field k] [Ring A] [Algebra k A] [Field K] [Algebra k K]
    (s : Arithmetic.SymplecticIsometryDescent.Involution k A) {n : ℕ},
    SplitComparison (SymplecticInvolutionModels.DivisionForms.toDivisionInvolution s) K n →
    ∃ z : A, z + s.toLinearMap z = 1 ∧
      ∀ e : A, e ≠ 0 → e * e = e → s.toLinearMap e * e = 0 → SplitTorusWitness s

/-- The corner on a chosen primitive coordinate idempotent carries the
involution induced from the original algebra. -/
def InvolutoryDivisionCorner : Prop :=
  ∀ {k A D : Type u} [Field k] [Ring A] [Algebra k A] [DivisionRing D] [Algebra k D]
    (s : Involution k A) {r : ℕ} (_e : A ≃ₐ[k] Matrix (Fin r) (Fin r) D)
    (i : Fin r), (∀ p : A, p ≠ 0 → p * p = p → antiValue s.anti p * p ≠ 0) →
    ∃ (f : A ≃ₐ[k] Matrix (Fin r) (Fin r) D) (σ : Involution k D),
      ∀ a : D,
        f (antiValue s.anti (f.symm (Matrix.single i i a))) =
          Matrix.single i i (antiValue σ.anti a)

/-- A presentation of the original involution on a matrix algebra over its
ground-field division corner. The corner normalization permits a Hermitian
Gram matrix. -/
structure HermitianModel {k A D : Type u} [Field k] [Ring A] [Algebra k A]
    [DivisionRing D] [Algebra k D] (s : Involution k A) (r : ℕ) where
  cornerIndex : Fin r
  equiv : A ≃ₐ[k] Matrix (Fin r) (Fin r) D
  involution : Involution k D
  gram : (Matrix (Fin r) (Fin r) D)ˣ
  corner (a : D) :
    equiv (antiValue s.anti (equiv.symm (Matrix.single cornerIndex cornerIndex a))) =
      Matrix.single cornerIndex cornerIndex (antiValue involution.anti a)
  hermitian : dagger involution.anti gram.val = gram.val
  adjoint (a : A) :
    equiv (antiValue s.anti a) = gram.inv * dagger involution.anti (equiv a) * gram.val
  formLaws : HermitianLaws involution.anti (hermitianValue involution.anti gram.val)
  nondegenerate (x : Fin r → D) :
    x ≠ 0 → ∃ y, hermitianValue involution.anti gram.val x y ≠ 0
  anisotropic (x : Fin r → D) : x ≠ 0 → hermitianValue involution.anti gram.val x x ≠ 0

/-- The existence of the global division-corner model uses the symplectic
splitting and split anisotropy over the ground field. -/
def GlobalHermitianModel : Prop :=
  ∀ {k A K : Type u} [Field k] [Ring A] [Algebra k A] [Field K] [Algebra k K]
    (_hA : _root_.Specs.RM03.CSA.isCentralSimple k A)
    (s : Arithmetic.SymplecticIsometryDescent.Involution k A) {n : ℕ},
    let t := SymplecticInvolutionModels.DivisionForms.toDivisionInvolution s
    SplitComparison t K n → IsAnisotropic s →
    ∃ (r : ℕ) (D : Type u) (_ : DivisionRing D) (_ : Algebra k D),
      _root_.Specs.RM03.CSA.isCentralDivision k D ∧ Nonempty (HermitianModel t r (D := D))

/-- The Hermitian description uses the extension of the original algebra
and form, and is compatible with maps of coefficient algebras. -/
def HermitianModelBaseChange : Prop :=
  ∀ {k A D : Type u} [Field k] [Ring A] [Algebra k A] [DivisionRing D] [Algebra k D]
    {s : Involution k A} {r : ℕ} (m : HermitianModel s r (D := D)),
    ∃ E : ∀ (R : Type u) [CommRing R] [Algebra k R],
        (R ⊗[k] A) ≃ₐ[R] Matrix (Fin r) (Fin r) (R ⊗[k] D),
      (∀ (R : Type u) [CommRing R] [Algebra k R] (a : A),
        E R (1 ⊗ₜ[k] a) = (m.equiv a).map (intoTensor R D)) ∧
      (∀ (R : Type u) [CommRing R] [Algebra k R],
        HermitianLaws (extendAnti m.involution.anti R)
          (hermitianValue (extendAnti m.involution.anti R) (m.gram.val.map (intoTensor R D)))) ∧
      (∀ (R : Type u) [CommRing R] [Algebra k R] (g : (R ⊗[k] A)ˣ),
        antiValue (extendAnti s.anti R) g.val * g.val = 1 ↔
          let h := hermitianValue (extendAnti m.involution.anti R) (m.gram.val.map (intoTensor R D))
          ∀ x y, h (E R g.val *ᵥ x) (E R g.val *ᵥ y) = h x y) ∧
      ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
        (f : R →ₐ[k] S) (x : R ⊗[k] A), E S (tensorMap A f x) = (E R x).map (tensorMap D f)

/-- The actual scalar extension of matrix multiplication on the right module,
viewed as a linear map over the test algebra. -/
def columnAction {C R I : Type*} [Ring C] [CommRing R] [Algebra R C]
    [Fintype I] (g : Matrix I I C) : (I → C) →ₗ[R] (I → C) where
  toFun x := g *ᵥ x
  map_add' := Matrix.mulVec_add g
  map_smul' a x := Matrix.mulVec_smul g a x

/-- The determinant on the full coefficient-extended right module is one
for isometries of the original symplectic involution. -/
def SymplecticColumnDeterminant : Prop :=
  ∀ {k A D K : Type u} [Field k] [Ring A] [Algebra k A] [DivisionRing D] [Algebra k D]
    [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (_hD : _root_.Specs.RM03.CSA.isCentralDivision k D)
    (s : Arithmetic.SymplecticIsometryDescent.Involution k A) {n r : ℕ},
    SplitComparison (SymplecticInvolutionModels.DivisionForms.toDivisionInvolution s) K n →
    ∀ (R : Type u) [Field R] [Algebra k R]
      (e : (R ⊗[k] A) ≃ₐ[R] Matrix (Fin r) (Fin r) (R ⊗[k] D))
      (g : (s.baseChange R).isometries),
      LinearMap.det (columnAction (R := R) (e g.val.val)) = 1

/-- The coordinate diagonal family in a ground-field basis, and the
simultaneous stabilizer of right multiplications and the full form. -/
def DiagonalCoordinatesAndStabilizer : Prop :=
  ∀ {k D : Type u} {I : Type v} {J : Type w} [Field k] [DivisionRing D] [Algebra k D]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (σ : Involution k D) (H : (Matrix I I D)ˣ) (b : Module.Basis J k D),
    (∀ x : I → D, x ≠ 0 → hermitianValue σ.anti H.val x x ≠ 0) →
    ∃ P : J → MvPolynomial (I × J) k,
      (∀ j, (P j).IsHomogeneous 2) ∧
      (∀ x : I × J → k, x ≠ 0 → ∃ j, (P j).eval x ≠ 0) ∧
      ∀ (R : Type u) [Field R] [Algebra k R],
        let bR := b.baseChange R
        let h := hermitianValue (extendAnti σ.anti R) (H.val.map (intoTensor R D))
        let coords (x : I → R ⊗[k] D) (ij : I × J) := bR.repr (x ij.1) ij.2
        (∀ x j, (P j).eval₂ (algebraMap k R) (coords x) = bR.repr (h x x) j) ∧
        ∀ f : (I → R ⊗[k] D) ≃ₗ[R] (I → R ⊗[k] D),
          ((∀ j x, f (fun i => x i * bR j) = fun i => f x i * bR j) ∧
            (∀ x y, h (f x) (f y) = h x y)) ↔
          ∃ g : (Matrix I I (R ⊗[k] D))ˣ,
            (∀ x, f x = g.val *ᵥ x) ∧
              (∀ x y, h (g.val *ᵥ x) (g.val *ᵥ y) = h x y)

/-- In a basis of the global division algebra the coordinates of the anisotropic
diagonal are quadratic invariants. For each coefficient field, in particular
each completion, the original involution group is exactly the stabilizer
of the right multiplications and the full coefficient-extended form. -/
def SymplecticTensorModel : Prop :=
  ∀ {k A D K J : Type u} [Field k] [Ring A] [Algebra k A] [DivisionRing D] [Algebra k D]
    [Field K] [Algebra k K] [Algebra.IsAlgebraic k K] [Fintype J] [DecidableEq J]
    (_hD : _root_.Specs.RM03.CSA.isCentralDivision k D)
    (s : Arithmetic.SymplecticIsometryDescent.Involution k A) {n r : ℕ},
    let t := SymplecticInvolutionModels.DivisionForms.toDivisionInvolution s
    SplitComparison t K n → (m : HermitianModel t r (D := D)) → (b : Module.Basis J k D) →
    ∃ (P : J → MvPolynomial (Fin r × J) k)
      (E : ∀ (R : Type u) [CommRing R] [Algebra k R],
        (R ⊗[k] A) ≃ₐ[R] Matrix (Fin r) (Fin r) (R ⊗[k] D)),
      (∀ j, (P j).IsHomogeneous 2) ∧
      (∀ x : Fin r × J → k, x ≠ 0 → ∃ j, (P j).eval x ≠ 0) ∧
      (∀ (R : Type u) [CommRing R] [Algebra k R] (a : A),
        E R (1 ⊗ₜ[k] a) = (m.equiv a).map (intoTensor R D)) ∧
      (∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
        (f : R →ₐ[k] S) (x : R ⊗[k] A),
          E S (tensorMap A f x) = (E R x).map (tensorMap D f)) ∧
      ∀ (R : Type u) [Field R] [Algebra k R],
        let bR := b.baseChange R
        let h := hermitianValue (extendAnti m.involution.anti R) (m.gram.val.map (intoTensor R D))
        let coords (x : Fin r → R ⊗[k] D) (ij : Fin r × J) := bR.repr (x ij.1) ij.2
        (∀ x j, (P j).eval₂ (algebraMap k R) (coords x) = bR.repr (h x x) j) ∧
        (∀ g : (s.baseChange R).isometries,
          let M := E R g.val.val
          LinearMap.det (columnAction (R := R) M) = 1 ∧
            ∀ x j, (P j).eval₂ (algebraMap k R) (coords (M *ᵥ x)) =
              (P j).eval₂ (algebraMap k R) (coords x)) ∧
        ∀ f : (Fin r → R ⊗[k] D) ≃ₗ[R] (Fin r → R ⊗[k] D),
          ((∀ j x, f (fun i => x i * bR j) = fun i => f x i * bR j) ∧
            (∀ x y, h (f x) (f y) = h x y)) ↔
          ∃ g : (s.baseChange R).isometries, ∀ x, f x = E R g.val.val *ᵥ x


end LinearAlgebraicGroups.Specs.AnisotropicSymplecticInvolutionTensors
