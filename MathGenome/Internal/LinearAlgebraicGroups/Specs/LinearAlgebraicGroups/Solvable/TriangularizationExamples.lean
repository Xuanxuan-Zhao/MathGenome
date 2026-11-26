import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.NormOneTorus
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.RelativeFrobenius
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Unipotent.Criteria
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
import Mathlib.Algebra.Algebra.Pi

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite WithConv Coalgebra
open Algebra.TensorProduct
open scoped TensorProduct DualNumber Matrix

universe u

namespace LinearAlgebraicGroups.Specs.TriangularizationExamples

noncomputable section

/-- The real multiplication action, with stability tested on real points. -/
def RealMultiplicationBoundary {W H L : AffineAlgebraicGroup ℝ}
    {e : (groupPointsFunctor ℝ).obj W.val ≅ WeilRestriction.extendedUnits ℝ ℂ}
    {n : W.val ⟶ H.val} (T : NormOneTorus.KernelModel e n)
    (g : (groupPointsFunctor ℝ).obj L.val ≅ StandardGroups.generalLinearPoints ℝ (Fin 2)) : Prop :=
    ∃ ρ : specGroup T.coordinate ⟶ L.val,
      (∀ (R : TestAlgebra ℝ) (f : WithConv (T.coordinate →ₐ[ℝ] R)),
        let v := NormOneTorus.complexCoordinates R (T.points R f).val.val
        (g.hom.app R (((groupPointsFunctor ℝ).map ρ).app R
          ((testSpec ℝ).map (CommAlgCat.ofHom f.ofConv).op)) :
          Matrix.GeneralLinearGroup (Fin 2) R).val = !![v 0, -v 1; v 1, v 0]) ∧
      let R := CommAlgCat.of ℝ ℝ
      let action (f : WithConv (T.coordinate →ₐ[ℝ] R)) :=
        (g.hom.app R (((groupPointsFunctor ℝ).map ρ).app R
          ((testSpec ℝ).map (CommAlgCat.ofHom f.ofConv).op)) :
          Matrix.GeneralLinearGroup (Fin 2) R).val
      (∃ f, action f = !![0, -1; 1, 0]) ∧
      ∀ P : Submodule ℝ (Fin 2 → ℝ), Module.finrank ℝ P = 1 →
        ¬ ∀ x ∈ P, ∀ f, action f *ᵥ x ∈ P

/-- The determinant norm-one torus over the reals has a two-dimensional
rational representation with no invariant real line. -/
def RealNormOneBoundary : Prop :=
  ∃ (W H L : AffineAlgebraicGroup ℝ)
    (e : (groupPointsFunctor ℝ).obj W.val ≅ WeilRestriction.extendedUnits ℝ ℂ)
    (t : (groupPointsFunctor ℝ).obj H.val ≅ StandardGroups.multiplicativePoints ℝ)
    (n : W.val ⟶ H.val) (T : NormOneTorus.KernelModel e n)
    (g : (groupPointsFunctor ℝ).obj L.val ≅ StandardGroups.generalLinearPoints ℝ (Fin 2)),
    NormOneTorus.RealizesNorm e t n ∧ CharacterDescent.IsTorus T.coordinate ∧
      RealMultiplicationBoundary T g

/-- The lengths and point counts of the two Frobenius kernels, including over
the algebraic closure. -/
def InfinitesimalSizes : Prop :=
  RelativeFrobenius.KernelLengths.{u} ∧ RelativeFrobenius.KernelFieldPoints.{u}

/-- The multiplicative Frobenius kernel and its tautological character. The coordinates
of the ambient multiplicative group are normalized by its usual group-like parameter. -/
def MultiplicativeKernelBoundary : Prop :=
  ∀ (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p],
    ∃ (M : HopfAlgebraCategory k) (e : M ≃ₐ[k] LaurentPolynomial k)
      (F : RelativeFrobenius.twistCoordinates k p M ⟶ M)
      (h : (kernelIdeal F).IsHopfIdeal k),
      letI := h
      let I := kernelIdeal F
      let Q := hopfQuotient M I
      let t := e.symm (LaurentPolynomial.T 1)
      let i := hopfQuotientMap M I
      RelativeFrobenius.PullbackFormula k p M F ∧
      Coalgebra.comul (R := k) t = t ⊗ₜ[k] t ∧
      Coalgebra.counit (R := k) t = 1 ∧
      IsPullback (specGroupMap i) (specGroupMap (hopfUnit Q))
        (specGroupMap F) (specGroupMap (hopfCounit _)) ∧
      (∃ j : Q ≃ₐ[k] RelativeFrobenius.MuCoordinates k p,
        j (i.hom t) = RelativeFrobenius.muCoordinate k p) ∧
      ∃ finite : Algebra.FiniteType k Q,
        let U := (finiteTypeHopfSpec k).obj (op ⟨Q, finite⟩)
        (∃ f : Q →ₐ[k] k[ε], ((f.comp i.hom.toAlgHom) t = (1 : k[ε]) + (ε : k[ε])) ∧
          (f.comp i.hom.toAlgHom) t ≠ 1) ∧
        ¬ Unipotent.IsUnipotent U

abbrev S₃ := Equiv.Perm (Fin 3)
abbrev SumZeroPlane := LinearMap.ker (∑ i : Fin 3, (LinearMap.proj i : (Fin 3 → ℂ) →ₗ[ℂ] ℂ))

/-- The evaluation maps at a pair of points of a finite constant scheme. -/
def pairEvaluation (k : Type*) [Field k] {G H : Type*} (g : G) (h : H) :
    ((G → k) ⊗[k] (H → k)) →ₐ[k] k :=
  Algebra.TensorProduct.lift (Pi.evalAlgHom k (fun _ : G ↦ k) g)
    (Pi.evalAlgHom k (fun _ : H ↦ k) h) (fun _ _ ↦ Commute.all _ _)

/-- The coaction restricts the permutation action to the plane and is simple. -/
def SimplePermutationComodule (A : HopfAlgebraCategory ℂ) (ev : S₃ → A →ₐ[ℂ] ℂ) : Prop :=
  ∃ ρ : RightComodule ℂ A SumZeroPlane,
    (∀ (g : S₃) (x : SumZeroPlane) (i : Fin 3),
      ((TensorProduct.rid ℂ SumZeroPlane)
        (RationalRepresentations.evaluate A ρ (ev g) x)).val i = x.val (g⁻¹ i)) ∧
    ∀ P : Submodule ℂ SumZeroPlane, ρ.IsSubcomodule P → P = ⊥ ∨ P = ⊤

/-- The constant scheme on the permutations of three letters is disconnected and
solvable. Its rational permutation action restricts to a simple sum-zero plane. -/
def SymmetricGroupBoundary : Prop :=
  ∃ operations : StandardGroups.HopfOperations ℂ (S₃ → ℂ),
    letI := operations.hopf
    let A := CommHopfAlgCat.of ℂ (S₃ → ℂ)
    (∀ (f : S₃ → ℂ) (g h : S₃), pairEvaluation ℂ g h (operations.delta f) = f (g * h)) ∧
    (∀ f : S₃ → ℂ, operations.epsilon f = f 1) ∧
    (∀ (f : S₃ → ℂ) (g : S₃), operations.inverse f g = f g⁻¹) ∧
    Module.finrank ℂ (S₃ → ℂ) = 6 ∧
    ¬ ConnectedSpace (specGroup A).X.left ∧
    SchemeDerivedGroup.IsSolvable (specGroup A) ∧
    Module.finrank ℂ SumZeroPlane = 2 ∧
    SimplePermutationComodule A (Pi.evalAlgHom ℂ (fun _ : S₃ ↦ ℂ))

end

end LinearAlgebraicGroups.Specs.TriangularizationExamples
