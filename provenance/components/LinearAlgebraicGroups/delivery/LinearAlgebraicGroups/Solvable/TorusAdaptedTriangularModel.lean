import Specs.LinearAlgebraicGroups.Solvable.TorusAdaptedTriangularModel
import LinearAlgebraicGroups.Solvable.SplitSolvableRadical
import Specs.LinearAlgebraicGroups.Solvable.Triangularization
import LinearAlgebraicGroups.Multiplicative.WeightDecomposition
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory WithConv
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.TorusAdaptedTriangularModel

noncomputable section

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme)
open Specs.SmoothDiagonalKernel Specs.TorusAdaptedTriangularModel
open Specs.Unipotent (Index closedSubgroupAlgebraicGroup)
open Specs.DiagonalizableGroups (groupAlgebra)
open Specs.StandardGroups (generalLinearPoints multiplicativePowerPoints)
open RationalRepresentations WeightDecomposition

open private tensorCoefficients weightProjection projection_mem sum_projections
  from LinearAlgebraicGroups.Multiplicative.WeightDecomposition
open private tensorCoordinate_tmul pointMatrix pointMatrix_evaluation representationPointsEquiv
  from LinearAlgebraicGroups.Affine.RationalRepresentations
open private exponentsEquiv from LinearAlgebraicGroups.Affine.StandardGroups
open private conjugateMatrixPoints from LinearAlgebraicGroups.Solvable.SplitSolvableRadical

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

private abbrev Exponents (r : ℕ) := Multiplicative (Index.{u} r → ℤ)

private def torusCoordinates (r : ℕ) :
    convolutionPoints (groupAlgebra k (Exponents r)) ≅ multiplicativePowerPoints k (Index.{u} r) :=
  DiagonalizableGroups.convolutionCharacterIso (Exponents r) ≪≫
    NatIso.ofComponents (fun R ↦ (exponentsEquiv (ι := Index.{u} r) R).toGrpIso) (by
      intro R S f
      apply GrpCat.ext
      intro a
      rfl)

private theorem evalMonomial {r : ℕ} (R : TestAlgebra k)
    (g : groupAlgebra k (Exponents r) →ₐ[k] R) (m : Exponents.{u} r) :
    g (MonoidAlgebra.of k _ m) =
      (characterValue m.toAdd ((torusCoordinates r).hom.app R (toConv g)) : R) := by
  let χ : Exponents.{u} r →* Rˣ :=
    (DiagonalizableGroups.convolutionCharacterIso (Exponents r)).hom.app R (toConv g)
  change (χ m : R) =
    (((exponentsEquiv (ι := Index.{u} r) R).symm
      (exponentsEquiv (ι := Index.{u} r) R χ)) m : R)
  rw [MulEquiv.symm_apply_apply]

private theorem tensorCoefficients_tmul_apply {M V : Type u} [CommGroup M] [DecidableEq M]
    [AddCommGroup V] [Module k V] (v : V) (a : MonoidAlgebra k M) (m : M) :
    tensorCoefficients (v ⊗ₜ[k] a) m = a.coeff m • v := by
  simp [tensorCoefficients, TensorProduct.finsuppScalarRight_apply_tmul_apply]

/-- A weight component of each standard basis vector can be chosen with
nonzero coordinate in that position and with every later coordinate zero. -/
private theorem adaptedEigenvectors {n : ℕ} {M : Type u} [CommGroup M]
    (ρ : RightComodule k (groupAlgebra k M) (Index.{u} n → k))
    (h : (coefficients (groupAlgebra k M) (Pi.basisFun k (Index.{u} n)) ρ).IsUpperTriangular) :
    ∃ (P : Matrix (Index.{u} n) (Index.{u} n) k) (m : Index.{u} n → M),
      P.IsUpperTriangular ∧ (∀ j, P j j ≠ 0) ∧
        ∀ j, ρ.coaction (fun i ↦ P i j) = (fun i ↦ P i j) ⊗ₜ[k] MonoidAlgebra.of k M (m j) := by
  classical
  let A := groupAlgebra k M
  let b := Pi.basisFun k (Index.{u} n)
  have select (j : Index.{u} n) : ∃ m, weightProjection ρ m (b j) j ≠ 0 := by
    obtain ⟨s, hs⟩ := sum_projections ρ (b j)
    by_contra! hz
    have hj := congrFun hs j
    simp only [Finset.sum_apply, hz, Finset.sum_const_zero] at hj
    exact zero_ne_one (hj.trans (by simp [b]))
  choose m hm using select
  refine ⟨fun i j ↦ weightProjection ρ (m j) (b j) i, m, ?_, hm, ?_⟩
  · intro i j hij
    change tensorCoefficients (ρ.coaction (b j)) (m j) i = 0
    rw [coaction_apply_basis A b ρ]
    simp only [map_sum, Finsupp.finsetSum_apply, Finset.sum_apply]
    rw [Finset.sum_eq_single i]
    · have hi : coefficients A b ρ i j = 0 := h hij
      simp [hi]
    · intro l _ hl
      rw [tensorCoefficients_tmul_apply (M := M) (b l) (coefficients A b ρ l j), Pi.smul_apply]
      simp [b, Pi.single_eq_of_ne hl.symm]
    · simp
  · intro j
    exact mem_weightSpace.mp (projection_mem ρ (m j) (b j))

private theorem eigenmatrix {n : ℕ} {M : Type u} [CommGroup M]
    (ρ : RightComodule k (groupAlgebra k M) (Index.{u} n → k))
    (P : Matrix (Index.{u} n) (Index.{u} n) k) (m : Index.{u} n → M)
    (h : ∀ j, ρ.coaction (fun i ↦ P i j) = (fun i ↦ P i j) ⊗ₜ[k] MonoidAlgebra.of k M (m j)) :
    let A := groupAlgebra k M
    let Q := (algebraMap k A).mapMatrix P
    coefficients A (Pi.basisFun k (Index.{u} n)) ρ * Q =
      Q * Matrix.diagonal (fun j ↦ MonoidAlgebra.of k M (m j)) := by
  classical
  dsimp only
  let A := groupAlgebra k M
  let b := Pi.basisFun k (Index.{u} n)
  apply Matrix.ext
  intro i j
  let v : Index.{u} n → k := fun l ↦ P l j
  have hv := congrArg (tensorCoordinate b i) (h j)
  change tensorCoordinate b i (ρ.coaction v) = tensorCoordinate b i (v ⊗ₜ[k] _) at hv
  conv_lhs at hv => rw [← b.sum_repr v]
  simp only [map_sum, map_smul, tensorCoordinate_tmul] at hv
  change (∑ l, b.repr v l • coefficients A b ρ i l) = b.coord i v • _ at hv
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  change (∑ l, coefficients A b ρ i l * algebraMap k A (P l j)) =
    algebraMap k A (P i j) * MonoidAlgebra.of k M (m j)
  simpa only [Algebra.smul_def, Module.Basis.coord_apply, Pi.basisFun_repr, v, b, mul_comm]
    using hv

theorem existsTorusAdaptedTriangularModel : HasTorusAdaptedTriangularModel.{u} := by
  classical
  intro k _ G T hG hT
  obtain ⟨n, H, j, e, hj, htri⟩ := SplitSolvableRadical.faithfulTriangularization G hG
  obtain ⟨r, ⟨t⟩⟩ := hT
  let A := groupAlgebra k (Exponents r)
  let D : AffineGroupCategory k := ⟨T.group, (closedSubgroupAlgebraicGroup T).property.1⟩
  let s : convolutionPoints A ≅ (groupPointsFunctor k).obj D.val :=
    torusCoordinates r ≪≫ t.symm
  let f : D.val ⟶ H.val := T.inclusion ≫ j
  let b := Pi.basisFun k (Index.{u} n)
  obtain ⟨E, hE⟩ := representationCoactionComparison A b D H.val s e
  let ρ := E f
  have hcoeff : coefficients A b ρ = universalMatrix A D H.val s e f := hE f
  have htriT (R : TestAlgebra k) (a : ((groupPointsFunctor k).obj T.group).obj R) :
      (matrixPoint f e R a).val.IsUpperTriangular := by
    change ((e.hom.app R) (((groupPointsFunctor k).map (T.inclusion ≫ j)).app R a)).val.IsUpperTriangular
    rw [Functor.map_comp, NatTrans.comp_app, GrpCat.comp_apply]
    exact htri R (((groupPointsFunctor k).map T.inclusion).app R a)
  obtain ⟨P, m, hP, hp, heig⟩ := adaptedEigenvectors ρ (by
    rw [hcoeff]
    exact htriT _ _)
  let p : Matrix.GeneralLinearGroup (Index.{u} n) k :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero P
      (by rw [Matrix.det_of_isUpperTriangular hP]; exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ hp i)
  let e' := e ≪≫ conjugateMatrixPoints p
  let liftP (R : TestAlgebra k) : Matrix.GeneralLinearGroup (Index.{u} n) R :=
    Matrix.GeneralLinearGroup.map (algebraMap k R) p
  have hLift (R : TestAlgebra k) :
      (liftP R).val = (algebraMap k R).mapMatrix P := rfl
  have hchange {L : GroupScheme k} (q : L ⟶ H.val) (R : TestAlgebra k)
      (x : ((groupPointsFunctor k).obj L).obj R) :
      matrixPoint q e' R x = (liftP R)⁻¹ * matrixPoint q e R x * liftP R := rfl
  refine ⟨n, r, H, j, e', t, fun i ↦ (m i).toAdd, hj, ?_, ?_⟩
  · intro R x
    let B := Specs.Triangularization.upperTriangular (Index.{u} n) R
    have hpR : liftP R ∈ B := by
      change (liftP R).val.IsUpperTriangular
      rw [hLift]
      intro i l hil
      change algebraMap k R (P i l) = 0
      rw [hP hil, map_zero]
    rw [hchange]
    exact B.mul_mem (B.mul_mem (B.inv_mem hpR) (htri R x)) hpR
  · intro R a i l
    let g : A →ₐ[k] R := (s.inv.app R a : (convolutionPoints A).obj R).ofConv
    have hg : s.hom.app R (toConv g) = a :=
      DFunLike.congr_fun (congrArg GrpCat.Hom.hom (s.inv_hom_id_app R)) a
    let α := representationPointsEquiv A D H.val s e f
    have hmat : (matrixPoint f e R a).val = g.mapMatrix (coefficients A b ρ) := by
      rw [hcoeff, ← hg]
      exact pointMatrix_evaluation A α R (toConv g)
    have hmon : ∀ j, g (MonoidAlgebra.of k _ (m j)) =
        (characterValue (m j).toAdd (t.hom.app R a) : R) := by
      intro j
      have hc : (torusCoordinates r).hom.app R (toConv g) = t.hom.app R a := by
        have he := congrArg (t.hom.app R) hg
        change t.hom.app R (t.inv.app R ((torusCoordinates r).hom.app R (toConv g))) = _ at he
        simpa using he
      rw [evalMonomial, hc]
    let C := Matrix.diagonal (fun j ↦ g (MonoidAlgebra.of k _ (m j)))
    have heq : (matrixPoint f e R a).val * (liftP R).val = (liftP R).val * C := by
      have h := congrArg (g.toRingHom.mapMatrix) (eigenmatrix ρ P m heig)
      rw [hmat, hLift]
      change (coefficients A b ρ * (algebraMap k A).mapMatrix P).map g =
        ((algebraMap k A).mapMatrix P * Matrix.diagonal (fun j ↦ MonoidAlgebra.of k _ (m j))).map g at h
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero g)] at h
      have hbase : ((algebraMap k A).mapMatrix P).map g = (algebraMap k R).mapMatrix P := by
        apply Matrix.ext
        intro i j
        exact g.commutes (P i j)
      rw [hbase] at h
      exact h
    have hdiag : (matrixPoint f e' R a).val = C := by
      rw [hchange]
      change ((liftP R)⁻¹).val * (matrixPoint f e R a).val * (liftP R).val = C
      rw [mul_assoc, heq, ← mul_assoc, Units.inv_mul, one_mul]
    change (matrixPoint f e' R a).val i l = _
    rw [hdiag]
    change Matrix.diagonal (fun j ↦ g (MonoidAlgebra.of k _ (m j))) i l = _
    rw [Matrix.diagonal_apply]
    split_ifs with hil
    · subst l
      exact hmon i
    · rfl

end
end LinearAlgebraicGroups.TorusAdaptedTriangularModel
