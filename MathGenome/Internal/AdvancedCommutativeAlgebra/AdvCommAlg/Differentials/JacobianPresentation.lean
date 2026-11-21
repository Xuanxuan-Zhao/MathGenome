import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Polynomial
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Conormal
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.JacobianPresentation
import Mathlib.Algebra.Module.Presentation.Differentials
import Mathlib.LinearAlgebra.Isomorphisms

namespace AdvCommAlg.Differentials

universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Specs.AdvCommAlg.Differentials

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  {n m : ℕ} (P : Algebra.Presentation A B (Fin n) (Fin m))

/-- Coordinates of the library's differential relations are the displayed
partial derivatives, reduced by the specified presentation map. -/
theorem differential_relation_coordinate (j : Fin m) (i : Fin n) :
    P.differentialsRelations.relation j i = presentationJacobian P i j := by
  change algebraMap P.Ring B
    ((KaehlerDifferential.mvPolynomialBasis A (Fin n)).repr
      (KaehlerDifferential.D A (MvPolynomial (Fin n) A) (P.relation j)) i) = _
  rw [KaehlerDifferential.mvPolynomialBasis_repr_apply]
  exact P.algebraMap_apply _

/-- Convert the library's finitely supported relation map into finite powers. -/
theorem jacobian_relation_map_eq :
    jacobianRelationMap P =
      (Finsupp.linearEquivFunOnFinite B B (Fin n)).toLinearMap.comp
        (P.differentialsRelations.map.comp
          (Finsupp.linearEquivFunOnFinite B B (Fin m)).symm.toLinearMap) := by
  apply (Pi.basisFun B (Fin m)).ext
  intro j
  rw [Pi.basisFun_apply]
  change (presentationJacobian P).mulVecLin (Pi.single j 1) =
    (Finsupp.linearEquivFunOnFinite B B (Fin n))
      (P.differentialsRelations.map
        ((Finsupp.linearEquivFunOnFinite B B (Fin m)).symm (Pi.single j 1)))
  rw [Finsupp.linearEquivFunOnFinite_symm_single, Module.Relations.map_single,
    Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  ext i
  exact (differential_relation_coordinate P j i).symm

theorem jacobian_differential_map_eq :
    jacobianDifferentialMap P = P.differentialsSolution.π.comp
      (Finsupp.linearEquivFunOnFinite B B (Fin n)).symm.toLinearMap := by
  apply (Pi.basisFun B (Fin n)).ext
  intro i
  rw [Pi.basisFun_apply]
  change ((Pi.basisFun B (Fin n)).constr B
      (fun i => KaehlerDifferential.D A B (P.val i))) (Pi.single i 1) =
    P.differentialsSolution.π
      ((Finsupp.linearEquivFunOnFinite B B (Fin n)).symm (Pi.single i 1))
  rw [Finsupp.linearEquivFunOnFinite_symm_single, Module.Relations.Solution.π_single]
  dsimp only [Algebra.Presentation.differentialsSolution]
  simpa only [Pi.basisFun_apply] using
    (Pi.basisFun B (Fin n)).constr_basis B
      (fun i => KaehlerDifferential.D A B (P.val i)) i

theorem jacobian_columns : jacobianColumns.{u,v} := by
  intro A B _ _ _ n m P j
  rw [jacobianRelationMap, Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  ext i
  simp [Finset.sum_apply, Pi.single_apply, presentationJacobian]

theorem jacobian_variables : jacobianVariables.{u,v} := by
  intro A B _ _ _ n m P i
  change ((Pi.basisFun B (Fin n)).constr B
    (fun i => KaehlerDifferential.D A B (P.val i))) (Pi.single i 1) = _
  rw [← Pi.basisFun_apply B (Fin n) i, Module.Basis.constr_basis]

theorem jacobian_exact : jacobianExact.{u,v} := by
  intro A B _ _ _ n m P
  let en := Finsupp.linearEquivFunOnFinite B B (Fin n)
  let em := Finsupp.linearEquivFunOnFinite B B (Fin m)
  have h := P.differentialsSolution_isPresentation
  rw [jacobian_relation_map_eq, jacobian_differential_map_eq]
  constructor
  · intro x
    change P.differentialsSolution.π (en.symm x) = 0 ↔
      ∃ y, en (P.differentialsRelations.map (em.symm y)) = x
    rw [h.exact (en.symm x)]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨em y, by rw [em.symm_apply_apply, hy, en.apply_symm_apply]⟩
    · rintro ⟨y, hy⟩
      exact ⟨em.symm y, en.injective (by simpa only [LinearEquiv.apply_symm_apply] using hy)⟩
  · exact h.surjective_π.comp en.symm.surjective

theorem jacobian_cokernel : jacobianCokernel.{u,v} := by
  intro A B _ _ _ n m P
  obtain ⟨he, hs⟩ := jacobian_exact A B n m P
  have hk : LinearMap.range (jacobianRelationMap P) =
      LinearMap.ker (jacobianDifferentialMap P) := (LinearMap.exact_iff.mp he).symm
  let e := (Submodule.quotEquivOfEq _ _ hk).trans
    ((jacobianDifferentialMap P).quotKerEquivOfSurjective hs)
  have hx (x : Fin n → B) : e ((LinearMap.range (jacobianRelationMap P)).mkQ x) =
      jacobianDifferentialMap P x := by
    simp [e, Submodule.quotEquivOfEq_mk, Submodule.mkQ_apply]
  exact ⟨e, hx, fun i => (hx _).trans (jacobian_variables A B n m P i)⟩

/-- Apply the result to any finite list of polynomials and its literal quotient. -/
theorem quotient_jacobian_cokernel : quotientJacobianCokernel.{u} := by
  intro A _ n m f
  let I := Ideal.span (Set.range f)
  let P : Algebra.Presentation A (JacobianQuotient A n m f) (Fin n) (Fin m) :=
    Algebra.Presentation.naive (v := f)
  have hval (i : Fin n) : P.val i = Ideal.Quotient.mk I (MvPolynomial.X i) := rfl
  have heval : MvPolynomial.aeval P.val = Ideal.Quotient.mkₐ A I := by
    ext i
    rw [MvPolynomial.aeval_X, hval]
    rfl
  have hm : presentationJacobian P = quotientJacobianMatrix A n m f := by
    ext i j
    change MvPolynomial.aeval P.val (MvPolynomial.pderiv i (f j)) = _
    rw [heval]
    rfl
  obtain ⟨e, _, hv⟩ := jacobian_cokernel A (JacobianQuotient A n m f) n m P
  have hc : ∃ e : ((Fin n → JacobianQuotient A n m f) ⧸
      LinearMap.range (presentationJacobian P).mulVecLin) ≃ₗ[JacobianQuotient A n m f]
        KaehlerDifferential A (JacobianQuotient A n m f),
      ∀ i : Fin n, e ((LinearMap.range (presentationJacobian P).mulVecLin).mkQ
        (Pi.single i 1)) = KaehlerDifferential.D A (JacobianQuotient A n m f) (P.val i) :=
    ⟨e, hv⟩
  rw [hm] at hc
  simpa only [hval] using hc

end
end AdvCommAlg.Differentials
