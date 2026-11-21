import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.SquareJacobianCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Etale.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.StandardPresentation
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-! The global square Jacobian criterion, ET-03. -/
namespace AdvCommAlg.Etale

universe u v
noncomputable section

open Specs.AdvCommAlg.Differentials
open Specs.AdvCommAlg.Etale

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- With the identity choice of rows, the selected minor is the full Jacobian. -/
theorem jacobian_eq_full_determinant {n : ℕ}
    (P : Algebra.PreSubmersivePresentation A B (Fin n) (Fin n))
    (hmap : P.map = id) :
    P.jacobian = (presentationJacobian P.toPresentation).det := by
  simpa [Specs.AdvCommAlg.Smooth.selectedMinor, hmap,
    Function.Embedding.coe_refl, Matrix.submatrix_id_id] using
    (Smooth.selected_minor_jacobian P)

theorem etale_iff_square_presentation : squarePresentationCriterion.{u,v} := by
  intro A B _ _ _
  change Algebra.Etale A B ↔ _
  rw [Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero]
  constructor
  · intro h
    obtain ⟨ι, σ, hσ, hι, P, hd⟩ := h.out
    letI := hσ
    letI := hι
    letI := Fintype.ofFinite ι
    letI := Fintype.ofFinite σ
    have hle : Nat.card ι ≤ Nat.card σ := by
      exact Nat.sub_eq_zero_iff_le.mp hd
    have heq : Fintype.card σ = Fintype.card ι := by
      apply Nat.le_antisymm
      · exact Fintype.card_le_of_injective P.map P.map_inj
      · simpa only [Nat.card_eq_fintype_card] using hle
    let e : σ ≃ ι := Equiv.ofBijective P.map
      ((Fintype.bijective_iff_injective_and_card _).mpr ⟨P.map_inj, heq⟩)
    let f := (Fintype.equivFin σ).symm
    let Q := P.reindex (f.trans e) f
    have hmap : Q.map = id := by
      funext i
      change (f.trans e).symm (P.map (f i)) = i
      exact (f.trans e).symm_apply_apply i
    refine ⟨Fintype.card σ, Q.toPresentation, ?_⟩
    rw [← jacobian_eq_full_determinant Q.toPreSubmersivePresentation hmap]
    exact Q.jacobian_isUnit
  · rintro ⟨n, P, hP⟩
    let Q : Algebra.PreSubmersivePresentation A B (Fin n) (Fin n) :=
      { P with map := id, map_inj := Function.injective_id }
    let Q' : Algebra.SubmersivePresentation A B (Fin n) (Fin n) :=
      { Q with
        jacobian_isUnit := by
          rw [jacobian_eq_full_determinant Q rfl]
          exact hP }
    exact Q'.isStandardSmoothOfRelativeDimension (by
      simp [Algebra.Presentation.dimension])

/-- The isomorphism associated to a presentation evaluates each polynomial
at the specified generators, after passing to the literal relation quotient. -/
theorem presentation_quotient_equiv {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B] {n m : ℕ}
    (P : Algebra.Presentation A B (Fin n) (Fin m)) :
    ∃ e : JacobianQuotient A n m P.relation ≃ₐ[A] B,
      ∀ p, e (Ideal.Quotient.mk _ p) = MvPolynomial.aeval P.val p := by
  let e := (Ideal.quotientEquivAlgOfEq A P.span_range_relation_eq_ker).trans
    (P.quotientEquiv.restrictScalars A)
  refine ⟨e, fun p => ?_⟩
  change P.quotientEquiv (Ideal.quotientEquivAlgOfEq A
    P.span_range_relation_eq_ker (Ideal.Quotient.mk _ p)) = _
  rw [Ideal.quotientEquivAlgOfEq_mk, P.quotientEquiv_mk, P.algebraMap_apply]

theorem square_jacobian_criterion : squareJacobianCriterion.{u,v} := by
  intro A B _ _ _
  rw [etale_iff_square_presentation A B]
  constructor
  · rintro ⟨n, P, hP⟩
    obtain ⟨e, he⟩ := presentation_quotient_equiv P
    refine ⟨n, P.relation, e.symm, ?_⟩
    have hm : e.toRingHom.mapMatrix (quotientJacobianMatrix A n n P.relation) =
        presentationJacobian P := by
      ext i j
      exact he (MvPolynomial.pderiv i (P.relation j))
    change IsUnit (e.toRingHom (quotientJacobianMatrix A n n P.relation).det)
    rw [RingHom.map_det, hm]
    exact hP
  · rintro ⟨n, f, e, he⟩
    let P₀ : Algebra.Presentation A (JacobianQuotient A n n f) (Fin n) (Fin n) :=
      Algebra.Presentation.naive (v := f)
    let P := P₀.ofAlgEquiv e.symm
    have heval : MvPolynomial.aeval P.val =
        e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ A (Ideal.span (Set.range f))) := by
      ext i
      rw [MvPolynomial.aeval_X]
      rfl
    have hm : presentationJacobian P =
        e.symm.toRingHom.mapMatrix (quotientJacobianMatrix A n n f) := by
      ext i j
      change MvPolynomial.aeval P.val (MvPolynomial.pderiv i (f j)) = _
      rw [heval]
      rfl
    refine ⟨n, P, ?_⟩
    rw [hm, ← RingHom.map_det]
    exact he

theorem empty_square_jacobian : emptySquareJacobian.{u} := by
  intro A _ f
  exact Matrix.det_isEmpty

end
end AdvCommAlg.Etale
