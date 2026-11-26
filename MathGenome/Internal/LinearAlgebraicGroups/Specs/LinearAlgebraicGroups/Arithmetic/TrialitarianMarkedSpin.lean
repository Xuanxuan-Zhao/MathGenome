import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertDescent

namespace LinearAlgebraicGroups.Specs.Arithmetic.TrialitarianMarkedSpin

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj TensorProduct
open LinearAlgebraicGroups.Albert
open LinearAlgebraicGroups.Arithmetic.TrialitarianAlbertDescentSpecification
open LinearAlgebraicGroups.Composition.ZornSpecification (norm)
open SpinSpecification (SchemePoints ScalarClifford IsSpinPointRepresentation vectors conjugate)

universe u

set_option autoImplicit false

/-- The spin comparison for the given cubic stabilizer, with its vector action on
the block indexed by the embedding defined by (E → S). -/
def MarkedSpinComparison : Prop :=
  ∀ (F E S : Type u) [Field F] [Field E] [Field S]
    [Algebra F E] [Algebra F S] [Algebra E S] [IsScalarTower F E S]
    [Module.Finite F E] [Algebra.IsSeparable F E] [IsSepClosure F S],
    Module.finrank F E = 3 →
    ∀ (G : AffineAlgebraicGroup F) (D : DiagramPresentation G E S)
      (J : AlbertModel F) (B : CubicStabilizer J E) (r : G.val ≅ B.stabilizer.group)
      (t : S ⊗[F] J.V ≃ₗ[S] TrialitySpecification.Model S),
      t (1 ⊗ₜ[F] J.law.unit) = CubicSpecification.cubicUnit →
      (∀ x y, t (J.law.op S x y) = TrialitySpecification.modelOp (t x) (t y)) →
      (∀ e : E, t (1 ⊗ₜ[F] B.diagonal e) = (fun i => D.numbering.symm i e, 0)) →
      ∀ (q : QuadraticForm E (Fin 8 → E)), LinearMap.ker q.polarBilin = ⊥ →
      ∀ (j₀ : (Fin 8 → E) →ₗ[E] E ⊗[F] J.V), Function.Injective j₀ →
      ∀ (d : (CliffordSpecification.coefficientForm S q (Pi.basisFun E (Fin 8))).IsometryEquiv
          (norm S)),
        (∀ v : Fin 8 → E,
          t (TensorProduct.map (IsScalarTower.toAlgHom F E S).toLinearMap LinearMap.id (j₀ v)) =
            CubicSpecification.singleBlockCoordinates (D.numbering (IsScalarTower.toAlgHom F E S))
              (d (1 ⊗ₜ[E] v))) →
        ∃ p : ∀ R : TestAlgebra E, SchemePoints ((groupBaseChange F E).obj G.val) R →*
            (ScalarClifford q R)ˣ,
          IsSpinPointRepresentation q ((groupBaseChange F E).obj G.val) p ∧
          ∀ (R : TestAlgebra E) (g : SchemePoints ((groupBaseChange F E).obj G.val) R),
            let R₀ := (restrictTestAlgebra F E).obj R
            letI : Algebra F R := inferInstanceAs (Algebra F R₀)
            letI : IsScalarTower F E R := IsScalarTower.of_algebraMap_eq' rfl
            let j_R := (TensorProduct.AlgebraTensorModule.cancelBaseChange F E R R J.V).toLinearMap ∘ₗ
              j₀.baseChange R
            let g₀ := baseChangePoint F E G.val.X R g
            let a := J.action R₀ (g₀ ≫ r.hom.hom.hom ≫ B.stabilizer.inclusion.hom.hom)
            ∀ x : R ⊗[E] (Fin 8 → E), ∃ y : R ⊗[E] (Fin 8 → E),
              j_R y = a (j_R x) ∧ vectors q R y = conjugate q R (p R g) (vectors q R x)

end LinearAlgebraicGroups.Specs.Arithmetic.TrialitarianMarkedSpin
