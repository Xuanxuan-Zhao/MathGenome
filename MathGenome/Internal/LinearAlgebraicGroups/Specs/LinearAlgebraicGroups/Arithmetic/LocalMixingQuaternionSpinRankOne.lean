import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuaternionSpinCharacteristicTwo
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.RelativeChambers

open AlgebraicGeometry CategoryTheory ValuativeRel
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.LocalMixingQuaternionSpinRankOne

open _root_.Specs.RM03.CSA (degree isCentralSimple)
open _root_.RM03.Brauer.SemilinearDescent (AlgebraAction)
open _root_.LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport
  (RationalPoints pointTopology)
open _root_.LinearAlgebraicGroups.CocharacterDynamics
  (HasLimit cocharacterPoint oppositeCocharacter)
open CharacterDescent (Cocharacter)
open NontrialitarianSpinModels (DescendedQuadraticPair SpinModel)
open QuaternionSpinScaleCover (QuaternionHyperbolicPresentation spinVectorProjection)
open QuaternionScalarCliffordLift (scalarDiagonal scalarPairMatrix)
open QuaternionSpinCharacteristicTwo (oppositeWords)
open Relative.MaximalSplitTori (IsMaximalSplitTorus)
open Relative.RelativeChambers (IsRegular)
open RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)

noncomputable section

/-- The scalar split rank-one group on the given quaternionic hyperbolic pair,
transported by rational conjugation so that an elementary direction contracts
for the inverse of the given regular cocharacter. The opposite radicals of
its diagonal generate densely in the original group's coordinate topology. -/
def QuaternionSpinRankOne : Prop :=
  ∀ {F K I B : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K] [Fintype I] [DecidableEq I]
    [DivisionRing B] [Algebra F B]
    {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
    {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ}
    (M : SpinModel G D), IsAbsolutelyAlmostSimple G → 4 ≤ Fintype.card I →
    ∀ (hB : isCentralSimple F B), degree F B = 2 →
    ∀ {d : ℕ}, ((2 : F) ≠ 0 → 0 < d) →
    ∀ Q : QuaternionHyperbolicPresentation D hB d,
    ∀ S : ClosedSubgroup G.val, IsMaximalSplitTorus S →
    ∀ c : Cocharacter S.group, IsRegular S c →
      ∃ (A : AffineAlgebraicGroup F)
        (e : (groupPointsFunctor F).obj A.val ≅
          StandardGroups.specialLinearPoints F (ULift.{u} (Fin 2)))
        (j : A.val ⟶ G.val) (b : Cocharacter A.val)
        (g : RationalPoints G.val.X),
        IsClosedImmersion j.hom.hom.left ∧
        (∀ (R : TestAlgebra F) (p : Points A.val.X R),
          let a : CommAlgCat.of F F ⟶ R := CommAlgCat.ofHom (Algebra.ofId F R)
          let gR := mapPoints a g
          let m := (e.hom.app R p).val.submatrix ULift.up ULift.up
          Q.matrixAt R (spinVectorProjection M R (gR⁻¹ * (p ≫ j.hom.hom) * gR)).val =
            scalarPairMatrix R ⟨m, by
              exact (Matrix.det_submatrix_equiv_self
                (Equiv.ulift.symm : Fin 2 ≃ ULift.{u} (Fin 2)) _).trans
                  (e.hom.app R p).property⟩) ∧
        (∀ (R : TestAlgebra F) (t : Rˣ),
          (e.hom.app R (cocharacterPoint b R t)).val.submatrix ULift.up ULift.up =
            (scalarDiagonal t).val) ∧
        let diag := b ≫ j
        let point (R : TestAlgebra F) (z : (StandardGroups.specialLinearPoints
            F (ULift.{u} (Fin 2))).obj R) : Points G.val.X R :=
          e.inv.app R z ≫ j.hom.hom
        let upper (R : TestAlgebra F) (x : R) :=
          point R (Matrix.SpecialLinearGroup.transvection
            (show (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)) ≠ ULift.up 1 by decide) x)
        let lower (R : TestAlgebra F) (x : R) :=
          point R (Matrix.SpecialLinearGroup.transvection
            (show (ULift.up (1 : Fin 2) : ULift.{u} (Fin 2)) ≠ ULift.up 0 by decide) x)
        let R₀ := CommAlgCat.of F F
        (∀ (R : TestAlgebra F) (x : R),
          HasLimit diag (upper R x) 1 ∧ HasLimit (oppositeCocharacter diag) (lower R x) 1) ∧
        ((∀ x : F, HasLimit (oppositeCocharacter (c ≫ S.inclusion)) (upper R₀ x) 1) ∨
          (∀ x : F, HasLimit (oppositeCocharacter (c ≫ S.inclusion)) (lower R₀ x) 1)) ∧
        @Dense (RationalPoints G.val.X) (pointTopology G.val.X)
          {p | p ∈ oppositeWords diag}

end

end LinearAlgebraicGroups.Specs.Arithmetic.LocalMixingQuaternionSpinRankOne
