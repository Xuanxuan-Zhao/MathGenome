import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison

namespace LinearAlgebraicGroups.Specs.ExceptionalPinnedPairCompatibility

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj
open Pinning (BasedRootDatum)
open AdjointRepresentation (GroupPoints)
open AdjointBorelCohomology (PinnedTwist)
open ExceptionalMarkedRootDescent
  (MarkedFibre coordinatePointEquiv pinnedMarkedPoint quadraticIntegralAlgebra)
open ExceptionalIwahoriImageComparison (pinnedGroundPoint)
open ExceptionalIwahoriCongruence (changeRingHom integralRingMap)
open IntegralSemisimpleModel (Model integerAlgebra)

universe u

attribute [local instance] integerAlgebra

/-- A marked comparison of the ambient groups over the coefficient field
restricts to the specified Borels and tori and evaluates on ground sections
via the given tensor field isomorphism. -/
def Statement : Prop :=
  ∀ {F L k K : Type u} [Field F] [Field L] [Field k] [Field K]
    [Algebra F L] [Algebra F k] [Algebra F K] [Algebra k K] [IsScalarTower F k K]
    [FiniteDimensional F L] [IsGalois F L] [FiniteDimensional k K] [IsGalois k K]
    {D : BasedRootDatum.{u}} {M : Model D}
    (C : MarkedFibre M F) (Ck : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {lk : Aut Ck.realization.attached.toBased ≃* Aut Ck.realization.pinned}
    {G : AffineAlgebraicGroup F} {Gk : AffineAlgebraicGroup k}
    {B T : ClosedSubgroup G.val} {Bk Tk : ClosedSubgroup Gk.val}
    (d : PinnedTwist L C.realization.attached l B T)
    (dk : PinnedTwist K Ck.realization.attached lk Bk Tk)
    (e : (L ⊗[F] k) ≃ₐ[F] K),
    (∀ y : k, e ((1 : L) ⊗ₜ[F] y) = algebraMap k K y) →
    ∀ (c : restrictTestAlgebra F k ⋙ quadraticIntegralAlgebra F L ≅
        quadraticIntegralAlgebra k K)
      (j : Gk.val ≅ (groupBaseChange F k).obj G.val),
      (∀ (R : TestAlgebra k) (z : L) (r : R),
        (c.hom.app R).hom
          (show L ⊗[F] ((restrictTestAlgebra F k).obj R) from z ⊗ₜ[F] r) =
          (e (z ⊗ₜ[F] (1 : k))) ⊗ₜ[k] r) →
      (∀ (R : TestAlgebra k) (p : GroupPoints Gk.val R),
        let R₀ := (restrictTestAlgebra F k).obj R
        let x := baseChangePoint F k G.val.X R (p ≫ j.hom.hom.hom)
        pinnedMarkedPoint Ck dk R ((coordinatePointEquiv Gk R).symm p) =
          changeRingHom M.group (c.hom.app R)
            (pinnedMarkedPoint C d R₀ ((coordinatePointEquiv G R₀).symm x))) →
      ∃ (jB : Bk.group ≅ (groupBaseChange F k).obj B.group)
        (jT : Tk.group ≅ (groupBaseChange F k).obj T.group),
        Bk.inclusion ≫ j.hom = jB.hom ≫ (groupBaseChange F k).map B.inclusion ∧
        Tk.inclusion ≫ j.hom = jT.hom ≫ (groupBaseChange F k).map T.inclusion ∧
        ∀ g : 𝟙_ (SchemeOver k) ⟶ Gk.val.X,
          let p : GroupPoints G.val (CommAlgCat.of F k) :=
            baseChangePoint F k G.val.X (CommAlgCat.of k k)
              (CartesianMonoidalCategory.toUnit _ ≫ g ≫ j.hom.hom.hom)
          pinnedGroundPoint Ck dk g =
            changeRingHom M.group (integralRingMap e.toRingHom)
              (pinnedMarkedPoint C d (CommAlgCat.of F k)
                ((coordinatePointEquiv G (CommAlgCat.of F k)).symm p))

end LinearAlgebraicGroups.Specs.ExceptionalPinnedPairCompatibility
