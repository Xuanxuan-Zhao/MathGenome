import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence

namespace LinearAlgebraicGroups.Specs.ExceptionalPinnedGroupComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open Pinning (BasedRootDatum)
open AdjointRepresentation (GroupPoints)
open AutomorphismSequence (AdjointQuotient SplitSequence)
open AdjointBorelCohomology (PinnedTwist)
open ExceptionalMarkedRootDescent (MarkedFibre coordinatePointEquiv pinnedMarkedPoint
  quadraticIntegralAlgebra)
open ExceptionalValuedTorusNormalizer (markedDiagramEquiv)
open ExceptionalIwahoriCongruence (changeRingHom)
open IntegralSemisimpleModel (Model)

universe u

/-- Comparison of the specified quadratic pinned twists under extension of
the coefficient field, on the actual groups and on all test algebras. -/
def Statement : Prop :=
  ∀ {F L k K : Type u} [Field F] [Field L] [Field k] [Field K]
    [Algebra F L] [Algebra F k] [Algebra F K] [Algebra k K] [IsScalarTower F k K]
    [FiniteDimensional F L] [IsGalois F L] [FiniteDimensional k K] [IsGalois k K]
    {D : BasedRootDatum.{u}} {M : Model D} (C : MarkedFibre M F) (Ck : MarkedFibre M k)
    {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
    {lk : Aut Ck.realization.attached.toBased ≃* Aut Ck.realization.pinned}
    {Q : AdjointQuotient C.realization.pinned.pair.G}
    {Qk : AdjointQuotient Ck.realization.pinned.pair.G}
    (_ : SplitSequence C.realization.pinned C.realization.attached l Q)
    (_ : SplitSequence Ck.realization.pinned Ck.realization.attached lk Qk)
    {G : AffineAlgebraicGroup F} {B T : ClosedSubgroup G.val}
    {Gk : AffineAlgebraicGroup k} {Bk Tk : ClosedSubgroup Gk.val}
    (d : PinnedTwist L C.realization.attached l B T)
    (dk : PinnedTwist K Ck.realization.attached lk Bk Tk)
    (σ : Gal(L/F)) (β : Gal(K/k)) (e : (L ⊗[F] k) ≃ₐ[F] K),
    (markedDiagramEquiv C.realization (d.outer σ)).asIso.hom =
      (markedDiagramEquiv Ck.realization (dk.outer β)).asIso.hom →
    Module.finrank F L = 2 → Module.finrank k K = 2 → σ ≠ 1 → β ≠ 1 →
    (∀ y : k, e ((1 : L) ⊗ₜ[F] y) = algebraMap k K y) →
    (∀ z : L, β (e (z ⊗ₜ[F] (1 : k))) = e ((σ z) ⊗ₜ[F] (1 : k))) →
    ∃ (c : restrictTestAlgebra F k ⋙ quadraticIntegralAlgebra F L ≅ quadraticIntegralAlgebra k K)
      (j : Gk.val ≅ (groupBaseChange F k).obj G.val),
      (∀ (R : TestAlgebra k) (z : L) (r : R),
        (c.hom.app R).hom (z ⊗ₜ[F] r) = e (z ⊗ₜ[F] (1 : k)) ⊗ₜ[k] r) ∧
      ∀ (R : TestAlgebra k) (p : GroupPoints Gk.val R),
        let R₀ := (restrictTestAlgebra F k).obj R
        let x := baseChangePoint F k G.val.X R (p ≫ j.hom.hom.hom)
        pinnedMarkedPoint Ck dk R ((coordinatePointEquiv Gk R).symm p) =
          changeRingHom M.group (c.hom.app R)
            (pinnedMarkedPoint C d R₀ ((coordinatePointEquiv G R₀).symm x))

end LinearAlgebraicGroups.Specs.ExceptionalPinnedGroupComparison
