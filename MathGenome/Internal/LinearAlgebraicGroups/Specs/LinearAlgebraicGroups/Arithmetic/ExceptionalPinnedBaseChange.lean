import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalLocalRootCoordinates
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriCongruence

namespace LinearAlgebraicGroups.Specs.ExceptionalPinnedBaseChange

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open Pinning (BasedRootDatum)
open AdjointRepresentation (GroupPoints)
open AutomorphismSequence (AdjointQuotient SplitSequence)
open PinnedPairDescent (DescendedPair)
open ExceptionalMarkedRootDescent (MarkedFibre pinnedMarkedPoint coordinatePointEquiv)
open ExceptionalIwahoriImageComparison (pinnedGroundPoint)
open ExceptionalIwahoriCongruence (changeRingHom integralRingMap)
open ExceptionalValuedTorusNormalizer (markedDiagramEquiv)
open Relative.MaximalSplitTori (IsMaximalSplitTorus)

universe u

attribute [local instance] IntegralSemisimpleModel.integerAlgebra

section TensorFields

variable (F L k K : Type u) [Field F] [Field L] [Field k] [Field K]
  [Algebra F L] [Algebra F k] [Algebra F K] [Algebra k K] [IsScalarTower F k K]

/-- In the field compositum the two inclusions are the images of the
given tensor factors. The involution over the coefficient field is the
extension of the original diagram involution. -/
def ExtendsDiagram (σ : Gal(L/F)) (β : Gal(K/k))
    (e : (L ⊗[F] k) ≃ₐ[F] K) : Prop :=
  (∀ y : k, e ((1 : L) ⊗ₜ[F] y) = algebraMap k K y) ∧
  ∀ z : L, β (e (z ⊗ₜ[F] (1 : k))) = e ((σ z) ⊗ₜ[F] (1 : k))

end TensorFields

section Comparisons

/-- Extension of the given marked pinned descent under an actual tensor
field compositum, with the point comparison on coefficient-field points. -/
def Statement : Prop :=
  ∀ {F L : Type u} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  {D : BasedRootDatum.{u}} {M : IntegralSemisimpleModel.Model D}
  (C : MarkedFibre M F) {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
  {Q : AdjointQuotient C.realization.pinned.pair.G}
  {ω : Gal(L/F) →* Aut C.realization.attached.toBased}
  (d : DescendedPair L (l := l) ω) (σ : Gal(L/F)),
  SplitSequence C.realization.pinned C.realization.attached l Q →
  Module.finrank F L = 2 → σ ≠ 1 →
  (D.datum.corootSpan ℤ = ⊤ ∨ D.datum.rootSpan ℤ = ⊤) →
  ∀ (k K : Type u) [Field k] [Field K] [Algebra F k] [Algebra F K] [Algebra k K]
    [IsScalarTower F k K] [FiniteDimensional k K] [IsGalois k K],
    Module.finrank k K = 2 →
    ∀ (β : Gal(K/k)), β ≠ 1 →
    ∀ (e : (L ⊗[F] k) ≃ₐ[F] K), ExtendsDiagram F L k K σ β e →
    ∃ (Ck : MarkedFibre M k)
      (lk : Aut Ck.realization.attached.toBased ≃* Aut Ck.realization.pinned)
      (Qk : AdjointQuotient Ck.realization.pinned.pair.G)
      (ωk : Gal(K/k) →* Aut Ck.realization.attached.toBased)
      (dk : DescendedPair K (l := lk) ωk)
      (_ : SplitSequence Ck.realization.pinned Ck.realization.attached lk Qk),
      (markedDiagramEquiv Ck.realization (dk.data.outer β)).asIso.hom =
        (markedDiagramEquiv C.realization (d.data.outer σ)).asIso.hom ∧
      let B := groupBaseChange F k
      ∃ (j : dk.group.val ≅ B.obj d.group.val)
        (jB : dk.borel.group ≅ B.obj d.borel.group)
        (jT : dk.torus.group ≅ B.obj d.torus.group),
        dk.borel.inclusion ≫ j.hom = jB.hom ≫ B.map d.borel.inclusion ∧
        dk.torus.inclusion ≫ j.hom = jT.hom ≫ B.map d.torus.inclusion ∧
        ∀ g : 𝟙_ (SchemeOver k) ⟶ dk.group.val.X,
          let t := CommAlgCat.of k k
          let p : GroupPoints d.group.val (CommAlgCat.of F k) :=
            baseChangePoint F k d.group.val.X t
              (CartesianMonoidalCategory.toUnit _ ≫ g ≫ j.hom.hom.hom)
          pinnedGroundPoint Ck dk.data g =
            changeRingHom M.group (integralRingMap e.toRingHom)
              (pinnedMarkedPoint C d.data (CommAlgCat.of F k)
                ((coordinatePointEquiv d.group (CommAlgCat.of F k)).symm p))

/-- The maximal split subtorus of the pinned torus stays maximal under
scalar extension that retains the same quadratic diagram field. The
torus and subtorus have the same normalizing points at these levels. -/
def SplitTorusAtLevels : Prop :=
  ∀ {F L : Type u} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  {D : BasedRootDatum.{u}} {M : IntegralSemisimpleModel.Model D}
  (C : MarkedFibre M F) {l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned}
  {Q : AdjointQuotient C.realization.pinned.pair.G}
  {ω : Gal(L/F) →* Aut C.realization.attached.toBased}
  (d : DescendedPair L (l := l) ω) (σ : Gal(L/F)),
  SplitSequence C.realization.pinned C.realization.attached l Q →
  Module.finrank F L = 2 → σ ≠ 1 →
  (D.datum.corootSpan ℤ = ⊤ ∨ D.datum.rootSpan ℤ = ⊤) →
  ∃ S : ClosedSubgroup d.group.val,
    SchemeDerivedGroup.IsSubgroupOf S d.torus ∧ IsMaximalSplitTorus S ∧
    (∀ U : ClosedSubgroup d.group.val, GeometricRadicals.IsSplitTorus U.group →
      SchemeDerivedGroup.IsSubgroupOf U d.torus → SchemeDerivedGroup.IsSubgroupOf U S) ∧
    (∀ g : GroupPoints d.group.val (CommAlgCat.of F F),
      Normalizes S.inclusion g ↔ Normalizes d.torus.inclusion g) ∧
    ∀ (k K : Type u) [Field k] [Field K] [Algebra F k] [Algebra F K] [Algebra k K]
      [IsScalarTower F k K] [FiniteDimensional k K] [IsGalois k K],
      Module.finrank k K = 2 →
      ∀ (β : Gal(K/k)), β ≠ 1 →
      ∀ (e : (L ⊗[F] k) ≃ₐ[F] K), ExtendsDiagram F L k K σ β e →
      ∃ h : IsClosedImmersion ((groupBaseChange F k).map S.inclusion).hom.hom.left,
        IsMaximalSplitTorus (GeometricRadicals.baseChangedSubgroup k S h) ∧
        ∀ g : GroupPoints d.group.val (CommAlgCat.of F k),
          Normalizes S.inclusion g ↔ Normalizes d.torus.inclusion g

end Comparisons
end LinearAlgebraicGroups.Specs.ExceptionalPinnedBaseChange
