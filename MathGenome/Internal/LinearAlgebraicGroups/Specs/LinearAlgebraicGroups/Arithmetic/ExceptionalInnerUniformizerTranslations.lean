import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalStableAlcoves
import Mathlib.LinearAlgebra.TensorProduct.Basic

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Opposite WithConv
open scoped CategoryTheory.MonObj TensorProduct WithZero

universe u

namespace LinearAlgebraicGroups.Specs.ExceptionalInnerUniformizerTranslations

open ExceptionalAffineRootSystems (ApartmentRoots)
open ExceptionalAffineBruhat (FieldPoints IsUnramifiedLocalExtension SplitLevel scalarPoints)
open ExceptionalAffineBuilding (CoefficientAction EuclideanApartment SplitBuildingLevel Weights
  typeChange)
open ExceptionalIwahoriImageComparison (MarkedCentralCover integralPointHom)
open ExceptionalLocalRootCoordinates (normalizedValuation)
open ExceptionalStableAlcoveRepresentatives (IsArithmeticFrobenius)
open ExceptionalTwistedTraceComparison (PointCocycle Twist extendPoint)
open IntegralSemisimpleModel (Model fibre integerAlgebra forgetFibrePoint)
open Pinning (BasedRootDatum)
open AutomorphismSequence (AdjointQuotient)
open AdjointRepresentation (GroupPoints)
open SteinbergPinnedDescent (comparisonOnPoints)
open StandardGroups (multiplicativePowerGroup multiplicativePowerPoints LaurentPowerCoordinates
  laurentVariable)

attribute [local instance] integerAlgebra

noncomputable section

/-- The element of the split torus obtained by evaluating the cocharacter
with integer coordinates `z` at `π` in the displayed splitting. -/
def uniformizerPoint {F : Type u} [Field F] {H : GroupScheme F}
    (S : ClosedSubgroup H) {r : ℕ}
    (s : (multiplicativePowerGroup F (ULift.{u} (Fin r))).val ≅ S.group)
    (points : (groupPointsFunctor F).obj (multiplicativePowerGroup F (ULift.{u} (Fin r))).val ≅
      multiplicativePowerPoints F (ULift.{u} (Fin r)))
    (π : Fˣ) (z : Fin r → ℤ) : GroupPoints H (CommAlgCat.of F F) :=
  (points.inv.app (CommAlgCat.of F F)) (fun i => π ^ z i.down) ≫
    s.hom.hom.hom ≫ S.inclusion.hom.hom

/-- Finite inner descent and the independent uniformizer translations from
every split torus of the descended group on the given adjoint building. -/
def UniformizerTranslations : Prop :=
  ∀ (F K : Type u) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension F K],
    IsUnramifiedLocalExtension F K →
    ∀ {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
      (c : MarkedCentralCover M M')
      {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
      {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
      (Y : SplitLevel K c p p' e) (B : SplitBuildingLevel Y)
      (G : AffineAlgebraicGroup F) (Q : AdjointQuotient G)
      (iG : G.val ≅ (fibre F).obj M.group) (iQ : Q.quotient.val ≅ (fibre F).obj M'.group),
      Q.projection ≫ iQ.hom = iG.hom ≫ (fibre F).map c.map →
      ∀ (a : PointCocycle (S := K) Q.quotient.val) (T : Twist a),
        let aK := fun σ : Gal(K/F) =>
          forgetFibrePoint M'.group (CommAlgCat.of F K) (a.val σ ≫ iQ.hom.hom.hom)
        ∃ (ρ : Gal(K/F) →* MulAut (FieldPoints M' K))
          (coef : CoefficientAction B.ad ρ (fun _ => 1))
          (twist : Gal(K/F) →* (B.ad.realization.Point ≃ᵢ B.ad.realization.Point)),
          (∀ σ h, ρ σ h = scalarPoints M' σ.toRingHom h) ∧
          (∀ σ x, twist σ x = B.adjoint.action (aK σ) (coef.action σ x)) ∧
          (∀ σ, IsArithmeticFrobenius σ → ∀ g t,
            ∃ (h : Y.ad.G₀) (s : Weights ((ApartmentRoots.split E.datum ℚ).SimpleWall p')),
              twist σ (B.ad.realization.place g t) = B.ad.realization.place h s ∧
              ∀ i, s.val (Y.typeQuotient.wallPerm (typeChange Y.typeQuotient (aK σ)) i) =
                t.val i) ∧
          ∀ (S : ClosedSubgroup T.group.val) (r : ℕ)
            (s : (multiplicativePowerGroup F (ULift.{u} (Fin r))).val ≅ S.group)
            (π : Fˣ), normalizedValuation F (π : F) = WithZero.exp (-1 : ℤ) →
            ∃ (points :
                (groupPointsFunctor F).obj (multiplicativePowerGroup F (ULift.{u} (Fin r))).val ≅
                  multiplicativePowerPoints F (ULift.{u} (Fin r)))
              (coordinates : convolutionPoints
                  (CommHopfAlgCat.of F (LaurentPowerCoordinates F (ULift.{u} (Fin r)))) ≅
                (groupPointsFunctor F).obj (multiplicativePowerGroup F (ULift.{u} (Fin r))).val)
              (lattice : Multiplicative (Fin r → ℤ) →* FieldPoints M' K)
              (g : Y.ad.G₀) (v : (Fin r → ℝ) →ₗ[ℝ] EuclideanApartment (ℚ ⊗[ℤ] E.Y)),
              (∀ (R : TestAlgebra F) (f : LaurentPowerCoordinates F (ULift.{u} (Fin r)) →ₐ[F] R),
                (coordinates.hom.app R (toConv f) :
                  GroupPoints (multiplicativePowerGroup F (ULift.{u} (Fin r))).val R).left =
                    Spec.map (CommRingCat.ofHom f.toRingHom) ∧
                ∀ i, ((points.hom.app R (coordinates.hom.app R (toConv f)) :
                  ULift.{u} (Fin r) → Rˣ) i).val = f (laurentVariable F (ULift.{u} (Fin r)) i)) ∧
              (∀ z, lattice (Multiplicative.ofAdd z) =
                let y := (comparisonOnPoints T.trivialization).symm
                  (extendPoint (uniformizerPoint S s points π z))
                let yK := forgetFibrePoint M.group (CommAlgCat.of F K) (y ≫ iG.hom.hom.hom)
                integralPointHom c.map (CommAlgCat.of IntegralSemisimpleModel.Integers.{u} K) yK) ∧
              Function.Injective v ∧
              (∀ z σ x, B.adjoint.action (lattice z) (twist σ x) =
                twist σ (B.adjoint.action (lattice z) x)) ∧
              ∀ (z : Fin r → ℤ) x,
                B.adjoint.action (lattice (Multiplicative.ofAdd z))
                    (B.ad.realization.chart g x) =
                  B.ad.realization.chart g (x + v (fun i => (z i : ℝ)))

end
end LinearAlgebraicGroups.Specs.ExceptionalInnerUniformizerTranslations
